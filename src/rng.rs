use crate::arch_util::{CpuArchInfo};
use crate::io_util::{ReadBytesExt, WriteBytesExt, LE};
use crate::log::*;

use std::cmp::{min};
use std::fmt;
use std::io::{Read, Write, Error as IoError, Cursor};
use std::mem::{align_of, size_of};
use std::ptr;
use std::slice::{from_raw_parts};

/* rand_core:

Copyright 2018 Developers of the Rand project.

Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
<LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
option. This file may not be copied, modified, or distributed
except according to those terms. */

pub type RngError = ();

pub trait RngCore {
  fn next_u32(&mut self) -> u32;
  fn next_u64(&mut self) -> u64;
  fn fill_bytes(&mut self, dst: &mut [u8]);
  fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), RngError>;
}

pub trait SeedableRng: Sized {
  type Seed: Sized + AsMut<[u8]> + Default;

  fn from_seed(seed: Self::Seed) -> Self;

  fn from_rng<R: RngCore>(mut rng: R) -> Result<Self, RngError> {
    let mut seed = Self::Seed::default();
    rng.try_fill_bytes(seed.as_mut())?;
    Ok(Self::from_seed(seed))
  }
}

fn fill_via_chunks<U: Copy>(src: &[U], dst: &mut [u8]) -> (usize, usize) {
  let chunk_size_u8 = min(src.len() * size_of::<U>(), dst.len());
  let chunk_size = (chunk_size_u8 + size_of::<U>() - 1) / size_of::<U>();
  unsafe {
    let p = src.as_ptr() as *const u8;
    ptr::copy_nonoverlapping(p, dst.as_mut_ptr(), chunk_size_u8);
  }
  (chunk_size, chunk_size_u8)
}

pub trait BlockRngCore {
  type Item;
  type Results: AsRef<[Self::Item]> + AsMut<[Self::Item]> + Default;

  fn generate(&mut self, results: &mut Self::Results);
}

#[derive(Clone)]
pub struct BlockRng32<R: BlockRngCore + ?Sized> {
  results: R::Results,
  index: usize,
  unalign64: bool,
  pub core: R,
}

// Custom Debug implementation that does not expose the contents of `results`.
impl<R: BlockRngCore + fmt::Debug> fmt::Debug for BlockRng32<R> {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    fmt.debug_struct("BlockRng")
      .field("core", &self.core)
      .field("result_len", &self.results.as_ref().len())
      .field("index", &self.index)
      .field("unalign64", &self.unalign64)
      .finish()
  }
}

impl<R: BlockRngCore> BlockRng32<R> {
  #[inline]
  pub fn new(core: R) -> BlockRng32<R> {
    let results = R::Results::default();
    assert!(!results.as_ref().is_empty());
    let align_offset64 = results.as_ref().as_ptr().align_offset(align_of::<u64>());
    assert!(align_offset64 != usize::max_value());
    let unalign64 = match align_offset64 {
      0 => false,
      1 => true,
      _ => unreachable!()
    };
    BlockRng32{
      core,
      unalign64,
      index: results.as_ref().len(),
      results,
    }
  }

  #[inline]
  pub fn generate_and_set(&mut self, index: usize) {
    assert!(index <= self.results.as_ref().len());
    self.core.generate(&mut self.results);
    self.index = index;
  }
}

impl<R: BlockRngCore<Item=u32>> RngCore for BlockRng32<R>
where <R as BlockRngCore>::Results: AsRef<[u32]> + AsMut<[u32]>
{
  #[inline]
  fn next_u32(&mut self) -> u32 {
    let index = self.index;
    if index >= self.results.as_ref().len() {
      self.generate_and_set(1);
      self.results.as_ref()[0]
    } else {
      self.index += 1;
      self.results.as_ref()[index]
    }
  }

  #[inline]
  fn next_u64(&mut self) -> u64 {
    let len = self.results.as_ref().len();
    let index = self.index;
    if index >= len {
      self.generate_and_set(2);
      unsafe {
        if self.unalign64 {
          ptr::read_unaligned(self.results.as_ref().as_ptr() as *const u64)
        } else {
          ptr::read(self.results.as_ref().as_ptr() as *const u64)
        }
      }
    } else if index < len - 1 {
      self.index += 2;
      let offset32 = (index & 1) ^ (if self.unalign64 { 1 } else { 0 });
      unsafe {
        if offset32 != 0 {
          ptr::read_unaligned(self.results.as_ref()[index..].as_ptr() as *const u64)
        } else {
          ptr::read(self.results.as_ref()[index..].as_ptr() as *const u64)
        }
      }
    } else {
      let x = self.results.as_ref()[len - 1] as u64;
      self.generate_and_set(1);
      let y = self.results.as_ref()[0] as u64;
      x | (y << 32)
    }
  }

  #[inline]
  fn fill_bytes(&mut self, dst: &mut [u8]) {
    let mut read_len = 0;
    while read_len < dst.len() {
      if self.index >= self.results.as_ref().len() {
        self.generate_and_set(0);
      }
      let (consumed_u32, filled_u8) = fill_via_chunks(
          &self.results.as_ref()[self.index..],
          &mut dst[read_len..],
      );
      self.index += consumed_u32;
      read_len += filled_u8;
    }
  }

  #[inline(always)]
  fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), RngError> {
    self.fill_bytes(dst);
    Ok(())
  }
}

impl<R: BlockRngCore + SeedableRng> SeedableRng for BlockRng32<R> {
  type Seed = R::Seed;

  #[inline(always)]
  fn from_seed(seed: Self::Seed) -> Self {
    Self::new(R::from_seed(seed))
  }

  #[inline(always)]
  fn from_rng<S: RngCore>(rng: S) -> Result<Self, RngError> {
    Ok(Self::new(R::from_rng(rng)?))
  }
}


#[derive(Clone)]
pub struct BlockRng64<R: BlockRngCore + ?Sized> {
  results: R::Results,
  index: usize,
  half_used: bool, // true if only half of the previous result is used
  pub core: R,
}

// Custom Debug implementation that does not expose the contents of `results`.
impl<R: BlockRngCore + fmt::Debug> fmt::Debug for BlockRng64<R> {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    fmt.debug_struct("BlockRng64")
      .field("core", &self.core)
      .field("result_len", &self.results.as_ref().len())
      .field("index", &self.index)
      .field("half_used", &self.half_used)
      .finish()
  }
}

impl<R: BlockRngCore> BlockRng64<R> {
  #[inline]
  pub fn new(core: R) -> BlockRng64<R> {
    let results = R::Results::default();
    assert!(!results.as_ref().is_empty());
    BlockRng64{
      core,
      index: results.as_ref().len(),
      half_used: false,
      results,
    }
  }

  #[inline]
  pub fn generate_and_set(&mut self, index: usize, half_used: bool) {
    assert!(index <= self.results.as_ref().len());
    self.core.generate(&mut self.results);
    self.index = index;
    self.half_used = half_used;
  }
}

impl<R: BlockRngCore<Item=u64>> RngCore for BlockRng64<R>
where <R as BlockRngCore>::Results: AsRef<[u64]> + AsMut<[u64]>
{
  #[inline]
  fn next_u32(&mut self) -> u32 {
    let len_u32 = self.results.as_ref().len() * 2;
    let prev_half_offset = if self.half_used { 1 } else { 0 };
    let mut index = self.index * 2 - prev_half_offset;
    if index >= len_u32 {
      self.generate_and_set(0, false);
      index = 0;
    }
    self.half_used = !self.half_used;
    let next_half_offset = if self.half_used { 1 } else { 0 };
    self.index += next_half_offset;
    unsafe {
      let p = self.results.as_ref().as_ptr() as *const u32;
      let results = from_raw_parts(p, len_u32);
      results[index]
    }
  }

  #[inline]
  fn next_u64(&mut self) -> u64 {
    let index = self.index;
    if index >= self.results.as_ref().len() {
      self.generate_and_set(1, false);
      self.results.as_ref()[0]
    } else {
      self.index += 1;
      self.results.as_ref()[index]
    }
  }

  #[inline]
  fn fill_bytes(&mut self, dst: &mut [u8]) {
    let mut read_len = 0;
    self.half_used = false;
    while read_len < dst.len() {
      if self.index >= self.results.as_ref().len() {
        self.generate_and_set(0, false);
      }
      let (consumed_u64, filled_u8) = fill_via_chunks(
          &self.results.as_ref()[self.index..],
          &mut dst[read_len..],
      );
      self.index += consumed_u64;
      read_len += filled_u8;
    }
  }

  #[inline(always)]
  fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), RngError> {
    self.fill_bytes(dst);
    Ok(())
  }
}

impl<R: BlockRngCore + SeedableRng> SeedableRng for BlockRng64<R> {
  type Seed = R::Seed;

  #[inline(always)]
  fn from_seed(seed: Self::Seed) -> Self {
    Self::new(R::from_seed(seed))
  }

  #[inline(always)]
  fn from_rng<S: RngCore>(rng: S) -> Result<Self, RngError> {
    Ok(Self::new(R::from_rng(rng)?))
  }
}

/* The rdseed-based entropy source is derived from nagisa's rdrand crate:

Copyright (c) 2014, Simonas Kazlauskas <rdrand@kazlauskas.me>

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
*/

pub struct EntropySource{_mrk: ()}

#[cfg(target_arch = "x86_64")]
impl Default for EntropySource {
  fn default() -> EntropySource {
    if CpuArchInfo::cached().rdseed {
      EntropySource{_mrk: ()}
    } else {
      panic!("bug: EntropySource requires rdseed on x86_64");
    }
  }
}

#[cfg(target_arch = "x86_64")]
impl EntropySource {
  #[inline]
  pub fn retry_next_u64(&mut self, max_iters: usize) -> Option<u64> {
    let mut x: u64 = 0;
    for _ in 0 .. max_iters {
      if unsafe { std::arch::x86_64::_rdseed64_step(&mut x) } != 0 {
        return Some(x);
      }
    }
    None
  }
}

#[cfg(target_arch = "x86_64")]
impl BlockRngCore for EntropySource {
  type Item = u64;
  type Results = [u64; 1];

  #[inline]
  fn generate(&mut self, results: &mut [u64; 1]) {
    loop {
      match self.retry_next_u64(128) {
        None => {
          // FIXME: sleep.
        }
        Some(u) => {
          results[0] = u;
          return;
        }
      }
    }
  }
}

pub struct EntropyRng {
  rng:  BlockRng64<EntropySource>,
}

#[cfg(target_arch = "x86_64")]
impl Default for EntropyRng {
  #[inline(always)]
  fn default() -> EntropyRng {
    EntropyRng{
      rng:  BlockRng64::new(EntropySource::default()),
    }
  }
}

#[cfg(target_arch = "x86_64")]
impl RngCore for EntropyRng {
  #[inline(always)]
  fn next_u32(&mut self) -> u32 {
    let x = self.rng.next_u32();
    if log_debug() {
      println!("DEBUG: EntropyRng::next_u32: x={}", x);
    }
    x
  }

  #[inline(always)]
  fn next_u64(&mut self) -> u64 {
    let x = self.rng.next_u64();
    if log_debug() {
      println!("DEBUG: EntropyRng::next_u64: x={}", x);
    }
    x
  }

  #[inline(always)]
  fn fill_bytes(&mut self, dst: &mut [u8]) {
    self.rng.fill_bytes(dst);
    if log_debug() {
      println!("DEBUG: EntropyRng::fill_bytes: buf={:?}", dst);
    }
  }

  #[inline(always)]
  fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), RngError> {
    let res = self.rng.try_fill_bytes(dst);
    if log_debug() {
      if res.is_err() {
        println!("DEBUG: EntropyRng::try_fill_bytes: error");
      } else {
        println!("DEBUG: EntropyRng::try_fill_bytes: buf={:?}", dst);
      }
    }
    res
  }
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct ChaCha20State {
  state:    [u32; 16],
}

impl ChaCha20State {
  pub fn zeroed() -> ChaCha20State {
    ChaCha20State{
      state:    [0; 16],
    }
  }

  pub fn initialize<R: Read>(&mut self, constant: Option<&[u8; 16]>, counter: u64, nonce: u64, key: &mut R) -> Result<(), IoError> {
    assert!(counter != 0);
    let mut constant = Cursor::new(match constant {
      /*None => b"Reproducibility!",*/
      None => b"extend 32-byte k",
      Some(c) => c,
    });
    self.state[0]  = constant.read_u32::<LE>()?;
    self.state[1]  = constant.read_u32::<LE>()?;
    self.state[2]  = constant.read_u32::<LE>()?;
    self.state[3]  = constant.read_u32::<LE>()?;
    self.state[4]  = key.read_u32::<LE>()?;
    self.state[5]  = key.read_u32::<LE>()?;
    self.state[6]  = key.read_u32::<LE>()?;
    self.state[7]  = key.read_u32::<LE>()?;
    self.state[8]  = key.read_u32::<LE>()?;
    self.state[9]  = key.read_u32::<LE>()?;
    self.state[10] = key.read_u32::<LE>()?;
    self.state[11] = key.read_u32::<LE>()?;
    const MASK_LO_32: u64 = 0xffff_ffff_u64;
    self.state[12] = (counter & MASK_LO_32) as u32;
    self.state[13] = ((counter >> 32) & MASK_LO_32) as u32;
    self.state[14] = (nonce & MASK_LO_32) as u32;
    self.state[15] = ((nonce >> 32) & MASK_LO_32) as u32;
    Ok(())
  }

  pub fn restore<R: Read>(&mut self, buf: &mut R) -> Result<usize, IoError> {
    self.state[0]  = buf.read_u32::<LE>()?;
    self.state[1]  = buf.read_u32::<LE>()?;
    self.state[2]  = buf.read_u32::<LE>()?;
    self.state[3]  = buf.read_u32::<LE>()?;
    self.state[4]  = buf.read_u32::<LE>()?;
    self.state[5]  = buf.read_u32::<LE>()?;
    self.state[6]  = buf.read_u32::<LE>()?;
    self.state[7]  = buf.read_u32::<LE>()?;
    self.state[8]  = buf.read_u32::<LE>()?;
    self.state[9]  = buf.read_u32::<LE>()?;
    self.state[10] = buf.read_u32::<LE>()?;
    self.state[11] = buf.read_u32::<LE>()?;
    self.state[12] = buf.read_u32::<LE>()?;
    self.state[13] = buf.read_u32::<LE>()?;
    self.state[14] = buf.read_u32::<LE>()?;
    self.state[15] = buf.read_u32::<LE>()?;
    Ok(64)
  }

  pub fn save<W: Write>(&self, buf: &mut W) -> Result<usize, IoError> {
    buf.write_u32::<LE>(self.state[0])?;
    buf.write_u32::<LE>(self.state[1])?;
    buf.write_u32::<LE>(self.state[2])?;
    buf.write_u32::<LE>(self.state[3])?;
    buf.write_u32::<LE>(self.state[4])?;
    buf.write_u32::<LE>(self.state[5])?;
    buf.write_u32::<LE>(self.state[6])?;
    buf.write_u32::<LE>(self.state[7])?;
    buf.write_u32::<LE>(self.state[8])?;
    buf.write_u32::<LE>(self.state[9])?;
    buf.write_u32::<LE>(self.state[10])?;
    buf.write_u32::<LE>(self.state[11])?;
    buf.write_u32::<LE>(self.state[12])?;
    buf.write_u32::<LE>(self.state[13])?;
    buf.write_u32::<LE>(self.state[14])?;
    buf.write_u32::<LE>(self.state[15])?;
    Ok(64)
  }
}

impl ChaCha20State {
  #[inline(always)]
  pub fn _quarter_round(a: &mut u32, b: &mut u32, c: &mut u32, d: &mut u32) {
    *a += *b; *d = (*d ^ *a).rotate_left(16);
    *c += *d; *b = (*b ^ *c).rotate_left(12);
    *a += *b; *d = (*d ^ *a).rotate_left(8);
    *c += *d; *b = (*b ^ *c).rotate_left(7);
  }
}

impl BlockRngCore for ChaCha20State {
  type Item = u32;
  type Results = [u32; 16];

  /*#[inline]
  fn generate(&mut self, results: &mut [u32; 16]) {
    unsafe {
      let mut x0 = *self.state.get_unchecked(0);
      let mut x1 = *self.state.get_unchecked(1);
      let mut x2 = *self.state.get_unchecked(2);
      let mut x3 = *self.state.get_unchecked(3);
      let mut x4 = *self.state.get_unchecked(4);
      let mut x5 = *self.state.get_unchecked(5);
      let mut x6 = *self.state.get_unchecked(6);
      let mut x7 = *self.state.get_unchecked(7);
      let mut x8 = *self.state.get_unchecked(8);
      let mut x9 = *self.state.get_unchecked(9);
      let mut x10 = *self.state.get_unchecked(10);
      let mut x11 = *self.state.get_unchecked(11);
      let mut x12 = *self.state.get_unchecked(12);
      let mut x13 = *self.state.get_unchecked(13);
      let mut x14 = *self.state.get_unchecked(14);
      let mut x15 = *self.state.get_unchecked(15);
      let mut counter = (x12 as u64) | ((x13 as u64) << 32);
      assert!(counter != 0);
      for _ in 0 .. 10 {
        ChaCha20State::_quarter_round(&mut x0, &mut x4, &mut x8, &mut x12);
        ChaCha20State::_quarter_round(&mut x1, &mut x5, &mut x9, &mut x13);
        ChaCha20State::_quarter_round(&mut x2, &mut x6, &mut x10, &mut x14);
        ChaCha20State::_quarter_round(&mut x3, &mut x7, &mut x11, &mut x15);
        ChaCha20State::_quarter_round(&mut x0, &mut x5, &mut x10, &mut x15);
        ChaCha20State::_quarter_round(&mut x1, &mut x6, &mut x11, &mut x12);
        ChaCha20State::_quarter_round(&mut x2, &mut x7, &mut x8, &mut x13);
        ChaCha20State::_quarter_round(&mut x3, &mut x4, &mut x9, &mut x14);
      }
      x0 += *self.state.get_unchecked(0);
      x1 += *self.state.get_unchecked(1);
      x2 += *self.state.get_unchecked(2);
      x3 += *self.state.get_unchecked(3);
      x4 += *self.state.get_unchecked(4);
      x5 += *self.state.get_unchecked(5);
      x6 += *self.state.get_unchecked(6);
      x7 += *self.state.get_unchecked(7);
      x8 += *self.state.get_unchecked(8);
      x9 += *self.state.get_unchecked(9);
      x10 += *self.state.get_unchecked(10);
      x11 += *self.state.get_unchecked(11);
      x12 += *self.state.get_unchecked(12);
      x13 += *self.state.get_unchecked(13);
      x14 += *self.state.get_unchecked(14);
      x15 += *self.state.get_unchecked(15);
      counter += 1;
      *self.state.get_unchecked_mut(12) = (counter & 0xffff_ffff_u64) as u32;
      *self.state.get_unchecked_mut(13) = ((counter >> 32) & 0xffff_ffff_u64) as u32;
      *results.get_unchecked_mut(0) = x0;
      *results.get_unchecked_mut(1) = x1;
      *results.get_unchecked_mut(2) = x2;
      *results.get_unchecked_mut(3) = x3;
      *results.get_unchecked_mut(4) = x4;
      *results.get_unchecked_mut(5) = x5;
      *results.get_unchecked_mut(6) = x6;
      *results.get_unchecked_mut(7) = x7;
      *results.get_unchecked_mut(8) = x8;
      *results.get_unchecked_mut(9) = x9;
      *results.get_unchecked_mut(10) = x10;
      *results.get_unchecked_mut(11) = x11;
      *results.get_unchecked_mut(12) = x12;
      *results.get_unchecked_mut(13) = x13;
      *results.get_unchecked_mut(14) = x14;
      *results.get_unchecked_mut(15) = x15;
    }
  }*/

  #[inline]
  fn generate(&mut self, results: &mut [u32; 16]) {
    let mut x0 = self.state[0];
    let mut x1 = self.state[1];
    let mut x2 = self.state[2];
    let mut x3 = self.state[3];
    let mut x4 = self.state[4];
    let mut x5 = self.state[5];
    let mut x6 = self.state[6];
    let mut x7 = self.state[7];
    let mut x8 = self.state[8];
    let mut x9 = self.state[9];
    let mut x10 = self.state[10];
    let mut x11 = self.state[11];
    let mut x12 = self.state[12];
    let mut x13 = self.state[13];
    let mut x14 = self.state[14];
    let mut x15 = self.state[15];
    let mut counter = (x12 as u64) | ((x13 as u64) << 32);
    assert!(counter != 0);
    for _ in 0 .. 10 {
      ChaCha20State::_quarter_round(&mut x0, &mut x4, &mut x8, &mut x12);
      ChaCha20State::_quarter_round(&mut x1, &mut x5, &mut x9, &mut x13);
      ChaCha20State::_quarter_round(&mut x2, &mut x6, &mut x10, &mut x14);
      ChaCha20State::_quarter_round(&mut x3, &mut x7, &mut x11, &mut x15);
      ChaCha20State::_quarter_round(&mut x0, &mut x5, &mut x10, &mut x15);
      ChaCha20State::_quarter_round(&mut x1, &mut x6, &mut x11, &mut x12);
      ChaCha20State::_quarter_round(&mut x2, &mut x7, &mut x8, &mut x13);
      ChaCha20State::_quarter_round(&mut x3, &mut x4, &mut x9, &mut x14);
    }
    x0 += self.state[0];
    x1 += self.state[1];
    x2 += self.state[2];
    x3 += self.state[3];
    x4 += self.state[4];
    x5 += self.state[5];
    x6 += self.state[6];
    x7 += self.state[7];
    x8 += self.state[8];
    x9 += self.state[9];
    x10 += self.state[10];
    x11 += self.state[11];
    x12 += self.state[12];
    x13 += self.state[13];
    x14 += self.state[14];
    x15 += self.state[15];
    counter += 1;
    self.state[12] = (counter & 0xffff_ffff_u64) as u32;
    self.state[13] = ((counter >> 32) & 0xffff_ffff_u64) as u32;
    results[0] = x0;
    results[1] = x1;
    results[2] = x2;
    results[3] = x3;
    results[4] = x4;
    results[5] = x5;
    results[6] = x6;
    results[7] = x7;
    results[8] = x8;
    results[9] = x9;
    results[10] = x10;
    results[11] = x11;
    results[12] = x12;
    results[13] = x13;
    results[14] = x14;
    results[15] = x15;
  }
}

#[derive(Clone)]
pub struct ChaCha20Rng {
  rng:  BlockRng32<ChaCha20State>,
}

impl ChaCha20Rng {
  pub fn zeroed() -> ChaCha20Rng {
    ChaCha20Rng{
      rng:  BlockRng32::new(ChaCha20State::zeroed()),
    }
  }

  pub fn state(&self) -> &ChaCha20State {
    &self.rng.core
  }

  pub fn state_mut(&mut self) -> &mut ChaCha20State {
    &mut self.rng.core
  }
}

impl RngCore for ChaCha20Rng {
  #[inline]
  fn next_u32(&mut self) -> u32 {
    self.rng.next_u32()
  }

  #[inline]
  fn next_u64(&mut self) -> u64 {
    self.rng.next_u64()
  }

  #[inline]
  fn fill_bytes(&mut self, dst: &mut [u8]) {
    self.rng.fill_bytes(dst);
  }

  #[inline]
  fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), RngError> {
    self.rng.try_fill_bytes(dst)
  }
}

impl SeedableRng for ChaCha20Rng {
  type Seed = [u8; 32];

  fn from_seed(seed: Self::Seed) -> Self {
    let mut state = ChaCha20State::zeroed();
    assert!(state.initialize(None, 1, 1, &mut Cursor::new(seed.as_ref())).is_ok());
    ChaCha20Rng{
      rng:  BlockRng32::new(state),
    }
  }
}

/* splitmix64_next:

Written in 2015 by Sebastiano Vigna (vigna@acm.org)

To the extent possible under law, the author has dedicated all copyright
and related and neighboring rights to this software to the public domain
worldwide. This software is distributed without any warranty.

See <http://creativecommons.org/publicdomain/zero/1.0/>.
*/

pub fn splitmix64_next(state: &mut u64) -> u64 {
  let mut x = *state;
  x = x.wrapping_add(0x9e3779b97f4a7c15);
  let mut z = x;
  *state = x;
  z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
  z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
  z ^ (z >> 31)
}

#[derive(Clone, Copy, Debug)]
pub struct Xoshirostarstar256State {
  pub state: [u64; 4],
}

impl Xoshirostarstar256State {
  pub fn zeroed() -> Xoshirostarstar256State {
    Xoshirostarstar256State{
      state:    [0; 4],
    }
  }

  pub fn save<W: Write>(&self, buf: &mut W) -> Result<usize, IoError> {
    buf.write_u64::<LE>(self.state[0])?;
    buf.write_u64::<LE>(self.state[1])?;
    buf.write_u64::<LE>(self.state[2])?;
    buf.write_u64::<LE>(self.state[3])?;
    Ok(32)
  }

  pub fn restore<R: Read>(&mut self, buf: &mut R) -> Result<usize, IoError> {
    self.state[0] = buf.read_u64::<LE>()?;
    self.state[1] = buf.read_u64::<LE>()?;
    self.state[2] = buf.read_u64::<LE>()?;
    self.state[3] = buf.read_u64::<LE>()?;
    Ok(32)
  }

  pub fn validate(&self) -> bool {
    !(self.state[0] == 0
        && self.state[1] == 0
        && self.state[2] == 0
        && self.state[3] == 0)
  }
}

impl BlockRngCore for Xoshirostarstar256State {
  type Item = u64;
  type Results = [u64; 1];

  /*#[inline]
  fn generate(&mut self, results: &mut [u64; 1]) {
    unsafe {
      *results.get_unchecked_mut(0) = (((*self.state.get_unchecked(1)).wrapping_mul(5)).rotate_left(7)).wrapping_mul(9);
      let t = *self.state.get_unchecked(1) << 17;
      *self.state.get_unchecked_mut(2) ^= *self.state.get_unchecked(0);
      *self.state.get_unchecked_mut(3) ^= *self.state.get_unchecked(1);
      *self.state.get_unchecked_mut(1) ^= *self.state.get_unchecked(2);
      *self.state.get_unchecked_mut(0) ^= *self.state.get_unchecked(3);
      *self.state.get_unchecked_mut(2) ^= t;
      *self.state.get_unchecked_mut(3) = (*self.state.get_unchecked(3)).rotate_left(45);
    }
  }*/

  #[inline]
  fn generate(&mut self, results: &mut [u64; 1]) {
    results[0] = (((self.state[1]).wrapping_mul(5)).rotate_left(7)).wrapping_mul(9);
    let t = self.state[1] << 17;
    self.state[2] ^= self.state[0];
    self.state[3] ^= self.state[1];
    self.state[1] ^= self.state[2];
    self.state[0] ^= self.state[3];
    self.state[2] ^= t;
    self.state[3] = (self.state[3]).rotate_left(45);
  }
}

pub type XoshiroRng = Xoshirostarstar256Rng;

#[derive(Clone)]
pub struct Xoshirostarstar256Rng {
  rng:  BlockRng64<Xoshirostarstar256State>,
}

impl Xoshirostarstar256Rng {
  pub fn from_u64_seed(seed: u64) -> Self {
    let mut state = Xoshirostarstar256State::zeroed();
    let mut seedstate = seed;
    for i in 0 .. 4 {
      state.state[i] = splitmix64_next(&mut seedstate);
    }
    assert!(state.validate());
    Xoshirostarstar256Rng{
      rng:  BlockRng64::new(state),
    }
  }

  pub fn zeroed() -> Xoshirostarstar256Rng {
    Xoshirostarstar256Rng{
      rng:  BlockRng64::new(Xoshirostarstar256State::zeroed()),
    }
  }

  pub fn state(&self) -> &Xoshirostarstar256State {
    &self.rng.core
  }

  pub fn state_mut(&mut self) -> &mut Xoshirostarstar256State {
    &mut self.rng.core
  }
}

impl RngCore for Xoshirostarstar256Rng {
  #[inline]
  fn next_u32(&mut self) -> u32 {
    self.rng.next_u32()
  }

  #[inline]
  fn next_u64(&mut self) -> u64 {
    self.rng.next_u64()
  }

  #[inline]
  fn fill_bytes(&mut self, dst: &mut [u8]) {
    self.rng.fill_bytes(dst);
  }

  #[inline]
  fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), RngError> {
    self.rng.try_fill_bytes(dst)
  }
}

impl SeedableRng for Xoshirostarstar256Rng {
  type Seed = [u8; 32];

  fn from_seed(seed: Self::Seed) -> Self {
    let mut state = Xoshirostarstar256State::zeroed();
    assert!(state.restore(&mut Cursor::new(seed.as_ref())).is_ok());
    assert!(state.validate());
    Xoshirostarstar256Rng{
      rng:  BlockRng64::new(state),
    }
  }
}

#[derive(Clone, Copy, Debug)]
pub struct Uniform;

impl Uniform {
  pub fn draw<R: RngCore>(self, rng: &mut R) -> f64 {
    let mut sig = rng.next_u64();
    let mut exp = -64;
    while sig == 0 {
      exp -= 64;
      if exp < -1074 {
        return 0.0
      }
      sig = rng.next_u64();
    }
    let shift = sig.leading_zeros() as i32;
    if shift != 0 {
      sig <<= shift;
      exp -= shift;
      sig |= rng.next_u64() >> (64 - shift);
    }
    sig |= 1;
    /*f64::from_bits(f64::to_bits(sig) | ...)*/
    let u = sig as f64 * (exp as f64).exp2();
    assert!(u >= 0.0 && u <= 1.0);
    u
  }
}

#[derive(Clone, Copy, Debug)]
pub struct URange {
  pub ub:   usize,
  pub cut:  usize,
}

impl URange {
  pub fn new(ub: usize) -> URange {
    let m = usize::max_value();
    let r = m % ub;
    let cut = m - r;
    assert!(cut >= ub);
    URange{
      ub,
      cut,
    }
  }

  pub fn draw<R: RngCore>(&self, rng: &mut R) -> usize {
    loop {
      let x = rng.next_u64() as usize;
      if x >= self.cut {
        continue;
      }
      let u = x % self.ub;
      return u;
    }
  }
}

pub fn choose_one_mut<T, R: RngCore>(xs: &mut [T], rng: &mut R) -> usize {
  let idx = URange::new(xs.len()).draw(rng);
  xs.swap(0, idx);
  idx
}

pub fn shuffle_mut<T, R: RngCore>(xs: &mut [T], rng: &mut R) {
  let n = xs.len();
  for i in 0 .. n {
    let m = n - i;
    let j = URange::new(m).draw(rng) + i;
    xs.swap(i, j);
  }
}

#[derive(Default)]
pub struct CategoricalHeap {
  leaf: usize,
  len:  usize,
  buf:  Vec<f64>,
}

#[inline(always)]
fn _heap_left(i: usize) -> usize {
  i * 2
}

impl CategoricalHeap {
  fn _refill(&mut self) {
    for i in (1 .. self.leaf).rev() {
      let j = _heap_left(i);
      if j >= self.leaf + self.len {
        self.buf[i] = 0.;
      } else {
        self.buf[i] = self.buf[j] + self.buf[j + 1];
      }
    }
  }

  pub fn fill(&mut self, src: &[f64]) {
    let src_len = src.len();
    let src_even_len = ((src_len + 1) / 2) * 2;
    let leaf_off = match src_len.checked_next_power_of_two() {
      None => panic!("bug: CategoricalHeap: too big: {}", src_len),
      Some(n) => n
    };
    self.leaf = leaf_off;
    self.len = src_len;
    self.buf.resize(leaf_off + src_even_len, 0.);
    self.buf[leaf_off .. leaf_off + src_len].copy_from_slice(src);
    if src_len < src_even_len {
      self.buf[src_len] = 0.;
    }
    self._refill();
  }

  pub fn draw<R: RngCore>(&self, rng: &mut R) -> usize {
    let mut i = 1;
    let mut v = self.buf[1];
    while i < self.leaf {
      let u = Uniform.draw(rng);
      if u >= 1. {
        continue;
      }
      assert!(u >= 0.);
      let j = _heap_left(i);
      let w = self.buf[j];
      if u * v < w {
        i = j;
        v = w;
      } else {
        i = j + 1;
        v = self.buf[j + 1];
      }
    }
    i - self.leaf
  }
}
