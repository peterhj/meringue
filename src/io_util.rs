use std::io::{Read, Write, Error as IoError};

/* These traits are mostly copied from `byteorder`, except they are implemented
using the `from_<xx>_bytes` and `to_<xx>_bytes` functions on primitive types
(introduced in Rust 1.32?), where `<xx>` is one of `le`, `be`, or `ne`. */

/* byteorder:

Copyright (c) 2015 Andrew Gallant

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE. */

#[cfg(target_endian = "little")]
pub type NE = LE;

pub enum LE {}

pub trait ByteOrder {
  fn read_u16(buf: [u8; 2]) -> u16;
  fn read_u32(buf: [u8; 4]) -> u32;
  fn read_u64(buf: [u8; 8]) -> u64;
  fn write_u16(x: u16) -> [u8; 2];
  fn write_u32(x: u32) -> [u8; 4];
  fn write_u64(x: u64) -> [u8; 8];
}

impl ByteOrder for LE {
  #[inline(always)]
  fn read_u16(buf: [u8; 2]) -> u16 {
    u16::from_le_bytes(buf)
  }

  #[inline(always)]
  fn read_u32(buf: [u8; 4]) -> u32 {
    u32::from_le_bytes(buf)
  }

  #[inline(always)]
  fn read_u64(buf: [u8; 8]) -> u64 {
    u64::from_le_bytes(buf)
  }

  #[inline(always)]
  fn write_u16(x: u16) -> [u8; 2] {
    x.to_le_bytes()
  }

  #[inline(always)]
  fn write_u32(x: u32) -> [u8; 4] {
    x.to_le_bytes()
  }

  #[inline(always)]
  fn write_u64(x: u64) -> [u8; 8] {
    x.to_le_bytes()
  }
}

pub trait ReadBytesExt: Read {
  #[inline(always)]
  fn read_u8(&mut self) -> Result<u8, IoError> {
    let mut buf: [u8; 1] = [0; 1];
    self.read_exact(&mut buf)?;
    Ok(buf[0])
  }

  #[inline(always)]
  fn read_u16<T: ByteOrder>(&mut self) -> Result<u16, IoError> {
    let mut buf: [u8; 2] = [0; 2];
    self.read_exact(&mut buf)?;
    Ok(T::read_u16(buf))
  }

  #[inline(always)]
  fn read_u32<T: ByteOrder>(&mut self) -> Result<u32, IoError> {
    let mut buf: [u8; 4] = [0; 4];
    self.read_exact(&mut buf)?;
    Ok(T::read_u32(buf))
  }

  #[inline(always)]
  fn read_u64<T: ByteOrder>(&mut self) -> Result<u64, IoError> {
    let mut buf: [u8; 8] = [0; 8];
    self.read_exact(&mut buf)?;
    Ok(T::read_u64(buf))
  }
}

impl<R: ?Sized + Read> ReadBytesExt for R {}

pub trait WriteBytesExt: Write {
  #[inline(always)]
  fn write_u8(&mut self, x: u8) -> Result<(), IoError> {
    let buf: [u8; 1] = [x];
    self.write_all(&buf)
  }

  #[inline(always)]
  fn write_u16<T: ByteOrder>(&mut self, x: u16) -> Result<(), IoError> {
    let buf: [u8; 2] = T::write_u16(x);
    self.write_all(&buf)
  }

  #[inline(always)]
  fn write_u32<T: ByteOrder>(&mut self, x: u32) -> Result<(), IoError> {
    let buf: [u8; 4] = T::write_u32(x);
    self.write_all(&buf)
  }

  #[inline(always)]
  fn write_u64<T: ByteOrder>(&mut self, x: u64) -> Result<(), IoError> {
    let buf: [u8; 8] = T::write_u64(x);
    self.write_all(&buf)
  }
}

impl<W: ?Sized + Write> WriteBytesExt for W {}
