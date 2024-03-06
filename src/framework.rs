use std::borrow::{Borrow};
use std::cmp::{Ordering};
use std::slice::{from_raw_parts, from_raw_parts_mut};

//pub type TNum = u32;
pub type TNum = u64;

//pub type SNum = i8;
//pub type SNum = i16;
pub type SNum = i32;
//pub type SNum = i64;

#[inline(always)]
pub fn s_ub() -> SNum {
  SNum::max_value()
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct CVar(pub SNum);

impl Default for CVar {
  #[inline(always)]
  fn default() -> CVar {
    CVar(0)
  }
}

impl CVar {
  #[inline(always)]
  pub fn ub() -> CVar {
    CVar(SNum::max_value())
  }

  #[inline(always)]
  pub fn lower(self) -> SNum {
    assert!(self.0 > 0);
    self.0
  }
}

#[inline(always)]
pub fn as_cvars(r: &[SNum]) -> &[CVar] {
  unsafe { from_raw_parts(r.as_ptr() as *const CVar, r.len()) }
}

#[inline(always)]
pub fn as_cvars_mut(r: &mut [SNum]) -> &mut [CVar] {
  unsafe { from_raw_parts_mut(r.as_mut_ptr() as *mut CVar, r.len()) }
}

#[inline(always)]
pub fn cvars_to_raw(s: &[CVar]) -> &[SNum] {
  as_snums(s)
}

#[inline(always)]
pub fn as_snums(s: &[CVar]) -> &[SNum] {
  unsafe { from_raw_parts(s.as_ptr() as *const SNum, s.len()) }
}

#[inline(always)]
pub fn sorted_tup2<T: Ord>(x0: T, x1: T) -> (T, T) {
  let pair = if x0 > x1 { (x1, x0) } else { (x0, x1) };
  pair
}

/*#[inline(always)]
pub fn cyclic_tup2<T: Ord>(x0: T, x1: T) -> (T, T) {
  let pair = if x0 > x1 { (x1, x0) } else { (x0, x1) };
  pair
}*/

#[inline(always)]
pub fn sorted_tup3<T: Ord>(x0: T, x1: T, x2: T) -> (T, T, T) {
  let trip = if x0 > x1 {
    if x1 > x2 {
      (x2, x1, x0)
    } else if x0 > x2 {
      (x1, x2, x0)
    } else {
      (x1, x0, x2)
    }
  } else {
    if x0 > x2 {
      (x2, x0, x1)
    } else if x1 > x2 {
      (x0, x2, x1)
    } else {
      (x0, x1, x2)
    }
  };
  trip
}

#[inline(always)]
pub fn cyclic_tup3<T: Ord>(x0: T, x1: T, x2: T) -> (T, T, T) {
  let trip = if x0 > x1 {
    if x1 > x2 {
      (x2, x0, x1)
    } else {
      (x1, x2, x0)
    }
  } else {
    if x0 > x2 {
      (x2, x0, x1)
    } else {
      (x0, x1, x2)
    }
  };
  trip
}

#[inline(always)]
pub fn sort2<T: Copy + Ord>(xs: [T; 2]) -> [T; 2] {
  if xs[0] > xs[1] { [xs[1], xs[0]] } else { [xs[0], xs[1]] }
}

#[inline(always)]
pub fn symmetric_sort3<T: Copy + Ord>(xs: [T; 3]) -> [T; 3] {
  if xs[0] > xs[1] {
    if xs[1] > xs[2] {
      [xs[2], xs[1], xs[0]]
    } else if xs[0] > xs[2] {
      [xs[1], xs[2], xs[0]]
    } else {
      [xs[1], xs[0], xs[2]]
    }
  } else {
    if xs[0] > xs[2] {
      [xs[2], xs[0], xs[1]]
    } else if xs[1] > xs[2] {
      [xs[0], xs[2], xs[1]]
    } else {
      [xs[0], xs[1], xs[2]]
    }
  }
}

#[inline(always)]
pub fn cyclic_sort3<T: Copy + Ord>(xs: [T; 3]) -> [T; 3] {
  if xs[0] > xs[1] {
    if xs[1] > xs[2] {
      [xs[2], xs[0], xs[1]]
    } else {
      [xs[1], xs[2], xs[0]]
    }
  } else {
    if xs[0] > xs[2] {
      [xs[2], xs[0], xs[1]]
    } else {
      [xs[0], xs[1], xs[2]]
    }
  }
}

#[inline(always)]
pub fn cyclic_sort<T: Copy + Ord>(xs: &mut [T]) {
  let mut lb = None;
  for (i, &x) in xs.iter().enumerate() {
    match lb {
      None => {
        lb = Some((i, x));
      }
      Some((_, ox)) => if x < ox {
        lb = Some((i, x));
      }
    }
  }
  match lb {
    None => {}
    Some((ilb, _)) => {
      xs.rotate_left(ilb);
    }
  }
}

pub fn next_permutation<T: Copy + Ord>(xs: &mut [T]) -> Option<()> {
  if xs.len() <= 1 {
    return None;
  }
  let mut x_i_1 = xs[xs.len() - 1];
  for i in (0 .. xs.len() - 1).rev() {
    let x_i = xs[i];
    if x_i < x_i_1 {
      let mut jswap = i + 1;
      for j in i + 2 .. xs.len() {
        if x_i < xs[j] {
          jswap = j;
        } else {
          break;
        }
      }
      xs.swap(i, jswap);
      xs[i + 1 .. ].reverse();
      return Some(());
    }
    x_i_1 = x_i;
  }
  None
}

pub fn lub_permutation<T: Copy + Ord>(lb: &[T], xs: &mut [T]) -> Option<()> {
  while lb > xs {
    if next_permutation(xs).is_none() {
      return None;
    }
  }
  Some(())
}

pub fn xlub_permutation<T: Copy + Ord>(lb: &[T], xs: &mut [T]) -> Option<()> {
  while lb >= xs {
    if next_permutation(xs).is_none() {
      return None;
    }
  }
  Some(())
}

pub struct _SplitSlice<'a, T> {
  pub lo:   &'a [T],
  pub hi:   &'a [T],
}

impl<'a, T> _SplitSlice<'a, T> {
  pub fn from(x: &'a [T]) -> _SplitSlice<'a, T> {
    let (hi, lo) = x.split_at(0);
    _SplitSlice{lo, hi}
  }
}

impl<'a, T: Eq> PartialEq for _SplitSlice<'a, T> {
  fn eq(&self, other: &_SplitSlice<'a, T>) -> bool {
    // TODO
    if self.lo.len() < other.lo.len() {
      let (other_lo, other_mid) = other.lo.split_at(self.lo.len());
      if !self.lo.eq(other_lo) {
        return false;
      }
      let (self_mid, self_hi) = self.hi.split_at(other_mid.len());
      if !self_mid.eq(other_mid) {
        return false;
      }
      self_hi.eq(other.hi)
    } else {
      let (self_lo, self_mid) = self.lo.split_at(other.lo.len());
      if !self_lo.eq(other.lo) {
        return false;
      }
      let (other_mid, other_hi) = other.hi.split_at(self_mid.len());
      if !self_mid.eq(other_mid) {
        return false;
      }
      self.hi.eq(other_hi)
    }
  }
}

impl<'a, T: Eq> Eq for _SplitSlice<'a, T> {
}

impl<'a, T: Ord> PartialOrd for _SplitSlice<'a, T> {
  fn partial_cmp(&self, other: &_SplitSlice<'a, T>) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<'a, T: Ord> Ord for _SplitSlice<'a, T> {
  fn cmp(&self, other: &_SplitSlice<'a, T>) -> Ordering {
    // TODO
    if self.lo.len() < other.lo.len() {
      let (other_lo, other_mid) = other.lo.split_at(self.lo.len());
      let r = self.lo.cmp(other_lo);
      match r {
        Ordering::Equal => {}
        _ => return r
      }
      let (self_mid, self_hi) = self.hi.split_at(other_mid.len());
      let r = self_mid.cmp(other_mid);
      match r {
        Ordering::Equal => {}
        _ => return r
      }
      self_hi.cmp(other.hi)
    } else {
      let (self_lo, self_mid) = self.lo.split_at(other.lo.len());
      let r = self_lo.cmp(other.lo);
      match r {
        Ordering::Equal => {}
        _ => return r
      }
      let (other_mid, other_hi) = other.hi.split_at(self_mid.len());
      let r = self_mid.cmp(other_mid);
      match r {
        Ordering::Equal => {}
        _ => return r
      }
      self.hi.cmp(other_hi)
    }
  }
}

#[inline(always)]
pub fn _rotate_lo(xs: &mut [SNum]) {
  rotate_lo(xs)
}

pub fn rotate_lo<T: Copy + Ord>(xs: &mut [T]) {
  if xs.len() <= 1 {
    return;
  }
  let mut r = 0;
  let mut s = _SplitSlice::from(xs);
  for j in 1 .. xs.len() {
    let (hi, lo) = xs.split_at(j);
    let t = _SplitSlice{lo, hi};
    if t < s {
      r = j;
      s = t;
    }
  }
  drop(s);
  if r > 0 {
    xs.rotate_left(r);
  }
}

pub fn rotate<T: Copy + Ord>(xs: &mut [T]) {
  xs.rotate_left(1);
}

pub fn next_rotation<T: Copy + Ord>(xs: &mut [T]) -> Option<()> {
  if xs.len() <= 1 {
    return None;
  }
  let x_0 = xs[0];
  for j in 1 .. xs.len() {
    let x_j = xs[j];
    if x_0 < x_j {
      for k in j + 1 .. xs.len() {
        let x_k = xs[k];
        if x_j < x_k {
          xs.rotate_left(1);
          return Some(());
        } else if x_j > x_k {
          if j == 1 {
            xs.rotate_left(k - 1);
          } else {
            xs.rotate_left(1);
          }
          return Some(());
        }
      }
      if j == 1 {
        xs.rotate_right(1);
      } else {
        xs.rotate_left(1);
      }
      return Some(());
    } else if x_0 > x_j {
      let k = xs.len() - 1;
      if j < k {
        let x_k = xs[k];
        if x_0 == x_k {
          xs.rotate_right(1);
          return Some(());
        }
      }
      return None;
    }
  }
  None
}

pub fn lub_rotation<T: Copy + Ord>(lb: &[T], xs: &mut [T]) -> Option<()> {
  while lb > xs {
    if next_rotation(xs).is_none() {
      return None;
    }
  }
  Some(())
}

pub fn xlub_rotation<T: Copy + Ord>(lb: &[T], xs: &mut [T]) -> Option<()> {
  while lb >= xs {
    if next_rotation(xs).is_none() {
      return None;
    }
  }
  Some(())
}

pub fn perm_mult(tup: &[SNum]) -> u32 {
  let mut n = 1;
  let mut d = 1;
  let mut t = 1;
  let mut k = 1;
  let mut x = tup[0];
  for i in 1 .. tup.len() {
    let y = tup[i];
    n *= i as u32 + 1;
    if x < y {
      d *= t;
      t = 1;
      k = 1;
    } else if x == y {
      t *= k + 1;
      k += 1;
    } else {
      unreachable!();
    }
    x = y;
  }
  d *= t;
  n / d
}

#[inline(always)]
pub fn _perm_tup(perm: &[SNum], otup: &[SNum], tup: &mut [SNum]) -> bool {
  let mut s = false;
  for p in 0 .. perm.len() {
    let i = perm[p] as usize;
    tup[p] = otup[i];
    if p != i {
      s = true;
    }
  }
  /*for p in perm.len() .. tup.len() {
    tup[p] = otup[p];
  }*/
  tup[perm.len() .. ].copy_from_slice(&otup[perm.len() .. ]);
  s
}

#[inline(always)]
pub fn _swap_var(x: SNum, ox: SNum, nx: SNum) -> SNum {
  if x == ox {
    nx
  } else {
    x
  }
}

#[inline(always)]
pub fn swap_var(x: CVar, ox: CVar, nx: CVar) -> CVar {
  if x == ox {
    nx
  } else {
    x
  }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
#[repr(transparent)]
pub struct CTup2(pub [CVar; 2]);
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
#[repr(transparent)]
pub struct CTup3(pub [CVar; 3]);
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
#[repr(transparent)]
pub struct CTup4(pub [CVar; 4]);
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
#[repr(transparent)]
pub struct CTup5(pub [CVar; 5]);
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
#[repr(transparent)]
pub struct CTup6(pub [CVar; 6]);

impl CTup2 {
  #[inline(always)]
  pub fn ub() -> CTup2 {
    CTup2([CVar::ub(), CVar::ub()])
  }

  #[inline(always)]
  pub fn flip(self) -> CTup2 {
    let [lhs, rhs] = self.0;
    CTup2([rhs, lhs])
  }

  #[inline(always)]
  pub fn swap_var(self, ox: CVar, nx: CVar) -> CTup2 {
    let [x0, x1] = self.0;
    let nx0 = swap_var(x0, ox, nx);
    let nx1 = swap_var(x1, ox, nx);
    CTup2([nx0, nx1])
  }

  #[inline(always)]
  pub fn count_var(self, x: CVar) -> usize {
    let [x0, x1] = self.0;
    let mut n = 0;
    n += if x0 == x { 1 } else { 0 };
    n += if x1 == x { 1 } else { 0 };
    n
  }

  #[inline(always)]
  pub fn sort(mut self) -> CTup2 {
    self.0.sort();
    self
  }

  #[inline(always)]
  pub fn rotate_lo(mut self) -> CTup2 {
    _rotate_lo(self.as_mut());
    self
  }

  #[inline(always)]
  pub fn perm(self, perm: &[SNum]) -> CTup2 {
    let mut dst = self;
    _perm_tup(perm, self.as_ref(), dst.as_mut());
    dst
  }

  #[inline(always)]
  pub fn len(&self) -> usize {
    2
  }
}

impl From<&[SNum]> for CTup2 {
  #[inline(always)]
  fn from(src: &[SNum]) -> CTup2 {
    let mut buf: [CVar; 2] = Default::default();
    buf.copy_from_slice(as_cvars(src));
    CTup2(buf)
  }
}

impl From<&[CVar]> for CTup2 {
  #[inline(always)]
  fn from(src: &[CVar]) -> CTup2 {
    let mut buf: [CVar; 2] = Default::default();
    buf.copy_from_slice(src);
    CTup2(buf)
  }
}

impl From<[CVar; 2]> for CTup2 {
  #[inline(always)]
  fn from(buf: [CVar; 2]) -> CTup2 {
    CTup2(buf)
  }
}

impl AsRef<[CVar]> for CTup2 {
  #[inline(always)]
  fn as_ref(&self) -> &[CVar] {
    &self.0 as &[CVar]
  }
}

impl AsRef<[SNum]> for CTup2 {
  #[inline(always)]
  fn as_ref(&self) -> &[SNum] {
    let s = &self.0 as &[CVar];
    unsafe { from_raw_parts(s.as_ptr() as *const SNum, s.len()) }
  }
}

impl Borrow<[SNum]> for CTup2 {
  #[inline(always)]
  fn borrow(&self) -> &[SNum] {
    self.as_ref()
  }
}

impl AsMut<[CVar]> for CTup2 {
  #[inline(always)]
  fn as_mut(&mut self) -> &mut [CVar] {
    &mut self.0 as &mut [CVar]
  }
}

impl AsMut<[SNum]> for CTup2 {
  #[inline(always)]
  fn as_mut(&mut self) -> &mut [SNum] {
    let s = &mut self.0 as &mut [CVar];
    unsafe { from_raw_parts_mut(s.as_mut_ptr() as *mut SNum, s.len()) }
  }
}

impl CTup3 {
  #[inline(always)]
  pub fn ub() -> CTup3 {
    CTup3([CVar::ub(), CVar::ub(), CVar::ub()])
  }

  #[inline(always)]
  pub fn swap_var(self, ox: CVar, nx: CVar) -> CTup3 {
    let [x0, x1, x2] = self.0;
    let nx0 = swap_var(x0, ox, nx);
    let nx1 = swap_var(x1, ox, nx);
    let nx2 = swap_var(x2, ox, nx);
    CTup3([nx0, nx1, nx2])
  }

  #[inline(always)]
  pub fn count_var(self, x: CVar) -> usize {
    let [x0, x1, x2] = self.0;
    let mut n = 0;
    n += if x0 == x { 1 } else { 0 };
    n += if x1 == x { 1 } else { 0 };
    n += if x2 == x { 1 } else { 0 };
    n
  }

  #[inline(always)]
  pub fn sort(mut self) -> CTup3 {
    self.0.sort();
    self
  }

  #[inline(always)]
  pub fn rotate_lo(mut self) -> CTup3 {
    _rotate_lo(self.as_mut());
    self
  }

  #[inline(always)]
  pub fn perm(self, perm: &[SNum]) -> CTup3 {
    let mut dst = self;
    _perm_tup(perm, self.as_ref(), dst.as_mut());
    dst
  }

  #[inline(always)]
  pub fn len(&self) -> usize {
    3
  }
}

impl From<&[SNum]> for CTup3 {
  #[inline(always)]
  fn from(src: &[SNum]) -> CTup3 {
    let mut buf: [CVar; 3] = Default::default();
    buf.copy_from_slice(as_cvars(src));
    CTup3(buf)
  }
}

impl From<&[CVar]> for CTup3 {
  #[inline(always)]
  fn from(src: &[CVar]) -> CTup3 {
    let mut buf: [CVar; 3] = Default::default();
    buf.copy_from_slice(src);
    CTup3(buf)
  }
}

impl From<[CVar; 3]> for CTup3 {
  #[inline(always)]
  fn from(buf: [CVar; 3]) -> CTup3 {
    CTup3(buf)
  }
}

impl AsRef<[CVar]> for CTup3 {
  #[inline(always)]
  fn as_ref(&self) -> &[CVar] {
    &self.0 as &[CVar]
  }
}

impl AsRef<[SNum]> for CTup3 {
  #[inline(always)]
  fn as_ref(&self) -> &[SNum] {
    let s = &self.0 as &[CVar];
    unsafe { from_raw_parts(s.as_ptr() as *const SNum, s.len()) }
  }
}

impl Borrow<[SNum]> for CTup3 {
  #[inline(always)]
  fn borrow(&self) -> &[SNum] {
    self.as_ref()
  }
}

impl AsMut<[CVar]> for CTup3 {
  #[inline(always)]
  fn as_mut(&mut self) -> &mut [CVar] {
    &mut self.0 as &mut [CVar]
  }
}

impl AsMut<[SNum]> for CTup3 {
  #[inline(always)]
  fn as_mut(&mut self) -> &mut [SNum] {
    let s = &mut self.0 as &mut [CVar];
    unsafe { from_raw_parts_mut(s.as_mut_ptr() as *mut SNum, s.len()) }
  }
}

impl CTup4 {
  #[inline(always)]
  pub fn ub() -> CTup4 {
    CTup4([CVar::ub(), CVar::ub(), CVar::ub(), CVar::ub()])
  }

  #[inline(always)]
  pub fn swap_var(self, ox: CVar, nx: CVar) -> CTup4 {
    let [x0, x1, x2, x3] = self.0;
    let nx0 = swap_var(x0, ox, nx);
    let nx1 = swap_var(x1, ox, nx);
    let nx2 = swap_var(x2, ox, nx);
    let nx3 = swap_var(x3, ox, nx);
    CTup4([nx0, nx1, nx2, nx3])
  }

  #[inline(always)]
  pub fn count_var(self, x: CVar) -> usize {
    let [x0, x1, x2, x3] = self.0;
    let mut n = 0;
    n += if x0 == x { 1 } else { 0 };
    n += if x1 == x { 1 } else { 0 };
    n += if x2 == x { 1 } else { 0 };
    n += if x3 == x { 1 } else { 0 };
    n
  }

  #[inline(always)]
  pub fn sort(mut self) -> CTup4 {
    self.0.sort();
    self
  }

  #[inline(always)]
  pub fn rotate_lo(mut self) -> CTup4 {
    _rotate_lo(self.as_mut());
    self
  }

  #[inline(always)]
  pub fn perm(self, perm: &[SNum]) -> CTup4 {
    let mut dst = self;
    _perm_tup(perm, self.as_ref(), dst.as_mut());
    dst
  }

  #[inline(always)]
  pub fn len(&self) -> usize {
    4
  }
}

impl From<&[SNum]> for CTup4 {
  #[inline(always)]
  fn from(src: &[SNum]) -> CTup4 {
    let mut buf: [CVar; 4] = Default::default();
    buf.copy_from_slice(as_cvars(src));
    CTup4(buf)
  }
}

impl From<&[CVar]> for CTup4 {
  #[inline(always)]
  fn from(src: &[CVar]) -> CTup4 {
    let mut buf: [CVar; 4] = Default::default();
    buf.copy_from_slice(src);
    CTup4(buf)
  }
}

impl AsRef<[CVar]> for CTup4 {
  #[inline(always)]
  fn as_ref(&self) -> &[CVar] {
    &self.0 as &[CVar]
  }
}

impl AsRef<[SNum]> for CTup4 {
  #[inline(always)]
  fn as_ref(&self) -> &[SNum] {
    let s = &self.0 as &[CVar];
    unsafe { from_raw_parts(s.as_ptr() as *const SNum, s.len()) }
  }
}

impl Borrow<[SNum]> for CTup4 {
  #[inline(always)]
  fn borrow(&self) -> &[SNum] {
    self.as_ref()
  }
}

impl AsMut<[CVar]> for CTup4 {
  #[inline(always)]
  fn as_mut(&mut self) -> &mut [CVar] {
    &mut self.0 as &mut [CVar]
  }
}

impl AsMut<[SNum]> for CTup4 {
  #[inline(always)]
  fn as_mut(&mut self) -> &mut [SNum] {
    let s = &mut self.0 as &mut [CVar];
    unsafe { from_raw_parts_mut(s.as_mut_ptr() as *mut SNum, s.len()) }
  }
}

impl CTup5 {
  #[inline(always)]
  pub fn ub() -> CTup5 {
    CTup5([CVar::ub(), CVar::ub(), CVar::ub(), CVar::ub(), CVar::ub()])
  }

  #[inline(always)]
  pub fn swap_var(self, ox: CVar, nx: CVar) -> CTup5 {
    let [x0, x1, x2, x3, x4] = self.0;
    let nx0 = swap_var(x0, ox, nx);
    let nx1 = swap_var(x1, ox, nx);
    let nx2 = swap_var(x2, ox, nx);
    let nx3 = swap_var(x3, ox, nx);
    let nx4 = swap_var(x4, ox, nx);
    CTup5([nx0, nx1, nx2, nx3, nx4])
  }

  #[inline(always)]
  pub fn sort(mut self) -> CTup5 {
    self.0.sort();
    self
  }

  #[inline(always)]
  pub fn rotate_lo(mut self) -> CTup5 {
    _rotate_lo(self.as_mut());
    self
  }

  #[inline(always)]
  pub fn perm(self, perm: &[SNum]) -> CTup5 {
    let mut dst = self;
    _perm_tup(perm, self.as_ref(), dst.as_mut());
    dst
  }
}

impl From<&[SNum]> for CTup5 {
  #[inline(always)]
  fn from(src: &[SNum]) -> CTup5 {
    let mut buf: [CVar; 5] = Default::default();
    buf.copy_from_slice(as_cvars(src));
    CTup5(buf)
  }
}

impl From<&[CVar]> for CTup5 {
  #[inline(always)]
  fn from(src: &[CVar]) -> CTup5 {
    let mut buf: [CVar; 5] = Default::default();
    buf.copy_from_slice(src);
    CTup5(buf)
  }
}

impl AsRef<[CVar]> for CTup5 {
  #[inline(always)]
  fn as_ref(&self) -> &[CVar] {
    &self.0 as &[CVar]
  }
}

impl AsRef<[SNum]> for CTup5 {
  #[inline(always)]
  fn as_ref(&self) -> &[SNum] {
    let s = &self.0 as &[CVar];
    unsafe { from_raw_parts(s.as_ptr() as *const SNum, s.len()) }
  }
}

impl Borrow<[SNum]> for CTup5 {
  #[inline(always)]
  fn borrow(&self) -> &[SNum] {
    self.as_ref()
  }
}

impl AsMut<[CVar]> for CTup5 {
  #[inline(always)]
  fn as_mut(&mut self) -> &mut [CVar] {
    &mut self.0 as &mut [CVar]
  }
}

impl AsMut<[SNum]> for CTup5 {
  #[inline(always)]
  fn as_mut(&mut self) -> &mut [SNum] {
    let s = &mut self.0 as &mut [CVar];
    unsafe { from_raw_parts_mut(s.as_mut_ptr() as *mut SNum, s.len()) }
  }
}

impl CTup6 {
  #[inline(always)]
  pub fn ub() -> CTup6 {
    CTup6([CVar::ub(), CVar::ub(), CVar::ub(), CVar::ub(), CVar::ub(), CVar::ub()])
  }

  #[inline(always)]
  pub fn swap_var(self, ox: CVar, nx: CVar) -> CTup6 {
    let [x0, x1, x2, x3, x4, x5] = self.0;
    let nx0 = swap_var(x0, ox, nx);
    let nx1 = swap_var(x1, ox, nx);
    let nx2 = swap_var(x2, ox, nx);
    let nx3 = swap_var(x3, ox, nx);
    let nx4 = swap_var(x4, ox, nx);
    let nx5 = swap_var(x5, ox, nx);
    CTup6([nx0, nx1, nx2, nx3, nx4, nx5])
  }

  #[inline(always)]
  pub fn count_var(self, x: CVar) -> usize {
    let [x0, x1, x2, x3, x4, x5] = self.0;
    let mut n = 0;
    n += if x0 == x { 1 } else { 0 };
    n += if x1 == x { 1 } else { 0 };
    n += if x2 == x { 1 } else { 0 };
    n += if x3 == x { 1 } else { 0 };
    n += if x4 == x { 1 } else { 0 };
    n += if x5 == x { 1 } else { 0 };
    n
  }

  #[inline(always)]
  pub fn sort(mut self) -> CTup6 {
    self.0.sort();
    self
  }

  #[inline(always)]
  pub fn rotate_lo(mut self) -> CTup6 {
    _rotate_lo(self.as_mut());
    self
  }

  #[inline(always)]
  pub fn perm(self, perm: &[SNum]) -> CTup6 {
    let mut dst = self;
    _perm_tup(perm, self.as_ref(), dst.as_mut());
    dst
  }

  #[inline(always)]
  pub fn len(&self) -> usize {
    6
  }
}

impl From<&[SNum]> for CTup6 {
  #[inline(always)]
  fn from(src: &[SNum]) -> CTup6 {
    let mut buf: [CVar; 6] = Default::default();
    buf.copy_from_slice(as_cvars(src));
    CTup6(buf)
  }
}

impl From<&[CVar]> for CTup6 {
  #[inline(always)]
  fn from(src: &[CVar]) -> CTup6 {
    let mut buf: [CVar; 6] = Default::default();
    buf.copy_from_slice(src);
    CTup6(buf)
  }
}

impl AsRef<[CVar]> for CTup6 {
  #[inline(always)]
  fn as_ref(&self) -> &[CVar] {
    &self.0 as &[CVar]
  }
}

impl AsRef<[SNum]> for CTup6 {
  #[inline(always)]
  fn as_ref(&self) -> &[SNum] {
    let s = &self.0 as &[CVar];
    unsafe { from_raw_parts(s.as_ptr() as *const SNum, s.len()) }
  }
}

impl Borrow<[SNum]> for CTup6 {
  #[inline(always)]
  fn borrow(&self) -> &[SNum] {
    self.as_ref()
  }
}

impl AsMut<[CVar]> for CTup6 {
  #[inline(always)]
  fn as_mut(&mut self) -> &mut [CVar] {
    &mut self.0 as &mut [CVar]
  }
}

impl AsMut<[SNum]> for CTup6 {
  #[inline(always)]
  fn as_mut(&mut self) -> &mut [SNum] {
    let s = &mut self.0 as &mut [CVar];
    unsafe { from_raw_parts_mut(s.as_mut_ptr() as *mut SNum, s.len()) }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct CSymmTup2([CVar; 2]);
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct CSymmTup3([CVar; 3]);
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct CSymmTup4([CVar; 4]);
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct CSymmTup5([CVar; 5]);
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct CSymmTup6([CVar; 6]);

impl CSymmTup2 {
  #[inline(always)]
  pub fn into_tup(self) -> CTup2 {
    CTup2(self.0)
  }

  #[inline(always)]
  pub fn swap_var(self, ox: CVar, nx: CVar) -> CSymmTup2 {
    let [x0, x1] = self.0;
    let nx0 = swap_var(x0, ox, nx);
    let nx1 = swap_var(x1, ox, nx);
    CSymmTup2::from([nx0, nx1])
  }

  #[inline(always)]
  pub fn inner(&self) -> &[CVar; 2] {
    &self.0
  }

  #[inline(always)]
  pub fn perm_ub(&self) -> CTup2 {
    let [x0, x1] = self.0;
    CTup2([x1, x0])
  }
}

impl From<&[CVar]> for CSymmTup2 {
  #[inline(always)]
  fn from(src: &[CVar]) -> CSymmTup2 {
    let mut buf: [CVar; 2] = Default::default();
    buf.copy_from_slice(src);
    CSymmTup2::from(buf)
  }
}

impl From<[CVar; 2]> for CSymmTup2 {
  #[inline(always)]
  fn from(buf: [CVar; 2]) -> CSymmTup2 {
    CSymmTup2(sort2(buf))
  }
}

impl AsRef<[CVar]> for CSymmTup2 {
  #[inline(always)]
  fn as_ref(&self) -> &[CVar] {
    &self.0 as &[CVar]
  }
}

impl AsRef<[SNum]> for CSymmTup2 {
  #[inline(always)]
  fn as_ref(&self) -> &[SNum] {
    let s = &self.0 as &[CVar];
    unsafe { from_raw_parts(s.as_ptr() as *const SNum, s.len()) }
  }
}

impl AsMut<[SNum]> for CSymmTup2 {
  #[inline(always)]
  fn as_mut(&mut self) -> &mut [SNum] {
    let s = &mut self.0 as &mut [CVar];
    unsafe { from_raw_parts_mut(s.as_mut_ptr() as *mut SNum, s.len()) }
  }
}

impl CSymmTup3 {
  #[inline(always)]
  pub fn into_tup(self) -> CTup3 {
    CTup3(self.0)
  }

  #[inline(always)]
  pub fn swap_var(self, ox: CVar, nx: CVar) -> CSymmTup3 {
    let [x0, x1, x2] = self.0;
    let nx0 = swap_var(x0, ox, nx);
    let nx1 = swap_var(x1, ox, nx);
    let nx2 = swap_var(x2, ox, nx);
    CSymmTup3::from([nx0, nx1, nx2])
  }
}

impl From<&[CVar]> for CSymmTup3 {
  #[inline(always)]
  fn from(src: &[CVar]) -> CSymmTup3 {
    let mut buf: [CVar; 3] = Default::default();
    buf.copy_from_slice(src);
    CSymmTup3::from(buf)
  }
}

impl From<[CVar; 3]> for CSymmTup3 {
  #[inline(always)]
  fn from(buf: [CVar; 3]) -> CSymmTup3 {
    CSymmTup3(symmetric_sort3(buf))
  }
}

impl AsRef<[CVar]> for CSymmTup3 {
  #[inline(always)]
  fn as_ref(&self) -> &[CVar] {
    &self.0 as &[CVar]
  }
}

impl AsRef<[SNum]> for CSymmTup3 {
  #[inline(always)]
  fn as_ref(&self) -> &[SNum] {
    let s = &self.0 as &[CVar];
    unsafe { from_raw_parts(s.as_ptr() as *const SNum, s.len()) }
  }
}

impl AsMut<[SNum]> for CSymmTup3 {
  #[inline(always)]
  fn as_mut(&mut self) -> &mut [SNum] {
    let s = &mut self.0 as &mut [CVar];
    unsafe { from_raw_parts_mut(s.as_mut_ptr() as *mut SNum, s.len()) }
  }
}

impl CSymmTup4 {
  #[inline(always)]
  pub fn into_tup(self) -> CTup4 {
    CTup4(self.0)
  }
}

impl From<[CVar; 4]> for CSymmTup4 {
  #[inline(always)]
  fn from(mut buf: [CVar; 4]) -> CSymmTup4 {
    buf.sort();
    CSymmTup4(buf)
  }
}

impl From<[CVar; 5]> for CSymmTup5 {
  #[inline(always)]
  fn from(mut buf: [CVar; 5]) -> CSymmTup5 {
    buf.sort();
    CSymmTup5(buf)
  }
}

impl From<[CVar; 6]> for CSymmTup6 {
  #[inline(always)]
  fn from(mut buf: [CVar; 6]) -> CSymmTup6 {
    buf.sort();
    CSymmTup6(buf)
  }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct CCyclTup3([CVar; 3]);
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct CCyclTup4([CVar; 4]);
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct CCyclTup5([CVar; 5]);
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct CCyclTup6([CVar; 6]);

impl From<[CVar; 3]> for CCyclTup3 {
  #[inline(always)]
  fn from(buf: [CVar; 3]) -> CCyclTup3 {
    CCyclTup3(cyclic_sort3(buf))
  }
}

impl AsRef<[CVar]> for CCyclTup3 {
  #[inline(always)]
  fn as_ref(&self) -> &[CVar] {
    &self.0 as &[CVar]
  }
}

impl AsRef<[SNum]> for CCyclTup3 {
  #[inline(always)]
  fn as_ref(&self) -> &[SNum] {
    let s = &self.0 as &[CVar];
    unsafe { from_raw_parts(s.as_ptr() as *const SNum, s.len()) }
  }
}

impl CCyclTup4 {
  #[inline(always)]
  pub fn into_tup(self) -> CTup4 {
    CTup4(self.0)
  }

  #[inline(always)]
  pub fn swap_var(self, ox: CVar, nx: CVar) -> CCyclTup4 {
    let [x0, x1, x2, x3] = self.0;
    let nx0 = swap_var(x0, ox, nx);
    let nx1 = swap_var(x1, ox, nx);
    let nx2 = swap_var(x2, ox, nx);
    let nx3 = swap_var(x3, ox, nx);
    CCyclTup4::from([nx0, nx1, nx2, nx3])
  }
}

impl From<&[CVar]> for CCyclTup4 {
  #[inline(always)]
  fn from(src: &[CVar]) -> CCyclTup4 {
    let mut buf: [CVar; 4] = Default::default();
    buf.copy_from_slice(src);
    CCyclTup4::from(buf)
  }
}

impl From<[CVar; 4]> for CCyclTup4 {
  #[inline(always)]
  fn from(mut buf: [CVar; 4]) -> CCyclTup4 {
    cyclic_sort(&mut buf);
    CCyclTup4(buf)
  }
}

impl AsRef<[CVar]> for CCyclTup4 {
  #[inline(always)]
  fn as_ref(&self) -> &[CVar] {
    &self.0 as &[CVar]
  }
}

impl AsRef<[SNum]> for CCyclTup4 {
  #[inline(always)]
  fn as_ref(&self) -> &[SNum] {
    let s = &self.0 as &[CVar];
    unsafe { from_raw_parts(s.as_ptr() as *const SNum, s.len()) }
  }
}

impl AsMut<[SNum]> for CCyclTup4 {
  #[inline(always)]
  fn as_mut(&mut self) -> &mut [SNum] {
    let s = &mut self.0 as &mut [CVar];
    unsafe { from_raw_parts_mut(s.as_mut_ptr() as *mut SNum, s.len()) }
  }
}

impl From<[CVar; 5]> for CCyclTup5 {
  #[inline(always)]
  fn from(mut buf: [CVar; 5]) -> CCyclTup5 {
    cyclic_sort(&mut buf);
    CCyclTup5(buf)
  }
}

impl From<[CVar; 6]> for CCyclTup6 {
  #[inline(always)]
  fn from(mut buf: [CVar; 6]) -> CCyclTup6 {
    cyclic_sort(&mut buf);
    CCyclTup6(buf)
  }
}
