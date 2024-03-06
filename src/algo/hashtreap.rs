use std::borrow::{Borrow};
use std::cmp::{Ordering};
use std::convert::{TryInto};
use std::fmt::{Debug as FmtDebug, Error as FmtError, Formatter};
use std::hash::{Hasher, Hash};
use std::marker::{PhantomData};
use std::mem::{swap};
use std::ops::{Deref};
use std::sync::{Arc as Rc};

/*
An implementation of persistent treaps with (atomic) reference-counted pointers
and deterministic hash priorities. For further information, read:

- [BRM98] Guy E. Blelloch and Margaret Reid-Miller. "Fast Set Operations Using
  Treaps." SPAA '98, pp. 16-26, 1998.
- [SA96] Raimund Seidel and Cecilia R. Aragon. "Randomized Search Trees."
  Algorithmica 16(4-5), pp. 464-497, 1996.
*/

pub struct FxPrimeHasher32 {
  pub hash: u32
}

impl Default for FxPrimeHasher32 {
  #[inline(always)]
  fn default() -> FxPrimeHasher32 {
    FxPrimeHasher32{ hash: 0xb3c7a41a }
  }
}

impl FxPrimeHasher32 {
  #[inline(always)]
  pub fn zeroed() -> FxPrimeHasher32 {
    FxPrimeHasher32{ hash: 0 }
  }

  #[inline(always)]
  fn _write(&mut self, x: u32) {
    const K: u32 = 0x9e3779b1;
    self.hash = (self.hash.rotate_left(5) ^ x).wrapping_mul(K);
  }

  #[inline(always)]
  fn finish32(&self) -> u32 {
    self.hash
  }
}

impl Hasher for FxPrimeHasher32 {
  #[inline(always)]
  fn write(&mut self, mut buf: &[u8]) {
    while buf.len() >= 4 {
      let (tok, buf_) = buf.split_at(4);
      self._write(u32::from_ne_bytes(tok.try_into().unwrap()));
      buf = buf_;
    }
    if buf.len() >= 2 {
      let (tok, buf_) = buf.split_at(2);
      self._write(u16::from_ne_bytes(tok.try_into().unwrap()) as u32);
      buf = buf_;
    }
    if buf.len() >= 1 {
      self._write(buf[0] as u32);
    }
  }

  #[inline(always)]
  fn write_u8(&mut self, x: u8) {
    self._write(x as u32);
  }

  #[inline(always)]
  fn write_u16(&mut self, x: u16) {
    self._write(x as u32);
  }

  #[inline(always)]
  fn write_u32(&mut self, x: u32) {
    self._write(x);
  }

  #[inline(always)]
  fn write_u64(&mut self, x: u64) {
    self._write(x as u32);
    self._write((x >> 32) as u32);
  }

  #[inline(always)]
  fn write_u128(&mut self, x: u128) {
    self._write(x as u32);
    self._write((x >> 32) as u32);
    self._write((x >> 64) as u32);
    self._write((x >> 96) as u32);
  }

  #[cfg(target_pointer_width = "32")]
  #[inline(always)]
  fn write_usize(&mut self, x: usize) {
    self.write_u32(x as u32);
  }

  #[cfg(target_pointer_width = "64")]
  #[inline(always)]
  fn write_usize(&mut self, x: usize) {
    self.write_u64(x as u64);
  }

  #[inline(always)]
  fn write_i8(&mut self, x: i8) {
    self.write_u8(x as u8);
  }

  #[inline(always)]
  fn write_i16(&mut self, x: i16) {
    self.write_u16(x as u16);
  }

  #[inline(always)]
  fn write_i32(&mut self, x: i32) {
    self.write_u32(x as u32);
  }

  #[inline(always)]
  fn write_i64(&mut self, x: i64) {
    self.write_u64(x as u64);
  }

  #[inline(always)]
  fn write_i128(&mut self, x: i128) {
    self.write_u128(x as u128);
  }

  #[inline(always)]
  fn write_isize(&mut self, x: isize) {
    self.write_usize(x as usize);
  }

  #[inline(always)]
  fn finish(&self) -> u64 {
    self.finish32() as u64
  }
}

#[inline(always)]
pub fn hash_priority<K: Eq + Hash>(this: &K) -> u32 {
  //let mut state = FnvHasher::default();
  //let mut state = FxHasher::default();
  let mut state = FxPrimeHasher32::default();
  this.hash(&mut state);
  state.finish32()
}

pub struct HashTreapMapCloneIter<K, V, Storage> {
  iter: HTNodeCloneIter<K, Storage>,
  _pd:  PhantomData<V>,
}

impl<K, V, Storage: Clone + Into<Pair<K, V>>> Iterator for HashTreapMapCloneIter<K, V, Storage> {
  type Item = (K, V);

  fn next(&mut self) -> Option<(K, V)> {
    self.iter.next()
      .map(|data| data.into().0)
  }
}

pub struct HashTreapMapIter<'a, K, V, Storage> {
  iter: HTNodeIter<'a, K, Storage>,
  _pd:  PhantomData<V>,
}

impl<'a, K: 'a, V: 'a, Storage: Borrow<K> + AsRef<V>> Iterator for HashTreapMapIter<'a, K, V, Storage> {
  type Item = (&'a K, &'a V);

  fn next(&mut self) -> Option<(&'a K, &'a V)> {
    self.iter.next()
      .map(|data| (data.borrow(), data.as_ref()))
  }
}

pub struct HashTreapMapRevIter<'a, K, V, Storage> {
  iter: HTNodeRevIter<'a, K, Storage>,
  _pd:  PhantomData<V>,
}

impl<'a, K: 'a, V: 'a, Storage: Borrow<K> + AsRef<V>> Iterator for HashTreapMapRevIter<'a, K, V, Storage> {
  type Item = (&'a K, &'a V);

  fn next(&mut self) -> Option<(&'a K, &'a V)> {
    self.iter.next()
      .map(|data| (data.borrow(), data.as_ref()))
  }
}

pub type InlineHashTreapMap<K, V> = HashTreapMap<K, V, Record<K, V>>;

#[derive(Hash)]
pub struct HashTreapMap<K, V, Storage=RecordRef<K, V>> {
  root: HTNodeRef<K, Storage>,
  _pd:  PhantomData<V>,
}

impl<K, V> Default for InlineHashTreapMap<K, V> {
  fn default() -> InlineHashTreapMap<K, V> {
    InlineHashTreapMap::new_inline()
  }
}

impl<K, V> Default for HashTreapMap<K, V> {
  fn default() -> HashTreapMap<K, V> {
    HashTreapMap::new()
  }
}

impl<K, V> InlineHashTreapMap<K, V> {
  pub fn new_inline() -> InlineHashTreapMap<K, V> {
    HashTreapMap{
      root: None,
      _pd:  PhantomData,
    }
  }
}

impl<K, V> HashTreapMap<K, V> {
  pub fn new() -> HashTreapMap<K, V> {
    HashTreapMap{
      root: None,
      _pd:  PhantomData,
    }
  }
}

impl<K: FmtDebug, V: FmtDebug, Storage: Borrow<K> + AsRef<V>> FmtDebug for HashTreapMap<K, V, Storage> {
  fn fmt(&self, f: &mut Formatter) -> Result<(), FmtError> {
    let len = self.len();
    write!(f, "{{")?;
    for (i, item) in HTNodeIter::new(&self.root).enumerate() {
      item.borrow().fmt(f)?;
      write!(f, " => ")?;
      item.as_ref().fmt(f)?;
      if i != len - 1 {
        write!(f, ", ")?;
      }
    }
    write!(f, "}}")?;
    Ok(())
  }
}

impl<K, V, Storage> Clone for HashTreapMap<K, V, Storage> {
  fn clone(&self) -> HashTreapMap<K, V, Storage> {
    HashTreapMap{
      root: self.root.clone(),
      _pd:  PhantomData,
    }
  }
}

impl<K, V, Storage> HashTreapMap<K, V, Storage> {
  pub fn len(&self) -> usize {
    self.root.as_ref()
      .map(|x| x.size).unwrap_or_else(|| 0)
  }

  pub fn count_less(&self) -> usize {
    self.root.as_ref()
      .and_then(|x| x.lhs.as_ref())
      .map(|x| x.size).unwrap_or_else(|| 0)
  }

  pub fn count_greater(&self) -> usize {
    self.root.as_ref()
      .and_then(|x| x.rhs.as_ref())
      .map(|x| x.size).unwrap_or_else(|| 0)
  }

  pub fn is_empty(&self) -> bool {
    self.root.is_none()
  }

  pub fn ptr_eq(&self, other: &HashTreapMap<K, V, Storage>) -> bool {
    match (self.root.as_ref(), other.root.as_ref()) {
      (None, None) => true,
      (Some(lr), Some(rr)) => Rc::ptr_eq(lr, rr),
      _ => false
    }
  }

  pub fn clear(&mut self) {
    self.root = None;
  }
}

impl<K: Ord, V, Storage: Borrow<K> + AsRef<V>> HashTreapMap<K, V, Storage> {
  pub fn get<Q: ?Sized + Ord>(&self, key: &Q) -> Option<&V>
  where K: Borrow<Q> {
    self.root.as_ref()
      .and_then(|root| HTNode::search(root, key))
      .map(|data| data.as_ref())
  }
}

impl<K: Ord, V, Storage: Clone + Borrow<K> + AsMut<V>> HashTreapMap<K, V, Storage> {
  pub fn get_mut<Q: ?Sized + Ord>(&mut self, key: &Q) -> Option<&mut V>
  where K: Borrow<Q> {
    self.root.as_mut()
      .and_then(|root| HTNode::search_mut(Rc::make_mut(root), key))
      .map(|data| data.as_mut())
  }
}

impl<K: Ord, V, Storage: Borrow<K>> HashTreapMap<K, V, Storage> {
  pub fn contains_key<Q: ?Sized + Ord>(&self, key: &Q) -> bool
  where K: Borrow<Q> {
    self.root.as_ref()
      .and_then(|root| HTNode::search(root, key))
      .is_some()
  }

  pub fn clone_iter(&self) -> HashTreapMapCloneIter<K, V, Storage> {
    HashTreapMapCloneIter{
      iter: HTNodeCloneIter::new(self.root.clone()),
      _pd:  PhantomData,
    }
  }

  pub fn clone_iter_from<Q: ?Sized + Ord>(&self, key: &Q) -> HashTreapMapCloneIter<K, V, Storage>
  where K: Borrow<Q> {
    HashTreapMapCloneIter{
      iter: HTNodeCloneIter::search_lb(self.root.clone(), key),
      _pd:  PhantomData,
    }
  }

  pub fn clone_iter_from_excl<Q: ?Sized + Ord>(&self, key: &Q) -> HashTreapMapCloneIter<K, V, Storage>
  where K: Borrow<Q> {
    HashTreapMapCloneIter{
      iter: HTNodeCloneIter::search_lb_excl(self.root.clone(), key),
      _pd:  PhantomData,
    }
  }

  pub fn iter<'a>(&'a self) -> HashTreapMapIter<'a, K, V, Storage> {
    HashTreapMapIter{
      iter: HTNodeIter::new(&self.root),
      _pd:  PhantomData,
    }
  }

  pub fn iter_from<'a, Q: ?Sized + Ord>(&'a self, key: &Q) -> HashTreapMapIter<'a, K, V, Storage>
  where K: Borrow<Q> {
    HashTreapMapIter{
      iter: HTNodeIter::search_lb(&self.root, key),
      _pd:  PhantomData,
    }
  }

  pub fn iter_from_excl<'a, Q: ?Sized + Ord>(&'a self, key: &Q) -> HashTreapMapIter<'a, K, V, Storage>
  where K: Borrow<Q> {
    HashTreapMapIter{
      iter: HTNodeIter::search_lb_excl(&self.root, key),
      _pd:  PhantomData,
    }
  }

  pub fn rev_iter<'a>(&'a self) -> HashTreapMapRevIter<'a, K, V, Storage> {
    HashTreapMapRevIter{
      iter: HTNodeRevIter::new(&self.root),
      _pd:  PhantomData,
    }
  }

  pub fn rev_iter_from<'a, Q: ?Sized + Ord>(&'a self, key: &Q) -> HashTreapMapRevIter<'a, K, V, Storage>
  where K: Borrow<Q> {
    HashTreapMapRevIter{
      iter: HTNodeRevIter::search_ub(&self.root, key),
      _pd:  PhantomData,
    }
  }

  pub fn rev_iter_from_excl<'a, Q: ?Sized + Ord>(&'a self, key: &Q) -> HashTreapMapRevIter<'a, K, V, Storage>
  where K: Borrow<Q> {
    HashTreapMapRevIter{
      iter: HTNodeRevIter::search_ub_excl(&self.root, key),
      _pd:  PhantomData,
    }
  }

  pub fn keys_eq<VR, SR: Borrow<K>>(&self, other: &HashTreapMap<K, VR, SR>) -> bool {
    match (self.root.as_ref(), other.root.as_ref()) {
      (None, None) => true,
      (Some(_), Some(_)) => if self.len() == other.len() {
        for (li, ri) in HTNodeIter::new(&self.root).zip(HTNodeIter::new(&other.root)) {
          if li.borrow() != ri.borrow() {
            return false;
          }
        }
        true
      } else {
        false
      },
      _ => false
    }
  }
}

impl<K: Clone + Ord + Hash, V: Clone> InlineHashTreapMap<K, V> {
  pub fn insert_new(&self, key: K, value: V) -> InlineHashTreapMap<K, V> {
    let data = Record{key, value};
    let (new_root, _) = HTNode::insert(self.root.clone(), data);
    HashTreapMap{
      root: Some(new_root.into()),
      _pd:  PhantomData,
    }
  }

  /*pub fn insert_mut(&mut self, key: K, value: V) -> bool {
    let data = Record{key, value};
    let (new_root, old_data) = HTNode::insert(self.root.take(), data);
    self.root = Some(new_root.into());
    old_data.is_some()
  }*/

  pub fn insert(&mut self, key: K, value: V) -> Option<V> {
    let data = Record{key, value};
    let (new_root, old_data) = HTNode::insert(self.root.take(), data);
    self.root = Some(new_root.into());
    old_data.map(|x| x.value)
  }

  pub fn insert_drop(&mut self, key: K, value: V) -> bool {
    let data = Record{key, value};
    let (new_root, old_data) = HTNode::insert(self.root.take(), data.into());
    self.root = Some(new_root.into());
    old_data.is_some()
  }
}

impl<K: Ord + Hash, V> HashTreapMap<K, V> {
  pub fn insert_new(&self, key: K, value: V) -> HashTreapMap<K, V> {
    let data = Record{key, value};
    let (new_root, _) = HTNode::insert(self.root.clone(), data.into());
    HashTreapMap{
      root: Some(new_root.into()),
      _pd:  PhantomData,
    }
  }

  pub fn insert_drop(&mut self, key: K, value: V) -> bool {
    let data = Record{key, value};
    let (new_root, old_data) = HTNode::insert(self.root.take(), data.into());
    self.root = Some(new_root.into());
    old_data.is_some()
  }
}

impl<K: Ord + Hash, V: Clone> HashTreapMap<K, V> {
  pub fn insert(&mut self, key: K, value: V) -> Option<V> {
    let data = Record{key, value};
    let (new_root, old_data) = HTNode::insert(self.root.take(), data.into());
    self.root = Some(new_root.into());
    old_data.map(|data| match Rc::try_unwrap(data.0) {
      Ok(x) => x.value,
      Err(xx) => xx.value.clone(),
    })
  }
}

impl<K: Ord, V, Storage: Clone + Borrow<K>> HashTreapMap<K, V, Storage> {
  pub fn remove_new<Q: ?Sized + Ord>(&self, key: &Q) -> HashTreapMap<K, V, Storage>
  where K: Borrow<Q> {
    let (new_root, _) = HTNode::remove(self.root.clone(), key);
    HashTreapMap{
      root: new_root,
      _pd:  PhantomData,
    }
  }

  /*pub fn remove_mut<Q: ?Sized + Ord>(&mut self, key: &Q)
  where K: Borrow<Q> {
    let (new_root, _) = HTNode::remove(self.root.take(), key);
    self.root = new_root;
  }*/
}

impl<K: Clone + Ord, V: Clone> InlineHashTreapMap<K, V> {
  pub fn remove<Q: ?Sized + Ord>(&mut self, key: &Q) -> Option<V>
  where K: Borrow<Q> {
    let (new_root, data) = HTNode::remove(self.root.take(), key);
    self.root = new_root;
    data.map(|x| x.value)
  }
}

impl<K: Ord, V: Clone> HashTreapMap<K, V> {
  pub fn remove<Q: ?Sized + Ord>(&mut self, key: &Q) -> Option<V>
  where K: Borrow<Q> {
    let (new_root, data) = HTNode::remove(self.root.take(), key);
    self.root = new_root;
    data.map(|data| match Rc::try_unwrap(data.0) {
      Ok(x) => x.value,
      Err(xx) => xx.value.clone(),
    })
  }
}

impl<K: Clone + Ord, V> InlineHashTreapMap<K, V> {
  pub fn map_values<F: FnMut(&V) -> W, W>(&self, f: &mut F) -> InlineHashTreapMap<K, W> {
    let new_root = HTNode::map(self.root.clone(), &mut |_, v| f(v));
    InlineHashTreapMap{
      root: new_root,
      _pd:  PhantomData,
    }
  }
}

impl<K: Clone + Ord, V> HashTreapMap<K, V> {
  pub fn map_values<F: FnMut(&V) -> W, W>(&self, f: &mut F) -> HashTreapMap<K, W> {
    let new_root = HTNode::map_ref(self.root.clone(), &mut |_, v| f(v));
    HashTreapMap{
      root: new_root,
      _pd:  PhantomData,
    }
  }
}

impl<K: Clone + Ord, V: Clone> InlineHashTreapMap<K, V> {
  pub fn keys(&self) -> InlineHashTreapSet<K> {
    let new_root = HTNode::map(self.root.clone(), &mut |_, _| ());
    InlineHashTreapSet{
      root: new_root,
    }
  }

  pub fn keys_intersection(&self, other: &InlineHashTreapMap<K, V>) -> InlineHashTreapSet<K> {
    let new_root = HTNode::intersect_merge(self.root.clone(), other.root.clone(), &mut |_, _, _| ());
    InlineHashTreapSet{
      root: new_root,
    }
  }
}

impl<K: Clone + Ord, V: Clone> HashTreapMap<K, V> {
  pub fn keys(&self) -> HashTreapSet<K> {
    let new_root = HTNode::map_ref(self.root.clone(), &mut |_, _| ());
    HashTreapSet{
      root: new_root,
    }
  }

  pub fn keys_intersection(&self, other: &HashTreapMap<K, V>) -> HashTreapSet<K> {
    let new_root = HTNode::intersect_map_ref(self.root.clone(), other.root.clone(), &mut |_, _, _| ());
    HashTreapSet{
      root: new_root,
    }
  }
}

impl<K: Clone + Ord, V: Clone> InlineHashTreapMap<K, V> {
  pub fn merge_union<F: FnMut(&K, &V, &V) -> V>(&self, other: &InlineHashTreapMap<K, V>, merge_f: &mut F) -> InlineHashTreapMap<K, V> {
    let new_root = HTNode::union_merge(self.root.clone(), other.root.clone(), merge_f);
    HashTreapMap{
      root: new_root,
      _pd:  PhantomData,
    }
  }

  pub fn merge_intersection<F: FnMut(&K, &V, &V) -> W, W: Clone>(&self, other: &InlineHashTreapMap<K, V>, merge_f: &mut F) -> InlineHashTreapMap<K, W> {
    let new_root = HTNode::intersect_merge(self.root.clone(), other.root.clone(), merge_f);
    HashTreapMap{
      root: new_root,
      _pd:  PhantomData,
    }
  }
}

impl<K: Ord, V, Storage: Clone + Borrow<K>> HashTreapMap<K, V, Storage> {
  pub fn split_greater<Q: ?Sized + Ord>(&self, key: &Q) -> HashTreapMap<K, V, Storage>
  where K: Borrow<Q> {
    let (gtr, _) = HTNode::split_gtr(self.root.clone(), key);
    HashTreapMap{
      root: gtr,
      _pd:  PhantomData,
    }
  }

  pub fn left_intersection(&self, other: &HashTreapMap<K, V, Storage>) -> HashTreapMap<K, V, Storage> {
    let new_root = HTNode::intersect_left(self.root.clone(), other.root.clone());
    HashTreapMap{
      root: new_root,
      _pd:  PhantomData,
    }
  }

  pub fn left_intersection_mut(&mut self, other: &HashTreapMap<K, V, Storage>) {
    let new_root = HTNode::intersect_left(self.root.take(), other.root.clone());
    self.root = new_root;
  }

  pub fn set_intersection<S: Clone + Borrow<K>>(&self, other: &HashTreapSet<K, S>) -> HashTreapMap<K, V, Storage> {
    let new_root = HTNode::intersect_left(self.root.clone(), other.root.clone());
    HashTreapMap{
      root: new_root,
      _pd:  PhantomData,
    }
  }

  pub fn set_intersection_mut<S: Clone + Borrow<K>>(&mut self, other: &HashTreapSet<K, S>) {
    let new_root = HTNode::intersect_left(self.root.take(), other.root.clone());
    self.root = new_root;
  }

  pub fn left_union(&self, other: &HashTreapMap<K, V, Storage>) -> HashTreapMap<K, V, Storage> {
    let new_root = HTNode::union_left(self.root.clone(), other.root.clone());
    HashTreapMap{
      root: new_root,
      _pd:  PhantomData,
    }
  }

  pub fn left_union_mut(&mut self, other: &HashTreapMap<K, V, Storage>) {
    let new_root = HTNode::union_left(self.root.take(), other.root.clone());
    self.root = new_root;
  }

  pub fn difference(&self, other: &HashTreapMap<K, V, Storage>) -> HashTreapMap<K, V, Storage> {
    let new_root = HTNode::diff(self.root.clone(), other.root.clone(), true);
    HashTreapMap{
      root: new_root,
      _pd:  PhantomData,
    }
  }

  pub fn difference_mut(&mut self, other: &HashTreapMap<K, V, Storage>) {
    let new_root = HTNode::diff(self.root.take(), other.root.clone(), true);
    self.root = new_root;
  }

  pub fn set_difference<S: Clone + Borrow<K>>(&self, other: &HashTreapSet<K, S>) -> HashTreapMap<K, V, Storage> {
    let new_root = HTNode::diff_left(self.root.clone(), other.root.clone());
    HashTreapMap{
      root: new_root,
      _pd:  PhantomData,
    }
  }

  pub fn set_difference_mut<S: Clone + Borrow<K>>(&mut self, other: &HashTreapSet<K, S>) {
    let new_root = HTNode::diff_left(self.root.take(), other.root.clone());
    self.root = new_root;
  }

  pub fn symmetric_difference(&self, other: &HashTreapMap<K, V, Storage>) -> HashTreapMap<K, V, Storage> {
    let new_root = HTNode::symm_diff(self.root.clone(), other.root.clone());
    HashTreapMap{
      root: new_root,
      _pd:  PhantomData,
    }
  }

  pub fn symmetric_difference_mut(&mut self, other: &HashTreapMap<K, V, Storage>) {
    let new_root = HTNode::symm_diff(self.root.take(), other.root.clone());
    self.root = new_root;
  }
}

impl<K: Ord, V: Eq, Storage: Borrow<K> + AsRef<V>> PartialEq for HashTreapMap<K, V, Storage> {
  fn eq(&self, other: &HashTreapMap<K, V, Storage>) -> bool {
    match (self.root.as_ref(), other.root.as_ref()) {
      (None, None) => true,
      (Some(lr), Some(rr)) => if Rc::ptr_eq(lr, rr) {
        true
      } else if self.len() == other.len() {
        for ((lk, lv), (rk, rv)) in self.iter().zip(other.iter()) {
          if lk != rk || lv != rv {
            return false;
          }
        }
        true
      } else {
        false
      },
      _ => false,
    }
  }
}

impl<K: Ord, V: Eq, Storage: Borrow<K> + AsRef<V>> Eq for HashTreapMap<K, V, Storage> {
}

pub struct HashTreapSetCloneIter<K, Storage> {
  iter: HTNodeCloneIter<K, Storage>,
}

impl<K, Storage: Clone + Into<Key<K>>> Iterator for HashTreapSetCloneIter<K, Storage> {
  type Item = K;

  fn next(&mut self) -> Option<K> {
    self.iter.next()
      .map(|data| data.into().0)
  }
}

pub struct HashTreapSetIter<'a, K, Storage> {
  iter: HTNodeIter<'a, K, Storage>,
}

impl<'a, K: 'a, Storage: Borrow<K>> Iterator for HashTreapSetIter<'a, K, Storage> {
  type Item = &'a K;

  fn next(&mut self) -> Option<&'a K> {
    self.iter.next()
      .map(|data| data.borrow())
  }
}

pub struct HashTreapSetRevIter<'a, K, Storage> {
  iter: HTNodeRevIter<'a, K, Storage>,
}

impl<'a, K: 'a, Storage: Borrow<K>> Iterator for HashTreapSetRevIter<'a, K, Storage> {
  type Item = &'a K;

  fn next(&mut self) -> Option<&'a K> {
    self.iter.next()
      .map(|data| data.borrow())
  }
}

pub type InlineHashTreapSet<K> = HashTreapSet<K, Record<K, ()>>;

#[derive(Hash)]
pub struct HashTreapSet<K, Storage=RecordRef<K, ()>> {
  root: HTNodeRef<K, Storage>,
}

impl<K> Default for InlineHashTreapSet<K> {
  fn default() -> InlineHashTreapSet<K> {
    InlineHashTreapSet::new_inline()
  }
}

impl<K> Default for HashTreapSet<K> {
  fn default() -> HashTreapSet<K> {
    HashTreapSet::new()
  }
}

impl<K> InlineHashTreapSet<K> {
  pub fn new_inline() -> InlineHashTreapSet<K> {
    HashTreapSet{
      root: None,
    }
  }
}

impl<K> HashTreapSet<K> {
  pub fn new() -> HashTreapSet<K> {
    HashTreapSet{
      root: None,
    }
  }
}

impl<K: FmtDebug, Storage: Borrow<K>> FmtDebug for HashTreapSet<K, Storage> {
  fn fmt(&self, f: &mut Formatter) -> Result<(), FmtError> {
    let len = self.len();
    write!(f, "{{")?;
    for (i, item) in HTNodeIter::new(&self.root).enumerate() {
      item.borrow().fmt(f)?;
      if i != len - 1 {
        write!(f, ", ")?;
      }
    }
    write!(f, "}}")?;
    Ok(())
  }
}

impl<K, Storage> Clone for HashTreapSet<K, Storage> {
  fn clone(&self) -> HashTreapSet<K, Storage> {
    HashTreapSet{
      root: self.root.clone(),
    }
  }
}

impl<K, Storage> HashTreapSet<K, Storage> {
  pub fn len(&self) -> usize {
    self.root.as_ref()
      .map(|x| x.size).unwrap_or_else(|| 0)
  }

  pub fn count_less(&self) -> usize {
    self.root.as_ref()
      .and_then(|x| x.lhs.as_ref())
      .map(|x| x.size).unwrap_or_else(|| 0)
  }

  pub fn count_greater(&self) -> usize {
    self.root.as_ref()
      .and_then(|x| x.rhs.as_ref())
      .map(|x| x.size).unwrap_or_else(|| 0)
  }

  pub fn is_empty(&self) -> bool {
    self.root.is_none()
  }

  pub fn ptr_eq(&self, other: &HashTreapSet<K, Storage>) -> bool {
    match (self.root.as_ref(), other.root.as_ref()) {
      (None, None) => true,
      (Some(lr), Some(rr)) => Rc::ptr_eq(lr, rr),
      _ => false
    }
  }

  pub fn clear(&mut self) {
    self.root = None;
  }
}

impl<K: Ord, Storage: Borrow<K>> HashTreapSet<K, Storage> {
  pub fn get<Q: ?Sized + Ord>(&self, key: &Q) -> Option<&K>
  where K: Borrow<Q> {
    self.root.as_ref()
      .and_then(|root| HTNode::search(root, key))
      .map(|data| data.borrow())
  }

  pub fn contains<Q: ?Sized + Ord>(&self, key: &Q) -> bool
  where K: Borrow<Q> {
    self.root.as_ref()
      .and_then(|root| HTNode::search(root, key))
      .is_some()
  }

  pub fn clone_iter(&self) -> HashTreapSetCloneIter<K, Storage> {
    HashTreapSetCloneIter{
      iter: HTNodeCloneIter::new(self.root.clone()),
    }
  }

  pub fn clone_iter_from<Q: ?Sized + Ord>(&self, key: &Q) -> HashTreapSetCloneIter<K, Storage>
  where K: Borrow<Q> {
    HashTreapSetCloneIter{
      iter: HTNodeCloneIter::search_lb(self.root.clone(), key),
    }
  }

  pub fn clone_iter_from_excl<Q: ?Sized + Ord>(&self, key: &Q) -> HashTreapSetCloneIter<K, Storage>
  where K: Borrow<Q> {
    HashTreapSetCloneIter{
      iter: HTNodeCloneIter::search_lb_excl(self.root.clone(), key),
    }
  }

  pub fn iter<'a>(&'a self) -> HashTreapSetIter<'a, K, Storage> {
    HashTreapSetIter{
      iter: HTNodeIter::new(&self.root),
    }
  }

  pub fn iter_from<'a, Q: ?Sized + Ord>(&'a self, key: &Q) -> HashTreapSetIter<'a, K, Storage>
  where K: Borrow<Q> {
    HashTreapSetIter{
      iter: HTNodeIter::search_lb(&self.root, key),
    }
  }

  pub fn iter_from_excl<'a, Q: ?Sized + Ord>(&'a self, key: &Q) -> HashTreapSetIter<'a, K, Storage>
  where K: Borrow<Q> {
    HashTreapSetIter{
      iter: HTNodeIter::search_lb_excl(&self.root, key),
    }
  }

  pub fn rev_iter<'a>(&'a self) -> HashTreapSetRevIter<'a, K, Storage> {
    HashTreapSetRevIter{
      iter: HTNodeRevIter::new(&self.root),
    }
  }

  pub fn rev_iter_from<'a, Q: ?Sized + Ord>(&'a self, key: &Q) -> HashTreapSetRevIter<'a, K, Storage>
  where K: Borrow<Q> {
    HashTreapSetRevIter{
      iter: HTNodeRevIter::search_ub(&self.root, key),
    }
  }

  pub fn rev_iter_from_excl<'a, Q: ?Sized + Ord>(&'a self, key: &Q) -> HashTreapSetRevIter<'a, K, Storage>
  where K: Borrow<Q> {
    HashTreapSetRevIter{
      iter: HTNodeRevIter::search_ub_excl(&self.root, key),
    }
  }
}

impl<K: Clone + Ord + Hash> InlineHashTreapSet<K> {
  pub fn insert_new(&self, key: K) -> InlineHashTreapSet<K> {
    let (new_root, _) = HTNode::insert(self.root.clone(), key.into());
    HashTreapSet{
      root: Some(new_root.into()),
    }
  }

  pub fn insert(&mut self, key: K) -> bool {
    let (new_root, old_key) = HTNode::insert(self.root.take(), key.into());
    self.root = Some(new_root.into());
    old_key.is_some()
  }
}

impl<K: Ord + Hash> HashTreapSet<K> {
  pub fn insert_new(&self, key: K) -> HashTreapSet<K> {
    let (new_root, _) = HTNode::insert(self.root.clone(), key.into());
    HashTreapSet{
      root: Some(new_root.into()),
    }
  }

  pub fn insert(&mut self, key: K) -> bool {
    let (new_root, old_key) = HTNode::insert(self.root.take(), key.into());
    self.root = Some(new_root.into());
    old_key.is_some()
  }
}

impl<K: Ord, Storage: Clone + Borrow<K>> HashTreapSet<K, Storage> {
  pub fn remove_new<Q: ?Sized + Ord>(&self, key: &Q) -> HashTreapSet<K, Storage>
  where K: Borrow<Q> {
    let (new_root, _) = HTNode::remove(self.root.clone(), key);
    HashTreapSet{
      root: new_root,
    }
  }

  pub fn remove<Q: ?Sized + Ord>(&mut self, key: &Q) -> bool
  where K: Borrow<Q> {
    let (new_root, old_key) = HTNode::remove(self.root.take(), key);
    self.root = new_root;
    old_key.is_some()
  }
}

impl<K: Ord, Storage: Clone + Borrow<K>> HashTreapSet<K, Storage> {
  pub fn intersection(&self, other: &HashTreapSet<K, Storage>) -> HashTreapSet<K, Storage> {
    let new_root = HTNode::intersect_one(self.root.clone(), other.root.clone());
    HashTreapSet{
      root: new_root,
    }
  }

  pub fn intersection_mut(&mut self, other: &HashTreapSet<K, Storage>) {
    let new_root = HTNode::intersect_one(self.root.take(), other.root.clone());
    self.root = new_root;
  }

  pub fn union(&self, other: &HashTreapSet<K, Storage>) -> HashTreapSet<K, Storage> {
    let new_root = HTNode::union_one(self.root.clone(), other.root.clone());
    HashTreapSet{
      root: new_root,
    }
  }

  pub fn union_mut(&mut self, other: &HashTreapSet<K, Storage>) {
    let new_root = HTNode::union_one(self.root.take(), other.root.clone());
    self.root = new_root;
  }

  pub fn difference(&self, other: &HashTreapSet<K, Storage>) -> HashTreapSet<K, Storage> {
    let new_root = HTNode::diff(self.root.clone(), other.root.clone(), true);
    HashTreapSet{
      root: new_root,
    }
  }

  pub fn difference_mut(&mut self, other: &HashTreapSet<K, Storage>) {
    let new_root = HTNode::diff(self.root.take(), other.root.clone(), true);
    self.root = new_root;
  }

  pub fn symmetric_difference(&self, other: &HashTreapSet<K, Storage>) -> HashTreapSet<K, Storage> {
    let new_root = HTNode::symm_diff(self.root.clone(), other.root.clone());
    HashTreapSet{
      root: new_root,
    }
  }

  pub fn symmetric_difference_mut(&mut self, other: &HashTreapSet<K, Storage>) {
    let new_root = HTNode::symm_diff(self.root.take(), other.root.clone());
    self.root = new_root;
  }
}

impl<K: Ord, Storage: Borrow<K>> PartialEq for HashTreapSet<K, Storage> {
  fn eq(&self, other: &HashTreapSet<K, Storage>) -> bool {
    match (self.root.as_ref(), other.root.as_ref()) {
      (None, None) => true,
      (Some(lr), Some(rr)) => if Rc::ptr_eq(lr, rr) {
        true
      } else if self.len() == other.len() {
        for (lk, rk) in self.iter().zip(other.iter()) {
          if lk != rk {
            return false;
          }
        }
        true
      } else {
        false
      },
      _ => false,
    }
  }
}

impl<K: Ord, Storage: Borrow<K>> Eq for HashTreapSet<K, Storage> {
}

/*trait AsKey<K> {
  fn key(&self) -> &K;
}

trait AsValue<V> {
  fn value(&self) -> &V;
}*/

#[repr(transparent)]
pub struct KeyRef<K>(Rc<Key<K>>);

//#[derive(Copy)]
#[repr(transparent)]
pub struct Key<K>(K);

#[repr(transparent)]
pub struct PairRef<K, V>(Rc<Pair<K, V>>);

//#[derive(Copy)]
#[repr(transparent)]
pub struct Pair<K, V>((K, V));

impl<K, V> From<Record<K, V>> for Key<K> {
  #[inline(always)]
  fn from(record: Record<K, V>) -> Key<K> {
    Key(record.key)
  }
}

impl<K, V> From<Record<K, V>> for Pair<K, V> {
  #[inline(always)]
  fn from(record: Record<K, V>) -> Pair<K, V> {
    Pair((record.key, record.value))
  }
}

pub struct RecordRef<K, V>(pub Rc<Record<K, V>>);

#[derive(Copy)]
pub struct Record<K, V> {
  pub key:      K,
  pub value:    V,
}

impl<K> From<K> for Record<K, ()> {
  #[inline(always)]
  fn from(key: K) -> Record<K, ()> {
    Record{key, value: ()}
  }
}

impl<K> From<K> for RecordRef<K, ()> {
  #[inline(always)]
  fn from(key: K) -> RecordRef<K, ()> {
    RecordRef(Rc::new(Record{key, value: ()}))
  }
}

impl<K, V> From<Record<K, V>> for RecordRef<K, V> {
  #[inline(always)]
  fn from(data: Record<K, V>) -> RecordRef<K, V> {
    RecordRef(Rc::new(data))
  }
}

impl<K, V> Deref for RecordRef<K, V> {
  type Target = Record<K, V>;

  #[inline(always)]
  fn deref(&self) -> &Record<K, V> {
    &*self.0
  }
}

impl<K, V> Clone for RecordRef<K, V> {
  #[inline]
  fn clone(&self) -> RecordRef<K, V> {
    RecordRef(self.0.clone())
  }
}

impl<K: Clone, V: Clone> Clone for Record<K, V> {
  #[inline]
  fn clone(&self) -> Record<K, V> {
    Record{key: self.key.clone(), value: self.value.clone()}
  }
}

impl<K, V> Borrow<K> for Record<K, V> {
  #[inline(always)]
  fn borrow(&self) -> &K {
    &self.key
  }
}

impl<K, V> AsRef<V> for Record<K, V> {
  #[inline(always)]
  fn as_ref(&self) -> &V {
    &self.value
  }
}

impl<K, V> AsMut<V> for Record<K, V> {
  #[inline(always)]
  fn as_mut(&mut self) -> &mut V {
    &mut self.value
  }
}

impl<K, V> Borrow<K> for RecordRef<K, V> {
  #[inline(always)]
  fn borrow(&self) -> &K {
    &self.0.key
  }
}

impl<K, V> AsRef<V> for RecordRef<K, V> {
  #[inline(always)]
  fn as_ref(&self) -> &V {
    &self.0.value
  }
}

impl<K: Clone, V: Clone> AsMut<V> for RecordRef<K, V> {
  #[inline(always)]
  fn as_mut(&mut self) -> &mut V {
    &mut Rc::make_mut(&mut self.0).value
  }
}

type HTNodeRef<K, Item> = Option<Rc<HTNode<K, Item>>>;

#[derive(Hash)]
struct HTNode<K, Item> {
  lhs:      HTNodeRef<K, Item>,
  rhs:      HTNodeRef<K, Item>,
  size:     usize,
  priority: u32,
  data:     Item,
  _phantom: PhantomData<K>,
}

impl<K, Item: Clone> Clone for HTNode<K, Item> {
  #[inline]
  fn clone(&self) -> HTNode<K, Item> {
    HTNode{
      lhs:      self.lhs.clone(),
      rhs:      self.rhs.clone(),
      size:     self.size,
      priority: self.priority,
      data:     self.data.clone(),
      _phantom: PhantomData,
    }
  }
}

impl<K: Eq + Hash, Item: Borrow<K>> HTNode<K, Item> {
  #[inline(always)]
  fn new(data: Item) -> HTNode<K, Item> {
    let priority = hash_priority(data.borrow());
    HTNode::new2(data, priority)
  }
}

impl<K, Item> HTNode<K, Item> {
  #[inline(always)]
  fn new2(data: Item, priority: u32) -> HTNode<K, Item> {
    HTNode{
      lhs:      None,
      rhs:      None,
      size:     1,
      priority,
      data,
      _phantom: PhantomData,
    }
  }

  #[inline(always)]
  fn subtree_update(&mut self) {
    self.size =
        self.lhs.as_ref().map(|x| x.size).unwrap_or_else(|| 0) +
        self.rhs.as_ref().map(|x| x.size).unwrap_or_else(|| 0) +
        1;
  }
}

impl<K: Ord, Item: Borrow<K>> HTNode<K, Item> {
  fn search<'r, Q: ?Sized + Ord>(root: &'r HTNode<K, Item>, key: &Q) -> Option<&'r Item>
  where K: Borrow<Q> {
    match key.cmp(root.data.borrow().borrow()) {
      Ordering::Less => {
        root.lhs.as_ref().and_then(|lhs| HTNode::search(lhs, key))
      }
      Ordering::Greater => {
        root.rhs.as_ref().and_then(|rhs| HTNode::search(rhs, key))
      }
      Ordering::Equal => {
        Some(&root.data)
      }
    }
  }
}

//impl<K: Ord, Item: Borrow<K>> HTNode<K, Item> {
impl<K: Ord, Item: Clone + Borrow<K>> HTNode<K, Item> {
  fn search_mut<'r, Q: ?Sized + Ord>(root: &'r mut HTNode<K, Item>, key: &Q) -> Option<&'r mut Item>
  where K: Borrow<Q> {
    match key.cmp(root.data.borrow().borrow()) {
      Ordering::Less => {
        root.lhs.as_mut().and_then(|lhs| HTNode::search_mut(Rc::make_mut(lhs), key))
      }
      Ordering::Greater => {
        root.rhs.as_mut().and_then(|rhs| HTNode::search_mut(Rc::make_mut(rhs), key))
      }
      Ordering::Equal => {
        Some(&mut root.data)
      }
    }
  }
}

impl<K, Item: Clone> HTNode<K, Item> {
  fn join(lhs: HTNodeRef<K, Item>, rhs: HTNodeRef<K, Item>) -> HTNodeRef<K, Item> {
    HTNode::_join(
        //lhs.as_mut().map(|x| Rc::make_mut(x)),
        //rhs.as_mut().map(|x| Rc::make_mut(x))
        lhs.map(|x| Rc::try_unwrap(x).unwrap_or_else(|x| (*x).clone())),
        rhs.map(|x| Rc::try_unwrap(x).unwrap_or_else(|x| (*x).clone()))
    //).map(|x| x.clone().into())
    ).map(|x| x.into())
  }

  //fn _join<'r>(lhs: Option<&'r mut HTNode<K, Item>>, rhs: Option<&'r mut HTNode<K, Item>>) -> Option<&'r mut HTNode<K, Item>> {
  fn _join(lhs: Option<HTNode<K, Item>>, rhs: Option<HTNode<K, Item>>) -> Option<HTNode<K, Item>> {
    match (lhs, rhs) {
      (None, None) => None,
      (None, rhs) => rhs,
      (lhs, None) => lhs,
      (Some(mut lhs), Some(mut rhs)) => {
        if lhs.priority >= rhs.priority {
          lhs.rhs = HTNode::_join(
              //lhs.rhs.as_mut().map(|x| Rc::make_mut(x)),
              lhs.rhs.map(|x| Rc::try_unwrap(x).unwrap_or_else(|x| (*x).clone())),
              Some(rhs)
          //).map(|x| x.clone().into());
          ).map(|x| x.into());
          lhs.subtree_update();
          Some(lhs)
        } else {
          rhs.lhs = HTNode::_join(
              Some(lhs),
              //rhs.lhs.as_mut().map(|x| Rc::make_mut(x))
              rhs.lhs.map(|x| Rc::try_unwrap(x).unwrap_or_else(|x| (*x).clone()))
          //).map(|x| x.clone().into());
          ).map(|x| x.into());
          rhs.subtree_update();
          Some(rhs)
        }
      }
    }
  }
}

impl<K: Ord + Hash, Item: Clone + Borrow<K>> HTNode<K, Item> {
  fn insert(root: HTNodeRef<K, Item>, mut data: Item) -> (HTNode<K, Item>, Option<Item>) {
    match root {
      None => (HTNode::new(data), None),
      Some(root) => {
        let mut root = match Rc::try_unwrap(root) {
          Ok(r) => r,
          Err(rr) => (*rr).clone(),
        };
        match data.borrow().cmp(root.data.borrow()) {
          Ordering::Less => {
            let (mut new_lhs, old_data) = HTNode::insert(root.lhs, data);
            if new_lhs.priority <= root.priority {
              root.lhs = Some(new_lhs.into());
              root.subtree_update();
              (root, old_data)
            } else {
              root.lhs = new_lhs.rhs;
              root.subtree_update();
              new_lhs.rhs = Some(root.into());
              new_lhs.subtree_update();
              (new_lhs, old_data)
            }
          }
          Ordering::Greater => {
            let (mut new_rhs, old_data) = HTNode::insert(root.rhs, data);
            if new_rhs.priority <= root.priority {
              root.rhs = Some(new_rhs.into());
              root.subtree_update();
              (root, old_data)
            } else {
              root.rhs = new_rhs.lhs;
              root.subtree_update();
              new_rhs.lhs = Some(root.into());
              new_rhs.subtree_update();
              (new_rhs, old_data)
            }
          }
          Ordering::Equal => {
            swap(&mut root.data, &mut data);
            (root, Some(data))
          }
        }
      }
    }
  }
}

impl<K: Ord, Item: Clone + Borrow<K>> HTNode<K, Item> {
  fn split_gtr<Q: ?Sized + Ord>(root: HTNodeRef<K, Item>, key: &Q) -> (HTNodeRef<K, Item>, Option<Item>)
  where K: Borrow<Q> {
    match root {
      None => (None, None),
      Some(root) => {
        let mut root = match Rc::try_unwrap(root) {
          Ok(r) => r,
          Err(rr) => (*rr).clone(),
        };
        match key.borrow().cmp(root.data.borrow().borrow()) {
          Ordering::Less => {
            let (gtr, data) = HTNode::split_gtr(root.lhs, key);
            root.lhs = gtr;
            root.subtree_update();
            (Some(root.into()), data)
          }
          Ordering::Greater => {
            HTNode::split_gtr(root.rhs, key)
          }
          Ordering::Equal => {
            (root.rhs, Some(root.data))
          }
        }
      }
    }
  }

  fn split<Q: ?Sized + Ord>(root: HTNodeRef<K, Item>, key: &Q) -> (HTNodeRef<K, Item>, HTNodeRef<K, Item>, Option<Item>)
  where K: Borrow<Q> {
    match root {
      None => (None, None, None),
      Some(root) => {
        let mut root = match Rc::try_unwrap(root) {
          Ok(r) => r,
          Err(rr) => (*rr).clone(),
        };
        match key.borrow().cmp(root.data.borrow().borrow()) {
          Ordering::Less => {
            let (lss, gtr, data) = HTNode::split(root.lhs, key);
            root.lhs = gtr;
            root.subtree_update();
            (lss, Some(root.into()), data)
          }
          Ordering::Greater => {
            let (lss, gtr, data) = HTNode::split(root.rhs, key);
            root.rhs = lss;
            root.subtree_update();
            (Some(root.into()), gtr, data)
          }
          Ordering::Equal => {
            (root.lhs, root.rhs, Some(root.data))
          }
        }
      }
    }
  }

  fn remove<Q: ?Sized + Ord>(root: HTNodeRef<K, Item>, key: &Q) -> (HTNodeRef<K, Item>, Option<Item>)
  where K: Borrow<Q> {
    let (lss, gtr, query) = HTNode::split(root.clone(), key);
    match query {
      None => (root, None),
      Some(query) => {
        (HTNode::join(lss, gtr), Some(query))
      }
    }
  }

  fn diff(lhs: HTNodeRef<K, Item>, rhs: HTNodeRef<K, Item>, mut sub_rhs: bool) -> HTNodeRef<K, Item> {
    match (lhs, rhs) {
      (None, None) => None,
      (None, rhs) => {
        if sub_rhs { None } else { rhs }
      }
      (lhs, None) => {
        if sub_rhs { lhs } else { None }
      }
      (Some(mut lhs), Some(mut rhs)) => {
        if lhs.priority < rhs.priority {
          sub_rhs = !sub_rhs;
          swap(&mut lhs, &mut rhs);
        }
        let (lss, gtr, query) = HTNode::split(Some(rhs), lhs.data.borrow());
        let new_lhs = HTNode::diff(lhs.lhs.clone(), lss, sub_rhs);
        let new_rhs = HTNode::diff(lhs.rhs.clone(), gtr, sub_rhs);
        if query.is_none() && sub_rhs {
          let mut new_root = HTNode{
            lhs:        new_lhs,
            rhs:        new_rhs,
            size:       0,
            priority:   lhs.priority,
            data:       lhs.data.clone(),
            _phantom:   PhantomData,
          };
          new_root.subtree_update();
          Some(new_root.into())
        } else {
          HTNode::join(new_lhs, new_rhs)
        }
      }
    }
  }

  fn diff_left<ItemR: Clone + Borrow<K>>(lhs: HTNodeRef<K, Item>, rhs: HTNodeRef<K, ItemR>) -> HTNodeRef<K, Item> {
    match (lhs, rhs) {
      (None, None) |
      (None, _) |
      (_, None) => None,
      (Some(lhs), Some(rhs)) => {
        let (new_lhs, new_rhs, noquery) = if lhs.priority >= rhs.priority {
          let (lss, gtr, query) = HTNode::split(Some(rhs), lhs.data.borrow());
          let new_lhs = HTNode::diff_left(lhs.lhs.clone(), lss);
          let new_rhs = HTNode::diff_left(lhs.rhs.clone(), gtr);
          (new_lhs, new_rhs, query.is_none())
        } else {
          let (lss, gtr, _) = HTNode::split(Some(lhs.clone()), rhs.data.borrow());
          let new_lhs = HTNode::diff_left(lss, rhs.lhs.clone());
          let new_rhs = HTNode::diff_left(gtr, rhs.rhs.clone());
          (new_lhs, new_rhs, false)
        };
        if noquery {
          let mut new_root = HTNode{
            lhs:        new_lhs,
            rhs:        new_rhs,
            size:       0,
            priority:   lhs.priority,
            data:       lhs.data.clone(),
            _phantom:   PhantomData,
          };
          new_root.subtree_update();
          Some(new_root.into())
        } else {
          HTNode::join(new_lhs, new_rhs)
        }
      }
    }
  }

  fn symm_diff(lhs: HTNodeRef<K, Item>, rhs: HTNodeRef<K, Item>) -> HTNodeRef<K, Item> {
    match (lhs, rhs) {
      (None, None) |
      (None, _) |
      (_, None) => None,
      (Some(mut lhs), Some(mut rhs)) => {
        if lhs.priority < rhs.priority {
          swap(&mut lhs, &mut rhs);
        }
        let (lss, gtr, query) = HTNode::split(Some(rhs), lhs.data.borrow());
        let new_lhs = HTNode::symm_diff(lhs.lhs.clone(), lss);
        let new_rhs = HTNode::symm_diff(lhs.rhs.clone(), gtr);
        if query.is_none() {
          let mut new_root = HTNode{
            lhs:        new_lhs,
            rhs:        new_rhs,
            size:       0,
            priority:   lhs.priority,
            data:       lhs.data.clone(),
            _phantom:   PhantomData,
          };
          new_root.subtree_update();
          Some(new_root.into())
        } else {
          HTNode::join(new_lhs, new_rhs)
        }
      }
    }
  }

  fn union_one(lhs: HTNodeRef<K, Item>, rhs: HTNodeRef<K, Item>) -> HTNodeRef<K, Item> {
    match (lhs, rhs) {
      (None, None) => None,
      (None, Some(rhs)) => Some(rhs),
      (Some(lhs), None) => Some(lhs),
      (Some(mut lhs), Some(mut rhs)) => {
        if lhs.priority < rhs.priority {
          swap(&mut lhs, &mut rhs);
        }
        let (lss, gtr, _) = HTNode::split(Some(rhs), lhs.data.borrow());
        let new_lhs = HTNode::union_one(lhs.lhs.clone(), lss);
        let new_rhs = HTNode::union_one(lhs.rhs.clone(), gtr);
        let mut new_root = HTNode{
          lhs:      new_lhs,
          rhs:      new_rhs,
          size:     0,
          priority: lhs.priority,
          data:     lhs.data.clone(),
          _phantom: PhantomData,
        };
        new_root.subtree_update();
        Some(new_root.into())
      }
    }
  }

  fn union_left(lhs: HTNodeRef<K, Item>, rhs: HTNodeRef<K, Item>) -> HTNodeRef<K, Item> {
    match (lhs, rhs) {
      (None, None) => None,
      (None, Some(rhs)) => Some(rhs),
      (Some(lhs), None) => Some(lhs),
      (Some(lhs), Some(rhs)) => {
        let (new_lhs, new_rhs) = if lhs.priority >= rhs.priority {
          let (lss, gtr, _) = HTNode::split(Some(rhs), lhs.data.borrow());
          let new_lhs = HTNode::union_left(lhs.lhs.clone(), lss);
          let new_rhs = HTNode::union_left(lhs.rhs.clone(), gtr);
          (new_lhs, new_rhs)
        } else {
          let (lss, gtr, _) = HTNode::split(Some(lhs.clone()), rhs.data.borrow());
          let new_lhs = HTNode::union_left(lss, lhs.lhs.clone());
          let new_rhs = HTNode::union_left(gtr, lhs.rhs.clone());
          (new_lhs, new_rhs)
        };
        let mut new_root = HTNode{
          lhs:      new_lhs,
          rhs:      new_rhs,
          size:     0,
          priority: lhs.priority,
          data:     lhs.data.clone(),
          _phantom: PhantomData,
        };
        new_root.subtree_update();
        Some(new_root.into())
      }
    }
  }

  fn intersect_one(lhs: HTNodeRef<K, Item>, rhs: HTNodeRef<K, Item>) -> HTNodeRef<K, Item> {
    match (lhs, rhs) {
      (None, None) |
      (None, _) |
      (_, None) => None,
      (Some(mut lhs), Some(mut rhs)) => {
        if lhs.priority < rhs.priority {
          swap(&mut lhs, &mut rhs);
        }
        let (lss, gtr, query) = HTNode::split(Some(rhs), lhs.data.borrow());
        let new_lhs = HTNode::intersect_one(lhs.lhs.clone(), lss);
        let new_rhs = HTNode::intersect_one(lhs.rhs.clone(), gtr);
        if query.is_none() {
          HTNode::join(new_lhs, new_rhs)
        } else {
          let mut new_root = HTNode{
            lhs:        new_lhs,
            rhs:        new_rhs,
            size:       0,
            priority:   lhs.priority,
            data:       lhs.data.clone(),
            _phantom:   PhantomData,
          };
          new_root.subtree_update();
          Some(new_root.into())
        }
      }
    }
  }

  fn intersect_left<ItemR: Clone + Borrow<K>>(lhs: HTNodeRef<K, Item>, rhs: HTNodeRef<K, ItemR>) -> HTNodeRef<K, Item> {
    match (lhs, rhs) {
      (None, None) |
      (None, _) |
      (_, None) => None,
      (Some(lhs), Some(rhs)) => {
        let (new_lhs, new_rhs, noquery) = if lhs.priority >= rhs.priority {
          let (lss, gtr, query) = HTNode::split(Some(rhs), lhs.data.borrow());
          let new_lhs = HTNode::intersect_left(lhs.lhs.clone(), lss);
          let new_rhs = HTNode::intersect_left(lhs.rhs.clone(), gtr);
          (new_lhs, new_rhs, query.is_none())
        } else {
          let (lss, gtr, query) = HTNode::split(Some(lhs.clone()), rhs.data.borrow());
          let new_lhs = HTNode::intersect_left(lss, rhs.lhs.clone());
          let new_rhs = HTNode::intersect_left(gtr, rhs.rhs.clone());
          (new_lhs, new_rhs, query.is_none())
        };
        if noquery {
          HTNode::join(new_lhs, new_rhs)
        } else {
          let mut new_root = HTNode{
            lhs:        new_lhs,
            rhs:        new_rhs,
            size:       0,
            priority:   lhs.priority,
            data:       lhs.data.clone(),
            _phantom:   PhantomData,
          };
          new_root.subtree_update();
          Some(new_root.into())
        }
      }
    }
  }
}

impl<K: Clone + Ord, V> HTNode<K, Record<K, V>> {
  fn map<F: FnMut(&K, &V) -> W, W>(root: HTNodeRef<K, Record<K, V>>, f: &mut F) -> HTNodeRef<K, Record<K, W>> {
    match root {
      None => None,
      Some(root) => {
        let priority = root.priority;
        let key = root.data.key.clone();
        let value = (f)(&key, &root.data.value);
        let new_data = Record{key, value};
        let mut new_root = HTNode{
          lhs:      HTNode::map(root.lhs.clone(), f),
          rhs:      HTNode::map(root.rhs.clone(), f),
          size:     0,
          priority,
          data:     new_data,
          _phantom: PhantomData,
        };
        new_root.subtree_update();
        Some(new_root.into())
      }
    }
  }
}

impl<K: Clone + Ord, V: Clone> HTNode<K, Record<K, V>> {
  fn union_merge<F: FnMut(&K, &V, &V) -> V>(lhs: HTNodeRef<K, Record<K, V>>, rhs: HTNodeRef<K, Record<K, V>>, f: &mut F) -> HTNodeRef<K, Record<K, V>> {
    match (lhs, rhs) {
      (None, None) => None,
      (None, Some(rhs)) => Some(rhs),
      (Some(lhs), None) => Some(lhs),
      (Some(mut lhs), Some(mut rhs)) => {
        if lhs.priority < rhs.priority {
          swap(&mut lhs, &mut rhs);
        }
        let (lss, gtr, query) = HTNode::split(Some(rhs), lhs.data.borrow());
        let new_lhs = HTNode::union_merge(lhs.lhs.clone(), lss, f);
        let new_rhs = HTNode::union_merge(lhs.rhs.clone(), gtr, f);
        let priority = lhs.priority;
        let new_data = match query {
          None => {
            lhs.data.clone()
          }
          Some(query) => {
            let key = lhs.data.key.clone();
            let value = (f)(&key, &lhs.data.value, &query.value);
            Record{key, value}
          }
        };
        let mut new_root = HTNode{
          lhs:      new_lhs,
          rhs:      new_rhs,
          size:     0,
          priority,
          data:     new_data,
          _phantom: PhantomData,
        };
        new_root.subtree_update();
        Some(new_root.into())
      }
    }
  }

  fn intersect_merge<F: FnMut(&K, &V, &V) -> W, W: Clone>(lhs: HTNodeRef<K, Record<K, V>>, rhs: HTNodeRef<K, Record<K, V>>, f: &mut F) -> HTNodeRef<K, Record<K, W>> {
    match (lhs, rhs) {
      (None, None) |
      (None, _) |
      (_, None) => None,
      (Some(mut lhs), Some(mut rhs)) => {
        if lhs.priority < rhs.priority {
          swap(&mut lhs, &mut rhs);
        }
        let (lss, gtr, query) = HTNode::split(Some(rhs), lhs.data.borrow());
        let new_lhs = HTNode::intersect_merge(lhs.lhs.clone(), lss, f);
        let new_rhs = HTNode::intersect_merge(lhs.rhs.clone(), gtr, f);
        match query {
          None => HTNode::join(new_lhs, new_rhs),
          Some(query) => {
            let priority = lhs.priority;
            let key = lhs.data.key.clone();
            let value = (f)(&key, &lhs.data.value, &query.value);
            let new_data = Record{key, value};
            let mut new_root = HTNode{
              lhs:      new_lhs,
              rhs:      new_rhs,
              size:     0,
              priority,
              data:     new_data,
              _phantom: PhantomData,
            };
            new_root.subtree_update();
            Some(new_root.into())
          }
        }
      }
    }
  }
}

impl<K: Clone + Ord, V> HTNode<K, RecordRef<K, V>> {
  fn map_ref<F: FnMut(&K, &V) -> W, W>(root: HTNodeRef<K, RecordRef<K, V>>, f: &mut F) -> HTNodeRef<K, RecordRef<K, W>> {
    match root {
      None => None,
      Some(root) => {
        let priority = root.priority;
        let key = root.data.key.clone();
        let value = (f)(&key, &root.data.value);
        let new_data = Record{key, value};
        let mut new_root = HTNode{
          lhs:      HTNode::map_ref(root.lhs.clone(), f),
          rhs:      HTNode::map_ref(root.rhs.clone(), f),
          size:     0,
          priority,
          data:     new_data.into(),
          _phantom: PhantomData,
        };
        new_root.subtree_update();
        Some(new_root.into())
      }
    }
  }

  fn intersect_map_ref<F: FnMut(&K, &V, &V) -> W, W>(lhs: HTNodeRef<K, RecordRef<K, V>>, rhs: HTNodeRef<K, RecordRef<K, V>>, f: &mut F) -> HTNodeRef<K, RecordRef<K, W>> {
    match (lhs, rhs) {
      (None, None) |
      (None, _) |
      (_, None) => None,
      (Some(mut lhs), Some(mut rhs)) => {
        if lhs.priority < rhs.priority {
          swap(&mut lhs, &mut rhs);
        }
        let (lss, gtr, query) = HTNode::split(Some(rhs), lhs.data.borrow());
        let new_lhs = HTNode::intersect_map_ref(lhs.lhs.clone(), lss, f);
        let new_rhs = HTNode::intersect_map_ref(lhs.rhs.clone(), gtr, f);
        match query {
          None => HTNode::join(new_lhs, new_rhs),
          Some(query) => {
            let priority = lhs.priority;
            let key = lhs.data.key.clone();
            let value = (f)(&key, &lhs.data.value, &query.value);
            let new_data = Record{key, value};
            let mut new_root = HTNode{
              lhs:      new_lhs,
              rhs:      new_rhs,
              size:     0,
              priority,
              data:     new_data.into(),
              _phantom: PhantomData,
            };
            new_root.subtree_update();
            Some(new_root.into())
          }
        }
      }
    }
  }
}

struct HTNodeCloneIter<K, Item> {
  next: HTNodeRef<K, Item>,
  stak: Vec<Rc<HTNode<K, Item>>>,
}

impl<K, Item> HTNodeCloneIter<K, Item> {
  fn new(root: HTNodeRef<K, Item>) -> HTNodeCloneIter<K, Item> {
    HTNodeCloneIter{
      next: root,
      stak: vec![],
    }
  }
}

impl<K, Item: Borrow<K>> HTNodeCloneIter<K, Item> {
  fn search_lb<Q: ?Sized + Ord>(root: HTNodeRef<K, Item>, key: &Q) -> HTNodeCloneIter<K, Item>
  where K: Borrow<Q> {
    let mut cursor = HTNodeCloneIter::new(root);
    loop {
      match cursor.next.take() {
        Some(next) => {
          match key.cmp(next.data.borrow().borrow()) {
            Ordering::Less => {
              cursor.next = next.lhs.clone();
              cursor.stak.push(next);
            }
            Ordering::Greater => {
              cursor.next = next.rhs.clone();
            }
            Ordering::Equal => {
              cursor.stak.push(next);
              break;
            }
          }
        }
        None => break
      }
    }
    cursor
  }

  fn search_lb_excl<Q: ?Sized + Ord>(root: HTNodeRef<K, Item>, key: &Q) -> HTNodeCloneIter<K, Item>
  where K: Borrow<Q> {
    let mut cursor = HTNodeCloneIter::new(root);
    loop {
      match cursor.next.take() {
        Some(next) => {
          match key.cmp(next.data.borrow().borrow()) {
            Ordering::Less => {
              cursor.next = next.lhs.clone();
              cursor.stak.push(next);
            }
            Ordering::Greater |
            Ordering::Equal => {
              cursor.next = next.rhs.clone();
            }
          }
        }
        None => break
      }
    }
    cursor
  }
}

impl<K, Item: Clone> Iterator for HTNodeCloneIter<K, Item> {
  type Item = Item;

  fn next(&mut self) -> Option<Item> {
    loop {
      match self.next.take() {
        Some(next) => {
          self.next = next.lhs.clone();
          self.stak.push(next);
        }
        None => return self.stak.pop().map(|top| {
          self.next = top.rhs.clone();
          top.data.clone()
        })
      }
    }
  }
}

struct HTNodeIter<'a, K, Item> {
  next: Option<&'a HTNode<K, Item>>,
  stak: Vec<&'a HTNode<K, Item>>,
}

impl<'a, K, Item> HTNodeIter<'a, K, Item> {
  fn new(root: &'a HTNodeRef<K, Item>) -> HTNodeIter<'a, K, Item> {
    HTNodeIter{
      next: root.as_ref().map(|r| &**r),
      stak: vec![],
    }
  }
}

impl<'a, K, Item: Borrow<K>> HTNodeIter<'a, K, Item> {
  fn search_lb<Q: ?Sized + Ord>(root: &'a HTNodeRef<K, Item>, key: &Q) -> HTNodeIter<'a, K, Item>
  where K: Borrow<Q> {
    let mut cursor = HTNodeIter::new(root);
    loop {
      match cursor.next.take() {
        Some(next) => {
          match key.cmp(next.data.borrow().borrow()) {
            Ordering::Less => {
              cursor.next = next.lhs.as_ref().map(|lhs| &**lhs);
              cursor.stak.push(next);
            }
            Ordering::Greater => {
              cursor.next = next.rhs.as_ref().map(|rhs| &**rhs);
            }
            Ordering::Equal => {
              cursor.stak.push(next);
              break;
            }
          }
        }
        None => break
      }
    }
    cursor
  }

  fn search_lb_excl<Q: ?Sized + Ord>(root: &'a HTNodeRef<K, Item>, key: &Q) -> HTNodeIter<'a, K, Item>
  where K: Borrow<Q> {
    let mut cursor = HTNodeIter::new(root);
    loop {
      match cursor.next.take() {
        Some(next) => {
          match key.cmp(next.data.borrow().borrow()) {
            Ordering::Less => {
              cursor.next = next.lhs.as_ref().map(|lhs| &**lhs);
              cursor.stak.push(next);
            }
            Ordering::Greater |
            Ordering::Equal => {
              cursor.next = next.rhs.as_ref().map(|rhs| &**rhs);
            }
          }
        }
        None => break
      }
    }
    cursor
  }
}

impl<'a, K, Item> Iterator for HTNodeIter<'a, K, Item> {
  type Item = &'a Item;

  fn next(&mut self) -> Option<&'a Item> {
    loop {
      match self.next.take() {
        Some(next) => {
          self.next = next.lhs.as_ref().map(|lhs| &**lhs);
          self.stak.push(next);
        }
        None => return self.stak.pop().map(|top| {
          self.next = top.rhs.as_ref().map(|rhs| &**rhs);
          &top.data
        })
      }
    }
  }
}

struct HTNodeRevIter<'a, K, Item> {
  next: Option<&'a HTNode<K, Item>>,
  stak: Vec<&'a HTNode<K, Item>>,
}

impl<'a, K, Item> HTNodeRevIter<'a, K, Item> {
  fn new(root: &'a HTNodeRef<K, Item>) -> HTNodeRevIter<'a, K, Item> {
    HTNodeRevIter{
      next: root.as_ref().map(|r| &**r),
      stak: vec![],
    }
  }
}

impl<'a, K, Item: Borrow<K>> HTNodeRevIter<'a, K, Item> {
  fn search_ub<Q: ?Sized + Ord>(root: &'a HTNodeRef<K, Item>, key: &Q) -> HTNodeRevIter<'a, K, Item>
  where K: Borrow<Q> {
    let mut cursor = HTNodeRevIter::new(root);
    loop {
      match cursor.next.take() {
        Some(next) => {
          match key.cmp(next.data.borrow().borrow()) {
            Ordering::Greater => {
              cursor.next = next.rhs.as_ref().map(|rhs| &**rhs);
              cursor.stak.push(next);
            }
            Ordering::Less => {
              cursor.next = next.lhs.as_ref().map(|lhs| &**lhs);
            }
            Ordering::Equal => {
              cursor.stak.push(next);
              break;
            }
          }
        }
        None => break
      }
    }
    cursor
  }

  fn search_ub_excl<Q: ?Sized + Ord>(root: &'a HTNodeRef<K, Item>, key: &Q) -> HTNodeRevIter<'a, K, Item>
  where K: Borrow<Q> {
    let mut cursor = HTNodeRevIter::new(root);
    loop {
      match cursor.next.take() {
        Some(next) => {
          match key.cmp(next.data.borrow().borrow()) {
            Ordering::Greater => {
              cursor.next = next.rhs.as_ref().map(|rhs| &**rhs);
              cursor.stak.push(next);
            }
            Ordering::Less |
            Ordering::Equal => {
              cursor.next = next.lhs.as_ref().map(|lhs| &**lhs);
            }
          }
        }
        None => break
      }
    }
    cursor
  }
}

impl<'a, K, Item> Iterator for HTNodeRevIter<'a, K, Item> {
  type Item = &'a Item;

  fn next(&mut self) -> Option<&'a Item> {
    loop {
      match self.next.take() {
        Some(next) => {
          self.next = next.rhs.as_ref().map(|rhs| &**rhs);
          self.stak.push(next);
        }
        None => return self.stak.pop().map(|top| {
          self.next = top.lhs.as_ref().map(|lhs| &**lhs);
          &top.data
        })
      }
    }
  }
}
