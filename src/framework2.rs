pub use self::TScanResult::{End, Hit, Skip};
pub use self::TSwapStatus::{Noswap, Merge, Fresh, Stale};

use crate::algo::*;
use crate::bench::*;
use crate::framework::*;
use crate::log::*;
use crate::rng::{CategoricalHeap, RngCore, URange, choose_one_mut};

use std::any::{Any};
use std::cell::{RefCell};
use std::cmp::{Ordering, max, min};
use std::hash::{Hash};
use std::mem::{swap};
use std::sync::{Arc as Rc};

#[derive(Clone, Debug)]
pub struct TClk {
  tctr: TNum
}

impl Default for TClk {
  fn default() -> TClk {
    TClk{tctr: 0}
  }
}

impl TClk {
  pub fn checkpoint(&self) -> TSnapshot {
    TSnapshot{t: self.tctr}
  }

  pub fn diff(&self, other: &TClk) -> TDiff {
    TDiff{dt: self.tctr as i64 - other.tctr as i64}
  }

  pub fn fresh(&mut self) -> TNum {
    let tnew = self.tctr + 1;
    assert!(tnew != 0);
    self.tctr = tnew;
    tnew
  }
}

#[derive(Clone, Copy, Debug)]
pub struct TSnapshot {
  t:    TNum,
}

impl TSnapshot {
  pub fn lub(&self) -> TNum {
    self.t
  }

  pub fn next_glb(&self) -> TNum {
    self.t + 1
  }
}

impl PartialEq for TSnapshot {
  fn eq(&self, other: &TSnapshot) -> bool {
    self.t == other.t
  }
}

impl Eq for TSnapshot {}

impl PartialOrd for TSnapshot {
  fn partial_cmp(&self, other: &TSnapshot) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for TSnapshot {
  fn cmp(&self, other: &TSnapshot) -> Ordering {
    self.t.cmp(&other.t)
  }
}

#[derive(Clone, Copy, Debug)]
pub struct TDiff {
  dt:   i64,
}

impl TDiff {
  pub fn offset(&self) -> i64 {
    self.dt
  }
}

#[derive(Clone, Debug)]
pub struct TUniverse {
  vctr: SNum,
}

impl Default for TUniverse {
  fn default() -> TUniverse {
    TUniverse{vctr: 0}
  }
}

impl TUniverse {
  pub fn checkpoint(&self) -> TAtlas {
    TAtlas{v: self.vctr}
  }

  pub fn provision(&self, chk: &mut TAtlas) -> SNum {
    let vnew = chk.v + 1;
    assert!(vnew != 0);
    chk.v = vnew;
    vnew
  }

  pub fn fresh(&mut self) -> SNum {
    let vnew = self.vctr + 1;
    assert!(vnew != 0);
    self.vctr = vnew;
    vnew
  }
}

#[derive(Clone, Copy, Debug)]
pub struct TAtlas {
  v:    SNum,
}

impl TAtlas {
  pub fn lub(&self) -> SNum {
    self.v
  }
}

#[derive(Clone, Copy, Debug)]
pub enum TAttr {
  Top,
  Gen,
  DefCom1(CVar, CVar),
  //DefComX(CVar, CVar),
  FunSwap(CVar, CVar),
  Swap(CVar),
  Fun(CVar),
  //Def(CVar),
}

#[derive(Clone, Copy, Debug)]
pub struct TUSnapshot {
  tu:   TNum,
}

impl Default for TUSnapshot {
  fn default() -> TUSnapshot {
    TUSnapshot{tu: 0}
  }
}

impl TUSnapshot {
  pub fn is_ulive(&self, uf: &TUnionFind) -> bool {
    if self.tu > uf.tu {
      panic!("bug: TUSnapshot::is_ulive");
    } else {
      self.tu == uf.tu
    }
  }
}

#[derive(Clone)]
pub struct TUDiff {
  dlog: IHTreapMap<(TNum, CVar), CVar>,
}

impl TUDiff {
  pub fn size(&self) -> u64 {
    self.dlog.len() as u64
  }
}

#[derive(Clone, Default)]
pub struct TDiagnosticUnionFind {
  t:    TNum,
  tu:   TNum,
  rdom: Vec<(TNum, CVar)>,
  //ulog: Vec<(TNum, CVar, CVar)>,
}

pub trait TCongruenceClosure<T> {
  fn tfind(&mut self, kp: T) -> T;
}

impl TCongruenceClosure<CVar> for TUnionFind {
  fn tfind(&mut self, k: CVar) -> CVar {
    let (_, x) = self.find(k);
    x
  }
}

impl TCongruenceClosure<CTup2> for TUnionFind {
  fn tfind(&mut self, kp: CTup2) -> CTup2 {
    let mut xp = CTup2::default();
    self.vfind(kp.as_ref(), xp.as_mut());
    xp
  }
}

impl TCongruenceClosure<CTup3> for TUnionFind {
  fn tfind(&mut self, kp: CTup3) -> CTup3 {
    let mut xp = CTup3::default();
    self.vfind(kp.as_ref(), xp.as_mut());
    xp
  }
}

impl TCongruenceClosure<CTup4> for TUnionFind {
  fn tfind(&mut self, kp: CTup4) -> CTup4 {
    let mut xp = CTup4::default();
    self.vfind(kp.as_ref(), xp.as_mut());
    xp
  }
}

impl TCongruenceClosure<CTup5> for TUnionFind {
  fn tfind(&mut self, kp: CTup5) -> CTup5 {
    let mut xp = CTup5::default();
    self.vfind(kp.as_ref(), xp.as_mut());
    xp
  }
}

impl TCongruenceClosure<CTup6> for TUnionFind {
  fn tfind(&mut self, kp: CTup6) -> CTup6 {
    let mut xp = CTup6::default();
    self.vfind(kp.as_ref(), xp.as_mut());
    xp
  }
}

#[derive(Clone, Default)]
pub struct TUnionFind {
  t:    TNum,
  tu:   TNum,
  rset: IHTreapMap<CVar, TNum>,
  //rset: IHTreapMap<CVar, (TNum, TDepth)>,
  rdom: IHTreapSet<(TNum, CVar)>,
  rmap: IHTreapMap<CVar, (TNum, CVar)>,
  ulog: IHTreapMap<(TNum, CVar), CVar>,
  //uset: IHTreapMap<CVar, (TNum, CVar)>,
  //hset: IHTreapMap<CVar, TNum>,
  //hdom: IHTreapMap<(TNum, CVar)>,
  //kmap: IHTreapMap<CVar, IHTreapSet<CVar>>,
  attr: IHTreapMap<TNum, TAttr>,
}

impl TUnionFind {
  pub fn diagnostic(&self) -> TDiagnosticUnionFind {
    let mut rdom = Vec::with_capacity(self.rdom.len());
    //let mut ulog = Vec::with_capacity(self.ulog.len());
    for &(t, k) in self.rdom.iter() {
      rdom.push((t, k));
    }
    /*for (&(t, k), &v) in self.ulog.iter() {
      ulog.push((t, k, v));
    }*/
    TDiagnosticUnionFind{
      t:    self.t,
      tu:   self.tu,
      rdom,
      //ulog,
    }
  }

  pub fn patchdiff(&mut self, older: &TUnionFind) -> (usize, usize) {
    // TODO
    let mut patch_rset = IHTreapMap::default();
    for (&k, &t) in older.rset.iter() {
      let (_, x) = self.find(k);
      patch_rset.insert(x, t);
    }
    /*(patch_rset.difference(&self.rset).len(),
     self.rset.difference(&patch_rset).len())*/
    (max(patch_rset.len(), older.rset.len()) - patch_rset.len(),
     max(patch_rset.len(), self.rset.len()) - patch_rset.len())
  }

  pub fn usnapshot(&self) -> TUSnapshot {
    TUSnapshot{tu: self.tu}
  }

  /*pub fn usnapdiffsize(&self, older: &TUSnapshot) -> usize {
    // TODO
    self.ulog.count_greater(&(older.tu, CVar::ub()))
  }*/

  pub fn usnapdiff(&self, older: &TUSnapshot) -> impl Iterator<Item=((TNum, CVar), CVar)> {
    self.ulog.clone_iter_from_excl(&(older.tu, CVar::ub()))
  }

  pub fn udiff(&self, older: &TUnionFind) -> TUDiff {
    TUDiff{dlog: self.ulog.difference(&older.ulog)}
  }

  pub fn lub(&self) -> TNum {
    self.t
  }

  pub fn count(&self) -> usize {
    self.rmap.len()
  }

  pub fn ucount(&self) -> usize {
    self.rset.len()
  }

  pub fn fresh(&mut self, a: TAttr, /*fwd: SDepth,*/ univ: &mut TUniverse, clk: &mut TClk) -> CVar {
    let k = CVar(univ.fresh());
    assert!(k < CVar::ub(), "BUG: TUnionFind::fresh: reached ub");
    let t = clk.fresh();
    self.t = t;
    self.rset.insert(k, t);
    //self.rset.insert(k, (t, TDepth::gen(fwd)));
    self.rdom.insert((t, k));
    self.rmap.insert(k, (t, k));
    self.attr.insert(t, a);
    k
  }

  pub fn vfind(&mut self, ks: &[CVar], xs: &mut [CVar]) {
    for (i, &k) in ks.iter().enumerate() {
      let (_, x) = self.find(k);
      xs[i] = x;
    }
  }

  pub fn find_nonmut(&self, k: CVar) -> (TNum, CVar) {
    if k.0 == 0 {
      // FIXME
      return (0, CVar(0));
      //return (0, CVar::ub());
    }
    match self.get_nonmut(k) {
      None => panic!("BUG: TUnionFind::find_nonmut: missing var: {:?}", k),
      Some((t, x)) => (t, x)
    }
  }

  pub fn get_nonmut(&self, k: CVar) -> Option<(TNum, CVar)> {
    let (nt, mut nx) = match self.rmap.get(&k) {
      None => {
        return None;
      }
      Some(&np) => np
    };
    if k == nx {
      return Some((nt, nx));
    }
    let mut x = k;
    let mut iter_ct = 0;
    loop {
      iter_ct += 1;
      /*if iter_ct == 100 {
        println!("TRACE: TUnionFind::get: loop 100x");
      }*/
      let (nt2, nx2) = match self.rmap.get(&nx) {
        None => unreachable!(),
        Some(&np2) => np2
      };
      if nx == nx2 {
        if iter_ct >= 100 {
          println!("WARNING: TUnionFind::get_nonmut: long loop iter_ct={}", iter_ct);
        }
        return Some((nt2, nx2));
      }
      x = nx;
      nx = nx2;
    }
  }

  pub fn find(&mut self, k: CVar) -> (TNum, CVar) {
    if k.0 == 0 {
      // FIXME
      return (0, CVar(0));
      //return (0, CVar::ub());
    }
    match self.get(k) {
      None => panic!("BUG: TUnionFind::find: missing var: {:?}", k),
      Some((t, x)) => (t, x)
    }
  }

  pub fn get(&mut self, k: CVar) -> Option<(TNum, CVar)> {
    let (nt, mut nx) = match self.rmap.get(&k) {
      None => {
        return None;
      }
      Some(&np) => np
    };
    if k == nx {
      return Some((nt, nx));
    }
    let mut x = k;
    let mut iter_ct = 0;
    loop {
      iter_ct += 1;
      /*if iter_ct == 100 {
        println!("TRACE: TUnionFind::get: loop 100x");
      }*/
      let (nt2, nx2) = match self.rmap.get(&nx) {
        None => unreachable!(),
        Some(&np2) => np2
      };
      if nx == nx2 {
        if iter_ct >= 100 {
          println!("WARNING: TUnionFind::get: long loop iter_ct={}", iter_ct);
        }
        return Some((nt2, nx2));
      }
      self.rmap.insert(x, (nt2, nx2));
      x = nx;
      nx = nx2;
    }
  }

  fn _lunify(&mut self, a: TAttr, lt: TNum, lr: CVar, rt: TNum, rr: CVar, t: TNum, ur: CVar) -> (TNum, CVar, bool) {
    // TODO
    self.t = t;
    self.tu = t;
    //self.rset.remove(&rr);
    self.rdom.remove(&(lt, lr));
    self.rdom.remove(&(rt, rr));
    //self.rdom.insert((t, lr));
    self.rdom.insert((t, ur));
    //self.rmap.insert(rr, (t, lr));
    //self.rmap.insert(lr, (t, lr));
    self.rmap.insert(rr, (t, ur));
    self.rmap.insert(lr, (t, ur));
    //self.ulog.insert((t, rr), lr);
    if lr == ur {
      self.rset.remove(&rr);
      self.ulog.insert((t, rr), ur);
    } else if rr == ur {
      self.rset.remove(&lr);
      self.ulog.insert((t, lr), ur);
    } else {
      unreachable!();
    }
    //self.uset.insert(rr, (t, lr));
    self.attr.insert(t, a);
    (t, lr, true)
  }

  pub fn unify(&mut self, a: TAttr, lk: CVar, rk: CVar, clk: &mut TClk) -> (TNum, CVar, bool) {
    if lk == CVar(0) || rk == CVar(0) {
      panic!("BUG: TUnionFind::unify: tried to unify with lb: lk={:?} rk={:?}", lk, rk);
    }
    let (lt, lr) = self.find(lk);
    if lk == rk {
      return (lt, lr, false);
    }
    let (rt, rr) = self.find(rk);
    if lr == rr {
      return (rt, rr, false);
    }
    let t = clk.fresh();
    if lt == rt {
      panic!("BUG: TUnionFind::unify: lt={} rt={}", lt, rt);
    } else if lt < rt {
      self._lunify(a, rt, rr, lt, lr, t, min(lr, rr))
    } else {
      self._lunify(a, lt, lr, rt, rr, t, min(lr, rr))
    }
  }
}

pub struct CUIter<V: Copy> {
  x:    Option<V>,
  k:    CVar,
  ch:   IHTreapMap<(CVar, V), V>,
}

impl<V: Copy + Ord + Hash> Iterator for CUIter<V> {
  type Item = V;

  fn next(&mut self) -> Option<V> {
    match self.x {
      None => None,
      Some(x) => {
        match self.ch.get(&(self.k, x)) {
          None => unreachable!(),
          Some(&nx) => if x == nx {
            self.x = None;
          } else {
            self.x = Some(nx);
          }
        }
        Some(x)
      }
    }
  }
}

#[derive(Clone)]
pub struct CUnionIter_<V: Clone> {
  data: IHTreapMap<CVar, IHTreapSet<V>>,
}

impl<V: Clone> Default for CUnionIter_<V> {
  fn default() -> CUnionIter_<V> {
    CUnionIter_{
      data: IHTreapMap::default(),
    }
  }
}

impl<V: Clone + Ord + Hash> CUnionIter_<V> {
  pub fn iter(&self, k: CVar) -> impl Iterator<Item=V> {
    match self.data.get(&k) {
      None => {
        // FIXME
        unimplemented!();
      }
      Some(set) => {
        set.clone_iter()
      }
    }
  }

  pub fn insert(&mut self, k: CVar, v: V) {
    match self.data.get_mut(&k) {
      None => {
        let mut set = IHTreapSet::default();
        set.insert(v);
        self.data.insert(k, set);
      }
      Some(set) => {
        set.insert(v);
      }
    }
  }

  pub fn remove(&mut self, k: CVar) {
    self.data.remove(&k);
  }
}

#[derive(Clone)]
pub struct CUnionIter<V: Copy> {
  rt:   IHTreapMap<CVar, (V, V)>,
  ch:   IHTreapMap<(CVar, V), V>,
}

impl<V: Copy> Default for CUnionIter<V> {
  fn default() -> CUnionIter<V> {
    CUnionIter{
      rt:   IHTreapMap::default(),
      ch:   IHTreapMap::default(),
    }
  }
}

impl<V: Copy + Ord + Hash> CUnionIter<V> {
  pub fn iter(&self, k: CVar) -> CUIter<V> {
    match self.rt.get(&k) {
      None => CUIter{
        x:  None,
        k,
        ch: self.ch.clone(),
      },
      Some(&(x, _)) => CUIter{
        x:  Some(x),
        k,
        ch: self.ch.clone(),
      }
    }
  }

  pub fn insert(&mut self, k: CVar, v: V) {
    match self.rt.get(&k) {
      None => {
        self.rt.insert(k, (v, v));
        self.ch.insert((k, v), v);
      }
      Some(&(lb, ub)) => {
        self.rt.insert(k, (lb, v));
        self.ch.insert((k, ub), v);
        self.ch.insert((k, v), v);
      }
    }
  }

  pub fn remove(&mut self, k: CVar) {
    match self.rt.remove(&k) {
      None => {}
      Some((mut x, _)) => {
        //let mut iter_ct = 0;
        loop {
          /*iter_ct += 1;
          if iter_ct == 100 {
            println!("TRACE: CUnionIter::remove: loop 100x");
          }*/
          match self.ch.remove(&(k, x)) {
            None => unreachable!(),
            Some(nx) => if x == nx {
              return;
            } else {
              x = nx;
            }
          }
        }
      }
    }
  }
}

pub type TMemoryRef = Rc<TMemory>;

#[derive(Clone, Default)]
pub struct TMemory {
  swf:  WFrame,
}

impl TMemory {
  pub fn eval(&self, cap: &WCapture) -> u32 {
    // TODO
    self.swf._eval(cap)
  }

  pub fn backup(&mut self, cap: &WCapture) {
    // TODO
    self.swf._backup(cap);
  }
}

#[derive(Clone, Copy, Debug)]
pub enum RecKind {
  Nul,
  Def,
  //Ext,
}

#[derive(Clone, Copy, Debug)]
pub enum RelKind {
  Rel,
  Fun,
}

#[derive(Clone, Copy, Debug)]
pub enum RelKind2 {
  Exact,
  Symm,
  Cycl,
  //Revl,
  //Rcyc,
  LSymmF,
  LCyclF,
  //LRevlF,
  //LRcycF,
}

pub type TSubRef = Rc<TSub>;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct TSub {
  pub rec:  SNum,
  pub sub:  Vec<SNum>,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct TTup {
  pub rel:  SNum,
  pub tup:  Vec<SNum>,
}

impl TTup {
  pub fn from(rel: SNum, tup: &[SNum]) -> TTup {
    TTup{
      rel,
      tup:  tup.to_owned(),
    }
  }

  pub fn borrow(&self) -> TTupBorrowed {
    TTupBorrowed{
      rel:  self.rel,
      tup:  &self.tup,
    }
  }

  pub fn _arity(&self) -> usize {
    self.tup.len()
  }

  pub fn _swap_var(&self, ox: SNum, nx: SNum) -> TTup {
    let mut n_tup = Vec::with_capacity(self.tup.len());
    for &x in self.tup.iter() {
      n_tup.push(_swap_var(x, ox, nx));
    }
    TTup{rel: self.rel, tup: n_tup}
  }

  pub fn _lo_tup_mut(&mut self, larity: usize, kind2: RelKind2) {
    match kind2 {
      RelKind2::Exact => {}
      RelKind2::Symm => {
        self.tup.sort();
      }
      RelKind2::Cycl => {
        rotate_lo(&mut self.tup);
      }
      RelKind2::LSymmF => {
        self.tup[ .. larity].sort();
      }
      RelKind2::LCyclF => {
        rotate_lo(&mut self.tup[ .. larity]);
      }
    }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TTupBorrowed<'a> {
  pub rel:  SNum,
  pub tup:  &'a [SNum],
}

#[derive(Clone)]
pub struct TKey {
  tups: HTreapSet<TTup>,
}

pub type WPtr = SkaPtr;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct SkaPtr(u64);

#[derive(Clone)]
pub struct SkaKey {
  rec:  CVar,
  tups: HTreapSet<TTup>,
  mark: HTreapSet<TTup>,
}

#[derive(Clone, Copy)]
pub struct SkaRecInfo {
  //knd:  RecKind,
}

#[derive(Clone, Copy)]
pub struct SkaRecStat {
  n_ct: u32,
}

pub type WFrame = SkaFrame;

#[derive(Clone, Default)]
pub struct SkaFrame {
  recs: IHTreapMap<CVar, (SkaRecInfo, SkaRecStat)>,
  //defs: IHTreapSet<CVar>,
}

impl SkaFrame {
  pub fn _eval(&self, cap: &SkaCapture) -> u32 {
    let mut v = i32::max_value() as u32;
    for ptr in cap.mark.iter() {
      match cap.ptrs.get(ptr) {
        None => panic!("bug: WFrame::_eval"),
        Some(key) => match self.recs.get(&key.rec) {
          None => {
            v = 0;
          }
          Some(&(_, ref stat)) => {
            v = min(v, stat.n_ct);
          }
        }
      }
    }
    v
  }

  pub fn _backup(&mut self, cap: &SkaCapture) {
    for ptr in cap.mark.iter() {
      match cap.ptrs.get(ptr) {
        None => panic!("bug: WFrame::_backup"),
        Some(key) => match self.recs.get_mut(&key.rec) {
          None => {
            // FIXME
            self.recs.insert(key.rec, (SkaRecInfo{/*knd: RecKind::Nul*/}, SkaRecStat{n_ct: 1}));
          }
          Some(&mut (_, ref mut stat)) => {
            stat.n_ct += 1;
          }
        }
      }
    }
  }
}

pub type WChannel<A> = SkaChannel<A>;

//#[derive(Default)]
pub struct SkaChannel<A> {
  //data: IHTreapMap<u32, IHTreapSet<(CVar, TTup)>>,
  data: IHTreapMap<u32, IHTreapMap<TTup, A>>,
  heap: CategoricalHeap,
}

impl<A> Default for SkaChannel<A> {
  fn default() -> SkaChannel<A> {
    SkaChannel{
      data: IHTreapMap::default(),
      heap: CategoricalHeap::default(),
    }
  }
}

impl<A> SkaChannel<A> {
  pub fn is_empty(&self) -> bool {
    self.data.is_empty()
  }

  pub fn len(&self) -> usize {
    let mut n = 0;
    for (_, recs) in self.data.iter() {
      n += recs.len();
    }
    n
  }
}

impl<A: Clone> SkaChannel<A> {
  pub fn cache(&mut self, /*rec_var: CVar,*/ tu: TTup, key: A, val: u32) {
    // TODO
    match self.data.get_mut(&val) {
      None => {
        let mut recs = IHTreapMap::default();
        //recs.insert((rec_var, tu));
        recs.insert(tu, key);
        self.data.insert(val, recs);
      }
      Some(recs) => {
        //recs.insert((rec_var, tu));
        recs.insert(tu, key);
      }
    }
  }

  pub fn find(&self, rel: SNum, tup: &[SNum]) -> Option<(u32, TTup, A)> {
    //let tu = TTup{rel, tup: tup.to_owned()};
    for (&val, tups) in self.data.iter() {
      /*if tups.contains(&tu) {
        return Some(val);
      }*/
      for (tu, key) in tups.iter() {
        if tu.rel < rel {
          continue;
        } else if tu.rel > rel {
          break;
        }
        if &tu.tup[ .. tup.len()] == tup {
          return Some((val, tu.clone(), key.clone()));
        }
      }
    }
    None
  }

  pub fn retrieve<R: RngCore>(&mut self, rng: &mut R) -> (/*CVar,*/ TTup, A, u32, usize, usize) {
    // TODO
    if log_debug() {
      let mut vals = Vec::with_capacity(self.data.len());
      let mut lens = Vec::with_capacity(self.data.len());
      for (&val, recs) in self.data.iter() {
        vals.push(val);
        lens.push(recs.len());
      }
      println!("DEBUG: WChannel::retrieve: vals={:?}", vals);
      println!("DEBUG: WChannel::retrieve: lens={:?}", lens);
      match self.data.get(&(i32::max_value() as u32)) {
        None => {}
        Some(recs) => {
          for (tu, _) in recs.iter() {
            println!("DEBUG: WChannel::retrieve:   nil rel={} tup={:?}", tu.rel, tu.tup);
          }
        }
      }
      /*for (&val, recs) in self.data.rev_iter() {
        if val == i32::max_value() as u32 {
          continue;
        }
        for (tu, _) in recs.iter() {
          println!("DEBUG: WChannel::retrieve:   lub={} rel={} tup={:?}", val, tu.rel, tu.tup);
        }
        break;
      }*/
      /*let mut ct = 0;
      for (&val, recs) in self.data.rev_iter() {
        for (tu, _) in recs.iter() {
          if tu.rel.abs() == 50 {
            ct += 1;
          }
        }
      }
      println!("DEBUG: WChannel::retrieve:   ct={}", ct);*/
    }
    match URange::new(2).draw(rng) {
      0 => {
        for (&val, recs) in self.data.iter() {
          /*if val >= (i32::max_value() as u32) {
            break;
          }*/
          if recs.is_empty() {
            panic!("bug: WChannel::retrieve: empty val={}", val);
          }
          let mut recs_ = Vec::with_capacity(recs.len());
          //for &(rec, ref tu) in recs.iter() {
          for (tu, key) in recs.iter() {
            //recs_.push((rec, tu.clone()));
            recs_.push((tu.clone(), key.clone()));
          }
          let idx = choose_one_mut(&mut recs_, rng);
          //return (recs_[0].0, recs_[0].1.clone(), val);
          return (recs_[0].0.clone(), recs_[0].1.clone(), val, idx, recs_.len());
        }
      }
      1 => {
        //let mut data = Vec::with_capacity(self.data.len());
        let mut data = BTreeMap::new();
        for (&val, recs) in self.data.iter() {
          /*if val >= (i32::max_value() as u32) {
            break;
          }*/
          if recs.is_empty() {
            panic!("bug: WChannel::retrieve: empty val={}", val);
          }
          //data.push((recs.len(), val));
          let key = recs.len();
          match data.get_mut(&key) {
            None => {
              let mut vals = Vec::new();
              vals.push(val);
              data.insert(key, vals);
            }
            Some(vals) => {
              vals.push(val);
            }
          }
        }
        if data.is_empty() {
          panic!("bug: WChannel::retrieve: no data");
        }
        //data.sort();
        //let val = data[0].1;
        for (_, vals) in data.iter_mut() {
          let val_idx = choose_one_mut(vals, rng);
          let val = vals[val_idx];
          match self.data.get(&val) {
            None => panic!("bug: WChannel::retrieve: empty val={}", val),
            Some(recs) => {
              let mut recs_ = Vec::with_capacity(recs.len());
              for (tu, key) in recs.iter() {
                recs_.push((tu.clone(), key.clone()));
              }
              let idx = choose_one_mut(&mut recs_, rng);
              return (recs_[0].0.clone(), recs_[0].1.clone(), val, idx, recs_.len());
            }
          }
        }
      }
      _ => unreachable!()
    }
    panic!("bug: WChannel::retrieve: no data");
  }
}

pub trait ECapture {
  fn _ubptr(&mut self) -> SkaPtr;
  fn _fresh(&mut self, rec_var: CVar, rel: &[SNum], off: &[u32], ary: &[u32], tup: &[SNum]) -> SkaPtr;
  fn _alloc(&mut self, xlb: &WPtr, rel: SNum, tup: &[SNum]);
}

#[derive(Default)]
pub struct DummyCapture {
}

impl DummyCapture {
  pub fn reset(&mut self) {
  }
}

impl ECapture for DummyCapture {
  fn _ubptr(&mut self) -> SkaPtr {
    SkaPtr(0)
  }

  fn _fresh(&mut self, _rec_var: CVar, _rel: &[SNum], _off: &[u32], _ary: &[u32], _tup: &[SNum]) -> SkaPtr {
    SkaPtr(0)
  }

  fn _alloc(&mut self, _xlb: &SkaPtr, _rel: SNum, _tup: &[SNum]) {
  }
}

pub type WCapture = SkaCapture;

#[derive(Default)]
pub struct SkaCapture {
  fptr: u64,
  ptrs: HTreapMap<SkaPtr, SkaKey>,
  keys: HTreapMap<TTup, IHTreapSet<SkaPtr>>,
  //attr: HTreapMap<TTup, IHTreapSet<SkaPtr>>,
  allo: HTreapMap<TTup, SkaPtr>,
  mark: IHTreapSet<SkaPtr>,
}

impl SkaCapture {
  pub fn reset(&mut self) {
    self.fptr = 0;
    self.ptrs = HTreapMap::default();
    self.keys = HTreapMap::default();
    //self.attr = HTreapMap::default();
    self.allo = HTreapMap::default();
    self.mark = IHTreapSet::default();
  }
}

impl ECapture for SkaCapture {
  fn _ubptr(&mut self) -> SkaPtr {
    SkaPtr(self.fptr)
  }

  fn _fresh(&mut self, rec_var: CVar, rel: &[SNum], off: &[u32], ary: &[u32], tup: &[SNum]) -> SkaPtr {
    // TODO
    self.fptr += 1;
    assert!(self.fptr != 0);
    let new_ptr = SkaPtr(self.fptr);
    let mut tups = HTreapSet::default();
    for r in 0 .. rel.len() {
      let o = off[r] as usize;
      let a = ary[r] as usize;
      let rel = rel[r];
      if o > tup.len() || o + a > tup.len() {
        println!("TRACE: WCapture::_fresh: out of bounds: rec={} rel={:?} off={:?} ary={:?} tup={:?}",
            rec_var.0, rel, off, ary, tup);
        panic!("BUG");
      }
      let tup = tup[o .. o + a].to_owned();
      if log_trace_vvv() {
        println!("TRACE: WCapture::_fresh: new tup key: ptr={} rec={} rel={} tup={:?}",
            new_ptr.0, rec_var.0, rel, &tup);
      }
      let tu = TTup{rel, tup};
      tups.insert(tu);
    }
    let key = SkaKey{rec: rec_var, tups, mark: HTreapSet::default()};
    for tu in key.tups.iter() {
      match self.keys.get_mut(tu) {
        None => {
          let mut ptrs = IHTreapSet::default();
          ptrs.insert(new_ptr.clone());
          self.keys.insert(tu.clone(), ptrs);
        }
        Some(ptrs) => {
          ptrs.insert(new_ptr.clone());
        }
      }
    }
    self.ptrs.insert_drop(new_ptr.clone(), key);
    new_ptr
  }

  fn _alloc(&mut self, xlb: &SkaPtr, rel: SNum, tup: &[SNum]) {
    // TODO
    let tu = TTup{
      rel,
      tup:  tup.to_owned(),
    };
    match self.allo.get(&tu) {
      None => {}
      Some(_) => {
        return;
      }
    }
    //match self.attr.get(&tu) {
    match self.keys.get(&tu) {
      None => {
        panic!("bug: WCapture::_alloc: no record for tup key: rel={}, tup={:?}", rel, tup);
      }
      Some(ptrs) => {
        for ptr in ptrs.iter_from_excl(xlb) {
          match self.mark.contains(ptr) {
            true => {
              match self.ptrs.get_mut(ptr) {
                None => panic!("bug: WCapture::_alloc"),
                Some(key) => if key.tups.contains(&tu) {
                  if key.mark.contains(&tu) {
                    continue;
                  }
                  key.mark.insert(tu.clone());
                } else {
                  panic!("bug: WCapture::_alloc");
                }
              }
              self.allo.insert(tu, ptr.clone());
              self.mark.insert(ptr.clone());
              return;
            }
            _ => {}
          }
        }
        for ptr in ptrs.iter_from_excl(xlb) {
          match self.mark.contains(ptr) {
            false => {
              match self.ptrs.get_mut(ptr) {
                None => panic!("bug: WCapture::_alloc"),
                Some(key) => if key.tups.contains(&tu) {
                  if key.mark.contains(&tu) {
                    panic!("bug: WCapture::_alloc");
                  }
                  key.mark.insert(tu.clone());
                } else {
                  panic!("bug: WCapture::_alloc");
                }
              }
              self.allo.insert(tu, ptr.clone());
              self.mark.insert(ptr.clone());
              return;
            }
            _ => {}
          }
        }
        panic!("bug: WCapture::_alloc: unreachable tup key: xlb={} rel={} tup={:?}", xlb.0, rel, tup);
      }
    }
  }
}

pub enum SwapEvent<'a> {
  Nul,
  Rec(CVar),
  Eva(CVar, &'a [SNum], &'a [SNum], /*&'a [u32], &'a [u32], &'a [SNum], &'a [SNum]*/),
  Pat(CVar, SNum, &'a [SNum], &'a [SNum]),
}

#[derive(Clone)]
pub struct EvalEvent {
  pub rec:  CVar,
  pub sub:  Vec<SNum>,
  pub off:  Vec<u32>,
  pub ary:  Vec<u32>,
  pub rel:  Vec<SNum>,
  pub tup:  Vec<SNum>,
}

pub trait ESwap: Any {
  fn reset_swapbuf(&mut self);
  fn fix_swapbuf(&self) -> bool;
  fn any_ref(&self) -> &dyn Any { unimplemented!(); }
  fn any_mut(&mut self) -> &mut dyn Any { unimplemented!(); }
  fn stage_fresh(&mut self, tlb: TNum, ub: SNum);
  fn stage_tup(&mut self, tlb: TNum, event: SwapEvent, rel: SNum, tup: &[SNum]);
  //fn unify_tup(&mut self, tlb: TNum, lx: SNum, rx: SNum);
  fn patch_tup(&mut self, _tlb: TNum, _rel: SNum, _oltup: &[SNum], _ortup: &[SNum], _ltup: &[SNum], _rtup: &[SNum]) { unimplemented!() }
  //fn _etups(&self) -> BTreeSet<TTup> { unimplemented!(); }
  fn _etups(&self, env: &TFrame) -> BTreeSet<TTup> { unimplemented!(); }
  fn _etups_(&self, env: &TFrame) -> BTreeMap<TTup, EvalEvent> { unimplemented!(); }
  fn swap_nocap(&mut self, _tlb: TNum, /*_swap_tlb: TNum,*/ _env: &mut TFrame, _newswap: &mut dyn ESwap, _defer: bool) { unimplemented!(); }
  fn swap(&mut self, _tlb: TNum, /*_swap_tlb: TNum,*/ _env: &mut TFrame, _newswap: &mut dyn ESwap, _xlb: &WPtr, _cap: &mut dyn ECapture, _defer: bool) { unimplemented!(); }
  fn _copy_from(&mut self, _other: &dyn ESwap) { unimplemented!(); }
}

impl ESwap for Vec<SNum> {
  fn reset_swapbuf(&mut self) {
    self.clear();
  }

  fn fix_swapbuf(&self) -> bool {
    self.is_empty()
  }

  fn stage_fresh(&mut self, _tlb: TNum, _ub: SNum) {
    unimplemented!();
  }

  fn stage_tup(&mut self, _tlb: TNum, event: SwapEvent, rel: SNum, tup: &[SNum]) {
    let rec_var = match event {
      SwapEvent::Nul => CVar(0),
      SwapEvent::Rec(rec_var) => rec_var,
      SwapEvent::Eva(rec_var, ..) => rec_var,
      SwapEvent::Pat(rec_var, ..) => rec_var,
    };
    self.push(rec_var.0);
    self.push(rel);
    self.extend_from_slice(tup);
  }
}

#[derive(Default)]
pub struct SwapBuf {
  pub fbuf: Vec<SNum>,
  pub buf:  Vec<SNum>,
}

impl SwapBuf {
  /*pub fn reset(&mut self) {
    self.buf.clear();
  }*/
}

impl ESwap for SwapBuf {
  fn reset_swapbuf(&mut self) {
    self.fbuf.clear();
    self.buf.clear();
  }

  fn any_ref(&self) -> &dyn Any {
    self
  }

  fn any_mut(&mut self) -> &mut dyn Any {
    self
  }

  fn fix_swapbuf(&self) -> bool {
    self.fbuf.is_empty() &&
    self.buf.is_empty()
  }

  fn stage_fresh(&mut self, _tlb: TNum, ub: SNum) {
    // TODO
    self.fbuf.push(ub);
  }

  fn stage_tup(&mut self, _tlb: TNum, event: SwapEvent, rel: SNum, tup: &[SNum]) {
    let rec_var = match event {
      SwapEvent::Nul => CVar(0),
      SwapEvent::Rec(rec_var) => rec_var,
      SwapEvent::Eva(rec_var, ..) => rec_var,
      SwapEvent::Pat(rec_var, ..) => rec_var,
    };
    self.buf.push(rec_var.0);
    self.buf.push(rel);
    self.buf.extend_from_slice(tup);
  }

  //fn patch_tup(&mut self, _tlb: TNum, _rel: SNum, _oltup: &[SNum], _ltup: &[SNum]) {
  fn patch_tup(&mut self, _tlb: TNum, _rel: SNum, _oltup: &[SNum], _ortup: &[SNum], _ltup: &[SNum], _rtup: &[SNum]) {
  }

  fn _etups(&self, env: &TFrame) -> BTreeSet<TTup> {
    let mut tups = BTreeSet::new();
    let mut o = 0;
    while o < self.buf.len() {
      let rel = self.buf[o + 1];
      let rel_var = CVar(rel.abs());
      let a = env.rel_arity(rel_var);
      o += 2;
      let tu = TTup{rel, tup: self.buf[o .. o + a].to_owned()};
      tups.insert(tu);
      o += a;
    }
    tups
  }

  fn swap_nocap(&mut self, tlb: TNum, /*_swap_tlb: TNum,*/ new_env: &mut TFrame, newswap: &mut dyn ESwap, defer: bool) {
    if log_trace() {
      println!("TRACE: SwapBuf::swap_nocap: flen={} len={} defer?{:?}", self.fbuf.len(), self.buf.len(), defer);
    }
    for &ub in self.fbuf.iter() {
      while new_env.shm._atlas().lub() < ub {
        new_env.shm._fresh_var(TAttr::Gen);
      }
    }
    if self.buf.is_empty() {
      if log_trace() {
        println!("TRACE: SwapBuf::swap_nocap:   done early");
      }
      return;
    }
    let mut swaptup = Vec::new();
    let mut swapoff = 0;
    while swapoff < self.buf.len() {
      let rec_var = CVar(self.buf[swapoff]);
      let raw_rel = self.buf[swapoff + 1];
      let (neg, rel_var) = if raw_rel < 0 {
        (true, CVar(-raw_rel))
      } else if raw_rel > 0 {
        (false, CVar(raw_rel))
      } else {
        unreachable!();
      };
      let arity = new_env.rel_arity(rel_var);
      if defer && rel_var == new_env.shm.evar && !neg {
        if log_trace_vvv() {
          println!("TRACE: SwapBuf::swap_nocap: rec={} rel={} arity={} neg={:?} defer",
              rec_var.0, rel_var.0, arity, neg);
        }
        swapoff += 2;
        newswap.stage_tup(tlb, SwapEvent::Rec(rec_var), raw_rel, &self.buf[swapoff .. swapoff + arity]);
        swapoff += arity;
        continue;
      }
      swapoff += 2;
      if log_trace_vvv() {
        let tup: &[SNum] = &self.buf[swapoff .. swapoff + arity];
        println!("TRACE: SwapBuf::swap_nocap: rec={} rel={} arity={} neg={:?} tup={:?}",
            rec_var.0, rel_var.0, arity, neg, tup);
      }
      let rel_mut = match new_env.rels.get_mut(&rel_var) {
        None => unreachable!(),
        Some(r) => match Rc::get_mut(r) {
          None => {
            *r = r.clone_ref();
            match Rc::get_mut(r) {
              None => unreachable!(),
              Some(rr) => rr
            }
          }
          Some(rr) => rr
        }
      };
      swaptup.clear();
      if neg {
        rel_mut.swap_neg_tup_(tlb, rec_var, rel_var, &self.buf[swapoff .. swapoff + arity], &mut swaptup, newswap, &mut new_env.shm);
      } else {
        rel_mut.swap_pos_tup_(tlb, rec_var, rel_var, &self.buf[swapoff .. swapoff + arity], &mut swaptup, newswap, &mut new_env.shm);
      }
      swapoff += arity;
    }
    assert_eq!(swapoff, self.buf.len());
    if log_trace() {
      //println!("TRACE: SwapBuf::swap_nocap:   done newlen={}", newswap.len());
      println!("TRACE: SwapBuf::swap_nocap:   done");
    }
  }

  fn swap(&mut self, tlb: TNum, /*_swap_tlb: TNum,*/ new_env: &mut TFrame, newswap: &mut dyn ESwap, xlb: &WPtr, cap: &mut dyn ECapture, defer: bool) {
    if log_trace() {
      println!("TRACE: SwapBuf::swap: flen={} len={} defer?{:?}", self.fbuf.len(), self.buf.len(), defer);
    }
    for &ub in self.fbuf.iter() {
      while new_env.shm._atlas().lub() < ub {
        new_env.shm._fresh_var(TAttr::Gen);
      }
    }
    if self.buf.is_empty() {
      if log_trace() {
        println!("TRACE: SwapBuf::swap:   done early");
      }
      return;
    }
    let mut swaptup = Vec::new();
    let mut swapoff = 0;
    while swapoff < self.buf.len() {
      let rec_var = CVar(self.buf[swapoff]);
      let raw_rel = self.buf[swapoff + 1];
      let (neg, rel_var) = if raw_rel < 0 {
        (true, CVar(-raw_rel))
      } else if raw_rel > 0 {
        (false, CVar(raw_rel))
      } else {
        unreachable!();
      };
      let arity = new_env.rel_arity(rel_var);
      if defer && rel_var == new_env.shm.evar && !neg {
        if log_trace_vvv() {
          println!("TRACE: SwapBuf::swap: rec={} rel={} arity={} neg={:?} defer",
              rec_var.0, rel_var.0, arity, neg);
        }
        assert_eq!(arity, 2);
        swapoff += 2;
        if self.buf[swapoff] != self.buf[swapoff + 1] {
          cap._alloc(xlb, raw_rel, &self.buf[swapoff .. swapoff + 2]);
        }
        newswap.stage_tup(tlb, SwapEvent::Rec(rec_var), raw_rel, &self.buf[swapoff .. swapoff + arity]);
        swapoff += arity;
        continue;
      }
      swapoff += 2;
      if log_trace_vvv() {
        let tup: &[SNum] = &self.buf[swapoff .. swapoff + arity];
        println!("TRACE: SwapBuf::swap: rec={} rel={} arity={} neg={:?} tup={:?}",
            rec_var.0, rel_var.0, arity, neg, tup);
      }
      let rel_mut = match new_env.rels.get_mut(&rel_var) {
        None => unreachable!(),
        Some(r) => match Rc::get_mut(r) {
          None => {
            *r = r.clone_ref();
            match Rc::get_mut(r) {
              None => unreachable!(),
              Some(rr) => rr
            }
          }
          Some(rr) => rr
        }
      };
      swaptup.clear();
      match if neg {
        rel_mut.swap_neg_tup_(tlb, rec_var, rel_var, &self.buf[swapoff .. swapoff + arity], &mut swaptup, newswap, &mut new_env.shm)
      } else {
        rel_mut.swap_pos_tup_(tlb, rec_var, rel_var, &self.buf[swapoff .. swapoff + arity], &mut swaptup, newswap, &mut new_env.shm)
      } {
        //Noswap | Stale(_) => {}
        (Noswap, _) |
        (Stale, _) => {}
        //Fresh(_) => {
        (Fresh, _) |
        (Merge, _) => {
          if !(rel_var == new_env.shm.evar && !neg) {
            cap._alloc(xlb, raw_rel, &self.buf[swapoff .. swapoff + arity]);
          } /*else {
            newswap.unify_tup(...);
          }*/
        }
      }
      swapoff += arity;
    }
    assert_eq!(swapoff, self.buf.len());
    if log_trace() {
      //println!("TRACE: SwapBuf::swap:   done newlen={}", newswap.len());
      println!("TRACE: SwapBuf::swap:   done");
    }
  }

  fn _copy_from(&mut self, _other: &dyn ESwap) {
  }
}

#[derive(Default)]
pub struct SwapBuf_ {
  fbuf: Vec<SNum>,
  ebuf: BTreeMap<TSubRef, TraceEEvent>,
}

impl ESwap for SwapBuf_ {
  fn reset_swapbuf(&mut self) {
    // TODO
    self.fbuf.clear();
    self.ebuf.clear();
  }

  fn fix_swapbuf(&self) -> bool {
    // TODO
    self.fbuf.is_empty() &&
    self.ebuf.is_empty()
  }

  fn any_ref(&self) -> &dyn Any {
    self
  }

  fn any_mut(&mut self) -> &mut dyn Any {
    self
  }

  fn stage_fresh(&mut self, _tlb: TNum, ub: SNum) {
    // TODO
    self.fbuf.push(ub);
  }

  fn stage_tup(&mut self, tlb: TNum, event: SwapEvent, qrel: SNum, qtup: &[SNum]) {
    match event {
      SwapEvent::Nul => {
        println!("bug: SwapBuf_::stage_tup: unsupported event: Nul");
      }
      SwapEvent::Rec(rec_var) => {
        println!("bug: SwapBuf_::stage_tup: unsupported event: Rec rec={}", rec_var.0);
      }
      SwapEvent::Eva(rec_var, sub, srnk, /*off, ary, rel, tup*/) => {
        let qtu = TTup{rel: qrel, tup: qtup.to_owned()};
        let mut nsub = Vec::with_capacity(sub.len());
        nsub.resize(sub.len(), 0);
        _perm_tup(srnk, sub, &mut nsub);
        let su: TSubRef = TSub{rec: rec_var.0, sub: nsub}.into();
        match self.ebuf.get_mut(&su) {
          None => {
            let mut cons = IHTreapSet::default();
            cons.insert(qtu);
            self.ebuf.insert(su.clone(), TraceEEvent{sub: su, cons});
          }
          Some(event) => {
            event.cons.insert(qtu);
          }
        }
      }
      SwapEvent::Pat(rec_var, rel, lsub, rsub) => {
        // FIXME
        let mut sub = Vec::with_capacity(lsub.len() + rsub.len());
        sub.extend_from_slice(lsub);
        sub.extend_from_slice(rsub);
        let su: TSubRef = TSub{rec: rec_var.0, sub: sub.to_owned()}.into();
        let rmid = rsub.len() / 2;
        match self.ebuf.get_mut(&su) {
          None => {
            let mut cons = IHTreapSet::default();
            for t in 0 .. rmid {
              let qtu = TTup{rel: 1, tup: [rsub[t], rsub[t + rmid]].to_vec()};
              cons.insert(qtu);
            }
            self.ebuf.insert(su.clone(), TraceEEvent{sub: su, cons});
          }
          Some(event) => {
            for t in 0 .. rmid {
              let qtu = TTup{rel: 1, tup: [rsub[t], rsub[t + rmid]].to_vec()};
              event.cons.insert(qtu);
            }
          }
        }
      }
    }
  }

  fn patch_tup(&mut self, _tlb: TNum, _rel: SNum, _oltup: &[SNum], _ortup: &[SNum], _ltup: &[SNum], _rtup: &[SNum]) {
    //unimplemented!();
  }

  fn _etups(&self, env: &TFrame) -> BTreeSet<TTup> {
    let mut tups = BTreeSet::new();
    for (_, event) in self.ebuf.iter() {
      for tu in event.cons.iter() {
        tups.insert(tu.clone());
      }
    }
    tups
  }

  fn _etups_(&self, env: &TFrame) -> BTreeMap<TTup, EvalEvent> {
    let mut tups = BTreeMap::new();
    for (_, event) in self.ebuf.iter() {
      let mut ev = EvalEvent{
        rec:  CVar(event.sub.rec),
        sub:  event.sub.sub.clone(),
        off:  Vec::new(),
        ary:  Vec::new(),
        rel:  Vec::new(),
        tup:  Vec::new(),
      };
      env.fill_bufs(ev.rec, &ev.sub, &mut ev.off, &mut ev.ary, &mut ev.rel, &mut ev.tup);
      for tu in event.cons.iter() {
        tups.insert(tu.clone(), ev.clone());
      }
    }
    tups
  }

  fn swap_nocap(&mut self, tlb: TNum, new_env: &mut TFrame, newswap: &mut dyn ESwap, defer: bool) {
    // TODO
    let mut swaptup = Vec::new();
    let mut swap_tlb = new_env.shm._snapshot().next_glb();
    for &ub in self.fbuf.iter() {
      while new_env.shm._atlas().lub() < ub {
        new_env.shm._fresh_var(TAttr::Gen);
      }
    }
    for (_, event) in self.ebuf.iter() {
      // TODO
      let rec_var = CVar(event.sub.rec);
      for tu in event.cons.iter() {
        if tu.rel == new_env.shm.evar.0 {
          if defer {
            if let Some(newswap) = newswap.any_mut().downcast_mut::<SwapBuf_>() {
              // TODO
              match newswap.ebuf.get_mut(&event.sub) {
                None => {
                  let mut cons = IHTreapSet::default();
                  cons.insert(tu.clone());
                  newswap.ebuf.insert(event.sub.clone(), TraceEEvent{sub: event.sub.clone(), cons});
                }
                Some(event) => {
                  event.cons.insert(tu.clone());
                }
              }
            } else {
              panic!("bug: SwapBuf_::swap_nocap: type mismatch");
            }
            continue;
          }
          swap_tlb = new_env.shm._snapshot().next_glb();
        }
        let (neg, rel_var) = if tu.rel < 0 {
          (true, CVar(-tu.rel))
        } else if tu.rel > 0 {
          (false, CVar(tu.rel))
        } else {
          panic!("bug: SwapBuf_::swap_nocap: sign");
        };
        let rel_mut = match new_env.rels.get_mut(&rel_var) {
          None => unreachable!(),
          Some(r) => match Rc::get_mut(r) {
            None => {
              *r = r.clone_ref();
              match Rc::get_mut(r) {
                None => unreachable!(),
                Some(rr) => rr
              }
            }
            Some(rr) => rr
          }
        };
        swaptup.clear();
        if neg {
          rel_mut.swap_neg_tup_(swap_tlb, rec_var, rel_var, &tu.tup, &mut swaptup, newswap, &mut new_env.shm);
        } else {
          rel_mut.swap_pos_tup_(swap_tlb, rec_var, rel_var, &tu.tup, &mut swaptup, newswap, &mut new_env.shm);
        }
      }
    }
  }

  fn swap(&mut self, tlb: TNum, new_env: &mut TFrame, newswap: &mut dyn ESwap, xlb: &WPtr, cap: &mut dyn ECapture, defer: bool) {
    // TODO
    let mut swaptup = Vec::new();
    let mut swap_tlb = new_env.snapshot().next_glb();
    for &ub in self.fbuf.iter() {
      while new_env.shm._atlas().lub() < ub {
        new_env.shm._fresh_var(TAttr::Gen);
      }
    }
    for (_, event) in self.ebuf.iter() {
      // TODO
      let rec_var = CVar(event.sub.rec);
      for tu in event.cons.iter() {
        if tu.rel == new_env.shm.evar.0 {
          if defer {
            //newswap.stage_tup(tlb, SwapEvent::Rec(rec_var), raw_rel, &self.buf[swapoff .. swapoff + arity]);
            if let Some(newswap) = newswap.any_mut().downcast_mut::<SwapBuf_>() {
              // TODO
              match newswap.ebuf.get_mut(&event.sub) {
                None => {
                  let mut cons = IHTreapSet::default();
                  cons.insert(tu.clone());
                  newswap.ebuf.insert(event.sub.clone(), TraceEEvent{sub: event.sub.clone(), cons});
                }
                Some(event) => {
                  event.cons.insert(tu.clone());
                }
              }
            } else {
              panic!("bug: SwapBuf_::swap: type mismatch");
            }
            continue;
          }
          swap_tlb = new_env.shm._snapshot().next_glb();
        }
        let (neg, rel_var) = if tu.rel < 0 {
          (true, CVar(-tu.rel))
        } else if tu.rel > 0 {
          (false, CVar(tu.rel))
        } else {
          panic!("bug: SwapBuf_::swap: sign");
        };
        let rel_mut = match new_env.rels.get_mut(&rel_var) {
          None => unreachable!(),
          Some(r) => match Rc::get_mut(r) {
            None => {
              *r = r.clone_ref();
              match Rc::get_mut(r) {
                None => unreachable!(),
                Some(rr) => rr
              }
            }
            Some(rr) => rr
          }
        };
        swaptup.clear();
        match if neg {
          rel_mut.swap_neg_tup_(swap_tlb, rec_var, rel_var, &tu.tup, &mut swaptup, newswap, &mut new_env.shm)
        } else {
          rel_mut.swap_pos_tup_(swap_tlb, rec_var, rel_var, &tu.tup, &mut swaptup, newswap, &mut new_env.shm)
        } {
          //Noswap => {}
          (Noswap, _) => {}
          //Stale(t) => {
          (Stale, t) => {
            assert!(t >= swap_tlb);
          }
          //Fresh(t) => {
          //(Fresh, t) => {
          (Fresh, _) |
          (Merge, _) => {
            //if !(rel_var == new_env.shm.evar && !neg) {
            if tu.rel != new_env.shm.evar.0 {
              cap._alloc(xlb, tu.rel, &tu.tup);
            }
          }
        }
      }
    }
  }

  fn _copy_from(&mut self, _other: &dyn ESwap) {
  }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
enum QueueNextKey {
  Vs(Vec<(TNum, TTup)>),
  E(TNum, TSubRef),
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
enum QueueKey {
  F(TNum, SNum),
  V(TNum, TTup),
  E(TNum, TSubRef),
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
enum HeapKey {
  F(TNum, SNum),
  //U(TNum, TTup),
  V(TNum, TTup),
  E(TNum, TSubRef),
}

#[derive(Clone, Copy)]
pub struct HeapCell {
  push: u32,
  pop:  u32,
}

impl HeapCell {
  pub fn _new() -> HeapCell {
    HeapCell{push: 1, pop: 0}
  }

  pub fn _push(&mut self) -> bool {
    let (p, q) = (self.push, self.pop);
    if q != 0 {
      panic!("bug: HeapCell::_push: pushv={} popv={}", p, q);
    }
    self.push = p + 1;
    //self.pop = q;
    p == 0
  }

  pub fn _pop(&mut self) -> bool {
    let (p, q) = (self.push, self.pop);
    if p <= q {
      panic!("bug: HeapCell::_pop: pushv={} popv={}", p, q);
    } else if p == q + 1 {
      self.push = 0;
      self.pop = 0;
      return true;
    }
    //self.push = p;
    self.pop = q + 1;
    false
  }
}

#[derive(Clone, Debug)]
pub enum TraceEvent {
  F(TNum, SNum),
  U(TNum, TTup, Vec<TTup>),
  //U(TNum, TTup, Vec<(TNum, TTup)>),
  V(TNum, TTup, TNum, SNum, Vec<TTup>),
  E(TNum, SNum, Vec<TTup>),
}

/*pub enum TraceEvent {
  E(IHTreapSet<TSubRef>),
  U(IHTreapSet<TTup>),
}*/

pub type TraceTNode = (TraceNode, TNum);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TraceNode {
  E(TSubRef),
  U(TTup),
  V(TTup),
}

pub type TraceUVNodeT = (TraceUVNode, TNum);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TraceUVNode {
  U(TTup),
  V(TTup),
}

pub type TraceENodeT = (TSubRef, TNum);

/*pub type TraceEventT = (TraceEvent, TNum);

#[derive(Clone)]
pub enum TraceEvent {
  E(TSubRef, IHTreapSet<TTup>),
  U(IHTreapSet<TTup>, TTup),
}*/

#[derive(Clone)]
pub struct TraceEEvent {
  sub:  TSubRef,
  cons: IHTreapSet<TTup>,
}

#[derive(Clone)]
pub struct TraceUEvent {
  //pre:  IHTreapSet<TTup>,
  //post: TTup,
  pre:  IHTreapSet<(TTup, TTup)>,
  post: (SNum, SNum),
}

#[derive(Clone, Default)]
pub struct TraceWork {
  //rank: IHTreapMap<TraceTNode, u32>,
  //dist: IHTreapMap<TraceTNode, u32>,
  //rank: IHTreapMap<TraceTNode, Vec<u32>>,
  //dist: IHTreapMap<TraceTNode, Vec<u32>>,
  ernk: IHTreapMap<TraceENodeT, IHTreapMap<TTup, u32>>,
  xrnk: IHTreapMap<TraceUVNodeT, u32>,
  edst: IHTreapMap<TraceENodeT, IHTreapMap<TTup, u32>>,
  xdst: IHTreapMap<TraceUVNodeT, u32>,
  //dst:  IHTreapMap<TraceTNode, Vec<u32>>,
  last: IHTreapMap<TTup, TraceTNode>,
  //last: IHTreapMap<TTup, IHTreapSet<TraceTNode>>,
}

impl TraceWork {
  pub fn _reset(&mut self) {
    // TODO
  }
}

#[derive(Default)]
struct EventBufs {
  ante: usize,
  cons: usize,
  off:  Vec<u32>,
  ary:  Vec<u32>,
  rel:  Vec<SNum>,
  tup:  Vec<SNum>,
}

#[derive(Clone, Default)]
pub struct SwapTrace {
  //sub:  IHTreapSet<TSubRef>,
  src:  IHTreapSet<TSubRef>,
  //bwd:  HTreapMap<TTup, (TNum, HTreapMap<TSub, u32>, Option<TNum>)>,
  //fwd:  HTreapMap<TTup, (TNum, HTreapSet<TTup>)>,
  //bwd:  IHTreapMap<TTup, (TNum, IHTreapSet<TSubRef>, TNum)>,
  //idx:  IHTreapMap<TTup, IHTreapSet<TSubRef>>,
  //fwd:  IHTreapMap<TSubRef, (TNum, IHTreapMap<TTup, TNum>)>,
  //fwd:  IHTreapMap<TTup, (TNum, IHTreapMap<TSubRef, TNum>)>,
  ffwd: IHTreapMap<SNum, TNum>,
  fwd:  IHTreapMap<TTup, IHTreapMap<TNum, IHTreapSet<TSubRef>>>,
  bwd:  IHTreapMap<TSubRef, IHTreapMap<TNum, IHTreapSet<TTup>>>,
  //bwd:  IHTreapMap<TSubRef, (TNum, IHTreapSet<TTup>)>,
  efwd: IHTreapMap<TSubRef, IHTreapMap<TNum, IHTreapSet<TTup>>>,
  ebwd: IHTreapMap<TTup, IHTreapMap<TNum, IHTreapSet<TSubRef>>>,
  ufwd: IHTreapMap<TTup, IHTreapMap<TNum, IHTreapSet<TTup>>>,
  ubwd: IHTreapMap<TTup, IHTreapMap<TNum, TTup>>,
  //lpat: IHTreapMap<TTup, (TNum, IHTreapMap<TTup, TNum>)>,
  //cfwd: IHTreapMap<SNum, (TNum, IHTreapSet<SNum>)>,
  //idx:  IHTreapMap<SNum, IHTreapMap<TTup, IHTreapSet<TNum>>>,
  idx:  IHTreapMap<SNum, IHTreapMap<TTup, TNum>>,
  //idx:  IHTreapMap<SNum, IHTreapMap<TNum, IHTreapSet<TTup>>>,
  uidx: IHTreapMap<SNum, (TNum, SNum)>,
  //stak: IHTreapMap<StackKey, StackCell>,
  fbuf: Vec<SNum>,
  ebuf: IHTreapMap<TSubRef, TraceEEvent>,
  //ubuf: IHTreapMap<(SNum, SNum), TraceUEvent>,
  //work: TraceWork,
}

// TODO

impl SwapTrace {
  pub fn _gen_trace(&self, tg: &[(TNum, TTup)], buffer: &mut Vec<TraceEvent>) {
    if log_debug() {
      println!("DEBUG: SwapTrace::_gen_trace: ffwd len={}", self.ffwd.len());
      println!("DEBUG: SwapTrace::_gen_trace: fwd  len={}", self.fwd.len());
      println!("DEBUG: SwapTrace::_gen_trace: ufwd len={}", self.ufwd.len());
      println!("DEBUG: SwapTrace::_gen_trace: efwd len={}", self.efwd.len());
    }
    buffer.clear();
    let mut heap: BTreeMap<HeapKey, HeapCell> = BTreeMap::new();
    let mut queue: Vec<QueueKey> = Vec::new();
    let mut nextqueue: Vec<QueueKey> = Vec::new();
    for &(tg_t, ref tgtu) in tg.iter() {
      queue.push(QueueKey::V(tg_t, tgtu.clone()));
    }
    loop {
      loop {
        let key = match queue.pop() {
          None => break,
          Some(k) => k
        };
        if log_trace_vvv() {
          println!("DEBUG: SwapTrace::_gen_trace: key={:?}", key);
        }
        match key {
          QueueKey::F(kt, x) => {
            match self.ffwd.get(&x) {
              None => {}
              Some(&t) => {
                if t > kt {
                  panic!("bug: SwapTrace::_gen_trace");
                } else if t < kt {
                  continue;
                }
                if log_trace_vvv() {
                  println!("DEBUG: SwapTrace::_gen_trace:   fresh");
                }
                let this_key = HeapKey::F(t, x);
                match heap.get_mut(&this_key) {
                  None => {
                    let cel = HeapCell::_new();
                    heap.insert(this_key.clone(), cel);
                  }
                  Some(cel) => {
                    cel._push();
                  }
                }
              }
            }
          }
          QueueKey::V(kt, tu) => {
            let mut this_t = 0;
            let mut this_key = None;
            let mut next_key = None;
            match self.ufwd.get(&tu) {
              None => {
                if log_trace_vvv() {
                  println!("DEBUG: SwapTrace::_gen_trace:   no ufwd");
                }
              }
              Some(e) => {
                if log_trace_vvv() {
                  println!("DEBUG: SwapTrace::_gen_trace:   ufwd: e={:?}", e);
                }
                for (&t, tups) in e.rev_iter_from(&kt) {
                  if log_trace_vvv() {
                    println!("DEBUG: SwapTrace::_gen_trace:   next ufwd? t={} tups={:?}", t, tups);
                  }
                  if this_t < t {
                    // TODO
                    let mut tups_ = Vec::new();
                    for tu in tups.iter() {
                      tups_.push((t, tu.clone()));
                    }
                    this_t = t;
                    //this_key = Some(HeapKey::U(t, tu.clone()));
                    this_key = Some(HeapKey::V(t, tu.clone()));
                    next_key = Some(QueueNextKey::Vs(tups_));
                    break;
                  }
                }
              }
            }
            match self.fwd.get(&tu) {
              None => {
                if log_trace_vvv() {
                  println!("DEBUG: SwapTrace::_gen_trace:   no fwd");
                }
              }
              Some(e) => {
                if log_trace_vvv() {
                  println!("DEBUG: SwapTrace::_gen_trace:   fwd: e={:?}", e);
                }
                for (&t, subs) in e.rev_iter_from(&kt) {
                  if log_trace_vvv() {
                    println!("DEBUG: SwapTrace::_gen_trace:   next fwd? t={} subs={:?}", t, subs);
                  }
                  if this_t < t {
                    // TODO
                    for su in subs.iter() {
                      this_t = t;
                      this_key = Some(HeapKey::V(t, tu.clone()));
                      next_key = Some(QueueNextKey::E(t, su.clone()));
                      break;
                    }
                    break;
                  }
                }
              }
            }
            let push = match this_key.as_ref() {
              None => {
                // TODO
                if log_trace_vvv() {
                  println!("DEBUG: SwapTrace::_gen_trace:   no next");
                }
                continue;
              }
              Some(this_key) => {
                match heap.get_mut(this_key) {
                  None => {
                    let cel = HeapCell::_new();
                    heap.insert(this_key.clone(), cel);
                    true
                  }
                  Some(cel) => {
                    cel._push()
                    //cel._push(this_t)
                  }
                }
              }
            };
            for &x in tu.tup.iter() {
              nextqueue.push(QueueKey::F(this_t, x));
            }
            match next_key {
              None => {
                // TODO
                panic!("bug: SwapTrace::_gen_trace");
              }
              Some(QueueNextKey::Vs(tups)) => {
                for (t, tu) in tups.into_iter() {
                  let next_key = QueueKey::V(t - 1, tu);
                  nextqueue.push(next_key.clone());
                }
              }
              Some(QueueNextKey::E(t, su)) => {
                let next_key = QueueKey::E(t, su);
                nextqueue.push(next_key.clone());
              }
            }
          }
          QueueKey::E(kt, su) => {
            // TODO
            match self.efwd.get(&su) {
              None => {
                match self.src.get(&su) {
                  None => {
                    unreachable!();
                  }
                  Some(_) => {
                    if log_trace_vvv() {
                      println!("DEBUG: SwapTrace::_gen_trace:   src");
                    }
                  }
                }
              }
              Some(e) => {
                // TODO
                if log_trace_vvv() {
                  println!("DEBUG: SwapTrace::_gen_trace:   efwd: e={:?}", e);
                }
                let mut this_t = 0;
                for (&t, tups) in e.rev_iter_from(&kt) {
                  if log_trace_vvv() {
                    println!("DEBUG: SwapTrace::_gen_trace:   t={} tups={:?}", t, tups);
                  }
                  this_t = t;
                  let this_key = HeapKey::E(t, su.clone());
                  let push = match heap.get_mut(&this_key) {
                    None => {
                      let cel = HeapCell::_new();
                      heap.insert(this_key.clone(), cel);
                      true
                    }
                    Some(cel) => {
                      cel._push()
                      //cel._push(this_t)
                    }
                  };
                  for tu in tups.iter() {
                    let next_key = QueueKey::V(t - 1, tu.clone());
                    nextqueue.push(next_key);
                  }
                  break;
                }
                assert!(this_t > 0);
              }
            }
          }
        }
      }
      if nextqueue.is_empty() {
        break;
      }
      swap(&mut queue, &mut nextqueue);
    }
    if log_debug() {
      println!("DEBUG: SwapTrace::_gen_trace: stack len={}", heap.len());
    }
    assert!(queue.is_empty());
    for &(tg_t, ref tgtu) in tg.iter() {
      queue.push(QueueKey::V(tg_t, tgtu.clone()));
    }
    loop {
      loop {
        if buffer.len() >= 100_000 {
          println!("TRACE: SwapTrace::_gen_trace: overflow");
          panic!("BUG");
        }
        let key = match queue.pop() {
          None => break,
          Some(k) => k
        };
        match key {
          QueueKey::F(kt, x) => {
            match self.ffwd.get(&x) {
              None => {}
              Some(&t) => {
                if t > kt {
                  panic!("bug: SwapTrace::_gen_trace");
                } else if t < kt {
                  continue;
                }
                let this_key = HeapKey::F(t, x);
                let pop = match heap.get_mut(&this_key) {
                  None => {
                    panic!("bug: SwapTrace::_gen_trace");
                  }
                  Some(cel) => {
                    cel._pop()
                  }
                };
                if pop {
                  buffer.push(TraceEvent::F(t, x));
                }
              }
            }
          }
          QueueKey::V(kt, tu) => {
            // FIXME
            let mut this_t = 0;
            let mut this_key = None;
            let mut next_key = None;
            match self.ufwd.get(&tu) {
              None => {}
              Some(e) => {
                for (&t, tups) in e.rev_iter_from(&kt) {
                  if this_t < t {
                    // TODO
                    let mut tups_ = Vec::new();
                    for tu in tups.iter() {
                      tups_.push((t, tu.clone()));
                    }
                    this_t = t;
                    //this_key = Some(HeapKey::U(t, tu.clone()));
                    this_key = Some(HeapKey::V(t, tu.clone()));
                    next_key = Some(QueueNextKey::Vs(tups_));
                    break;
                  }
                }
              }
            }
            match self.fwd.get(&tu) {
              None => {}
              Some(e) => {
                for (&t, subs) in e.rev_iter_from(&kt) {
                  if this_t < t {
                    // TODO
                    for su in subs.iter() {
                      this_t = t;
                      this_key = Some(HeapKey::V(t, tu.clone()));
                      next_key = Some(QueueNextKey::E(t, su.clone()));
                      break;
                    }
                    break;
                  }
                }
              }
            }
            let pop = match this_key.as_ref() {
              None => {
                // TODO
                continue;
              }
              Some(this_key) => {
                match heap.get_mut(this_key) {
                  None => {
                    panic!("bug: SwapTrace::_gen_trace");
                  }
                  Some(cel) => {
                    cel._pop()
                  }
                }
              }
            };
            for &x in tu.tup.iter() {
              nextqueue.push(QueueKey::F(this_t, x));
            }
            match next_key {
              None => {
                // TODO
                panic!("bug: SwapTrace::_gen_trace");
              }
              Some(QueueNextKey::Vs(tups)) => {
                if pop {
                  let mut tups_ = Vec::with_capacity(tups.len());
                  for &(_, ref tu) in tups.iter() {
                    tups_.push(tu.clone());
                  }
                  buffer.push(TraceEvent::U(this_t, tu, tups_));
                  //buffer.push(TraceEvent::U(this_t, tu, tups.clone()));
                }
                // FIXME
                for (t, tu) in tups.into_iter() {
                  let next_key = QueueKey::V(t - 1, tu);
                  nextqueue.push(next_key.clone());
                }
              }
              Some(QueueNextKey::E(t, su)) => {
                match self.efwd.get(&su) {
                  None => {
                    match self.src.get(&su) {
                      None => {
                        unreachable!();
                      }
                      Some(_) => {
                        if pop {
                          buffer.push(TraceEvent::V(this_t, tu, t, su.rec, Vec::new()));
                        }
                      }
                    }
                  }
                  Some(e) => {
                    match e.get(&t) {
                      None => {
                        unreachable!();
                      }
                      Some(tups) => {
                        if pop {
                          let mut tups_ = Vec::with_capacity(tups.len());
                          for tu in tups.iter() {
                            tups_.push(tu.clone());
                          }
                          buffer.push(TraceEvent::V(this_t, tu, t, su.rec, tups_));
                        }
                      }
                    }
                  }
                }
                let next_key = QueueKey::E(t, su);
                nextqueue.push(next_key.clone());
              }
            }
          }
          QueueKey::E(kt, su) => {
            // TODO
            match self.efwd.get(&su) {
              None => {
                match self.src.get(&su) {
                  None => {
                    unreachable!();
                  }
                  Some(_) => {}
                }
              }
              Some(e) => {
                // TODO
                let mut this_t = 0;
                for (&t, tups) in e.rev_iter_from(&kt) {
                  this_t = t;
                  let this_key = HeapKey::E(t, su.clone());
                  let pop = match heap.get_mut(&this_key) {
                    None => {
                      panic!("bug: SwapTrace::_gen_trace");
                    }
                    Some(cel) => {
                      cel._pop()
                    }
                  };
                  if pop {
                    let mut tups_ = Vec::with_capacity(tups.len());
                    for tu in tups.iter() {
                      tups_.push(tu.clone());
                    }
                    buffer.push(TraceEvent::E(this_t, su.rec, tups_));
                  }
                  for tu in tups.iter() {
                    let next_key = QueueKey::V(t - 1, tu.clone());
                    nextqueue.push(next_key);
                  }
                  break;
                }
                assert!(this_t > 0);
              }
            }
          }
        }
      }
      if nextqueue.is_empty() {
        break;
      }
      swap(&mut queue, &mut nextqueue);
    }
  }
}

impl ESwap for SwapTrace {
  /*fn reset(&mut self) {
    self.efwd.clear();
    //self.idx.clear();
    self.fwd.clear();
  }*/

  fn reset_swapbuf(&mut self) {
    // TODO
    self.fbuf.clear();
    self.ebuf.clear();
    //self.ubuf.clear();
  }

  fn fix_swapbuf(&self) -> bool {
    // TODO
    self.fbuf.is_empty() &&
    self.ebuf.is_empty() /*&& self.ubuf.is_empty()*/
  }

  fn any_ref(&self) -> &dyn Any {
    self
  }

  fn any_mut(&mut self) -> &mut dyn Any {
    self
  }

  fn stage_fresh(&mut self, _tlb: TNum, ub: SNum) {
    // TODO
    self.fbuf.push(ub);
  }

  fn stage_tup(&mut self, tlb: TNum, event: SwapEvent, qrel: SNum, qtup: &[SNum]) {
    match event {
      SwapEvent::Nul => {
        println!("bug: SwapTrace::stage_tup: unsupported event: Nul");
      }
      SwapEvent::Rec(rec_var) => {
        println!("bug: SwapTrace::stage_tup: unsupported event: Rec rec={}", rec_var.0);
      }
      SwapEvent::Eva(rec_var, sub, srnk, /*off, ary, rel, tup*/) => {
        let qtu = TTup{rel: qrel, tup: qtup.to_owned()};
        let mut nsub = Vec::with_capacity(sub.len());
        nsub.resize(sub.len(), 0);
        _perm_tup(srnk, sub, &mut nsub);
        /*if rec_var.0 == 174 || rec_var.0 == 175 {
          println!("TRACE: SwapTrace::stage_tup: eva: tlb={} rec={} qrel={} qtup={:?}",
              tlb, rec_var.0, qrel, qtup);
          println!("TRACE: SwapTrace::stage_tup: eva:   rec={} osub={:?} srnk={:?}",
              rec_var.0, sub, srnk);
          println!("TRACE: SwapTrace::stage_tup: eva:   rec={} nsub={:?}",
              rec_var.0, nsub);
        }*/
        let su: TSubRef = TSub{rec: rec_var.0, sub: nsub}.into();
        match self.ebuf.get_mut(&su) {
          None => {
            let mut cons = IHTreapSet::default();
            cons.insert(qtu);
            self.ebuf.insert(su.clone(), TraceEEvent{sub: su, cons});
          }
          Some(event) => {
            event.cons.insert(qtu);
          }
        }
      }
      SwapEvent::Pat(rec_var, rel, lsub, rsub) => {
        // FIXME
        let mut sub = Vec::with_capacity(lsub.len() + rsub.len());
        sub.extend_from_slice(lsub);
        sub.extend_from_slice(rsub);
        let su: TSubRef = TSub{rec: rec_var.0, sub: sub.to_owned()}.into();
        let rmid = rsub.len() / 2;
        match self.ebuf.get_mut(&su) {
          None => {
            let mut cons = IHTreapSet::default();
            for t in 0 .. rmid {
              let qtu = TTup{rel: 1, tup: [rsub[t], rsub[t + rmid]].to_vec()};
              cons.insert(qtu);
            }
            self.ebuf.insert(su.clone(), TraceEEvent{sub: su, cons});
          }
          Some(event) => {
            for t in 0 .. rmid {
              let qtu = TTup{rel: 1, tup: [rsub[t], rsub[t + rmid]].to_vec()};
              event.cons.insert(qtu);
            }
          }
        }
        /*let rmid = rsub.len() / 2;
        let mut pre_tup1 = Vec::with_capacity(lsub.len() + rmid);
        pre_tup1.extend_from_slice(lsub);
        pre_tup1.extend_from_slice(&rsub[ .. rmid]);
        let mut pre_tup2 = Vec::with_capacity(lsub.len() + rmid);
        pre_tup2.extend_from_slice(lsub);
        pre_tup2.extend_from_slice(&rsub[rmid .. ]);
        /*let mut post_tup = Vec::with_capacity(lsub.len() + rmid);
        post_tup.extend_from_slice(lsub);
        for t in 0 .. rmid {
          post_tup.push(min(rsub[t], rsub[t + rmid]));
        }
        let post_tu = TTup{rel, tup: post_tup};*/
        for t in 0 .. rmid {
          let post_key = if rsub[t] <= rsub[t + rmid] {
            (rsub[t], rsub[t + rmid])
          } else {
            (rsub[t + rmid], rsub[t])
          };
          match self.ubuf.get_mut(&post_key) {
            None => {
              let mut pre_set = IHTreapSet::default();
              if pre_tup1 <= pre_tup2 {
                pre_set.insert((TTup{rel, tup: pre_tup1.clone()}, TTup{rel, tup: pre_tup2.clone()}));
              } else {
                pre_set.insert((TTup{rel, tup: pre_tup2.clone()}, TTup{rel, tup: pre_tup1.clone()}));
              }
              self.ubuf.insert(post_key, TraceUEvent{pre: pre_set.clone(), post: post_key});
            }
            Some(event) => {
              if pre_tup1 <= pre_tup2 {
                event.pre.insert((TTup{rel, tup: pre_tup1.clone()}, TTup{rel, tup: pre_tup2.clone()}));
              } else {
                event.pre.insert((TTup{rel, tup: pre_tup2.clone()}, TTup{rel, tup: pre_tup1.clone()}));
              }
            }
          }
        }*/
      }
    }
  }

  //fn patch_tup(&mut self, _tlb: TNum, _rel: SNum, _oltup: &[SNum], _ltup: &[SNum]) {
  fn patch_tup(&mut self, _tlb: TNum, _rel: SNum, _oltup: &[SNum], _ortup: &[SNum], _ltup: &[SNum], _rtup: &[SNum]) {
    //unimplemented!();
  }

  fn _etups(&self, env: &TFrame) -> BTreeSet<TTup> {
    let mut tups = BTreeSet::new();
    for (_, event) in self.ebuf.iter() {
      for tu in event.cons.iter() {
        tups.insert(tu.clone());
      }
    }
    tups
  }

  fn _etups_(&self, env: &TFrame) -> BTreeMap<TTup, EvalEvent> {
    let mut tups = BTreeMap::new();
    for (_, event) in self.ebuf.iter() {
      let mut ev = EvalEvent{
        rec:  CVar(event.sub.rec),
        sub:  event.sub.sub.clone(),
        off:  Vec::new(),
        ary:  Vec::new(),
        rel:  Vec::new(),
        tup:  Vec::new(),
      };
      env.fill_bufs(ev.rec, &ev.sub, &mut ev.off, &mut ev.ary, &mut ev.rel, &mut ev.tup);
      for tu in event.cons.iter() {
        tups.insert(tu.clone(), ev.clone());
      }
    }
    tups
  }

  fn swap_nocap(&mut self, tlb: TNum, new_env: &mut TFrame, newswap: &mut dyn ESwap, defer: bool) {
    // TODO
    //newswap.copy_from(self);
    let mut swaptup = Vec::new();
    let mut swap_tlb = new_env.shm._snapshot().next_glb();
    let mut ev_bufs = None;
    for &ub in self.fbuf.iter() {
      while new_env.shm._atlas().lub() < ub {
        let x = new_env.shm._fresh_var(TAttr::Gen);
        let prev_tlb = self.ffwd.insert(x, swap_tlb);
        assert!(prev_tlb.is_none());
        //swap_tlb = new_env.shm._snapshot().next_glb();
      }
    }
    for (_, event) in self.ebuf.iter() {
      // TODO
      ev_bufs = None;
      let rec_var = CVar(event.sub.rec);
      let mut vvv = false;
      /*if rec_var.0 == 174 || rec_var.0 == 175 {
        vvv = true;
      }*/
      if vvv {
        println!("TRACE: SwapTrace::swap_nocap: tlb={} rec={} sub={:?} cons={:?}",
            tlb, rec_var.0, &event.sub.sub, &event.cons);
      }
      for tu in event.cons.iter() {
        if tu.rel == new_env.shm.evar.0 {
          if defer {
            if let Some(newswap) = newswap.any_mut().downcast_mut::<SwapTrace>() {
              // TODO
              match newswap.ebuf.get_mut(&event.sub) {
                None => {
                  let mut cons = IHTreapSet::default();
                  cons.insert(tu.clone());
                  newswap.ebuf.insert(event.sub.clone(), TraceEEvent{sub: event.sub.clone(), cons});
                }
                Some(event) => {
                  event.cons.insert(tu.clone());
                }
              }
            } else {
              panic!("bug: SwapTrace::swap_nocap: type mismatch");
            }
            continue;
          }
          swap_tlb = new_env.shm._snapshot().next_glb();
        }
        let (neg, rel_var) = if tu.rel < 0 {
          (true, CVar(-tu.rel))
        } else if tu.rel > 0 {
          (false, CVar(tu.rel))
        } else {
          panic!("bug: SwapTrace::swap_nocap: sign");
        };
        let rel_mut = match new_env.rels.get_mut(&rel_var) {
          None => unreachable!(),
          Some(r) => match Rc::get_mut(r) {
            None => {
              *r = r.clone_ref();
              match Rc::get_mut(r) {
                None => unreachable!(),
                Some(rr) => rr
              }
            }
            Some(rr) => rr
          }
        };
        swaptup.clear();
        let (swapped, fresh) = match if neg {
          rel_mut.swap_neg_tup_(swap_tlb, rec_var, rel_var, &tu.tup, &mut swaptup, newswap, &mut new_env.shm)
        } else {
          rel_mut.swap_pos_tup_(swap_tlb, rec_var, rel_var, &tu.tup, &mut swaptup, newswap, &mut new_env.shm)
        } {
          //Noswap => {
          (Noswap, _) => {
            // FIXME
            (false, false)
          }
          //Stale(t) => {
          (Stale, t) => {
            assert!(t >= swap_tlb);
            (true, false)
          }
          //Fresh(t) => {
          //(Fresh, t) => {
          (Fresh, _) |
          (Merge, _) => {
            (true, true)
          }
        };
        drop(rel_mut);
        /*if vvv && tu.rel == 49 {
          println!("TRACE: SwapTrace::swap_nocap:   swapped?{:?} fresh?{:?}",
              swapped, fresh);
        }*/
        if swapped {
          assert!(!swaptup.is_empty());
          match ev_bufs {
            None => {
              let mut bufs = EventBufs::default();
              let (ante, cons) = new_env.fill_bufs(rec_var, &event.sub.sub, &mut bufs.off, &mut bufs.ary, &mut bufs.rel, &mut bufs.tup);
              bufs.ante = ante;
              bufs.cons = cons;
              ev_bufs = Some(bufs);
            }
            Some(_) => {}
          }
          if event.sub.sub.is_empty() {
            self.src.insert(event.sub.clone());
          }
          for tup in swaptup.chunks(tu._arity()) {
            let tu = TTup{rel: tu.rel, tup: tup.to_owned()};
            if vvv {
              println!("TRACE: SwapTrace::swap_nocap:   swapped: rel={} tup={:?}",
                  tu.rel, &tu.tup);
            }
            match self.fwd.get_mut(&tu) {
              None => {
                let mut t_subs = IHTreapMap::default();
                let mut subs = IHTreapSet::default();
                subs.insert(event.sub.clone());
                t_subs.insert(swap_tlb, subs);
                self.fwd.insert(tu.clone(), t_subs);
                if vvv {
                  println!("TRACE: SwapTrace::swap_nocap:     fwd: new");
                }
              }
              Some(t_subs) => match t_subs.get_mut(&swap_tlb) {
                None => {
                  let mut subs = IHTreapSet::default();
                  subs.insert(event.sub.clone());
                  t_subs.insert(swap_tlb, subs);
                  if vvv {
                    println!("TRACE: SwapTrace::swap_nocap:     fwd: new sub");
                  }
                }
                Some(subs) => {
                  subs.insert(event.sub.clone());
                  if vvv {
                    println!("TRACE: SwapTrace::swap_nocap:     fwd: insert sub");
                  }
                }
              }
            }
            match self.bwd.get_mut(&event.sub) {
              None => {
                let mut t_tups = IHTreapMap::default();
                let mut tups = IHTreapSet::default();
                tups.insert(tu.clone());
                t_tups.insert(swap_tlb, tups);
                self.bwd.insert(event.sub.clone(), t_tups);
              }
              Some(t_tups) => match t_tups.get_mut(&swap_tlb) {
                None => {
                  let mut tups = IHTreapSet::default();
                  tups.insert(tu.clone());
                  t_tups.insert(swap_tlb, tups);
                }
                Some(tups) => {
                  tups.insert(tu.clone());
                }
              }
            }
            let ev_bufs = ev_bufs.as_ref().unwrap();
            for r in 0 .. ev_bufs.ante {
              let o = ev_bufs.off[r] as usize;
              let o2 = ev_bufs.off[r + 1] as usize;
              let mut tu = TTup{rel: ev_bufs.rel[r], tup: ev_bufs.tup[o .. o2].to_owned()};
              let (lar, rar) = new_env.rel_arity2(CVar(ev_bufs.rel[r].abs()));
              let (_, kind2) = new_env.rel_kind2(CVar(ev_bufs.rel[r].abs()));
              tu._lo_tup_mut(lar, kind2);
              match self.efwd.get_mut(&event.sub) {
                None => {
                  let mut t_tups = IHTreapMap::default();
                  let mut tups = IHTreapSet::default();
                  tups.insert(tu.clone());
                  t_tups.insert(swap_tlb, tups);
                  self.efwd.insert(event.sub.clone(), t_tups);
                }
                Some(t_tups) => match t_tups.get_mut(&swap_tlb) {
                  None => {
                    let mut tups = IHTreapSet::default();
                    tups.insert(tu.clone());
                    t_tups.insert(swap_tlb, tups);
                  }
                  Some(tups) => {
                    tups.insert(tu.clone());
                  }
                }
              }
              match self.ebwd.get_mut(&tu) {
                None => {
                  let mut t_subs = IHTreapMap::default();
                  let mut subs = IHTreapSet::default();
                  subs.insert(event.sub.clone());
                  t_subs.insert(swap_tlb, subs);
                  self.ebwd.insert(tu.clone(), t_subs);
                }
                Some(t_subs) => match t_subs.get_mut(&swap_tlb) {
                  None => {
                    let mut subs = IHTreapSet::default();
                    subs.insert(event.sub.clone());
                    t_subs.insert(swap_tlb, subs);
                  }
                  Some(subs) => {
                    subs.insert(event.sub.clone());
                  }
                }
              }
            }
            if fresh {
              for &x in tu.tup.iter() {
                match self.idx.get_mut(&x) {
                  None => {
                    let mut tups = IHTreapMap::default();
                    tups.insert(tu.clone(), swap_tlb);
                    self.idx.insert(x, tups);
                  }
                  Some(tups) => {
                    match tups.get(&tu) {
                      None => {
                        tups.insert(tu.clone(), swap_tlb);
                      }
                      Some(_) => {}
                    }
                  }
                }
              }
            }
            break;
          }
        }
        if fresh {
          if tu.rel == new_env.shm.evar.0 {
            swap_tlb = new_env.shm._snapshot().next_glb();
            let post = (min(tu.tup[0], tu.tup[1]), max(tu.tup[0], tu.tup[1]));
            assert!(post.0 < post.1);
            match self.uidx.get(&post.1) {
              None => {
                self.uidx.insert(post.1, (swap_tlb, post.0));
                match self.idx.get(&post.1) {
                  None => {}
                  Some(tups) => {
                    let tups = tups.clone();
                    for (o_tu, _) in tups.iter() {
                      let n_tu = o_tu._swap_var(post.1, post.0);
                      match self.ufwd.get_mut(&n_tu) {
                        None => {
                          let mut t_tups = IHTreapMap::default();
                          let mut tups = IHTreapSet::default();
                          /*for tup in swaptup.chunks(tu._arity()) {
                            let tu = TTup{rel: tu.rel, tup: tup.to_owned()};
                            tups.insert(tu.clone());
                          }*/
                          tups.insert(tu.clone());
                          tups.insert(n_tu.clone());
                          tups.insert(o_tu.clone());
                          t_tups.insert(swap_tlb, tups);
                          self.ufwd.insert(n_tu.clone(), t_tups);
                        }
                        Some(t_tups) => match t_tups.get_mut(&swap_tlb) {
                          None => {
                            let mut tups = IHTreapSet::default();
                            tups.insert(tu.clone());
                            tups.insert(n_tu.clone());
                            tups.insert(o_tu.clone());
                            t_tups.insert(swap_tlb, tups);
                          }
                          Some(tups) => {
                            tups.insert(tu.clone());
                            tups.insert(n_tu.clone());
                            tups.insert(o_tu.clone());
                          }
                        }
                      }
                      match self.ubwd.get_mut(&n_tu) {
                        None => {
                          let mut t_tups = IHTreapMap::default();
                          t_tups.insert(swap_tlb, n_tu.clone());
                          self.ubwd.insert(n_tu.clone(), t_tups);
                        }
                        Some(t_tups) => match t_tups.get(&swap_tlb) {
                          None => {
                            t_tups.insert(swap_tlb, n_tu.clone());
                          }
                          Some(q_tu) => {
                            println!("TRACE: SwapTrace::swap: ubwd: unexpected duplicate: {} {:?} {:?} {:?}", swap_tlb, n_tu, n_tu, q_tu);
                            panic!("BUG");
                          }
                        }
                      }
                      match self.ubwd.get_mut(o_tu) {
                        None => {
                          let mut t_tups = IHTreapMap::default();
                          t_tups.insert(swap_tlb, n_tu.clone());
                          self.ubwd.insert(o_tu.clone(), t_tups);
                        }
                        Some(t_tups) => match t_tups.get(&swap_tlb) {
                          None => {
                            t_tups.insert(swap_tlb, n_tu.clone());
                          }
                          Some(q_tu) => {
                            println!("TRACE: SwapTrace::swap: ubwd: unexpected duplicate: {} {:?} {:?} {:?}", swap_tlb, o_tu, n_tu, q_tu);
                            panic!("BUG");
                          }
                        }
                      }
                      match self.idx.get_mut(&post.0) {
                        None => {
                          let mut tups = IHTreapMap::default();
                          tups.insert(n_tu, swap_tlb);
                          self.idx.insert(post.0, tups);
                        }
                        Some(tups) => {
                          tups.insert(n_tu, swap_tlb);
                        }
                      }
                    }
                    /*self.idx.remove(&post.1);*/
                  }
                }
              }
              Some(_) => {}
            }
          }
        }
      }
    }
  }

  fn swap(&mut self, tlb: TNum, new_env: &mut TFrame, newswap: &mut dyn ESwap, xlb: &WPtr, cap: &mut dyn ECapture, defer: bool) {
    // TODO
    //newswap.copy_from(self);
    let mut swaptup = Vec::new();
    let mut swap_tlb = new_env.snapshot().next_glb();
    let mut ev_bufs = None;
    for &ub in self.fbuf.iter() {
      while new_env.shm._atlas().lub() < ub {
        let x = new_env.shm._fresh_var(TAttr::Gen);
        let prev_tlb = self.ffwd.insert(x, swap_tlb);
        assert!(prev_tlb.is_none());
        //swap_tlb = new_env.snapshot().next_glb();
      }
    }
    for (_, event) in self.ebuf.iter() {
      // TODO
      ev_bufs = None;
      let rec_var = CVar(event.sub.rec);
      let mut vvv = false;
      /*if rec_var.0 == 174 || rec_var.0 == 175 {
        vvv = true;
      }*/
      if vvv {
        println!("TRACE: SwapTrace::swap: tlb={} rec={} sub={:?} cons={:?}",
            tlb, rec_var.0, &event.sub.sub, &event.cons);
      }
      for tu in event.cons.iter() {
        if tu.rel == new_env.shm.evar.0 {
          if defer {
            //newswap.stage_tup(tlb, SwapEvent::Rec(rec_var), raw_rel, &self.buf[swapoff .. swapoff + arity]);
            if let Some(newswap) = newswap.any_mut().downcast_mut::<SwapTrace>() {
              // TODO
              match newswap.ebuf.get_mut(&event.sub) {
                None => {
                  let mut cons = IHTreapSet::default();
                  cons.insert(tu.clone());
                  newswap.ebuf.insert(event.sub.clone(), TraceEEvent{sub: event.sub.clone(), cons});
                }
                Some(event) => {
                  event.cons.insert(tu.clone());
                }
              }
              /*let key = (min(tu.tup[0], tu.tup[1]), max(tu.tup[0], tu.tup[1]));
              let pre_tup0 = TTup{rel: new_env.shm.evar.0, tup: vec![key.0, key.0]};
              let pre_tup1 = TTup{rel: new_env.shm.evar.0, tup: vec![key.1, key.1]};
              match newswap.ubuf.get_mut(&key) {
                None => {
                  let mut pre = IHTreapSet::default();
                  pre.insert((pre_tup0, pre_tup1));
                  newswap.ubuf.insert(key, TraceUEvent{pre, post: key});
                }
                Some(event) => {
                  event.pre.insert((pre_tup0, pre_tup1));
                }
              }*/
            } else {
              panic!("bug: SwapTrace::swap: type mismatch");
            }
            continue;
          }
          swap_tlb = new_env.shm._snapshot().next_glb();
        }
        let (neg, rel_var) = if tu.rel < 0 {
          (true, CVar(-tu.rel))
        } else if tu.rel > 0 {
          (false, CVar(tu.rel))
        } else {
          panic!("bug: SwapTrace::swap: sign");
        };
        let rel_mut = match new_env.rels.get_mut(&rel_var) {
          None => unreachable!(),
          Some(r) => match Rc::get_mut(r) {
            None => {
              *r = r.clone_ref();
              match Rc::get_mut(r) {
                None => unreachable!(),
                Some(rr) => rr
              }
            }
            Some(rr) => rr
          }
        };
        swaptup.clear();
        /*match if neg {
          rel_mut.swap_neg_tup_(tlb, rec_var, rel_var, &tu.tup, &mut swaptup, newswap, &mut new_env.shm)
        } else {
          rel_mut.swap_pos_tup_(tlb, rec_var, rel_var, &tu.tup, &mut swaptup, newswap, &mut new_env.shm)
        } {
          Noswap | Stale(_) => {}
          Fresh(_) => {
            if !(rel_var == new_env.shm.evar && !neg) {
              cap._alloc(xlb, tu.rel, &tu.tup);
            }
          }
        }*/
        let (swapped, fresh) = match if neg {
        //let (sw_t, swapped, fresh) = match if neg {
          rel_mut.swap_neg_tup_(swap_tlb, rec_var, rel_var, &tu.tup, &mut swaptup, newswap, &mut new_env.shm)
        } else {
          rel_mut.swap_pos_tup_(swap_tlb, rec_var, rel_var, &tu.tup, &mut swaptup, newswap, &mut new_env.shm)
        } {
          //Noswap => {
          (Noswap, _) => {
            // FIXME
            (false, false)
            //(0, false, false)
          }
          //Stale(t) => {
          (Stale, t) => {
            assert!(t >= swap_tlb);
            (true, false)
            //(t, t >= swap_tlb, false)
          }
          //Fresh(t) => {
          //(Fresh, t) => {
          (Fresh, _t) |
          (Merge, _t) => {
            //if !(rel_var == new_env.shm.evar && !neg) {
            if tu.rel != new_env.shm.evar.0 {
              cap._alloc(xlb, tu.rel, &tu.tup);
            }
            (true, true)
            //(t, true, true)
          }
        };
        /*if vvv && tu.rel == 49 {
          println!("TRACE: SwapTrace::swap:   swapped?{:?} fresh?{:?} t={}",
              swapped, fresh, sw_t);
        }*/
        if swapped {
          assert!(!swaptup.is_empty());
          match ev_bufs {
            None => {
              let mut bufs = EventBufs::default();
              let (ante, cons) = new_env.fill_bufs(rec_var, &event.sub.sub, &mut bufs.off, &mut bufs.ary, &mut bufs.rel, &mut bufs.tup);
              bufs.ante = ante;
              bufs.cons = cons;
              ev_bufs = Some(bufs);
            }
            Some(_) => {}
          }
          if event.sub.sub.is_empty() {
            self.src.insert(event.sub.clone());
          }
          for tup in swaptup.chunks(tu._arity()) {
            let tu = TTup{rel: tu.rel, tup: tup.to_owned()};
            if vvv {
              println!("TRACE: SwapTrace::swap:   swapped: rel={} tup={:?}",
                  tu.rel, &tu.tup);
            }
            match self.fwd.get_mut(&tu) {
              None => {
                let mut t_subs = IHTreapMap::default();
                let mut subs = IHTreapSet::default();
                subs.insert(event.sub.clone());
                t_subs.insert(swap_tlb, subs);
                self.fwd.insert(tu.clone(), t_subs);
                if vvv {
                  println!("TRACE: SwapTrace::swap:     fwd: new");
                }
              }
              Some(t_subs) => match t_subs.get_mut(&swap_tlb) {
                None => {
                  let mut subs = IHTreapSet::default();
                  subs.insert(event.sub.clone());
                  t_subs.insert(swap_tlb, subs);
                  if vvv {
                    println!("TRACE: SwapTrace::swap:     fwd: new sub");
                  }
                }
                Some(subs) => {
                  subs.insert(event.sub.clone());
                  if vvv {
                    println!("TRACE: SwapTrace::swap:     fwd: insert sub");
                  }
                }
              }
            }
            match self.bwd.get_mut(&event.sub) {
              None => {
                let mut t_tups = IHTreapMap::default();
                let mut tups = IHTreapSet::default();
                tups.insert(tu.clone());
                t_tups.insert(swap_tlb, tups);
                self.bwd.insert(event.sub.clone(), t_tups);
              }
              Some(t_tups) => match t_tups.get_mut(&swap_tlb) {
                None => {
                  let mut tups = IHTreapSet::default();
                  tups.insert(tu.clone());
                  t_tups.insert(swap_tlb, tups);
                }
                Some(tups) => {
                  tups.insert(tu.clone());
                }
              }
            }
            let ev_bufs = ev_bufs.as_ref().unwrap();
            for r in 0 .. ev_bufs.ante {
              let o = ev_bufs.off[r] as usize;
              let o2 = ev_bufs.off[r + 1] as usize;
              let mut tu = TTup{rel: ev_bufs.rel[r], tup: ev_bufs.tup[o .. o2].to_owned()};
              let (lar, rar) = new_env.rel_arity2(CVar(ev_bufs.rel[r].abs()));
              let (_, kind2) = new_env.rel_kind2(CVar(ev_bufs.rel[r].abs()));
              tu._lo_tup_mut(lar, kind2);
              match self.efwd.get_mut(&event.sub) {
                None => {
                  let mut t_tups = IHTreapMap::default();
                  let mut tups = IHTreapSet::default();
                  tups.insert(tu.clone());
                  t_tups.insert(swap_tlb, tups);
                  self.efwd.insert(event.sub.clone(), t_tups);
                }
                Some(t_tups) => match t_tups.get_mut(&swap_tlb) {
                  None => {
                    let mut tups = IHTreapSet::default();
                    tups.insert(tu.clone());
                    t_tups.insert(swap_tlb, tups);
                  }
                  Some(tups) => {
                    tups.insert(tu.clone());
                  }
                }
              }
              match self.ebwd.get_mut(&tu) {
                None => {
                  let mut t_subs = IHTreapMap::default();
                  let mut subs = IHTreapSet::default();
                  subs.insert(event.sub.clone());
                  t_subs.insert(swap_tlb, subs);
                  self.ebwd.insert(tu.clone(), t_subs);
                }
                Some(t_subs) => match t_subs.get_mut(&swap_tlb) {
                  None => {
                    let mut subs = IHTreapSet::default();
                    subs.insert(event.sub.clone());
                    t_subs.insert(swap_tlb, subs);
                  }
                  Some(subs) => {
                    subs.insert(event.sub.clone());
                  }
                }
              }
            }
            if fresh {
              for &x in tu.tup.iter() {
                match self.idx.get_mut(&x) {
                  None => {
                    let mut tups = IHTreapMap::default();
                    tups.insert(tu.clone(), swap_tlb);
                    self.idx.insert(x, tups);
                  }
                  Some(tups) => {
                    match tups.get(&tu) {
                      None => {
                        tups.insert(tu.clone(), swap_tlb);
                      }
                      Some(_) => {}
                    }
                  }
                }
              }
            }
            break;
          }
        }
        if fresh {
          if tu.rel == new_env.shm.evar.0 {
            swap_tlb = new_env.shm._snapshot().next_glb();
            let post = (min(tu.tup[0], tu.tup[1]), max(tu.tup[0], tu.tup[1]));
            assert!(post.0 < post.1);
            match self.uidx.get(&post.1) {
              None => {
                self.uidx.insert(post.1, (swap_tlb, post.0));
                match self.idx.get(&post.1) {
                  None => {}
                  Some(tups) => {
                    let tups = tups.clone();
                    for (o_tu, _) in tups.iter() {
                      let n_tu = o_tu._swap_var(post.1, post.0);
                      match self.ufwd.get_mut(&n_tu) {
                        None => {
                          let mut t_tups = IHTreapMap::default();
                          let mut tups = IHTreapSet::default();
                          tups.insert(tu.clone());
                          tups.insert(n_tu.clone());
                          tups.insert(o_tu.clone());
                          t_tups.insert(swap_tlb, tups);
                          self.ufwd.insert(n_tu.clone(), t_tups);
                        }
                        Some(t_tups) => match t_tups.get_mut(&swap_tlb) {
                          None => {
                            let mut tups = IHTreapSet::default();
                            tups.insert(tu.clone());
                            tups.insert(n_tu.clone());
                            tups.insert(o_tu.clone());
                            t_tups.insert(swap_tlb, tups);
                          }
                          Some(tups) => {
                            tups.insert(tu.clone());
                            tups.insert(n_tu.clone());
                            tups.insert(o_tu.clone());
                          }
                        }
                      }
                      match self.ubwd.get_mut(&n_tu) {
                        None => {
                          let mut t_tups = IHTreapMap::default();
                          t_tups.insert(swap_tlb, n_tu.clone());
                          self.ubwd.insert(n_tu.clone(), t_tups);
                        }
                        Some(t_tups) => match t_tups.get(&swap_tlb) {
                          None => {
                            t_tups.insert(swap_tlb, n_tu.clone());
                          }
                          Some(q_tu) => {
                            println!("TRACE: SwapTrace::swap: ubwd: unexpected duplicate: {} {:?} {:?} {:?}", swap_tlb, n_tu, n_tu, q_tu);
                            panic!("BUG");
                          }
                        }
                      }
                      match self.ubwd.get_mut(o_tu) {
                        None => {
                          let mut t_tups = IHTreapMap::default();
                          t_tups.insert(swap_tlb, n_tu.clone());
                          self.ubwd.insert(o_tu.clone(), t_tups);
                        }
                        Some(t_tups) => match t_tups.get(&swap_tlb) {
                          None => {
                            t_tups.insert(swap_tlb, n_tu.clone());
                          }
                          Some(q_tu) => {
                            println!("TRACE: SwapTrace::swap: ubwd: unexpected duplicate: {} {:?} {:?} {:?}", swap_tlb, o_tu, n_tu, q_tu);
                            panic!("BUG");
                          }
                        }
                      }
                      match self.idx.get_mut(&post.0) {
                        None => {
                          let mut tups = IHTreapMap::default();
                          tups.insert(n_tu, swap_tlb);
                          self.idx.insert(post.0, tups);
                        }
                        Some(tups) => {
                          tups.insert(n_tu, swap_tlb);
                        }
                      }
                    }
                    /*self.idx.remove(&post.1);*/
                  }
                }
              }
              Some(_) => {}
            }
          }
        }
      }
    }
  }

  fn _copy_from(&mut self, other: &dyn ESwap) {
    if let Some(other) = other.any_ref().downcast_ref::<SwapTrace>() {
      // TODO
      self.src = other.src.clone();
      self.ffwd = other.ffwd.clone();
      self.fwd = other.fwd.clone();
      self.bwd = other.bwd.clone();
      self.efwd = other.efwd.clone();
      self.ebwd = other.ebwd.clone();
      self.ufwd = other.ufwd.clone();
      self.ubwd = other.ubwd.clone();
      //self.cfwd = other.cfwd.clone();
      self.idx = other.idx.clone();
      self.uidx = other.uidx.clone();
    } else {
      panic!("bug: SwapTrace::copy_from: type mismatch");
    }
  }
}

impl SwapTrace {
  pub fn rollback_tup(&self, rel: SNum, tup: &[SNum], bwd_tups: &mut Vec<TTup>) -> Option<TNum> {
    // TODO
    unimplemented!();
  }

  pub fn rollback2_tup(&self, rel: SNum, tup: &[SNum], bwd_tups: &mut Vec<Vec<TTup>>) -> Option<TNum> {
    // TODO
    unimplemented!();
  }
}

#[derive(Clone, Copy, Debug)]
pub enum TStatus {
  Unsat,
  Sat,
  Par,
}

pub type EFrameRef = Rc<dyn EFrame>;
pub type ERelRef = Rc<dyn ERel>;
//pub type EScanRef = Rc<dyn EScan>;
pub type EScanBox = Box<dyn EScan>;

pub type TFrameRef = Rc<TFrame>;
pub type EquivRelRef = Rc<EquivRel>;

pub trait EFrame {
  fn snapshot(&self) -> TSnapshot { unimplemented!(); }
  fn terminal(&mut self, _tlb: TNum, /*_ts: &mut Vec<TNum>*/) -> Option<TStatus> { unimplemented!(); }

  fn nul_count(&self) -> usize { unimplemented!(); }
  fn def_count(&self) -> usize { unimplemented!(); }
  fn ext_count(&self) -> usize { unimplemented!(); }
  fn fill_nul(&self, _nul_buf: &mut [SNum]) { unimplemented!(); }
  fn fill_def(&self, _def_buf: &mut [SNum]) { unimplemented!(); }
  fn fill_ext(&self, _ext_buf: &mut [SNum]) { unimplemented!(); }

  fn rel_count(&self) -> usize { unimplemented!(); }
  fn fill_rel(&self, _rel_buf: &mut [SNum]) { unimplemented!(); }

  fn rel_arity(&self, _rel: CVar) -> usize { unimplemented!(); }
  fn rel_arity2(&self, _rel: CVar) -> (usize, usize) { unimplemented!(); }
  fn rel_kind2(&self, _rel: CVar) -> (RelKind, RelKind2) { unimplemented!(); }
  fn fun_arity(&self, _rel: CVar) -> Option<(usize, usize)> { unimplemented!(); }
  fn rec_arity(&self, _rec: CVar) -> (usize, usize) { unimplemented!(); }

  fn fill_bufs(&self, _rec: CVar, _sub: &[SNum], _off: &mut Vec<u32>, _ary: &mut Vec<u32>, _rel: &mut Vec<SNum>, _tup: &mut Vec<SNum>) -> (usize, usize) { unimplemented!(); }

  fn pos_tup_size(&self, _rel: CVar) -> u64 { unimplemented!(); }
  fn neg_tup_size(&self, _rel: CVar) -> u64 { unimplemented!(); }
  fn pos_least_ub(&self, _rel: CVar) -> TNum { unimplemented!(); }
  fn neg_least_ub(&self, _rel: CVar) -> TNum { unimplemented!(); }
  fn patch_rel(&mut self, _rel: CVar) { unimplemented!(); }
  fn patchdiff_rel(&mut self, _rel: CVar, _older: &TFrameRef) -> (usize, usize) { unimplemented!(); }

  fn test_pos_tup(&mut self, _rel: CVar, _tup: &[SNum]) -> TResult { unimplemented!(); }
  fn test_neg_tup(&mut self, _rel: CVar, _tup: &[SNum]) -> TResult { unimplemented!(); }

  fn scan_pos(&mut self, _rel: CVar, _lbtup: &[SNum], _ubtup: &[SNum]) -> EScanBox { unimplemented!(); }
  fn scan_neg(&mut self, _rel: CVar, _lbtup: &[SNum], _ubtup: &[SNum]) -> EScanBox { unimplemented!(); }

  fn swap_pos_tup(&mut self, _rec: CVar, _rel: CVar, _tup: &[SNum], _newswap: &mut Vec<SNum>, _swaptup: &mut Vec<SNum>) -> TResult { unimplemented!(); }
  fn swap_neg_tup(&mut self, _rec: CVar, _rel: CVar, _tup: &[SNum], _newswap: &mut Vec<SNum>, _swaptup: &mut Vec<SNum>) -> TResult { unimplemented!(); }

  fn prop_eval_1(&mut self, _tlb: TNum, _ts: &mut Vec<TNum>, _rel: &mut Vec<SNum>, _pat: &mut Vec<SNum>, _tup: &mut Vec<SNum>) -> Option<TStatus> { unimplemented!(); }
  fn nul_eval_1(&mut self, _tlb: TNum, _rec_var: CVar, _nod: &mut Vec<Vec<usize>>, _idx: &mut Vec<u32>, _sub: &mut Vec<SNum>, _off: &mut Vec<u32>, _ary: &mut Vec<u32>, _rel: &mut Vec<SNum>, _pat: &mut Vec<SNum>, _tup: &mut Vec<SNum>, _savepat: &mut Vec<SNum>, _swap: &mut dyn ESwap, _cap: &mut dyn ECapture) { unimplemented!(); }
  fn def_eval_1(&mut self, _tlb: TNum, _rec_var: CVar, _nod: &mut Vec<Vec<usize>>, _idx: &mut Vec<u32>, _sub: &mut Vec<SNum>, _off: &mut Vec<u32>, _ary: &mut Vec<u32>, _rel: &mut Vec<SNum>, _pat: &mut Vec<SNum>, _tup: &mut Vec<SNum>, _savepat: &mut Vec<SNum>, _swap: &mut dyn ESwap, _cap: &mut dyn ECapture) { unimplemented!(); }

  fn swap(&mut self, _swapbuf: &[SNum], _newswap: &mut Vec<SNum>) { unimplemented!(); }
  fn swapfix(&mut self, _swap: &mut Vec<SNum>, _newswap: &mut Vec<SNum>) { unimplemented!(); }
  fn swapfix_(&mut self, _tlb: TNum, _swap: &mut Vec<SNum>, _newswap: &mut Vec<SNum>, _xlb: WPtr, _cap: &mut dyn ECapture, _cap_first: bool) { unimplemented!(); }
  fn patch_swap(&mut self, _tlb: TNum, _newswap: &mut dyn ESwap) { unimplemented!(); }
  fn fix_swap(&mut self, _tlb: TNum, _swap: &mut dyn ESwap, _newswap: &mut dyn ESwap, _xlb: WPtr, _cap: &mut dyn ECapture, _cap_first: bool) { unimplemented!(); }
}

#[derive(Clone)]
pub struct STFrame {
  pub evar: CVar,
  pub clk:  TClk,
  pub univ: TUniverse,
  pub cc:   TUnionFind,
  pub pseu: IHTreapMap<CVar, CVar>,
  pub rpsu: IHTreapMap<CVar, CVar>,
  // TODO
  //pub flag: Option<(CVar, TNum)>,
  // TODO
  //pub cats: HTreapMap<CVar, STCat1>,
  //pub cats: HTreapMap<CVar, ECatRef>,
}

impl Default for STFrame {
  fn default() -> STFrame {
    let mut clk = TClk::default();
    let mut univ = TUniverse::default();
    let mut cc = TUnionFind::default();
    let evar = cc.fresh(TAttr::Top, &mut univ, &mut clk);
    assert_eq!(evar.0, 1);
    STFrame{
      evar,
      clk,
      univ,
      cc,
      pseu: IHTreapMap::default(),
      rpsu: IHTreapMap::default(),
      //flag: None,
      //cats: HTreapMap::default(),
    }
  }
}

impl STFrame {
  pub fn _snapshot(&self) -> TSnapshot {
    self.clk.checkpoint()
  }

  pub fn _atlas(&self) -> TAtlas {
    self.univ.checkpoint()
  }

  pub fn _provision(&self, chk: &mut TAtlas) -> SNum {
    self.univ.provision(chk)
  }

  pub fn _fresh_var(&mut self, a: TAttr) -> SNum {
    self.cc.fresh(a, &mut self.univ, &mut self.clk).0
  }

  pub fn fresh_var(&mut self, a: TAttr) -> CVar {
    CVar(self._fresh_var(a))
  }

  pub fn _pseudo_var(&self, rel_var: CVar) -> SNum {
    match self.pseu.get(&rel_var) {
      None => panic!("bug: STFrame::_pseudo_var: missing key: {}", rel_var.0),
      Some(&pseudo_var) => pseudo_var.0
    }
  }

  pub fn pseudo_var(&self, rel_var: CVar) -> CVar {
    CVar(self._pseudo_var(rel_var))
  }
}

#[derive(Clone, Default)]
pub struct Rel2RecIndex {
  pub ante: CUnionIter<CVar>,
  pub cons: CUnionIter<CVar>,
}

/*#[derive(Clone, Debug)]
pub struct FrameDiagnostics {
  pub horizon:      TNum,
  //pub uhorizon:     TNum,
  pub univ_size:    u32,
  pub rel_count:    u32,
  pub urec_count:   u32,
  pub drec_count:   u32,
  pub xrec_count:   u32,
  pub rel_ptupsize: u64,
  pub rel_ntupsize: u64,
  pub rel_memsize:  u64,
}*/

//#[derive(Clone)]
pub struct TDiagnosticFrame {
  clk:  TClk,
  univ: TUniverse,
  cc:   TDiagnosticUnionFind,
  //flag: Option<(CVar, TNum)>,
  evar: CVar,
  // TODO
}

impl TDiagnosticFrame {
  pub fn dump(&self) {
    self.print();
  }

  pub fn print(&self) {
    println!("DUMP:  clk:  t={}", self.clk.tctr);
    println!("DUMP:  univ: v={}", self.univ.vctr);
    println!("DUMP:  cc:   t={} tu={}", self.cc.t, self.cc.tu);
    println!("DUMP:  cc:   rdom: {:?}", self.cc.rdom);
    //println!("DUMP:  cc:   ulog: {:?}", self.cc.ulog);
    //println!("DUMP:  flag? {:?}", self.flag);
    println!("DUMP:  evar: {:?}", self.evar);
  }
}

#[derive(Clone, Default)]
pub struct TFrame {
  // TODO
  pub shm:  STFrame,
  pub rels: IHTreapMap<CVar, ERelRef>,
  pub urec: HTreapMap<CVar, TRec1>,
  pub drec: HTreapMap<CVar, TRec1>,
  pub xrec: HTreapMap<CVar, TRec1>,
  pub prop: Option<TFre1>,
}

impl TFrame {
  /*pub fn diagnostics(&self) -> FrameDiagnostics {
    let snapshot = self.clk.snapshot();
    let mut rel_ptupsize = 0;
    let mut rel_ntupsize = 0;
    let rel_memsize = 0;
    for (_, rel) in self.rels.iter() {
      rel_ptupsize += rel.pos_tup_size(&self.shm);
      rel_ntupsize += rel.neg_tup_size(&self.shm);
    }
    FrameDiagnostics{
      horizon:      snapshot.t,
      //uhorizon:     usnapshot.tu,
      univ_size:    self.univ.vctr as _,
      rel_count:    self.rels.len() as _,
      urec_count:   self.urec.len() as _,
      drec_count:   self.drec.len() as _,
      xrec_count:   self.xrec.len() as _,
      rel_ptupsize,
      rel_ntupsize,
      rel_memsize,
    }
  }*/

  pub fn diagnostic(&self) -> TDiagnosticFrame {
    TDiagnosticFrame{
      clk:  self.shm.clk.clone(),
      univ: self.shm.univ.clone(),
      cc:   self.shm.cc.diagnostic(),
      //flag: self.shm.flag,
      evar: self.shm.evar,
      // TODO
    }
  }

  pub fn tup_size(&self) -> (u64, u64) {
    let mut ptupsize = 0;
    let mut ntupsize = 0;
    for (_, rel) in self.rels.iter() {
      ptupsize += rel.pos_tup_size(&self.shm);
      ntupsize += rel.neg_tup_size(&self.shm);
    }
    (ptupsize, ntupsize)
  }

  pub fn debug_dump_tups(&self, rel_num: SNum) {
    match self.rels.get(&CVar(rel_num)) {
      None => {
        println!("DEBUG: TFrame::debug_dump_tups: invalid: rel={:?}", rel_num);
      }
      Some(r) => r.debug_dump_tups(CVar(rel_num), &self.shm)
    }
  }

  pub fn trace_dump_tups(&self, rel_num: SNum) {
    match self.rels.get(&CVar(rel_num)) {
      None => {
        println!("TRACE: TFrame::trace_dump_tups: invalid: rel={:?}", rel_num);
      }
      Some(r) => r.trace_dump_tups(CVar(rel_num), &self.shm)
    }
  }

  pub fn count_par(&self) -> usize {
    let mut ct = 0;
    let mut tup = Vec::new();
    for (&rel_var, rel) in self.rels.iter() {
      let ar = rel.arity();
      tup.resize(ar, 0);
      let mut scan = rel.scan_par(rel_var, &self.shm);
      loop {
        match scan.next_tup(&mut tup) {
          End => break,
          Skip => continue,
          Hit(_) => {
            ct += 1;
          }
        }
      }
    }
    ct
  }

  pub fn trace_dump_par(&self) {
    println!("TRACE: TFrame::trace_dump_par...");
    let mut ct = 0;
    let mut tup = Vec::new();
    for (&rel_var, rel) in self.rels.iter() {
      let ar = rel.arity();
      tup.resize(ar, 0);
      let mut scan = rel.scan_par(rel_var, &self.shm);
      loop {
        match scan.next_tup(&mut tup) {
          End => break,
          Skip => continue,
          Hit(t) => {
            println!("TRACE:   ! {} {} {:?}", t, rel_var.0, tup);
            ct += 1;
          }
        }
      }
    }
    println!("TRACE: TFrame::trace_dump_par: ct={}", ct);
  }

  pub fn trace_dump_ulog(&self, tlb: TNum) {
    println!("TRACE: TFrame::trace_dump_ulog...");
    print!("TRACE:   [");
    for (&(t, o), &n) in self.shm.cc.ulog.iter_from_excl(&(tlb, CVar(0))) {
      match self.shm.cc.attr.get(&t) {
        None => {
          print!("({},{}), ", o.0, n.0);
        }
        Some(a) => {
          print!("({:?},{},{}), ", a, o.0, n.0);
        }
      }
    }
    println!("]");
  }

  /*pub fn ante_iter(&self, r: CVar) -> impl Iterator<Item=CVar> {
    self.r2r.ante.iter(r)
  }*/

  pub fn track(&mut self, x: SNum) {
    //self.shm.trak.tset.insert(x);
  }

  pub fn terminal_(&mut self, _tlb: TNum, ts: &mut Vec<TNum>) -> Option<TStatus> {
    /*match self.shm.flag {
      None => {}
      Some(_) => {
        //Some(TStatus::Par)
        println!("WARNING: TFrame::terminal_: par");
      }
    }*/
    let mut rel = Vec::new();
    let mut pat = Vec::new();
    let mut tup = Vec::new();
    self.prop_eval_1(0, ts, &mut rel, &mut pat, &mut tup)
  }
}

impl EFrame for TFrame {
  fn snapshot(&self) -> TSnapshot {
    self.shm.clk.checkpoint()
  }

  fn terminal(&mut self, _tlb: TNum) -> Option<TStatus> {
    /*match self.shm.flag {
      None => {}
      Some(_) => {
        //Some(TStatus::Par)
        println!("WARNING: TFrame::terminal: par");
      }
    }*/
    let mut ts = Vec::new();
    let mut rel = Vec::new();
    let mut pat = Vec::new();
    let mut tup = Vec::new();
    self.prop_eval_1(0, &mut ts, &mut rel, &mut pat, &mut tup)
  }

  fn nul_count(&self) -> usize {
    self.urec.len()
  }

  fn def_count(&self) -> usize {
    self.drec.len()
  }

  fn ext_count(&self) -> usize {
    self.xrec.len()
  }

  fn fill_nul(&self, buf: &mut [SNum]) {
    for (i, (&k, _)) in self.urec.iter().enumerate() {
      buf[i] = k.0;
    }
  }

  fn fill_def(&self, buf: &mut [SNum]) {
    for (i, (&k, _)) in self.drec.iter().enumerate() {
      buf[i] = k.0;
    }
  }

  fn fill_ext(&self, buf: &mut [SNum]) {
    for (i, (&k, _)) in self.xrec.iter().enumerate() {
      buf[i] = k.0;
    }
  }

  fn rel_count(&self) -> usize {
    self.rels.len()
  }

  fn fill_rel(&self, buf: &mut [SNum]) {
    for (i, (&k, _)) in self.rels.iter().enumerate() {
      buf[i] = k.0;
    }
  }

  fn rel_arity(&self, rel_var: CVar) -> usize {
    match self.rels.get(&rel_var) {
      None => panic!("bug: TFrame::rel_arity: invalid: {:?}", rel_var),
      Some(rel) => rel.arity()
    }
  }

  fn rel_arity2(&self, rel_var: CVar) -> (usize, usize) {
    match self.rels.get(&rel_var) {
      None => panic!("bug: TFrame::rel_arity2: invalid: {:?}", rel_var),
      Some(rel) => rel.arity2()
    }
  }

  fn rel_kind2(&self, rel_var: CVar) -> (RelKind, RelKind2) {
    match self.rels.get(&rel_var) {
      None => panic!("bug: TFrame::rel_kind2: invalid: {:?}", rel_var),
      Some(rel) => rel.kind2()
    }
  }

  fn fun_arity(&self, rel_var: CVar) -> Option<(usize, usize)> {
    match self.rels.get(&rel_var) {
      None => panic!("bug: TFrame::fun_arity: invalid: {:?}", rel_var),
      Some(rel) => rel.fun_arity()
    }
  }

  fn rec_arity(&self, rec_var: CVar) -> (usize, usize) {
    match self.urec.get(&rec_var) {
      None => {}
      Some(rec) => return rec.rec_arity()
    }
    match self.drec.get(&rec_var) {
      None => {}
      Some(rec) => return rec.rec_arity()
    }
    match self.xrec.get(&rec_var) {
      None => {}
      Some(rec) => return rec.rec_arity()
    }
    panic!("bug: TFrame::rec_arity: invalid: {:?}", rec_var);
  }

  fn fill_bufs(&self, rec_var: CVar, sub: &[SNum], off: &mut Vec<u32>, ary: &mut Vec<u32>, rel: &mut Vec<SNum>, tup: &mut Vec<SNum>) -> (usize, usize) {
    // TODO
    match self.shm.rpsu.get(&rec_var) {
      None => {}
      Some(&pri_rel_var) => {
        // TODO
        let (larity, rarity) = self.rel_arity2(pri_rel_var);
        assert_eq!(larity + 2 * rarity, sub.len());
        off.clear();
        ary.clear();
        let mut o = 0;
        for _ in 0 .. 2 {
          off.push(o);
          ary.push((larity + rarity) as u32);
          o += (larity + rarity) as u32;
        }
        for _ in 0 .. rarity {
          off.push(o);
          ary.push(2);
          o += 2;
        }
        off.push(o);
        rel.clear();
        for _ in 0 .. 2 {
          rel.push(pri_rel_var.0);
        }
        for _ in 0 .. rarity {
          rel.push(self.shm.evar.0);
        }
        tup.clear();
        for t in 0 .. 2 {
          tup.extend_from_slice(&sub[ .. larity]);
          tup.extend_from_slice(&sub[larity + t * rarity .. larity + (t + 1) * rarity]);
        }
        for t in 0 .. rarity {
          tup.push(sub[larity + t]);
          tup.push(sub[larity + rarity + t]);
        }
        return (2, rarity);
      }
    }
    let rec = match self.urec.get(&rec_var).or_else(|| self.drec.get(&rec_var)) {
      None => panic!("bug: TFrame::fill_bufs: invalid: rec={}", rec_var.0),
      Some(rec) => rec
    };
    let atomlen = rec.antelen as usize + rec.conslen as usize;
    assert!(atomlen <= 127);
    off.clear();
    off.resize(atomlen + 1, 0);
    ary.clear();
    ary.resize(atomlen, 0);
    rel.clear();
    rel.resize(atomlen, 0);
    tup.clear();
    let mut p = 0;
    let mut rel_off = 0;
    let mut arg_off = 0;
    while p < rec.data.len() {
      let code = rec.data[p];
      let decode = match code {
        1 => FormDecode::Lit{neg: false},
        -1 => FormDecode::Lit{neg: true},
        _ => panic!("bug: TFrame::fill_bufs: unknown code: {} rec={}", code, rec_var.0)
      };
      p += 1;
      match decode {
        FormDecode::Lit{neg} => {
          let rel_pos = rec.data[p];
          assert!(rel_pos >= 0);
          let rel_var = CVar(rec.freevar[rel_pos as usize]);
          assert!(rel_var.0 > 0);
          match neg {
            false => rel[rel_off] = rel_var.0,
            true => rel[rel_off] = -rel_var.0,
          }
          let arity = self.rel_arity(rel_var);
          off[rel_off] = arg_off as u32;
          ary[rel_off] = arity as u32;
          tup.resize(arg_off + arity, 0);
          p += 1;
          if rec.data.len() < p + arity {
            panic!("bug: TFrame::fill_bufs: out of bounds: rec={}", rec_var.0);
          }
          for q in p .. p + arity {
            let var_pos = rec.data[q];
            if var_pos >= 0 {
              tup[arg_off + q - p] = rec.freevar[var_pos as usize];
            } else {
              tup[arg_off + q - p] = sub[-(var_pos + 1) as usize];
            }
          }
          rel_off += 1;
          arg_off += arity;
          p += arity;
        }
      }
    }
    assert_eq!(rel_off, atomlen);
    off[rel_off] = arg_off as u32;
    (rec.antelen as usize, rec.conslen as usize)
  }

  fn pos_tup_size(&self, rel_var: CVar) -> u64 {
    match self.rels.get(&rel_var) {
      None => panic!("bug: TFrame::pos_tup_size: invalid: {:?}", rel_var),
      Some(rel) => rel.pos_tup_size(&self.shm)
    }
  }

  fn neg_tup_size(&self, rel_var: CVar) -> u64 {
    match self.rels.get(&rel_var) {
      None => panic!("bug: TFrame::neg_tup_size: invalid: {:?}", rel_var),
      Some(rel) => rel.neg_tup_size(&self.shm)
    }
  }

  fn pos_least_ub(&self, rel_var: CVar) -> TNum {
    match self.rels.get(&rel_var) {
      None => panic!("bug: TFrame::pos_least_ub: invalid: {:?}", rel_var),
      Some(rel) => rel.pos_least_ub(&self.shm)
    }
  }

  fn neg_least_ub(&self, rel_var: CVar) -> TNum {
    match self.rels.get(&rel_var) {
      None => panic!("bug: TFrame::neg_least_ub: invalid: {:?}", rel_var),
      Some(rel) => rel.neg_least_ub(&self.shm)
    }
  }

  fn patch_rel(&mut self, rel_var: CVar) {
    let rel_mut = match self.rels.get_mut(&rel_var) {
      //None => unreachable!(),
      None => panic!("bug: TFrame::patch_rel: invalid: {:?}", rel_var),
      Some(r) => match Rc::get_mut(r) {
        None => {
          *r = r.clone_ref();
          match Rc::get_mut(r) {
            None => unreachable!(),
            Some(rr) => rr
          }
        }
        Some(rr) => rr
      }
    };
    rel_mut.patch(rel_var, &mut self.shm)
  }

  fn patchdiff_rel(&mut self, rel_var: CVar, older: &TFrameRef) -> (usize, usize) {
    let this_rel = match self.rels.get(&rel_var) {
      None => panic!("bug: TFrame::patchdiff_rel"),
      Some(r) => r
    };
    let older_rel = match older.rels.get(&rel_var) {
      None => panic!("bug: TFrame::patchdiff_rel"),
      Some(r) => r
    };
    this_rel.patchdiff(rel_var, &**older_rel, &mut self.shm)
  }

  fn test_pos_tup(&mut self, rel_var: CVar, tup: &[SNum]) -> TResult {
    let rel_mut = match self.rels.get_mut(&rel_var) {
      None => panic!("bug: TFrame::test_pos_tup: invalid: {:?}", rel_var),
      Some(r) => match Rc::get_mut(r) {
        None => {
          *r = r.clone_ref();
          match Rc::get_mut(r) {
            None => unreachable!(),
            Some(rr) => rr
          }
        }
        Some(rr) => rr
      }
    };
    rel_mut.test_pos_tup(rel_var, tup, &mut self.shm)
  }

  fn test_neg_tup(&mut self, rel_var: CVar, tup: &[SNum]) -> TResult {
    let rel_mut = match self.rels.get_mut(&rel_var) {
      None => panic!("bug: TFrame::test_neg_tup: invalid: {:?}", rel_var),
      Some(r) => match Rc::get_mut(r) {
        None => {
          *r = r.clone_ref();
          match Rc::get_mut(r) {
            None => unreachable!(),
            Some(rr) => rr
          }
        }
        Some(rr) => rr
      }
    };
    rel_mut.test_neg_tup(rel_var, tup, &mut self.shm)
  }

  fn scan_pos(&mut self, rel_var: CVar, lbtup: &[SNum], ubtup: &[SNum]) -> EScanBox {
    let rel_mut = match self.rels.get_mut(&rel_var) {
      None => panic!("bug: TFrame::scan_pos: invalid: {:?}", rel_var),
      Some(r) => match Rc::get_mut(r) {
        None => {
          *r = r.clone_ref();
          match Rc::get_mut(r) {
            None => unreachable!(),
            Some(rr) => rr
          }
        }
        Some(rr) => rr
      }
    };
    rel_mut.scan_pos(rel_var, lbtup, ubtup, &mut self.shm)
  }

  fn scan_neg(&mut self, rel_var: CVar, lbtup: &[SNum], ubtup: &[SNum]) -> EScanBox {
    let rel_mut = match self.rels.get_mut(&rel_var) {
      None => panic!("bug: TFrame::scan_neg: invalid: {:?}", rel_var),
      Some(r) => match Rc::get_mut(r) {
        None => {
          *r = r.clone_ref();
          match Rc::get_mut(r) {
            None => unreachable!(),
            Some(rr) => rr
          }
        }
        Some(rr) => rr
      }
    };
    rel_mut.scan_neg(rel_var, lbtup, ubtup, &mut self.shm)
  }

  //fn swap_pos_tup(&mut self, rel_var: CVar, tup: &mut [SNum]) -> TScanResult {
  fn swap_pos_tup(&mut self, rec_var: CVar, rel_var: CVar, tup: &[SNum], newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>) -> TResult {
  //fn swap_pos_tup(&mut self, rec_var: CVar, rel_var: CVar, tup: &[SNum], newswap: &mut dyn ESwap, swaptup: &mut Vec<SNum>) -> TResult {
    let rel_mut = match self.rels.get_mut(&rel_var) {
      None => panic!("bug: TFrame::swap_pos_tup: invalid: {:?}", rel_var),
      Some(r) => match Rc::get_mut(r) {
        None => {
          *r = r.clone_ref();
          match Rc::get_mut(r) {
            None => unreachable!(),
            Some(rr) => rr
          }
        }
        Some(rr) => rr
      }
    };
    rel_mut.swap_pos_tup(rec_var, rel_var, tup, newswap, swaptup, &mut self.shm)
  }

  //fn swap_neg_tup(&mut self, rel_var: CVar, tup: &mut [SNum]) -> TScanResult {
  fn swap_neg_tup(&mut self, rec_var: CVar, rel_var: CVar, tup: &[SNum], newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>) -> TResult {
  //fn swap_neg_tup(&mut self, rec_var: CVar, rel_var: CVar, tup: &[SNum], newswap: &mut dyn ESwap, swaptup: &mut Vec<SNum>) -> TResult {
    let rel_mut = match self.rels.get_mut(&rel_var) {
      None => panic!("bug: TFrame::swap_neg_tup: invalid: {:?}", rel_var),
      Some(r) => match Rc::get_mut(r) {
        None => {
          *r = r.clone_ref();
          match Rc::get_mut(r) {
            None => unreachable!(),
            Some(rr) => rr
          }
        }
        Some(rr) => rr
      }
    };
    rel_mut.swap_neg_tup(rec_var, rel_var, tup, newswap, swaptup, &mut self.shm)
  }

  fn prop_eval_1(&mut self, tlb: TNum, ts: &mut Vec<TNum>, rel: &mut Vec<SNum>, pat: &mut Vec<SNum>, tup: &mut Vec<SNum>) -> Option<TStatus> {
    self._prop_eval_1(tlb, ts, rel, pat, tup)
  }

  //fn nul_eval_1(&mut self, /*ilimit: Option<u32>,*/ tlb: TNum, rec_var: CVar, /*rht: &mut Vec<u32>,*/ idx: &mut Vec<u32>, sub: &mut Vec<SNum>, rel: &mut Vec<SNum>, pat: &mut Vec<SNum>, tup: &mut Vec<SNum>, savepat: &mut Vec<SNum>, swapbuf: &mut Vec<SNum>, cap: &mut dyn ECapture) -> bool {
  fn nul_eval_1(&mut self, tlb: TNum, rec_var: CVar, nod: &mut Vec<Vec<usize>>, idx: &mut Vec<u32>, sub: &mut Vec<SNum>, off: &mut Vec<u32>, ary: &mut Vec<u32>, rel: &mut Vec<SNum>, pat: &mut Vec<SNum>, tup: &mut Vec<SNum>, savepat: &mut Vec<SNum>, swap: &mut dyn ESwap, cap: &mut dyn ECapture) {
    //self._nul_pivoteval_1(ilimit, tlb, rec_var, rht, idx, sub, rel, pat, tup, savepat, swapbuf)
    self._nul_eval_1_(tlb, rec_var, nod, idx, sub, off, ary, rel, pat, tup, savepat, swap, cap);
  }

  //fn def_eval_1(&mut self, tlb: TNum, rec_var: CVar, nod: &mut Vec<Vec<usize>>, idx: &mut Vec<u32>, sub: &mut Vec<SNum>, rel: &mut Vec<SNum>, pat: &mut Vec<SNum>, tup: &mut Vec<SNum>, savepat: &mut Vec<SNum>, savetup: &mut Vec<SNum>, swapbuf: &mut Vec<SNum>) {
  fn def_eval_1(&mut self, tlb: TNum, rec_var: CVar, nod: &mut Vec<Vec<usize>>, idx: &mut Vec<u32>, sub: &mut Vec<SNum>, off: &mut Vec<u32>, ary: &mut Vec<u32>, rel: &mut Vec<SNum>, pat: &mut Vec<SNum>, tup: &mut Vec<SNum>, savepat: &mut Vec<SNum>, /*savetup: &mut Vec<SNum>,*/ swap: &mut dyn ESwap, cap: &mut dyn ECapture) {
    //self._def_eval_1_(tlb, rec_var, nod, idx, sub, rel, pat, tup, savepat, savetup, swapbuf);
    self._def_eval_1_(tlb, rec_var, nod, idx, sub, off, ary, rel, pat, tup, savepat, /*savetup,*/ swap, cap);
  }

  fn swap(&mut self, swapbuf: &[SNum], newswap: &mut Vec<SNum>) {
    self._swap(swapbuf, newswap, false);
  }

  fn swapfix(&mut self, swapbuf: &mut Vec<SNum>, newswap: &mut Vec<SNum>) {
    self._swapfix(swapbuf, newswap);
  }

  fn swapfix_(&mut self, tlb: TNum, swapbuf: &mut Vec<SNum>, newswap: &mut Vec<SNum>, xlb: WPtr, cap: &mut dyn ECapture, cap_first: bool) {
    self._swapfix_(tlb, swapbuf, newswap, xlb, cap, cap_first);
  }

  fn patch_swap(&mut self, tlb: TNum, newswap: &mut dyn ESwap) {
    self._patch_swap(tlb, newswap);
  }

  fn fix_swap(&mut self, tlb: TNum, swapbuf: &mut dyn ESwap, newswap: &mut dyn ESwap, xlb: WPtr, cap: &mut dyn ECapture, cap_first: bool) {
    self._fix_swap(tlb, swapbuf, newswap, xlb, cap, cap_first);
  }
}

fn _stableperm(pat: &mut [SNum], perm: &mut [SNum]) -> (usize, bool) {
  // NB: loop bounds.
  for i in 0 .. perm.len() {
    perm[i] = i as SNum;
  }
  let mut b = 0;
  let mut d = 0;
  let mut s = false;
  for i in 0 .. pat.len() {
    let p = pat[i];
    if p <= 0 {
      d += 1;
    } else {
      if d > 0 {
        for o in (b .. b + d).rev() {
          pat.swap(o, o + 1);
          perm.swap(o, o + 1);
        }
        s = true;
      }
      b += 1;
    }
  }
  (b, s)
}

fn _qmatch(qrel: SNum, qtup: &[SNum], rel: &[SNum], off: &[u32], ary: &[u32], tup: &[SNum]) -> Option<usize> {
  for r in 0 .. rel.len() {
    if qrel != rel[r] {
      continue;
    }
    let o = off[r] as usize;
    let a = ary[r] as usize;
    if qtup != &tup[o .. o + a] {
      continue;
    }
    return Some(r);
  }
  None
}

fn _insort(ins_rel_off: usize, rel: &mut [SNum], off: &mut [u32], ary: &mut [u32], tup: &mut [SNum]) {
  if ins_rel_off == 0 {
    return;
  }
  for r in (0 .. ins_rel_off).rev() {
    let od = off[r] as usize;
    let os = off[r + 1] as usize;
    let ad = ary[r] as usize;
    let a_ = ary[r + 1] as usize;
    rel.swap(r, r + 1);
    // TODO
    for o in os .. os + a_ {
      for o_ in ((o - ad) .. o).rev() {
        tup.swap(o_, o_ + 1);
      }
    }
  }
}

fn _renom(rev_sub: &mut BTreeMap<SNum, SNum>, tup: &mut [SNum]) {
  let mut p = 0;
  for i in 0 .. tup.len() {
    let x = tup[i];
    match rev_sub.get(&x) {
      None => {
        p -= 1;
        rev_sub.insert(x, p);
        tup[i] = p;
      }
      Some(&q) => {
        tup[i] = q;
      }
    }
  }
}

fn _precommit(sub: &[SNum]) -> bool {
  for k in 0 .. sub.len() {
    if sub[k] <= 0 {
      return false;
    }
  }
  true
}

fn _clobber_tup(sub: &[SNum], pat: &[SNum], tup: &mut [SNum]) -> bool {
  for i in 0 .. pat.len() {
    let p = pat[i];
    if p <= 0 {
      let k = (-1 - p) as usize;
      let y = sub[k];
      if y <= 0 {
        return false;
      } else {
        tup[i] = y;
      }
    } else {
      tup[i] = p;
    }
  }
  true
}

fn _init_tup(sub: &[SNum], pat: &[SNum], tup: &mut [SNum]) -> bool {
  for i in 0 .. pat.len() {
    let p = pat[i];
    if p <= 0 {
      let k = (-1 - p) as usize;
      let y = sub[k];
      if y <= 0 {
        if tup[i] <= 0 {
          tup[i] = 0;
          for j in i + 1 .. pat.len() {
            tup[j] = CVar::ub().0;
          }
          return false;
        }
      } else {
        let x = tup[i];
        if y < x {
          for j in i .. pat.len() {
            tup[j] = CVar::ub().0;
          }
          return false;
        } else {
          tup[i] = y;
        }
      }
    } else {
      let x = tup[i];
      if p < x {
        for j in i .. pat.len() {
          tup[j] = CVar::ub().0;
        }
        return false;
      } else {
        tup[i] = p;
      }
    }
  }
  true
}

fn _sub_tup_1(sub: &mut [SNum], pat: &[SNum], tup: &[SNum]) -> bool {
  for i in 0 .. pat.len() {
    let p = pat[i];
    let x = tup[i];
    if p <= 0 {
      let k = (-1 - p) as usize;
      let y = &mut sub[k];
      if *y <= 0 {
        if x > 0 {
          *y = x;
        } else {
          return false;
        }
      } else if *y != x {
        return false;
      }
    } else {
      if p != x {
        return false;
      }
    }
  }
  true
}

fn _sub_tup(rel_idx: u32, idx: &mut [u32], sub: &mut [SNum], pat: &[SNum], tup: &[SNum]) -> (bool, Option<usize>) {
  let mut isub = None;
  for i in 0 .. pat.len() {
    let p = pat[i];
    let x = tup[i];
    if p <= 0 {
      let k = (-1 - p) as usize;
      let y = &mut sub[k];
      if *y <= 0 {
        if x > 0 {
          *y = x;
          idx[k] = rel_idx;
          isub = Some(i);
        } else {
          return (false, isub);
        }
      } else if *y != x {
        return (false, isub);
      }
    } else {
      if p != x {
        return (false, isub);
      }
    }
  }
  (true, isub)
}

fn _unsub(rel_idx: u32, idx: &mut [u32], sub: &mut [SNum], pat: &[SNum]) {
  for i in (0 .. pat.len()).rev() {
    let p = pat[i];
    if p <= 0 {
      let k = (-1 - p) as usize;
      let idx = &mut idx[k];
      if *idx == rel_idx {
        *idx = 0;
      }
      sub[k] = 0;
    }
  }
}

fn _unsub_(rel_idx: u32, idx: &mut [u32], sub: &mut [CVar], pat: &[CVar]) {
  for i in (0 .. pat.len()).rev() {
    let p = pat[i];
    if p <= CVar(0) {
      let k = (-1 - p.0) as usize;
      let idx = &mut idx[k];
      if *idx == rel_idx {
        *idx = 0;
      }
      sub[k] = CVar(0);
    }
  }
}

pub fn _gen_bounds(sub: &[SNum], pat: &[SNum], lbpat: &mut [SNum], ubpat: &mut [SNum]) {
  lbpat.copy_from_slice(pat);
  ubpat.copy_from_slice(pat);
  for i in 0 .. pat.len() {
    let p = pat[i];
    if 0 > p {
      let k = (-1 - p) as usize;
      let y = sub[k];
      if y > 0 {
        lbpat[i] = y;
        ubpat[i] = y;
      } else {
        for i2 in i .. pat.len() {
          lbpat[i2] = 0;
          ubpat[i2] = s_ub();
        }
        break;
      }
    }
  }
}

pub fn _mat_tup(p_max: SNum, p_end: SNum, sub: &mut [SNum], pat: &[SNum], tup: &[SNum]) -> bool {
  let mut ps = 0;
  for i in 0 .. pat.len() {
    let p = pat[i];
    let x = tup[i];
    if p <= 0 {
      let k = (-1 - p) as usize;
      let y = &mut sub[k];
      if p_max >= p && p >= p_end {
        if p == ps {
          if *y != x {
            return false;
          }
        } else if *y <= 0 {
          if x > 0 {
            *y = x;
            ps = p;
          } else {
            return false;
          }
          ps = p;
        } else if *y < x {
          *y = x;
          ps = p;
          for p2 in p_end .. p {
            let k2 = (-1 - p2) as usize;
            sub[k2] = s_ub();
          }
        } else if *y > x {
          return false;
        }
      } else if *y != x {
        return false;
      }
    } else {
      if p != x {
        return false;
      }
    }
  }
  true
}

pub fn _unmat(p_max: SNum, p_end: SNum, sub: &mut [SNum], pat: &[SNum]) {
  for i in (0 .. pat.len()).rev() {
    let p = pat[i];
    if p <= 0 {
      if p_max >= p && p >= p_end {
        let k = (-1 - p) as usize;
        /*let idx = &mut idx[k];
        if *idx == rel_idx {
          *idx = 0;
        }*/
        sub[k] = 0;
      }
    }
  }
}

thread_local! {
  static TL_FIX_EVAL_STATS: RefCell<FixEvalStats> = RefCell::new(FixEvalStats::default());
}

#[derive(Default)]
pub struct FixEvalStats {
  tlb:  TNum,
  buf:  Vec<(u32, SNum)>,
}

impl FixEvalStats {
  // TODO
  pub fn tl_reset(tlb: TNum) {
    TL_FIX_EVAL_STATS.with(|stats| {
      let mut stats = stats.borrow_mut();
      stats.tlb = tlb;
      stats.buf.clear();
    });
  }

  pub fn tl_dump(tlb: TNum, top_k: Option<usize>) -> Vec<(u32, SNum)> {
    TL_FIX_EVAL_STATS.with(|stats| {
      let mut stats = stats.borrow_mut();
      stats.buf.sort();
      match top_k.map(|top_k| min(top_k, stats.buf.len())) {
        Some(top_k) => {
          stats.buf[stats.buf.len() - top_k .. ].to_owned()
        }
        None => {
          stats.buf.clone()
        }
      }
    })
  }
}

impl TFrame {
  fn _swap_(&mut self, swapbuf: &[SNum], newswap: &mut Vec<SNum>, xlb: &WPtr, cap: &mut dyn ECapture, defer: bool) {
    if log_trace() {
      println!("TRACE: TFrame::_swap_: len={} defer?{:?}", swapbuf.len(), defer);
    }
    if swapbuf.is_empty() {
      if log_trace() {
        println!("TRACE: TFrame::_swap_:   done early");
      }
      return;
    }
    let mut swaptup = Vec::new();
    let mut swapoff = 0;
    while swapoff < swapbuf.len() {
      let rec_var = CVar(swapbuf[swapoff]);
      let raw_rel = swapbuf[swapoff + 1];
      let (neg, rel_var) = if raw_rel < 0 {
        (true, CVar(-raw_rel))
      } else if raw_rel > 0 {
        (false, CVar(raw_rel))
      } else {
        unreachable!();
      };
      let arity = self.rel_arity(rel_var);
      if defer && rel_var == self.shm.evar && !neg {
        let tup = &swapbuf[swapoff + 2 .. swapoff + 2 + arity];
        if log_trace_vvv() {
          println!("TRACE: TFrame::_swap_: rec={} rel={} arity={} neg={:?} defer",
              rec_var.0, rel_var.0, arity, neg);
        }
        assert_eq!(arity, 2);
        if tup[0] != tup[1] {
          cap._alloc(xlb, raw_rel, tup);
        }
        newswap.extend_from_slice(&swapbuf[swapoff .. swapoff + 2 + arity]);
        swapoff += 2 + arity;
        continue;
      }
      swapoff += 2;
      if log_trace_vvv() {
        let tup: &[SNum] = &swapbuf[swapoff .. swapoff + arity];
        println!("TRACE: TFrame::_swap_: rec={} rel={} arity={} neg={:?} tup={:?}",
            rec_var.0, rel_var.0, arity, neg, tup);
      }
      let rel_mut = match self.rels.get_mut(&rel_var) {
        None => unreachable!(),
        Some(r) => match Rc::get_mut(r) {
          None => {
            *r = r.clone_ref();
            match Rc::get_mut(r) {
              None => unreachable!(),
              Some(rr) => rr
            }
          }
          Some(rr) => rr
        }
      };
      swaptup.clear();
      match if neg {
        rel_mut.swap_neg_tup(rec_var, rel_var, &swapbuf[swapoff .. swapoff + arity], newswap, &mut swaptup, &mut self.shm)
      } else {
        rel_mut.swap_pos_tup(rec_var, rel_var, &swapbuf[swapoff .. swapoff + arity], newswap, &mut swaptup, &mut self.shm)
      } {
        None => {}
        Some(_) => {
          if !(rel_var == self.shm.evar && !neg) {
            cap._alloc(xlb, raw_rel, &swapbuf[swapoff .. swapoff + arity]);
          }
        }
      }
      swapoff += arity;
    }
    assert_eq!(swapoff, swapbuf.len());
    if log_trace() {
      println!("TRACE: TFrame::_swap_:   done newlen={}", newswap.len());
    }
  }

  fn _swap(&mut self, swapbuf: &[SNum], newswap: &mut Vec<SNum>, /*cap: &mut SkaCapture,*/ defer: bool) {
    if log_trace() {
      println!("TRACE: TFrame::_swap: len={} defer?{:?}", swapbuf.len(), defer);
    }
    if swapbuf.is_empty() {
      if log_trace() {
        println!("TRACE: TFrame::_swap:   done early");
      }
      return;
    }
    let mut swaptup = Vec::new();
    let mut swapoff = 0;
    //let mut iter_ct = 0;
    while swapoff < swapbuf.len() {
      /*iter_ct += 1;
      if iter_ct == 100 {
        println!("TRACE: TFrame::_swap: loop 100x");
      }*/
      let rec_var = CVar(swapbuf[swapoff]);
      let raw_rel = swapbuf[swapoff + 1];
      let (neg, rel_var) = if raw_rel > 0 {
        (false, CVar(raw_rel))
      } else if raw_rel < 0 {
        (true, CVar(-raw_rel))
      } else {
        unreachable!();
      };
      let arity = self.rel_arity(rel_var);
      if defer && rel_var == self.shm.evar && !neg {
        if log_trace_vvv() {
          println!("TRACE: TFrame::_swap: rec={} rel={} arity={} neg={:?} defer",
              rec_var.0, rel_var.0, arity, neg);
        }
        // FIXME: capture.
        let tup = &swapbuf[swapoff + 2 .. swapoff + 2 + arity];
        if tup[0] != tup[1] {
          //cap._\capture(raw_rel, tup);
        }
        newswap.extend_from_slice(&swapbuf[swapoff .. swapoff + 2 + arity]);
        swapoff += 2 + arity;
        continue;
      }
      swapoff += 2;
      if log_trace_vvv() {
        let tup: &[SNum] = &swapbuf[swapoff .. swapoff + arity];
        println!("TRACE: TFrame::_swap: rec={} rel={} arity={} neg={:?} tup={:?}",
            rec_var.0, rel_var.0, arity, neg, tup);
      }
      let rel_mut = match self.rels.get_mut(&rel_var) {
        None => unreachable!(),
        Some(r) => match Rc::get_mut(r) {
          None => {
            *r = r.clone_ref();
            match Rc::get_mut(r) {
              None => unreachable!(),
              Some(rr) => rr
            }
          }
          Some(rr) => rr
        }
      };
      swaptup.clear();
      if neg {
        rel_mut.swap_neg_tup(rec_var, rel_var, &swapbuf[swapoff .. swapoff + arity], newswap, &mut swaptup, &mut self.shm);
      } else {
        rel_mut.swap_pos_tup(rec_var, rel_var, &swapbuf[swapoff .. swapoff + arity], newswap, &mut swaptup, &mut self.shm);
      }
      /*let mut o = 0;
      while o < swaptup.len() {
        // FIXME: deferred.
        if raw_rel != self.shm.evar.0 {
          self.inc._join_tup(raw_rel, &swaptup[o .. o + arity]);
        }
        o += arity;
      }*/
      swapoff += arity;
    }
    assert_eq!(swapoff, swapbuf.len());
    if log_trace() {
      println!("TRACE: TFrame::_swap:   done newlen={}", newswap.len());
    }
  }

  fn _patch_swap(&mut self, tlb: TNum, newswap: &mut dyn ESwap) {
    if log_trace() {
      //println!("TRACE: TFrame::_patchswap: newlen={}", newswap.len());
      println!("TRACE: TFrame::_patch_swap");
    }
    for (rel_var, _) in self.rels.clone_iter() {
      let rel_mut = match self.rels.get_mut(&rel_var) {
        None => unreachable!(),
        Some(r) => match Rc::get_mut(r) {
          None => {
            *r = r.clone_ref();
            match Rc::get_mut(r) {
              None => unreachable!(),
              Some(rr) => rr
            }
          }
          Some(rr) => rr
        }
      };
      rel_mut.patch_swap(tlb, rel_var, newswap, &mut self.shm);
    }
    if log_trace() {
      //println!("TRACE: TFrame::_patchswap:   done newlen={}", newswap.len());
      println!("TRACE: TFrame::_patch_swap:   done");
    }
  }

  fn _patchswap(&mut self, newswap: &mut Vec<SNum>) {
    if log_trace() {
      println!("TRACE: TFrame::_patchswap: newlen={}", newswap.len());
    }
    for (rel_var, _) in self.rels.clone_iter() {
      let rel_mut = match self.rels.get_mut(&rel_var) {
        None => unreachable!(),
        Some(r) => match Rc::get_mut(r) {
          None => {
            *r = r.clone_ref();
            match Rc::get_mut(r) {
              None => unreachable!(),
              Some(rr) => rr
            }
          }
          Some(rr) => rr
        }
      };
      rel_mut.patchswap(rel_var, newswap, &mut self.shm);
    }
    if log_trace() {
      println!("TRACE: TFrame::_patchswap:   done newlen={}", newswap.len());
    }
  }

  fn _patch_inc(&mut self) {
  }

  fn _fix_swap(&mut self, tlb: TNum, swap: &mut dyn ESwap, newswap: &mut dyn ESwap, mut xlb: WPtr, cap: &mut dyn ECapture, cap_first: bool) {
    if log_trace() {
      println!("TRACE: TFrame::_fix_swap: tlb={} cap first?{:?}", tlb, cap_first);
    }
    // TODO
    let mut first = true;
    let mut new = false;
    newswap.reset_swapbuf();
    //let mut checkpt = self.snapshot();
    //tlb = checkpt.next_glb();
    loop {
      let fix = match new {
        false => {
          if first && !cap_first {
            swap.swap_nocap(tlb, self, newswap, true);
          } else {
            swap.swap(tlb, self, newswap, &xlb, cap, first);
          }
          swap.reset_swapbuf();
          newswap._copy_from(swap);
          self._patch_swap(tlb, newswap);
          first = false;
          newswap.fix_swapbuf()
        }
        true  => {
          newswap.swap(tlb, self, swap, &xlb, cap, false);
          newswap.reset_swapbuf();
          swap._copy_from(newswap);
          self._patch_swap(tlb, swap);
          swap.fix_swapbuf()
        }
      };
      if fix {
        break;
      }
      //checkpt = self.snapshot();
      //tlb = checkpt.next_glb();
      xlb = cap._ubptr();
      new = !new;
    }
    if log_trace() {
      println!("TRACE: TFrame::_fix_swap:   done");
    }
  }

  fn _swapfix_(&mut self, tlb: TNum, swap: &mut Vec<SNum>, newswap: &mut Vec<SNum>, mut xlb: WPtr, cap: &mut dyn ECapture, cap_first: bool) {
    if log_trace() {
      println!("TRACE: TFrame::_swapfix_: len={} newlen={}", swap.len(), newswap.len());
    }
    // TODO
    let mut first = true;
    let mut new = false;
    loop {
      let brk = match new {
        false => {
          if first && !cap_first {
            self._swap(swap, newswap, true);
          } else {
            self._swap_(swap, newswap, &xlb, cap, first);
          }
          swap.clear();
          self._patchswap(newswap);
          first = false;
          newswap.is_empty()
        }
        true  => {
          self._swap_(newswap, swap, &xlb, cap, false);
          newswap.clear();
          self._patchswap(swap);
          swap.is_empty()
        }
      };
      if brk {
        break;
      }
      xlb = cap._ubptr();
      new = !new;
    }
    /*self._patch_inc();*/
    if log_trace() {
      println!("TRACE: TFrame::_swapfix_:   done");
    }
  }

  fn _swapfix(&mut self, swap: &mut Vec<SNum>, newswap: &mut Vec<SNum>) {
    if log_trace() {
      println!("TRACE: TFrame::_swapfix: len={} newlen={}", swap.len(), newswap.len());
    }
    // TODO
    let mut first = true;
    let mut new = false;
    loop {
      let brk = match new {
        false => {
          self._swap(swap, newswap, first);
          swap.clear();
          self._patchswap(newswap);
          first = false;
          newswap.is_empty()
        }
        true  => {
          self._swap(newswap, swap, false);
          newswap.clear();
          self._patchswap(swap);
          swap.is_empty()
        }
      };
      if brk {
        break;
      }
      new = !new;
    }
    self._patch_inc();
    if log_trace() {
      println!("TRACE: TFrame::_swapfix:   done");
    }
  }

  fn _prop_join_1(&mut self, rel_off: usize, arg_off: usize, /*idx: &mut Vec<u32>, pat: &mut Vec<SNum>,*/ ts: &mut [TNum], rel: &[SNum], pat: &[SNum], tup: &mut [SNum]) -> Option<TStatus> {
    //let rel_idx = (rel_off + 1) as u32;
    let rel_num = rel[rel_off];
    let (neg, rel_var) = if rel_num < 0 {
      (true, CVar(-rel_num))
    } else if rel_num > 0 {
      (false, CVar(rel_num))
    } else {
      unreachable!();
    };
    let arity = self.rel_arity(rel_var);
    let last = rel_off + 1 >= rel.len();
    for i in arg_off .. arg_off + arity {
      tup[i] = 0;
    }
    let rel_mut = match self.rels.get_mut(&rel_var) {
      None => panic!("bug: TFrame::_prop_join_1"),
      Some(r) => match Rc::get_mut(r) {
        None => {
          *r = r.clone_ref();
          match Rc::get_mut(r) {
            None => unreachable!(),
            Some(rr) => rr
          }
        }
        Some(rr) => rr
      }
    };
    if !_clobber_tup(&[], &pat[arg_off .. arg_off + arity], &mut tup[arg_off .. arg_off + arity]) {
      return None;
    }
    if log_trace_vvv() {
      println!("TRACE: TFrame::_prop_join_1: r={} rel={} tup={:?} last?{:?}", rel_off, rel_var.0, &tup[arg_off .. arg_off + arity], last);
    }
    let r_pos = rel_mut.test_pos_tup(rel_var, &tup[arg_off .. arg_off + arity], &mut self.shm);
    let r_neg = rel_mut.test_neg_tup(rel_var, &tup[arg_off .. arg_off + arity], &mut self.shm);
    match (neg, r_pos, r_neg) {
      (false, Some(t), None) => {
        ts[rel_off] = t;
        if last {
          if log_trace_vvv() {
            println!("TRACE: TFrame::_prop_join_1: sat");
          }
          return Some(TStatus::Sat);
        }
        self._prop_join_1(rel_off + 1, arg_off + arity, ts, rel, pat, tup)
      }
      (true, None, Some(t)) => {
        ts[rel_off] = t;
        if last {
          if log_trace_vvv() {
            println!("TRACE: TFrame::_prop_join_1: sat");
          }
          return Some(TStatus::Sat);
        }
        self._prop_join_1(rel_off + 1, arg_off + arity, ts, rel, pat, tup)
      }
      (_, Some(pt), Some(nt)) => {
        ts[rel_off] = max(pt, nt);
        if log_trace_vvv() {
          println!("TRACE: TFrame::_prop_join_1: par");
        }
        return Some(TStatus::Par);
      }
      _ => {
        return Some(TStatus::Unsat);
      }
    }
  }

  fn _prop_eval_1(&mut self, _tlb: TNum, /*idx: &mut Vec<u32>, pat: &mut Vec<SNum>,*/ ts: &mut Vec<TNum>, rel: &mut Vec<SNum>, pat: &mut Vec<SNum>, tup: &mut Vec<SNum>) -> Option<TStatus> {
    match self.prop.as_ref() {
      None => {
        if log_debug() {
          println!("DEBUG: TFrame::_prop_eval_1: no prop");
        }
        return None;
      }
      Some(prop) => {
        if log_trace_vvv() {
          println!("TRACE: TFrame::_prop_eval_1: init bufs");
        }
        prop.init_bufs(self, rel, pat);
      }
    }
    tup.clear();
    tup.resize(pat.len(), 0);
    ts.clear();
    ts.resize(rel.len(), 0);
    if rel.is_empty() {
      panic!("bug: TFrame::_prop_eval_1: nothing to eval");
    }
    self._prop_join_1(0, 0, ts, rel, pat, tup)
  }

  fn _fix_commit_1(&self, tlb: TNum, rec_var: CVar, def_off: usize, rel_off: usize, arg_off: usize, sub: &mut [SNum], srnk: &[SNum], off: &[u32], ary: &[u32], rel: &[SNum], pat: &[SNum], tup: &mut [SNum], swap: &mut dyn ESwap, cap: &mut dyn ECapture, shmcopy: &STFrame) {
    let mut chk = shmcopy._atlas();
    let mut r = rel_off;
    let mut t = arg_off;
    for i in def_off .. sub.len() {
      sub[i] = shmcopy._provision(&mut chk);
    }
    while r < rel.len() {
      let rel_var = if rel[r] < 0 {
        CVar(-rel[r])
      } else if rel[r] > 0 {
        CVar(rel[r])
      } else {
        unreachable!();
      };
      assert_eq!(t, off[r] as usize);
      let arity = ary[r] as usize;
      if !_clobber_tup(sub, &pat[t .. t + arity], &mut tup[t .. t + arity]) {
        panic!("bug: TFrame::_fix_commit_1: clobber");
      }
      r += 1;
      t += arity;
    }
    assert_eq!(r, rel.len());
    assert_eq!(t, off[rel.len()] as usize);
    assert_eq!(t, tup.len());
    let vvv = log_trace_vvv();
    if vvv {
      /*println!("TRACE: TFrame::_fix_commit_1: rec={} r={} rel={:?} pat={:?} tup={:?} sub={:?}",
          rec_var.0, rel_off,
          &rel[rel_off .. ],
          &pat[arg_off .. ],
          &tup[arg_off .. ],
          sub,
      );*/
      println!("TRACE: TFrame::_fix_commit_1: rec={} r={} sub={:?} srnk={:?} rel={:?} pat={:?} tup={:?}",
          rec_var.0, rel_off,
          sub,
          srnk,
          &rel[rel_off .. ],
          &pat[arg_off .. ],
          &tup[arg_off .. ],
      );
    }
    let mut r = rel_off;
    let mut t = arg_off;
    while r < rel.len() {
      let rel_var = if rel[r] < 0 {
        CVar(-rel[r])
      } else if rel[r] > 0 {
        CVar(rel[r])
      } else {
        unreachable!();
      };
      assert_eq!(t, off[r] as usize);
      let arity = ary[r] as usize;
      assert_eq!(arity, self.rel_arity(rel_var));
      swap.stage_tup(tlb, SwapEvent::Eva(rec_var, sub, srnk, /*off, ary, rel, tup*/), rel[r], &tup[t .. t + arity]);
      if vvv {
        if rel[r] < 0 {
          println!("TRACE: TFrame::_fix_commit_1:   - {} {:?}", -rel[r], &tup[t .. t + arity]);
        } else {
          println!("TRACE: TFrame::_fix_commit_1:   + {} {:?}", rel[r], &tup[t .. t + arity]);
        }
      }
      r += 1;
      t += arity;
    }
    assert_eq!(r, rel.len());
    assert_eq!(t, off[rel.len()] as usize);
    assert_eq!(t, tup.len());
    /*cap._fresh(rec_var, &rel[rel_off .. ], &off[rel_off .. ], &ary[rel_off .. ], &tup[arg_off .. ]);*/
    cap._fresh(rec_var, &rel[rel_off .. ], &off[rel_off .. ], &ary[rel_off .. ], tup);
    for i in def_off .. sub.len() {
      sub[i] = 0;
    }
  }

  fn _fix_prejoin_pos_1_perm(&mut self, icount: &mut u32, tlb: TNum, rec_var: CVar, def_off: usize, rel_off: usize, p_max: SNum, sub: &[SNum], off: &[u32], ary: &[u32], rel: &[SNum], pat: &[SNum], tup: &mut [SNum], lbpat: &mut [SNum], ubpat: &mut [SNum], perm: &[SNum], swap: &mut dyn ESwap, cap: &mut dyn ECapture) -> Option<bool> {
    let arg_off = off[rel_off] as usize;
    let rel_var = CVar(rel[rel_off]);
    let arity = ary[rel_off] as usize;
    assert_eq!(arity, self.rel_arity(rel_var));
    let (larity, _) = self.rel_arity2(rel_var);
    for i in arg_off .. arg_off + arity {
      tup[i] = 0;
    }
    let mut shift = false;
    for i in arg_off .. arg_off + arity - 1 {
      if perm[i] > perm[i + 1] {
        shift = true;
        break;
      }
    }
    _gen_bounds(
        sub,
        &pat[arg_off .. arg_off + arity],
        &mut lbpat[arg_off .. arg_off + arity],
        &mut ubpat[arg_off .. arg_off + arity],
    );
    let rel_mut = match self.rels.get_mut(&rel_var) {
      None => panic!("bug: TFrame::_fix_prejoin_pos_1_perm"),
      Some(r) => match Rc::get_mut(r) {
        None => {
          *r = r.clone_ref();
          match Rc::get_mut(r) {
            None => unreachable!(),
            Some(rr) => rr
          }
        }
        Some(rr) => rr
      }
    };
    let mut scan = if shift {
      rel_mut.permscan_pos(rel_var, &perm[arg_off .. arg_off + larity], &lbpat[arg_off .. arg_off + arity], &ubpat[arg_off .. arg_off + arity], &mut self.shm)
    } else {
      rel_mut.scan_pos(rel_var, &lbpat[arg_off .. arg_off + arity], &ubpat[arg_off .. arg_off + arity], &mut self.shm)
    };
    drop(rel_mut);
    *icount += 1;
    match scan.next_tup(&mut tup[arg_off .. arg_off + arity]) {
      End => {
        Some(false)
      }
      Hit(_) => {
        None
      }
      _ => unreachable!()
    }
  }

  fn _fix_prejoin_neg_1_perm(&mut self, icount: &mut u32, tlb: TNum, rec_var: CVar, def_off: usize, rel_off: usize, p_max: SNum, sub: &[SNum], off: &[u32], ary: &[u32], rel: &[SNum], pat: &[SNum], tup: &mut [SNum], lbpat: &mut [SNum], ubpat: &mut [SNum], perm: &[SNum], swap: &mut dyn ESwap, cap: &mut dyn ECapture) -> Option<bool> {
    let arg_off = off[rel_off] as usize;
    let rel_var = CVar(-rel[rel_off]);
    let arity = ary[rel_off] as usize;
    assert_eq!(arity, self.rel_arity(rel_var));
    let (larity, _) = self.rel_arity2(rel_var);
    for i in arg_off .. arg_off + arity {
      tup[i] = 0;
    }
    let mut shift = false;
    for i in arg_off .. arg_off + arity - 1 {
      if perm[i] > perm[i + 1] {
        shift = true;
        break;
      }
    }
    _gen_bounds(
        sub,
        &pat[arg_off .. arg_off + arity],
        &mut lbpat[arg_off .. arg_off + arity],
        &mut ubpat[arg_off .. arg_off + arity],
    );
    let rel_mut = match self.rels.get_mut(&rel_var) {
      None => panic!("bug: TFrame::_fix_prejoin_neg_1_perm"),
      Some(r) => match Rc::get_mut(r) {
        None => {
          *r = r.clone_ref();
          match Rc::get_mut(r) {
            None => unreachable!(),
            Some(rr) => rr
          }
        }
        Some(rr) => rr
      }
    };
    let mut scan = if shift {
      rel_mut.permscan_neg(rel_var, &perm[arg_off .. arg_off + larity], &lbpat[arg_off .. arg_off + arity], &ubpat[arg_off .. arg_off + arity], &mut self.shm)
    } else {
      rel_mut.scan_neg(rel_var, &lbpat[arg_off .. arg_off + arity], &ubpat[arg_off .. arg_off + arity], &mut self.shm)
    };
    drop(rel_mut);
    *icount += 1;
    match scan.next_tup(&mut tup[arg_off .. arg_off + arity]) {
      End => {
        Some(false)
      }
      Hit(_) => {
        None
      }
      _ => unreachable!()
    }
  }

  fn _fix_prejoin_1_perm(&mut self, icount: &mut u32, tlb: TNum, rec_var: CVar, def_off: usize, rel_off: usize, p_max: SNum, sub: &[SNum], off: &[u32], ary: &[u32], rel: &[SNum], pat: &[SNum], tup: &mut [SNum], lbpat: &mut [SNum], ubpat: &mut [SNum], perm: &[SNum], swap: &mut dyn ESwap, cap: &mut dyn ECapture) -> Option<bool> {
    if rel[rel_off] > 0 {
      self._fix_prejoin_pos_1_perm(icount, tlb, rec_var, def_off, rel_off, p_max, sub, off, ary, rel, pat, tup, lbpat, ubpat, perm, swap, cap)
    } else if rel[rel_off] < 0 {
      self._fix_prejoin_neg_1_perm(icount, tlb, rec_var, def_off, rel_off, p_max, sub, off, ary, rel, pat, tup, lbpat, ubpat, perm, swap, cap)
    } else {
      panic!("bug: TFrame::_fix_prejoin_1_perm");
    }
  }

  fn _fix_join_pos_1_perm(&mut self, icount: &mut u32, tlb: TNum, vlb: bool, rec_var: CVar, def_off: usize, rel_off: usize, v_off: usize, anterel: usize, antearg: usize, rbuf: &[u32], vbuf: &[u32], pbuf: &[Vec<u32>], sub: &mut [SNum], srnk: &[SNum], pmax: &[SNum], off: &[u32], ary: &[u32], rel: &[SNum], pat: &[SNum], tup: &mut [SNum], lbpat: &mut [SNum], ubpat: &mut [SNum], perm: &[SNum], swap: &mut dyn ESwap, cap: &mut dyn ECapture) {
    let save_rel_off = rel_off;
    let rel_off = rbuf[rel_off] as usize;
    let arg_off = off[rel_off] as usize;
    let pivot = if v_off < vbuf.len() { rel_off == vbuf[v_off] as usize } else { false };
    let next_v_off = if pivot { v_off + 1 } else { v_off };
    let last_pivot = pivot && v_off == vbuf.len() - 1;
    let itlb = if !vlb && last_pivot { tlb } else { 0 };
    let rel_var = CVar(rel[rel_off]);
    let arity = ary[rel_off] as usize;
    assert_eq!(arity, self.rel_arity(rel_var));
    let (larity, _) = self.rel_arity2(rel_var);
    for i in arg_off .. arg_off + arity {
      tup[i] = 0;
    }
    let p_max = pmax[rel_off];
    let p_end = pat[arg_off + arity - 1];
    let mut shift = false;
    for i in arg_off .. arg_off + arity - 1 {
      if perm[i] > perm[i + 1] {
        shift = true;
        break;
      }
    }
    _gen_bounds(
        sub,
        &pat[arg_off .. arg_off + arity],
        &mut lbpat[arg_off .. arg_off + arity],
        &mut ubpat[arg_off .. arg_off + arity],
    );
    let rel_mut = match self.rels.get_mut(&rel_var) {
      None => panic!("bug: TFrame::_fix_join_pos_1_perm"),
      Some(r) => match Rc::get_mut(r) {
        None => {
          *r = r.clone_ref();
          match Rc::get_mut(r) {
            None => unreachable!(),
            Some(rr) => rr
          }
        }
        Some(rr) => rr
      }
    };
    let mut scan = if shift {
      rel_mut.permscan_pos(rel_var, &perm[arg_off .. arg_off + larity], &lbpat[arg_off .. arg_off + arity], &ubpat[arg_off .. arg_off + arity], &mut self.shm)
    } else {
      rel_mut.scan_pos(rel_var, &lbpat[arg_off .. arg_off + arity], &ubpat[arg_off .. arg_off + arity], &mut self.shm)
    };
    drop(rel_mut);
    let mut t = 0;
    *icount += 1;
    match scan.next_tup(&mut tup[arg_off .. arg_off + arity]) {
      End => return,
      Hit(t_) => t = t_,
      _ => unreachable!()
    }
    loop {
      if t >= itlb {
        let mat = _mat_tup(p_max, p_end, sub, &pat[arg_off .. arg_off + arity], &tup[arg_off .. arg_off + arity]);
        if mat {
          let save_vlb = vlb;
          let vlb = vlb || t >= tlb;
          if save_rel_off + 1 >= anterel {
            if _precommit(&sub[ .. def_off]) {
              self._fix_commit_1(tlb, rec_var, def_off, anterel, antearg, sub, srnk, off, ary, rel, pat, tup, swap, cap, &self.shm);
            } else {
              panic!("bug: TFrame::_fix_join_pos_1_perm: precommit failure");
            }
          } else {
            let mut reject = false;
            for g in 0 .. pbuf[rel_off].len() {
              let next_rel_off = pbuf[rel_off][g] as usize;
              let result = self._fix_prejoin_1_perm(icount, tlb, rec_var, def_off, next_rel_off, p_max, sub, off, ary, rel, pat, tup, lbpat, ubpat, perm, swap, cap);
              match result {
                None => {}
                Some(_jump) => {
                  reject = true;
                  break;
                }
              }
            }
            if !reject {
              self._fix_join_1_perm(icount, tlb, vlb, rec_var, def_off, save_rel_off + 1, next_v_off, anterel, antearg, rbuf, vbuf, pbuf, sub, srnk, pmax, off, ary, rel, pat, tup, lbpat, ubpat, perm, swap, cap);
            }
          }
        } else {
          panic!("bug: TFrame::_fix_join_pos_1_perm: maybe unreachable case");
        }
        _unmat(p_max, p_end, sub, &pat[arg_off .. arg_off + arity]);
      }
      *icount += 1;
      match scan.next_tup(&mut tup[arg_off .. arg_off + arity]) {
        End => break,
        Hit(t_) => t = t_,
        _ => unreachable!()
      }
    }
  }

  fn _fix_join_neg_1_perm(&mut self, icount: &mut u32, tlb: TNum, vlb: bool, rec_var: CVar, def_off: usize, rel_off: usize, v_off: usize, anterel: usize, antearg: usize, rbuf: &[u32], vbuf: &[u32], pbuf: &[Vec<u32>], sub: &mut [SNum], srnk: &[SNum], pmax: &[SNum], off: &[u32], ary: &[u32], rel: &[SNum], pat: &[SNum], tup: &mut [SNum], lbpat: &mut [SNum], ubpat: &mut [SNum], perm: &[SNum], swap: &mut dyn ESwap, cap: &mut dyn ECapture) {
    let save_rel_off = rel_off;
    let rel_off = rbuf[rel_off] as usize;
    let arg_off = off[rel_off] as usize;
    let pivot = if v_off < vbuf.len() { rel_off == vbuf[v_off] as usize } else { false };
    let next_v_off = if pivot { v_off + 1 } else { v_off };
    let last_pivot = pivot && v_off == vbuf.len() - 1;
    let itlb = if !vlb && last_pivot { tlb } else { 0 };
    let rel_var = CVar(-rel[rel_off]);
    let arity = ary[rel_off] as usize;
    assert_eq!(arity, self.rel_arity(rel_var));
    let (larity, _) = self.rel_arity2(rel_var);
    for i in arg_off .. arg_off + arity {
      tup[i] = 0;
    }
    let p_max = pmax[rel_off];
    let p_end = pat[arg_off + arity - 1];
    let mut shift = false;
    for i in arg_off .. arg_off + arity - 1 {
      if perm[i] > perm[i + 1] {
        shift = true;
        break;
      }
    }
    _gen_bounds(
        sub,
        &pat[arg_off .. arg_off + arity],
        &mut lbpat[arg_off .. arg_off + arity],
        &mut ubpat[arg_off .. arg_off + arity],
    );
    let rel_mut = match self.rels.get_mut(&rel_var) {
      None => panic!("bug: TFrame::_fix_join_neg_1_perm"),
      Some(r) => match Rc::get_mut(r) {
        None => {
          *r = r.clone_ref();
          match Rc::get_mut(r) {
            None => unreachable!(),
            Some(rr) => rr
          }
        }
        Some(rr) => rr
      }
    };
    let mut scan = if shift {
      rel_mut.permscan_neg(rel_var, &perm[arg_off .. arg_off + larity], &lbpat[arg_off .. arg_off + arity], &ubpat[arg_off .. arg_off + arity], &mut self.shm)
    } else {
      rel_mut.scan_neg(rel_var, &lbpat[arg_off .. arg_off + arity], &ubpat[arg_off .. arg_off + arity], &mut self.shm)
    };
    drop(rel_mut);
    let mut t = 0;
    *icount += 1;
    match scan.next_tup(&mut tup[arg_off .. arg_off + arity]) {
      End => return,
      Hit(t_) => t = t_,
      _ => unreachable!()
    }
    loop {
      if t >= itlb {
        let mat = _mat_tup(p_max, p_end, sub, &pat[arg_off .. arg_off + arity], &tup[arg_off .. arg_off + arity]);
        if mat {
          let save_vlb = vlb;
          let vlb = vlb || t >= tlb;
          if save_rel_off + 1 >= anterel {
            if _precommit(&sub[ .. def_off]) {
              self._fix_commit_1(tlb, rec_var, def_off, anterel, antearg, sub, srnk, off, ary, rel, pat, tup, swap, cap, &self.shm);
            } else {
              panic!("bug: TFrame::_fix_join_neg_1_perm: precommit failure");
            }
          } else {
            let mut reject = false;
            for g in 0 .. pbuf[rel_off].len() {
              let next_rel_off = pbuf[rel_off][g] as usize;
              let result = self._fix_prejoin_1_perm(icount, tlb, rec_var, def_off, next_rel_off, p_max, sub, off, ary, rel, pat, tup, lbpat, ubpat, perm, swap, cap);
              match result {
                None => {}
                Some(_jump) => {
                  reject = true;
                  break;
                }
              }
            }
            if !reject {
              self._fix_join_1_perm(icount, tlb, vlb, rec_var, def_off, save_rel_off + 1, next_v_off, anterel, antearg, rbuf, vbuf, pbuf, sub, srnk, pmax, off, ary, rel, pat, tup, lbpat, ubpat, perm, swap, cap);
            }
          }
        } else {
          panic!("bug: TFrame::_fix_join_neg_1_perm: maybe unreachable case");
        }
        _unmat(p_max, p_end, sub, &pat[arg_off .. arg_off + arity]);
      }
      *icount += 1;
      match scan.next_tup(&mut tup[arg_off .. arg_off + arity]) {
        End => break,
        Hit(t_) => t = t_,
        _ => unreachable!()
      }
    }
  }

  fn _fix_join_1_perm(&mut self, icount: &mut u32, tlb: TNum, vlb: bool, rec_var: CVar, def_off: usize, rel_off: usize, v_off: usize, anterel: usize, antearg: usize, rbuf: &[u32], vbuf: &[u32], pbuf: &[Vec<u32>], sub: &mut [SNum], srnk: &[SNum], pmax: &[SNum], off: &[u32], ary: &[u32], rel: &[SNum], pat: &[SNum], tup: &mut [SNum], lbpat: &mut [SNum], ubpat: &mut [SNum], perm: &[SNum], swap: &mut dyn ESwap, cap: &mut dyn ECapture) {
    let save_rel_off = rel_off;
    let rel_off = rbuf[rel_off] as usize;
    if rel[rel_off] > 0 {
      self._fix_join_pos_1_perm(icount, tlb, vlb, rec_var, def_off, save_rel_off, 0, anterel, antearg, rbuf, vbuf, pbuf, sub, srnk, pmax, off, ary, rel, pat, tup, lbpat, ubpat, perm, swap, cap)
    } else if rel[rel_off] < 0 {
      self._fix_join_neg_1_perm(icount, tlb, vlb, rec_var, def_off, save_rel_off, 0, anterel, antearg, rbuf, vbuf, pbuf, sub, srnk, pmax, off, ary, rel, pat, tup, lbpat, ubpat, perm, swap, cap)
    } else {
      panic!("bug: TFrame::_fix_join_1_perm");
    }
  }

  fn _fix_eval_1(&mut self, tlb: TNum, rec_var: CVar, def_off: usize, anterel: usize, antearg: usize, useset: &BTreeMap<SNum, BTreeSet<u32>>, defset: &BTreeMap<SNum, u32>, nod: &mut Vec<Vec<usize>>, _idx: &mut Vec<u32>, sub: &mut Vec<SNum>, off: &mut Vec<u32>, ary: &mut Vec<u32>, rel: &mut Vec<SNum>, pat: &mut Vec<SNum>, tup: &mut Vec<SNum>, savepat: &mut Vec<SNum>, swap: &mut dyn ESwap, cap: &mut dyn ECapture) {
    TL_FIX_EVAL_STATS.with(|stats| {
      let mut stats = stats.borrow_mut();
      if stats.tlb != tlb {
        stats.tlb = tlb;
        stats.buf.clear();
      }
    });
    tup.clear();
    tup.resize(pat.len(), 0);
    savepat.clear();
    savepat.resize(pat.len(), 0);
    let mut ubpat = Vec::with_capacity(pat.len());
    ubpat.resize(pat.len(), 0);
    let mut perm = Vec::with_capacity(antearg);
    perm.resize(antearg, 0);
    if rel.is_empty() {
      panic!("bug: TFrame::_fix_eval_1_: nothing to eval");
    }
    if log_trace_v() {
      flush_log();
      println!("TRACE: TFrame::_fix_eval_1_: tlb={} rec={} rel={:?}", tlb, rec_var.0, rel);
      flush_log();
    }
    if anterel == 0 {
      if _precommit(&sub[ .. def_off]) {
        self._fix_commit_1(tlb, rec_var, def_off, 0, 0, sub, &[], off, ary, rel, pat, tup, swap, cap, &self.shm);
        TL_FIX_EVAL_STATS.with(|stats| {
          let mut stats = stats.borrow_mut();
          stats.buf.push((0, rec_var.0));
        });
      } else {
        panic!("bug: TFrame::_fix_eval_1_: precommit failure");
      }
      return;
    }
    let mut buf = Vec::with_capacity(anterel);
    let mut rbuf = Vec::with_capacity(anterel);
    let mut rrnk = Vec::with_capacity(anterel);
    rrnk.resize(anterel, 0);
    for nod in nod.iter() {
      if log_trace_v() {
        println!("TRACE: TFrame::_fix_eval_1_:   nod: {:?}", nod);
      }
      rbuf.clear();
      for &rel_off in nod.iter() {
        if rel_off >= anterel {
          continue;
        }
        let rel_raw = rel[rel_off];
        let rel_var = if rel_raw < 0 {
          CVar(-rel_raw)
        } else {
          CVar(rel_raw)
        };
        let t_ct = if rel_raw < 0 {
          self.neg_tup_size(rel_var)
        } else {
          self.pos_tup_size(rel_var)
        };
        rbuf.push((t_ct, rel_off as u32));
      }
      rbuf.sort();
      if log_trace_v() {
        println!("TRACE: TFrame::_fix_eval_1_:     buf: {:?}", &rbuf);
      }
      for (rank, &(_, r)) in rbuf.iter().enumerate() {
        buf.push(r);
        rrnk[r as usize] = rank as u32;
      }
    }
    let mut vbuf = Vec::with_capacity(anterel);
    for &rel_off in buf.iter() {
      let rel_raw = rel[rel_off as usize];
      let rel_var = if rel_raw < 0 {
        CVar(-rel_raw)
      } else {
        CVar(rel_raw)
      };
      let lub = if rel_raw < 0 {
        self.neg_least_ub(rel_var)
      } else {
        self.pos_least_ub(rel_var)
      };
      if tlb <= lub {
        vbuf.push(rel_off);
      }
    }
    if vbuf.is_empty() {
      return;
    }
    let mut psub = Vec::with_capacity(sub.len());
    let mut pmax = Vec::with_capacity(buf.len());
    //let mut pmin = Vec::with_capacity(buf.len());
    pmax.resize(buf.len(), 0);
    //pmin.resize(buf.len(), 0);
    let mut args = BTreeSet::new();
    let mut rels = BTreeSet::new();
    let mut pmap = BTreeMap::new();
    let mut e = BTreeSet::new();
    for &rel_off in buf.iter() {
      let o = off[rel_off as usize] as usize;
      let a = ary[rel_off as usize] as usize;
      e.clear();
      let mut frsh = true;
      for t in o .. o + a {
        let p = pat[t];
        if p < 0 {
          if !args.contains(&p) {
            match useset.get(&p) {
              None => {}
              Some(uses) => {
                for &r in uses.iter() {
                  if rels.contains(&r) || r >= anterel as u32 || r == rel_off as u32 {
                    continue;
                  }
                  match defset.get(&p) {
                    None => {}
                    Some(&def) => {
                      assert!(r != def, "bug");
                    }
                  }
                  e.insert(r);
                }
              }
            }
            if frsh {
              pmax[rel_off as usize] = -1 - (psub.len() as SNum);
              frsh = false;
            }
            psub.push(p);
            args.insert(p);
          }
        }
      }
      if frsh {
        pmax[rel_off as usize] = -1 - psub.len() as SNum;
      }
      rels.insert(rel_off as u32);
      let mut ebuf = Vec::new();
      for &r in e.iter() {
        ebuf.push(r);
      }
      ebuf.sort_by_key(|&r| rrnk[r as usize]);
      pmap.insert(rel_off, ebuf);
    }
    drop(e);
    assert_eq!(def_off, psub.len());
    let mut prnk = Vec::with_capacity(psub.len());
    prnk.resize(psub.len(), 0);
    for (rank, &p) in psub.iter().enumerate() {
      let k = (-1 - p) as usize;
      assert_eq!(prnk[k], 0);
      prnk[k] = rank as SNum;
    }
    for &rel_off in buf.iter() {
      let o = off[rel_off as usize] as usize;
      let a = ary[rel_off as usize] as usize;
      perm[o .. o + a].copy_from_slice(&pat[o .. o + a]);
      perm[o .. o + a].sort_by_key(|&p| if p < 0 {
        let k = (-1 - p) as usize;
        prnk[k]
      } else {
        -p
      });
      // FIXME: quadratic, but lazy.
      for t in o .. o + a {
        let p = pat[t];
        if p >= 0 {
          panic!("bug: TFrame::_fix_eval_1: unimplemented");
        }
        for t2 in o .. o + a {
          let p2 = perm[t2];
          if p2 < 0 {
            if p == p2 {
              perm[t2] = (t - o) as SNum;
              break;
            }
          }
        }
      }
    }
    for r in 0 .. rel.len() {
      let o = off[r] as usize;
      let a = ary[r] as usize;
      for t in o .. o + a {
        let p = pat[t];
        let k = (-1 - p) as usize;
        if k < def_off {
          let rank = prnk[k];
          assert!(0 <= rank);
          assert!(rank < def_off as SNum);
          let p2 = -1 - rank;
          pat[t] = p2;
        }
      }
    }
    for &rel_off in buf.iter() {
      let o = off[rel_off as usize] as usize;
      let a = ary[rel_off as usize] as usize;
      _perm_tup(&perm[o .. o + a], &pat[o .. o + a], &mut tup[o .. o + a]);
      pat[o .. o + a].copy_from_slice(&tup[o .. o + a]);
      for t in o .. o + a - 1 {
        assert!(pat[t] >= pat[t + 1]);
      }
    }
    let mut pbuf = Vec::new();
    for (r, (r2, ebuf)) in pmap.into_iter().enumerate() {
      assert_eq!(r, r2 as usize);
      pbuf.push(ebuf);
    }
    let mut icount = 0;
    self._fix_join_1_perm(&mut icount, tlb, false, rec_var, def_off, 0, 0, anterel, antearg, &buf, &vbuf, &pbuf, sub, &prnk, &pmax, off, ary, rel, pat, tup, savepat, &mut ubpat, &perm, swap, cap);
    TL_FIX_EVAL_STATS.with(|stats| {
      let mut stats = stats.borrow_mut();
      stats.buf.push((icount, rec_var.0));
    });
  }

  fn _nul_eval_1_(&mut self, tlb: TNum, rec_var: CVar, nod: &mut Vec<Vec<usize>>, idx: &mut Vec<u32>, sub: &mut Vec<SNum>, off: &mut Vec<u32>, ary: &mut Vec<u32>, rel: &mut Vec<SNum>, pat: &mut Vec<SNum>, tup: &mut Vec<SNum>, savepat: &mut Vec<SNum>, swap: &mut dyn ESwap, cap: &mut dyn ECapture) {
    match self.urec.get(&rec_var) {
      None => {
        panic!("bug: TFrame::_nul_eval_1_: not a nul: rec={}", rec_var.0);
      }
      Some(rec) => {
        assert_eq!(rec.dvlen, 0);
        assert_eq!(rec.xvlen, 0);
        let (anterel, antearg) = rec.init_bufs_(self, rec_var, nod, idx, sub, off, ary, rel, pat);
        let useset = rec.useset.clone();
        let defset = rec.defset.clone();
        return self._fix_eval_1(tlb, rec_var, sub.len(), anterel, antearg, &useset, &defset, nod, idx, sub, off, ary, rel, pat, tup, savepat, swap, cap);
      }
    }
  }

  fn _def_eval_1_(&mut self, tlb: TNum, rec_var: CVar, nod: &mut Vec<Vec<usize>>, idx: &mut Vec<u32>, sub: &mut Vec<SNum>, off: &mut Vec<u32>, ary: &mut Vec<u32>, rel: &mut Vec<SNum>, pat: &mut Vec<SNum>, tup: &mut Vec<SNum>, savepat: &mut Vec<SNum>, swap: &mut dyn ESwap, cap: &mut dyn ECapture) {
    match self.drec.get(&rec_var) {
      None => {
        panic!("bug: TFrame::_def_eval_1_: not a def: rec={}", rec_var.0);
      }
      Some(rec) => {
        assert_eq!(rec.xvlen, 0);
        let (def_off, (anterel, antearg)) =
            (rec.uvlen as usize,
             rec.init_bufs_(self, rec_var, nod, idx, sub, off, ary, rel, pat));
        let useset = rec.useset.clone();
        let defset = rec.defset.clone();
        return self._fix_eval_1(tlb, rec_var, def_off, anterel, antearg, &useset, &defset, nod, idx, sub, off, ary, rel, pat, tup, savepat, swap, cap);
      }
    }
  }

  //fn _ext_eval_1(&mut self, rec_var: CVar, idx: &mut Vec<u32>, sub: &mut Vec<SNum>, rel: &mut Vec<SNum>, pat: &mut Vec<SNum>, tup: &mut Vec<SNum>, swapbuf: &mut Vec<SNum>) {
  fn _ext_eval_1(&mut self, /*_tdelta: TNum,*/ _rec_var: CVar, _idx: &mut Vec<u32>, _sub: &mut Vec<SNum>, _rel: &mut Vec<SNum>, _pat: &mut Vec<SNum>, _tup: &mut Vec<SNum>, _savetup: &mut Vec<SNum>, _swapbuf: &mut Vec<SNum>) {
    // FIXME
    unimplemented!();
  }
}

#[derive(Clone, Copy)]
enum FormDecode {
  Lit{neg: bool},
}

#[derive(Clone, Default)]
pub struct TFre1 {
  pub freevar:  Vec<SNum>,
  pub data:     Vec<i8>,
  pub rel_len:  u8,
}

impl TFre1 {
  pub fn init_bufs(&self, frame: &dyn EFrame, rel: &mut Vec<SNum>, pat: &mut Vec<SNum>) -> usize {
    rel.resize(self.rel_len as usize, 0);
    let mut rel_off = 0;
    let mut arg_off = 0;
    let mut p = 0;
    while p < self.data.len() {
      let code = self.data[p];
      let decode = match code {
        1 => FormDecode::Lit{neg: false},
        -1 => FormDecode::Lit{neg: true},
        _ => panic!("bug: TFre1::init_bufs: unknown code: {}", code)
      };
      p += 1;
      match decode {
        FormDecode::Lit{neg} => {
          let rel_idx = self.data[p];
          assert!(rel_idx >= 0);
          let rel_var = CVar(self.freevar[rel_idx as usize]);
          assert!(rel_var.0 > 0);
          match neg {
            false => rel[rel_off] = rel_var.0,
            true => rel[rel_off] = -rel_var.0,
          }
          let arity = frame.rel_arity(rel_var);
          pat.resize(arg_off + arity, 0);
          p += 1;
          for q in p .. p + arity {
            let var_idx = self.data[q];
            if var_idx >= 0 {
              pat[arg_off + q - p] = self.freevar[var_idx as usize];
            } else {
              panic!("bug: TFre1::init_bufs: wild pat");
            }
          }
          rel_off += 1;
          arg_off += arity;
          p += arity;
        }
      }
    }
    assert_eq!(rel_off, self.rel_len as usize);
    self.rel_len as usize
  }
}

#[derive(Clone, Default)]
pub struct TRec1 {
  pub freevar:  Vec<SNum>,
  pub uvlen:    u8,
  pub dvlen:    u8,
  pub xvlen:    u8,
  pub antelen:  u8,
  pub conslen:  u8,
  pub useset:   BTreeMap<SNum, BTreeSet<u32>>,
  pub defset:   BTreeMap<SNum, u32>,
  pub node:     Vec<u8>,
  pub data:     Vec<i8>,
}

impl TRec1 {
  pub fn rec_arity(&self) -> (usize, usize) {
    (self.antelen as usize, self.conslen as usize)
  }

  pub fn bind_arity(&self) -> (usize, usize, usize) {
    (self.uvlen as usize, self.dvlen as usize, self.xvlen as usize)
  }

  pub fn init_bufs_(&self, frame: &dyn EFrame, rec_var: CVar, nod: &mut Vec<Vec<usize>>, idx: &mut Vec<u32>, sub: &mut Vec<SNum>, off: &mut Vec<u32>, ary: &mut Vec<u32>, rel: &mut Vec<SNum>, pat: &mut Vec<SNum>) -> (usize, usize) {
    let bindlen = self.uvlen as usize + self.dvlen as usize + self.xvlen as usize;
    assert!(bindlen <= 127);
    let atomlen = self.antelen as usize + self.conslen as usize;
    assert!(atomlen <= 127);
    nod.clear();
    idx.clear();
    idx.resize(bindlen, 0);
    sub.clear();
    sub.resize(bindlen, 0);
    let mut p = 0;
    let nodelen = self.node[p] as usize;
    p += 1;
    while p < self.node.len() {
      let g = self.node[p] as usize;
      p += 1;
      let mut gg = Vec::with_capacity(g);
      for q in p .. p + g {
        gg.push(self.node[q] as usize);
      }
      nod.push(gg);
      p += g;
    }
    assert_eq!(nod.len(), nodelen);
    rel.clear();
    rel.resize(atomlen, 0);
    off.clear();
    off.resize(atomlen + 1, 0);
    ary.clear();
    ary.resize(atomlen, 0);
    pat.clear();
    let mut p = 0;
    let mut rel_off = 0;
    let mut arg_off = 0;
    let mut antearg = 0;
    while p < self.data.len() {
      let code = self.data[p];
      let decode = match code {
        1 => FormDecode::Lit{neg: false},
        -1 => FormDecode::Lit{neg: true},
        _ => panic!("bug: TRec1::init_bufs_: unknown code: {} rec={}", code, rec_var.0)
      };
      p += 1;
      match decode {
        FormDecode::Lit{neg} => {
          let rel_pos = self.data[p];
          assert!(rel_pos >= 0);
          let rel_var = CVar(self.freevar[rel_pos as usize]);
          assert!(rel_var.0 > 0);
          match neg {
            false => rel[rel_off] = rel_var.0,
            true => rel[rel_off] = -rel_var.0,
          }
          let arity = frame.rel_arity(rel_var);
          off[rel_off] = arg_off as u32;
          ary[rel_off] = arity as u32;
          pat.resize(arg_off + arity, 0);
          p += 1;
          if self.data.len() < p + arity {
            panic!("bug: TRec1::init_bufs_: out of bounds: rec={}", rec_var.0);
          }
          for q in p .. p + arity {
            let var_pos = self.data[q];
            if var_pos >= 0 {
              pat[arg_off + q - p] = self.freevar[var_pos as usize];
            } else {
              pat[arg_off + q - p] = var_pos as SNum;
            }
          }
          if rel_off < self.antelen as usize {
            antearg += arity;
          }
          rel_off += 1;
          arg_off += arity;
          p += arity;
        }
      }
    }
    assert_eq!(rel_off, atomlen);
    off[rel_off] = arg_off as u32;
    (self.antelen as usize, antearg)
  }

  pub fn init_bufs(&self, frame: &dyn EFrame, rec_var: CVar, idx: &mut Vec<u32>, sub: &mut Vec<SNum>, rel: &mut Vec<SNum>, pat: &mut Vec<SNum>) -> usize {
    let bindlen = self.uvlen as usize + self.dvlen as usize + self.xvlen as usize;
    assert!(bindlen <= 127);
    let atomlen = self.antelen as usize + self.conslen as usize;
    assert!(atomlen <= 127);
    rel.resize(atomlen, 0);
    let mut rel_off = 0;
    let mut arg_off = 0;
    let mut p = 0;
    //let mut iter_ct = 0;
    while p < self.data.len() {
      /*iter_ct += 1;
      if iter_ct == 100 {
        println!("TRACE: TRec1::init_bufs: loop 100x");
      }*/
      let code = self.data[p];
      let decode = match code {
        1 => FormDecode::Lit{neg: false},
        -1 => FormDecode::Lit{neg: true},
        _ => panic!("bug: TRec1::init_bufs: unknown code: {} {:?}", code, rec_var)
      };
      p += 1;
      match decode {
        FormDecode::Lit{neg} => {
          let rel_idx = self.data[p];
          assert!(rel_idx >= 0);
          //assert_eq!(rel_idx as usize, rel_off);
          let rel_var = CVar(self.freevar[rel_idx as usize]);
          assert!(rel_var.0 > 0);
          match neg {
            false => rel[rel_off] = rel_var.0,
            true => rel[rel_off] = -rel_var.0,
          }
          let arity = frame.rel_arity(rel_var);
          pat.resize(arg_off + arity, 0);
          //println!("TRACE: TRec1::init_bufs: p={} arity={} data={} free={}", p, arity, self.data.len(), self.freevar.len());
          p += 1;
          if self.data.len() < p + arity {
            panic!("bug: TRec1::init_bufs: out of bounds: {:?}", rec_var);
          }
          for q in p .. p + arity {
            let var_idx = self.data[q];
            if var_idx >= 0 {
              pat[arg_off + q - p] = self.freevar[var_idx as usize];
            } else {
              pat[arg_off + q - p] = var_idx as SNum;
            }
          }
          rel_off += 1;
          arg_off += arity;
          p += arity;
        }
      }
    }
    assert_eq!(rel_off, atomlen);
    idx.clear();
    idx.resize(bindlen, 0);
    sub.clear();
    sub.resize(bindlen, 0);
    self.antelen as usize
  }
}

pub type TResult = Option<TNum>;

#[derive(Clone, Copy, Debug)]
pub enum TScanResult {
  End,
  Hit(TNum, /*bool*/),
  Skip/*(bool)*/,
}

#[derive(Clone, Copy, Debug)]
pub enum TSwapStatus {
  Noswap,
  Fresh,
  Merge,
  Stale,
}

pub type TSwapResult = (TSwapStatus, TNum);

#[inline(always)]
pub fn _from_fresh_stale(fresh: Option<TNum>, stale: Option<TNum>) -> TSwapResult {
  match (fresh, stale) {
    (None, None) => (Noswap, 0),
    (None, Some(t)) => (Stale, t),
    (Some(t), _) => (Fresh, t),
  }
}

#[inline(always)]
pub fn _from_merge_fresh_stale(merge: Option<TNum>, fresh: Option<TNum>, stale: Option<TNum>) -> TSwapResult {
  // TODO
  match (merge, fresh, stale) {
    (None, None, None) => (Noswap, 0),
    (None, None, Some(t)) => (Stale, t),
    (None, Some(t), _) => (Fresh, t),
    (Some(t), _, _) => (Merge, t),
  }
}

pub trait EScan {
  fn next_tup(&mut self, _tup: &mut [SNum], /*_shm: &mut STFrame*/) -> TScanResult;
}

pub trait ERel: Any {
  fn clone_ref(&self) -> ERelRef;
  fn anycast_ref(&self) -> &dyn Any { unimplemented!() }
  fn arity(&self) -> usize { unimplemented!(); }
  fn fun_arity(&self) -> Option<(usize, usize)> { None }
  fn map_arity(&self) -> Option<(usize, usize)> { self.fun_arity() }
  fn arity2(&self) -> (usize, usize) {
    match self.fun_arity() {
      None => (self.arity(), 0),
      Some(a) => a
    }
  }
  fn kind2(&self) -> (RelKind, RelKind2) { unimplemented!(); }
  fn pos_least_ub(&self, _shm: &STFrame) -> TNum { unimplemented!(); }
  fn neg_least_ub(&self, _shm: &STFrame) -> TNum { unimplemented!(); }
  fn pos_tup_size(&self, _shm: &STFrame) -> u64 { unimplemented!(); }
  fn neg_tup_size(&self, _shm: &STFrame) -> u64 { unimplemented!(); }
  fn debug_dump_tups(&self, rel: CVar, _shm: &STFrame) { self.dump_tups(rel, "DEBUG: ", _shm); }
  fn trace_dump_tups(&self, rel: CVar, _shm: &STFrame) { self.dump_tups(rel, "TRACE: ", _shm); }
  fn dump_tups(&self, _rel: CVar, _prefix: &str, _shm: &STFrame) {}
  fn patchdiff(&self, _rel: CVar, _older: &dyn ERel, _shm: &mut STFrame) -> (usize, usize) { unimplemented!(); }
  fn patch(&mut self, _rel: CVar, /*_clk: &mut TClk,*/ _shm: &mut STFrame) /*-> bool*/ { unimplemented!(); }
  fn patchswap(&mut self, _rel: CVar, _newswap: &mut Vec<SNum>, /*_clk: &mut TClk,*/ _shm: &mut STFrame) { unimplemented!(); }
  fn patch_swap(&mut self, _tlb: TNum, _rel: CVar, _newswap: &mut dyn ESwap, _shm: &mut STFrame) { unimplemented!(); }
  fn flag_tup(&mut self, /*_rec: CVar,*/ _rel: CVar, _tup: &mut [SNum]) -> TResult { unimplemented!(); }
  fn test_pos_tup(&mut self, /*_rec: CVar,*/ _rel: CVar, _tup: &[SNum], _shm: &mut STFrame) -> TResult { unimplemented!(); }
  fn test_neg_tup(&mut self, /*_rec: CVar,*/ _rel: CVar, _tup: &[SNum], _shm: &mut STFrame) -> TResult { unimplemented!(); }
  fn scan_pos(&mut self, /*_rec: CVar,*/ _rel: CVar, _lbtup: &[SNum], _ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox { unimplemented!(); }
  fn scan_neg(&mut self, /*_rec: CVar,*/ _rel: CVar, _lbtup: &[SNum], _ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox { unimplemented!(); }
  fn permscan_pos(&mut self, /*_rec: CVar,*/ _rel: CVar, _perm: &[SNum], _lbtup: &[SNum], _ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox { unimplemented!(); }
  fn permscan_neg(&mut self, /*_rec: CVar,*/ _rel: CVar, _perm: &[SNum], _lbtup: &[SNum], _ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox { unimplemented!(); }
  fn scan_par(&self, /*_rec: CVar,*/ _rel: CVar, _shm: &STFrame) -> EScanBox { unimplemented!(); }
  fn next_pos_tup(&mut self, /*_rec: CVar,*/ _rel: CVar, _tlb: TNum, _tup: &mut [SNum], _shm: &mut STFrame) -> TResult { unimplemented!(); }
  fn next_neg_tup(&mut self, /*_rec: CVar,*/ _rel: CVar, _tlb: TNum, _tup: &mut [SNum], _shm: &mut STFrame) -> TResult { unimplemented!(); }
  fn swap_pos_tup(&mut self, _rec: CVar, _rel: CVar, _tup: &[SNum], _newswap: &mut Vec<SNum>, _swaptup: &mut Vec<SNum>, _shm: &mut STFrame) -> TResult { unimplemented!(); }
  fn swap_neg_tup(&mut self, _rec: CVar, _rel: CVar, _tup: &[SNum], _newswap: &mut Vec<SNum>, _swaptup: &mut Vec<SNum>, _shm: &mut STFrame) -> TResult { unimplemented!(); }
  fn swap_pos_tup_(&mut self, _tlb: TNum, _rec: CVar, _rel: CVar, _tup: &[SNum], _swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, _shm: &mut STFrame) -> TSwapResult { unimplemented!(); }
  fn swap_neg_tup_(&mut self, _tlb: TNum, _rec: CVar, _rel: CVar, _tup: &[SNum], _swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, _shm: &mut STFrame) -> TSwapResult { unimplemented!(); }
}

pub struct CcScan {
  ub:   CVar,
  iter: IHTreapMapCloneIter<CVar, TNum>,
}

impl EScan for CcScan {
  fn next_tup(&mut self, tup: &mut [SNum], /*shm: &mut STFrame*/) -> TScanResult {
    match self.iter.next() {
      None => {
        End
      }
      Some((x, t)) => if x > self.ub {
        End
      } else {
        tup[0] = x.0;
        tup[1] = x.0;
        Hit(t)
      }
    }
  }
}

pub struct CcParScan {
  iter: IHTreapMapCloneIter<CVar, TNum>,
  nset: IHTreapMap<CTup2, TNum>,
}

impl EScan for CcParScan {
  fn next_tup(&mut self, tup: &mut [SNum], /*shm: &mut STFrame*/) -> TScanResult {
    // TODO
    loop {
      match self.iter.next() {
        None => {
          return End;
        }
        Some((x, pt)) => {
          match self.nset.get(&CTup2([x, x])) {
            None => continue,
            Some(&nt) => {
              tup[0] = x.0;
              tup[1] = x.0;
              return Hit(max(pt, nt));
            }
          }
        }
      }
    }
  }
}

#[derive(Clone, Default)]
pub struct EquivRel {
  // TODO
  chk:  TUSnapshot,
  attr: IHTreapMap<TNum, CVar>,
  nlub: TNum,
  nidx: CUnionIter<(TNum, CTup2)>,
  //ndom: IHTreapSet<(TNum, CTup2)>,
  nset: IHTreapMap<CTup2, TNum>,
  //flag: Option<(TNum, CTup2)>,
}

impl EquivRel {
  fn _patch_neg(&mut self, _rel: CVar, shm: &mut STFrame) -> bool {
    //bench_patch_start();
    /*println!("TRACE: EquivRel::_patch_neg: chk.tu={} cc.tu={}",
        self.chk.tu, shm.cc.tu);*/
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut nlub = self.nlub;
    let u_it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in u_it {
      for (_, np) in self.nidx.iter(nx) {
        let np_: &[CVar] = np.as_ref();
        let nx0 = np_[0];
        let nx1 = np_[1];
        match self.nset.get(&np) {
          None => {}
          Some(&t) => if ut > t {
            patch = true;
            let t = shm.clk.fresh();
            nlub = t;
            self.nidx.insert(nx0, (t, np));
            self.nidx.insert(nx1, (t, np));
            self.nset.insert(np, t);
          }
        }
      }
      for (ot, op) in self.nidx.iter(ox) {
        match self.nset.get(&op) {
          None => {}
          Some(&ot) => {
            let np = op.swap_var(ox, nx);
            let np_: &[CVar] = np.as_ref();
            let nx0 = np_[0];
            let nx1 = np_[1];
            match self.nset.get(&np) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                nlub = t;
                self.nidx.insert(nx0, (t, np));
                self.nidx.insert(nx1, (t, np));
                self.nset.remove(&op);
                self.nset.insert(np, t);
              }
              Some(&t) => if ut > t || ut > ot {
                patch = true;
                let t = shm.clk.fresh();
                nlub = t;
                self.nidx.insert(nx0, (t, np));
                self.nidx.insert(nx1, (t, np));
                self.nset.remove(&op);
                self.nset.insert(np, t);
              }
            }
          }
        }
      }
      self.nidx.remove(ox);
    }
    self.nlub = nlub;
    //bench_patch_stop();
    patch
  }
}

impl ERel for EquivRel {
  fn clone_ref(&self) -> ERelRef {
    Rc::new(self.clone())
  }

  fn arity(&self) -> usize {
    2
  }

  fn kind2(&self) -> (RelKind, RelKind2) {
    (RelKind::Rel, RelKind2::Symm)
  }

  fn pos_least_ub(&self, shm: &STFrame) -> TNum {
    shm.cc.lub()
  }

  fn neg_least_ub(&self, _shm: &STFrame) -> TNum {
    self.nlub
  }

  fn pos_tup_size(&self, shm: &STFrame) -> u64 {
    shm.cc.ucount() as u64
  }

  fn neg_tup_size(&self, _shm: &STFrame) -> u64 {
    self.nset.len() as u64
  }

  fn dump_tups(&self, rel: CVar, prefix: &str, shm: &STFrame) {
    println!("{}EquivRel::dump_tups: rel={} +{} -{}",
        prefix, rel.0, shm.cc.rset.len(), self.nset.len());
    for (&x, &t) in shm.cc.rset.iter() {
      print!("{}  + {} [{}] = [", prefix, t, x.0);
      // FIXME(HACK)
      for (&y, &(_, r)) in shm.cc.rmap.iter() {
        let (_, ry) = shm.cc.find_nonmut(y);
        if x == ry {
          print!("{}, ", y.0)
        }
      }
      println!("]");
    }
    for (xp, &t) in self.nset.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  - {} {:?}", prefix, t, xp_);
    }
  }

  /*fn patch(&mut self, _rel: CVar, shm: &mut STFrame) {
    //self._patch_neg(&mut shm.cc, clk);
    self._patch_neg(_rel, shm);
  }*/

  fn patchswap(&mut self, _rel: CVar, _newswap: &mut Vec<SNum>, shm: &mut STFrame) {
    self._patch_neg(_rel, shm);
  }

  fn patch_swap(&mut self, _tlb: TNum, _rel: CVar, _newswap: &mut dyn ESwap, shm: &mut STFrame) {
    //println!("TRACE: EquivRel::patch_swap: tlb={}", _tlb);
    self._patch_neg(_rel, shm);
  }

  /*fn flag_tup(&mut self, _rel: CVar, tup: &mut [SNum]) -> Option<TNum> {
    match self.flag {
      None => {
        None
      }
      Some((t, xp)) => {
        tup.copy_from_slice(xp.as_ref());
        Some(t)
      }
    }
  }*/

  fn flag_tup(&mut self, _rel: CVar, _tup: &mut [SNum]) -> Option<TNum> {
    None
  }

  fn test_pos_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[lk, rk] = as_cvars(tup) {
      let (lt, lx) = shm.cc.find(lk);
      let (rt, rx) = shm.cc.find(rk);
      if lx == rx {
        return Some(max(lt, rt));
      }
      None
    } else {
      unreachable!();
    }
  }

  fn test_neg_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[lk, rk] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        //self._patch_neg(&mut shm.cc, clk);
        self._patch_neg(_rel, clk, shm);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx) = shm.cc.find(lk);
      let (_, rx) = shm.cc.find(rk);
      let xp = CTup2::from([lx, rx]);
      let ret = match self.nset.get(&xp) {
        None => {
          None
        }
        Some(&t) => {
          Some(t)
        }
      };
      if lx == rx {
        return ret;
      }
      let xp = CTup2::from([rx, lx]);
      let ret2 = match self.nset.get(&xp) {
        None => {
          None
        }
        Some(&t) => {
          Some(t)
        }
      };
      max(ret, ret2)
    } else {
      unreachable!();
    }
  }

  fn scan_pos(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], shm: &mut STFrame) -> EScanBox {
    let lb = if let &[lk, rk] = as_cvars(lbtup) {
      let lb = if lk < rk {
        CVar(lk.0 + 1)
      } else {
        lk
      };
      /*if lk.0 == 92 || rk.0 == 92 {
        println!("TRACE: EquivRel: scan_pos: rel={} lk={} rk={} lb={}", _rel.0, lk.0, rk.0, lb.0);
      }*/
      lb
    } else {
      unreachable!();
    };
    let ub = if let &[lk, rk] = as_cvars(ubtup) {
      let ub = if lk > rk {
        CVar(max(0, lk.0 - 1))
      } else {
        lk
      };
      /*if lk.0 == 92 || rk.0 == 92 {
        println!("TRACE: EquivRel: scan_pos: rel={} lk={} rk={} ub={}", _rel.0, lk.0, rk.0, ub.0);
      }*/
      ub
    } else {
      unreachable!();
    };
    let iter = shm.cc.rset.clone_iter_from(&lb);
    let scan = Box::new(CcScan{ub, iter});
    scan
  }

  fn scan_neg(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup2::from(ubtup);
    let iter = self.nset.clone_iter_from(lbtup);
    let scan = Box::new(RScan2{ub, iter});
    scan
  }

  fn permscan_pos(&mut self, _rel: CVar, _perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    self.scan_pos(_rel, lbtup, ubtup, _shm)
  }

  fn permscan_neg(&mut self, _rel: CVar, _perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    self.scan_neg(_rel, lbtup, ubtup, _shm)
  }

  fn scan_par(&self, _rel: CVar, shm: &STFrame) -> EScanBox {
    let iter = shm.cc.rset.clone_iter();
    let nset = self.nset.clone();
    let scan = Box::new(CcParScan{iter, nset});
    scan
  }

  fn swap_pos_tup(&mut self, rec: CVar, _rel: CVar, tup: &[SNum], _newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[lk, rk] = as_cvars(tup) {
      /*let (t, x, u) = shm.cc.unify_(TAttr::Swap(rec), lk, rk, &mut shm.clk, &shm.trak);*/
      let (t, x, u) = shm.cc.unify(TAttr::Swap(rec), lk, rk, &mut shm.clk);
      if u {
        //self._flag_pos(t, x);
        swaptup.push(x.0);
        swaptup.push(x.0);
        Some(t)
      } else {
        None
      }
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup(&mut self, _rec: CVar, _rel: CVar, tup: &[SNum], newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let mut ret = None;
      let xp = CTup2([x0, x1]);
      match self.nset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.nlub = t;
          self.nidx.insert(x0, (t, xp));
          self.nidx.insert(x1, (t, xp));
          self.nset.insert(xp, t);
          //self._flag_neg(t, x0, x1);
          swaptup.extend_from_slice(xp.as_ref());
          ret = Some(t);
        }
        Some(_) => {}
      }
      if x0 == x1 {
        return ret;
      }
      let xp = CTup2([x1, x0]);
      match self.nset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.nlub = t;
          self.nidx.insert(x0, (t, xp));
          self.nidx.insert(x1, (t, xp));
          self.nset.insert(xp, t);
          //self._flag_neg(t, x0, x1);
          swaptup.extend_from_slice(xp.as_ref());
          ret = Some(t);
        }
        Some(_) => {}
      }
      ret
    } else {
      unreachable!();
    }
  }

  fn swap_pos_tup_(&mut self, tlb: TNum, rec: CVar, rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[lk, rk] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        println!("TRACE: EquivRel::swap_pos_tup_: rec={} rel={} tup={:?} chk.tu={} cc.tu={}",
            rec.0, rel.0, tup,
            self.chk.tu, shm.cc.tu);
        panic!("BUG");
      }*/
      let (_, lx) = shm.cc.find(lk);
      let (_, rx) = shm.cc.find(rk);
      /*let (t, x, u) = shm.cc.unify_(TAttr::Swap(rec), lk, rk, &mut shm.clk, &shm.trak);*/
      let (t, x, u) = shm.cc.unify(TAttr::Swap(rec), lk, rk, &mut shm.clk);
      if u {
        //self._flag_pos(t, x);
        /*swaptup.push(x.0);
        swaptup.push(x.0);*/
        /*swaptup.push(lx.0);
        swaptup.push(rx.0);
        swaptup.push(rx.0);
        swaptup.push(lx.0);*/
        let (x0, x1) = (min(lx.0, rx.0), max(lx.0, rx.0));
        swaptup.push(x0);
        swaptup.push(x1);
        swaptup.push(x1);
        swaptup.push(x0);
        (Fresh, t)
      } else if t >= tlb {
        /*swaptup.push(x.0);
        swaptup.push(x.0);*/
        /*swaptup.push(lx.0);
        swaptup.push(rx.0);
        swaptup.push(rx.0);
        swaptup.push(lx.0);*/
        let (x0, x1) = (min(lx.0, rx.0), max(lx.0, rx.0));
        swaptup.push(x0);
        swaptup.push(x1);
        swaptup.push(x1);
        swaptup.push(x0);
        (Stale, t)
      } else {
        (Noswap, 0)
      }
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup_(&mut self, tlb: TNum, rec: CVar, rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[k0, k1] = as_cvars(tup) {
      //assert!(self.chk.is_ulive(&shm.cc));
      if !self.chk.is_ulive(&shm.cc) {
        println!("TRACE: EquivRel::swap_neg_tup_: rec={} rel={} tup={:?} chk.tu={} cc.tu={}",
            rec.0, rel.0, tup,
            self.chk.tu, shm.cc.tu);
        panic!("BUG");
      }
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (x0, x1) = (min(x0, x1), max(x0, x1));
      let mut fresh = None;
      let mut stale = None;
      let xp = CTup2([x0, x1]);
      match self.nset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.nlub = t;
          self.nidx.insert(x0, (t, xp));
          self.nidx.insert(x1, (t, xp));
          self.nset.insert(xp, t);
          //self._flag_neg(t, x0, x1);
          //swaptup.extend_from_slice(xp.as_ref());
          fresh = Some(t);
        }
        Some(&t) => if t >= tlb {
          //swaptup.extend_from_slice(xp.as_ref());
          stale = Some(t);
        }
      }
      swaptup.extend_from_slice(xp.as_ref());
      if x0 == x1 {
        return _from_fresh_stale(fresh, stale);
      }
      let xp = CTup2([x1, x0]);
      match self.nset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.nlub = t;
          self.nidx.insert(x0, (t, xp));
          self.nidx.insert(x1, (t, xp));
          self.nset.insert(xp, t);
          //self._flag_neg(t, x0, x1);
          //swaptup.extend_from_slice(xp.as_ref());
          fresh = Some(t);
        }
        Some(&t) => if t >= tlb {
          //swaptup.extend_from_slice(xp.as_ref());
          stale = Some(t);
        }
      }
      swaptup.extend_from_slice(xp.as_ref());
      _from_fresh_stale(fresh, stale)
    } else {
      unreachable!();
    }
  }
}

#[derive(Clone, Default)]
pub struct VRel {
  var:  CVar,
  chk:  TUSnapshot,
  plub: TNum,
  nlub: TNum,
  set1: IHTreapMap<(CVar, CVar), TNum>,
  set2: IHTreapMap<(CVar, CTup2), TNum>,
  set3: IHTreapMap<(CVar, CTup3), TNum>,
  set4: IHTreapMap<(CVar, CTup4), TNum>,
  set5: IHTreapMap<(CVar, CTup5), TNum>,
  set6: IHTreapMap<(CVar, CTup6), TNum>,
  //setx: IHTreapMap<(CVar, CVTup), TNum>,
  //flag: Option<(TNum, (CVar, CVTup))>,
}

pub struct RScan1 {
  ub:   CVar,
  iter: IHTreapMapCloneIter<CVar, TNum>,
}

impl EScan for RScan1 {
  fn next_tup(&mut self, tup: &mut [SNum], /*shm: &mut STFrame*/) -> TScanResult {
    match self.iter.next() {
      None => {
        End
      }
      Some((x, t)) => if x > self.ub {
        End
      } else {
        tup[0] = x.0;
        Hit(t)
      }
    }
  }
}

#[derive(Clone, Default)]
pub struct Rel1 {
  chk:  TUSnapshot,
  attr: IHTreapMap<TNum, CVar>,
  plub: TNum,
  nlub: TNum,
  //pdom: IHTreapSet<(TNum, CVar)>,
  pset: IHTreapMap<CVar, TNum>,
  //ndom: IHTreapSet<(TNum, CVar)>,
  nset: IHTreapMap<CVar, TNum>,
  //flag: Option<(TNum, CVar)>,
}

impl Rel1 {
  fn _patch(&mut self, _rel: CVar, shm: &mut STFrame) -> bool {
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    bench_patch_start();
    let mut patch = false;
    let mut plub = self.plub;
    let mut nlub = self.nlub;
    let u_it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ok), nk) in u_it {
      match self.pset.get(&nk) {
        None => {}
        Some(&t) => if ut > t {
          patch = true;
          let t = shm.clk.fresh();
          plub = t;
          self.pset.insert(nk, t);
        }
      }
      match self.pset.get(&ok) {
        None => {}
        Some(&ot) => {
          match self.pset.get(&nk) {
            None => {
              patch = true;
              let t = shm.clk.fresh();
              plub = t;
              self.pset.remove(&ok);
              self.pset.insert(nk, t);
            }
            Some(&t) => if ut > t || ut > ot {
              patch = true;
              let t = shm.clk.fresh();
              plub = t;
              self.pset.remove(&ok);
              self.pset.insert(nk, t);
            }
          }
        }
      }
      match self.nset.get(&nk) {
        None => {}
        Some(&t) => if ut > t {
          patch = true;
          let t = shm.clk.fresh();
          nlub = t;
          self.nset.insert(nk, t);
        }
      }
      match self.nset.get(&ok) {
        None => {}
        Some(&ot) => {
          match self.pset.get(&nk) {
            None => {
              patch = true;
              let t = shm.clk.fresh();
              nlub = t;
              self.nset.remove(&ok);
              self.nset.insert(nk, t);
            }
            Some(&t) => if ut > t || ut > ot {
              patch = true;
              let t = shm.clk.fresh();
              nlub = t;
              self.nset.remove(&ok);
              self.nset.insert(nk, t);
            }
          }
        }
      }
    }
    self.plub = plub;
    self.nlub = nlub;
    bench_patch_stop();
    patch
  }
}

impl ERel for Rel1 {
  fn clone_ref(&self) -> ERelRef {
    Rc::new(self.clone())
  }

  fn arity(&self) -> usize {
    1
  }

  fn kind2(&self) -> (RelKind, RelKind2) {
    (RelKind::Rel, RelKind2::Exact)
  }

  fn pos_least_ub(&self, _shm: &STFrame) -> TNum {
    self.plub
  }

  fn neg_least_ub(&self, _shm: &STFrame) -> TNum {
    self.nlub
  }

  fn pos_tup_size(&self, _shm: &STFrame) -> u64 {
    self.pset.len() as u64
  }

  fn neg_tup_size(&self, _shm: &STFrame) -> u64 {
    self.nset.len() as u64
  }

  fn dump_tups(&self, rel: CVar, prefix: &str, _shm: &STFrame) {
    println!("{}Rel1::dump_tups: rel={} +{} -{}",
        prefix, rel.0, self.pset.len(), self.nset.len());
    for (&x, &t) in self.pset.iter() {
      println!("{}  + {} [{}]", prefix, t, x.0);
    }
    for (&x, &t) in self.nset.iter() {
      println!("{}  - {} [{}]", prefix, t, x.0);
    }
  }

  /*fn patch(&mut self, rel: CVar, shm: &mut STFrame) {
    self._patch(rel, shm);
  }*/

  fn patchswap(&mut self, _rel: CVar, _newswap: &mut Vec<SNum>, shm: &mut STFrame) {
    self._patch(_rel, shm);
  }

  fn patch_swap(&mut self, _tlb: TNum, _rel: CVar, _newswap: &mut dyn ESwap, shm: &mut STFrame) {
    self._patch(_rel, shm);
  }

  /*fn flag_tup(&mut self, _rel: CVar, tup: &mut [SNum]) -> Option<TNum> {
    match self.flag {
      None => {
        None
      }
      Some((t, x)) => {
        tup[0] = x.0;
        Some(t)
      }
    }
  }*/

  fn flag_tup(&mut self, _rel: CVar, _tup: &mut [SNum]) -> Option<TNum> {
    None
  }

  fn test_pos_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[k] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(_rel, clk, shm);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x) = shm.cc.find(k);
      match self.pset.get(&x) {
        None => {}
        Some(&t) => {
          return Some(t);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn test_neg_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[k] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(_rel, clk, shm);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x) = shm.cc.find(k);
      match self.nset.get(&x) {
        None => {}
        Some(&t) => {
          return Some(t);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn scan_pos(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let lb = CVar(lbtup[0]);
    let ub = CVar(ubtup[0]);
    let iter = self.pset.clone_iter_from(&lb);
    let scan = Box::new(RScan1{ub, iter});
    scan
  }

  fn scan_neg(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let lb = CVar(lbtup[0]);
    let ub = CVar(ubtup[0]);
    let iter = self.nset.clone_iter_from(&lb);
    let scan = Box::new(RScan1{ub, iter});
    scan
  }

  fn permscan_pos(&mut self, _rel: CVar, _perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    self.scan_pos(_rel, lbtup, ubtup, _shm)
  }

  fn permscan_neg(&mut self, _rel: CVar, _perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    self.scan_neg(_rel, lbtup, ubtup, _shm)
  }

  fn scan_par(&self, _rel: CVar, _shm: &STFrame) -> EScanBox {
    let ub = CVar::ub();
    let iter = self.pset.merge_intersection(&self.nset, &mut |_, &lt, &rt| max(lt, rt)).clone_iter();
    let scan = Box::new(RScan1{ub, iter});
    scan
  }

  fn swap_pos_tup(&mut self, _rec: CVar, _rel: CVar, tup: &[SNum], _newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[k] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(_rel, clk, shm);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x) = shm.cc.find(k);
      match self.pset.get(&x) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          //self.pdom.insert((t, x));
          self.pset.insert(x, t);
          swaptup.push(x.0);
          Some(t)
        }
        Some(_) => {
          None
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup(&mut self, _rec: CVar, _rel: CVar, tup: &[SNum], _newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[k] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(_rel, clk, shm);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x) = shm.cc.find(k);
      match self.nset.get(&x) {
        None => {
          let t = shm.clk.fresh();
          self.nlub = t;
          //self.ndom.insert((t, x));
          self.nset.insert(x, t);
          swaptup.push(x.0);
          Some(t)
        }
        Some(_) => {
          None
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_pos_tup_(&mut self, tlb: TNum, _rec: CVar, _rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[k] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x) = shm.cc.find(k);
      match self.pset.get(&x) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          //self.pdom.insert((t, x));
          self.pset.insert(x, t);
          swaptup.push(x.0);
          (Fresh, t)
        }
        Some(&t) => if t >= tlb {
          swaptup.push(x.0);
          (Stale, t)
        } else {
          (Noswap, 0)
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup_(&mut self, tlb: TNum, _rec: CVar, _rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[k] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x) = shm.cc.find(k);
      match self.nset.get(&x) {
        None => {
          let t = shm.clk.fresh();
          self.nlub = t;
          //self.ndom.insert((t, x));
          self.nset.insert(x, t);
          swaptup.push(x.0);
          (Fresh, t)
        }
        Some(&t) => if t >= tlb {
          swaptup.push(x.0);
          (Stale, t)
        } else {
          (Noswap, 0)
        }
      }
    } else {
      unreachable!();
    }
  }
}

pub struct RScan2 {
  ub:   CTup2,
  iter: IHTreapMapCloneIter<CTup2, TNum>,
}

impl EScan for RScan2 {
  fn next_tup(&mut self, tup: &mut [SNum], /*shm: &mut STFrame*/) -> TScanResult {
    match self.iter.next() {
      None => {
        End
      }
      Some((xp, t)) => if xp > self.ub {
        End
      } else {
        tup.copy_from_slice(xp.as_ref());
        Hit(t)
      }
    }
  }
}

#[derive(Clone, Default)]
pub struct Rel2 {
  chk:  TUSnapshot,
  attr: IHTreapMap<TNum, CVar>,
  plub: TNum,
  nlub: TNum,
  pidx: CUnionIter<(TNum, CTup2)>,
  //pdom: IHTreapSet<(TNum, CTup2)>,
  pset: IHTreapMap<CTup2, TNum>,
  ps2:  IHTreapMap<CTup2, IHTreapMap<CTup2, TNum>>,
  nidx: CUnionIter<(TNum, CTup2)>,
  //ndom: IHTreapSet<(TNum, CTup2)>,
  nset: IHTreapMap<CTup2, TNum>,
  ns2:  IHTreapMap<CTup2, IHTreapMap<CTup2, TNum>>,
  //flag: Option<(TNum, CTup2)>,
}

impl Rel2 {
  fn _patch(&mut self, _rel: CVar, shm: &mut STFrame) -> bool {
    //bench_patch_start();
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let mut nlub = self.nlub;
    let u_it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in u_it {
      for (_, np) in self.pidx.iter(nx) {
        let np_: &[CVar] = np.as_ref();
        let nx0 = np_[0];
        let nx1 = np_[1];
        match self.pset.get(&np) {
          None => {}
          Some(&t) => if ut > t {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.pidx.insert(nx0, (t, np));
            self.pidx.insert(nx1, (t, np));
            self.pset.insert(np, t);
            for (perm, _) in self.ps2.clone_iter() {
              let np = np.perm(perm.as_ref());
              match self.ps2.get_mut(&perm) {
                None => unreachable!(),
                Some(pset) => {
                  pset.insert(np, t);
                }
              }
            }
          }
        }
      }
      for (ot, op) in self.pidx.iter(ox) {
        match self.pset.get(&op) {
          None => {}
          Some(&ot) => {
            let np = op.swap_var(ox, nx);
            let np_: &[CVar] = np.as_ref();
            let nx0 = np_[0];
            let nx1 = np_[1];
            match self.pset.get(&np) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.pidx.insert(nx0, (t, np));
                self.pidx.insert(nx1, (t, np));
                self.pset.remove(&op);
                self.pset.insert(np, t);
                for (perm, _) in self.ps2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ps2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pset) => {
                      pset.remove(&op);
                      pset.insert(np, t);
                    }
                  }
                }
              }
              Some(&t) => if ut > t || ut > ot {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.pidx.insert(nx0, (t, np));
                self.pidx.insert(nx1, (t, np));
                self.pset.remove(&op);
                self.pset.insert(np, t);
                for (perm, _) in self.ps2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ps2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pset) => {
                      pset.remove(&op);
                      pset.insert(np, t);
                    }
                  }
                }
              }
            }
          }
        }
      }
      self.pidx.remove(ox);
      for (_, np) in self.nidx.iter(nx) {
        let np_: &[CVar] = np.as_ref();
        let nx0 = np_[0];
        let nx1 = np_[1];
        match self.nset.get(&np) {
          None => {}
          Some(&t) => if ut > t {
            patch = true;
            let t = shm.clk.fresh();
            nlub = t;
            self.nidx.insert(nx0, (t, np));
            self.nidx.insert(nx1, (t, np));
            self.nset.insert(np, t);
            for (perm, _) in self.ns2.clone_iter() {
              let np = np.perm(perm.as_ref());
              match self.ns2.get_mut(&perm) {
                None => unreachable!(),
                Some(nset) => {
                  nset.insert(np, t);
                }
              }
            }
          }
        }
      }
      for (ot, op) in self.nidx.iter(ox) {
        match self.nset.get(&op) {
          None => {}
          Some(&ot) => {
            let np = op.swap_var(ox, nx);
            let np_: &[CVar] = np.as_ref();
            let nx0 = np_[0];
            let nx1 = np_[1];
            match self.nset.get(&np) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                nlub = t;
                self.nidx.insert(nx0, (t, np));
                self.nidx.insert(nx1, (t, np));
                self.nset.remove(&op);
                self.nset.insert(np, t);
                for (perm, _) in self.ns2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ns2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(nset) => {
                      nset.remove(&op);
                      nset.insert(np, t);
                    }
                  }
                }
              }
              Some(&t) => if ut > t || ut > ot {
                patch = true;
                let t = shm.clk.fresh();
                nlub = t;
                self.nidx.insert(nx0, (t, np));
                self.nidx.insert(nx1, (t, np));
                self.nset.remove(&op);
                self.nset.insert(np, t);
                for (perm, _) in self.ns2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ns2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(nset) => {
                      nset.remove(&op);
                      nset.insert(np, t);
                    }
                  }
                }
              }
            }
          }
        }
      }
      self.nidx.remove(ox);
    }
    self.plub = plub;
    self.nlub = nlub;
    //bench_patch_stop();
    patch
  }
}

impl ERel for Rel2 {
  fn clone_ref(&self) -> ERelRef {
    Rc::new(self.clone())
  }

  fn arity(&self) -> usize {
    2
  }

  fn kind2(&self) -> (RelKind, RelKind2) {
    (RelKind::Rel, RelKind2::Exact)
  }

  fn pos_least_ub(&self, _shm: &STFrame) -> TNum {
    self.plub
  }

  fn neg_least_ub(&self, _shm: &STFrame) -> TNum {
    self.nlub
  }

  fn pos_tup_size(&self, _shm: &STFrame) -> u64 {
    self.pset.len() as u64
  }

  fn neg_tup_size(&self, _shm: &STFrame) -> u64 {
    self.nset.len() as u64
  }

  fn dump_tups(&self, rel: CVar, prefix: &str, _shm: &STFrame) {
    println!("{}Rel2::dump_tups: rel={} +{} -{}",
        prefix, rel.0, self.pset.len(), self.nset.len());
    for (xp, &t) in self.pset.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  + {} {:?}", prefix, t, xp_);
    }
    for (xp, &t) in self.nset.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  - {} {:?}", prefix, t, xp_);
    }
  }

  /*fn patch(&mut self, _rel: CVar, clk: &mut TClk, shm: &mut STFrame) {
    self._patch(_rel, clk, shm);
  }*/

  fn patchswap(&mut self, _rel: CVar, _newswap: &mut Vec<SNum>, shm: &mut STFrame) {
    self._patch(_rel, shm);
  }

  fn patch_swap(&mut self, _tlb: TNum, _rel: CVar, _newswap: &mut dyn ESwap, shm: &mut STFrame) {
    self._patch(_rel, shm);
  }

  /*fn flag_tup(&mut self, _rel: CVar, tup: &mut [SNum]) -> Option<TNum> {
    match self.flag {
      None => {
        None
      }
      Some((t, xp)) => {
        tup.copy_from_slice(xp.as_ref());
        Some(t)
      }
    }
  }*/

  fn flag_tup(&mut self, _rel: CVar, _tup: &mut [SNum]) -> Option<TNum> {
    None
  }

  fn test_pos_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(_rel, clk, shm);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let xp = CTup2([x0, x1]);
      match self.pset.get(&xp) {
        None => {}
        Some(&t) => {
          return Some(t);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn test_neg_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(_rel, clk, shm);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let xp = CTup2([x0, x1]);
      match self.nset.get(&xp) {
        None => {}
        Some(&t) => {
          return Some(t);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn scan_pos(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup2::from(ubtup);
    let iter = self.pset.clone_iter_from(lbtup);
    let scan = Box::new(RScan2{ub, iter});
    scan
  }

  fn scan_neg(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup2::from(ubtup);
    let iter = self.nset.clone_iter_from(lbtup);
    let scan = Box::new(RScan2{ub, iter});
    scan
  }

  fn permscan_pos(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    match self.ps2.get(perm) {
      None => {
        let mut pset = IHTreapMap::default();
        for (xp, &t) in self.pset.iter() {
          let xp = xp.perm(perm);
          pset.insert(xp, t);
        }
        self.ps2.insert(CTup2::from(perm), pset);
      }
      Some(_) => {}
    }
    match self.ps2.get(perm) {
      None => unreachable!(),
      Some(pset) => {
        let ub = CTup2::from(ubtup);
        let iter = pset.clone_iter_from(lbtup);
        let scan = Box::new(RScan2{ub, iter});
        scan
      }
    }
  }

  fn permscan_neg(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    match self.ns2.get(perm) {
      None => {
        let mut nset = IHTreapMap::default();
        for (xp, &t) in self.nset.iter() {
          let xp = xp.perm(perm);
          nset.insert(xp, t);
        }
        self.ns2.insert(CTup2::from(perm), nset);
      }
      Some(_) => {}
    }
    match self.ns2.get(perm) {
      None => unreachable!(),
      Some(nset) => {
        let ub = CTup2::from(ubtup);
        let iter = nset.clone_iter_from(lbtup);
        let scan = Box::new(RScan2{ub, iter});
        scan
      }
    }
  }

  fn scan_par(&self, _rel: CVar, _shm: &STFrame) -> EScanBox {
    let ub = CTup2::ub();
    let iter = self.pset.merge_intersection(&self.nset, &mut |_, &lt, &rt| max(lt, rt)).clone_iter();
    let scan = Box::new(RScan2{ub, iter});
    scan
  }

  fn swap_pos_tup(&mut self, _rec: CVar, _rel: CVar, tup: &[SNum], _newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(_rel, clk, shm);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let xp = CTup2([x0, x1]);
      match self.pset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.pidx.insert(x0, (t, xp));
          self.pidx.insert(x1, (t, xp));
          //self.pdom.insert((t, xp));
          self.pset.insert(xp, t);
          for (perm, _) in self.ps2.clone_iter() {
            let xp = xp.perm(perm.as_ref());
            match self.ps2.get_mut(&perm) {
              None => unreachable!(),
              Some(pset) => {
                pset.insert(xp, t);
              }
            }
          }
          //self._flag_pos(_rel, t, xp, shm);
          swaptup.extend_from_slice(xp.as_ref());
          Some(t)
        }
        Some(&t) => {
          None
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup(&mut self, _rec: CVar, _rel: CVar, tup: &[SNum], _newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(_rel, clk, shm);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let xp = CTup2([x0, x1]);
      match self.nset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.nlub = t;
          self.nidx.insert(x0, (t, xp));
          self.nidx.insert(x1, (t, xp));
          //self.ndom.insert((t, xp));
          self.nset.insert(xp, t);
          for (perm, _) in self.ns2.clone_iter() {
            let xp = xp.perm(perm.as_ref());
            match self.ns2.get_mut(&perm) {
              None => unreachable!(),
              Some(nset) => {
                nset.insert(xp, t);
              }
            }
          }
          //self._flag_neg(_rec, _rel, t, xp, shm);
          swaptup.extend_from_slice(xp.as_ref());
          Some(t)
        }
        Some(&t) => {
          None
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_pos_tup_(&mut self, tlb: TNum, _rec: CVar, _rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[k0, k1] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let xp = CTup2([x0, x1]);
      match self.pset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.pidx.insert(x0, (t, xp));
          self.pidx.insert(x1, (t, xp));
          //self.pdom.insert((t, xp));
          self.pset.insert(xp, t);
          for (perm, _) in self.ps2.clone_iter() {
            let xp = xp.perm(perm.as_ref());
            match self.ps2.get_mut(&perm) {
              None => unreachable!(),
              Some(pset) => {
                pset.insert(xp, t);
              }
            }
          }
          //self._flag_pos(_rel, t, xp, shm);
          swaptup.extend_from_slice(xp.as_ref());
          (Fresh, t)
        }
        Some(&t) => if t >= tlb {
          swaptup.extend_from_slice(xp.as_ref());
          (Stale, t)
        } else {
          (Noswap, 0)
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup_(&mut self, tlb: TNum, _rec: CVar, _rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[k0, k1] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let xp = CTup2([x0, x1]);
      match self.nset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.nlub = t;
          self.nidx.insert(x0, (t, xp));
          self.nidx.insert(x1, (t, xp));
          //self.ndom.insert((t, xp));
          self.nset.insert(xp, t);
          for (perm, _) in self.ns2.clone_iter() {
            let xp = xp.perm(perm.as_ref());
            match self.ns2.get_mut(&perm) {
              None => unreachable!(),
              Some(nset) => {
                nset.insert(xp, t);
              }
            }
          }
          //self._flag_neg(_rec, _rel, t, xp, shm);
          swaptup.extend_from_slice(xp.as_ref());
          (Fresh, t)
        }
        Some(&t) => if t >= tlb {
          swaptup.extend_from_slice(xp.as_ref());
          (Stale, t)
        } else {
          (Noswap, 0)
        }
      }
    } else {
      unreachable!();
    }
  }
}

#[derive(Clone, Default)]
pub struct SymmRel2 {
  chk:  TUSnapshot,
  attr: IHTreapMap<TNum, CVar>,
  plub: TNum,
  nlub: TNum,
  pidx: CUnionIter<(TNum, CTup2)>,
  pset: IHTreapMap<CTup2, TNum>,
  nidx: CUnionIter<(TNum, CTup2)>,
  nset: IHTreapMap<CTup2, TNum>,
  //flag: Option<(TNum, CTup2)>,
}

// TODO

impl SymmRel2 {
  fn _patch(&mut self, _rel: CVar, shm: &mut STFrame) -> bool {
    //bench_patch_start();
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let mut nlub = self.nlub;
    let u_it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in u_it {
      for (_, np) in self.pidx.iter(nx) {
        let np_: &[CVar] = np.as_ref();
        let nx0 = np_[0];
        let nx1 = np_[1];
        match self.pset.get(&np) {
          None => {}
          Some(&t) => if ut > t {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.pidx.insert(nx0, (t, np));
            self.pidx.insert(nx1, (t, np));
            self.pset.insert(np, t);
          }
        }
      }
      for (ot, op) in self.pidx.iter(ox) {
        match self.pset.get(&op) {
          None => {}
          Some(&ot) => {
            let np = op.swap_var(ox, nx);
            let np_: &[CVar] = np.as_ref();
            let nx0 = np_[0];
            let nx1 = np_[1];
            match self.pset.get(&np) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.pidx.insert(nx0, (t, np));
                self.pidx.insert(nx1, (t, np));
                self.pset.remove(&op);
                self.pset.insert(np, t);
              }
              Some(&t) => if ut > t || ut > ot {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.pidx.insert(nx0, (t, np));
                self.pidx.insert(nx1, (t, np));
                self.pset.remove(&op);
                self.pset.insert(np, t);
              }
            }
          }
        }
      }
      self.pidx.remove(ox);
      for (_, np) in self.nidx.iter(nx) {
        let np_: &[CVar] = np.as_ref();
        let nx0 = np_[0];
        let nx1 = np_[1];
        match self.nset.get(&np) {
          None => {}
          Some(&t) => if ut > t {
            patch = true;
            let t = shm.clk.fresh();
            nlub = t;
            self.nidx.insert(nx0, (t, np));
            self.nidx.insert(nx1, (t, np));
            self.nset.insert(np, t);
          }
        }
      }
      for (ot, op) in self.nidx.iter(ox) {
        match self.nset.get(&op) {
          None => {}
          Some(&ot) => {
            let np = op.swap_var(ox, nx);
            let np_: &[CVar] = np.as_ref();
            let nx0 = np_[0];
            let nx1 = np_[1];
            match self.nset.get(&np) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                nlub = t;
                self.nidx.insert(nx0, (t, np));
                self.nidx.insert(nx1, (t, np));
                self.nset.remove(&op);
                self.nset.insert(np, t);
              }
              Some(&t) => if ut > t || ut > ot {
                patch = true;
                let t = shm.clk.fresh();
                nlub = t;
                self.nidx.insert(nx0, (t, np));
                self.nidx.insert(nx1, (t, np));
                self.nset.remove(&op);
                self.nset.insert(np, t);
              }
            }
          }
        }
      }
      self.nidx.remove(ox);
    }
    self.plub = plub;
    self.nlub = nlub;
    //bench_patch_stop();
    patch
  }
}

impl ERel for SymmRel2 {
  fn clone_ref(&self) -> ERelRef {
    Rc::new(self.clone())
  }

  fn arity(&self) -> usize {
    2
  }

  fn kind2(&self) -> (RelKind, RelKind2) {
    (RelKind::Rel, RelKind2::Symm)
  }

  fn pos_least_ub(&self, _shm: &STFrame) -> TNum {
    self.plub
  }

  fn neg_least_ub(&self, _shm: &STFrame) -> TNum {
    self.nlub
  }

  fn pos_tup_size(&self, _shm: &STFrame) -> u64 {
    self.pset.len() as u64
  }

  fn neg_tup_size(&self, _shm: &STFrame) -> u64 {
    self.nset.len() as u64
  }

  fn dump_tups(&self, rel: CVar, prefix: &str, _shm: &STFrame) {
    println!("{}SymmRel2::dump_tups: rel={} +{} -{}",
        prefix, rel.0, self.pset.len(), self.nset.len());
    for (xp, &t) in self.pset.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  + {} {:?}", prefix, t, xp_);
    }
    for (xp, &t) in self.nset.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  - {} {:?}", prefix, t, xp_);
    }
  }

  /*fn patch(&mut self, _rel: CVar, shm: &mut STFrame) {
    self._patch(&shm.cc, &mut shm.clk);
  }*/

  fn patchswap(&mut self, _rel: CVar, _newswap: &mut Vec<SNum>, shm: &mut STFrame) {
    self._patch(_rel, shm);
  }

  fn patch_swap(&mut self, _tlb: TNum, _rel: CVar, _newswap: &mut dyn ESwap, shm: &mut STFrame) {
    self._patch(_rel, shm);
  }

  /*fn flag_tup(&mut self, _rel: CVar, tup: &mut [SNum]) -> Option<TNum> {
    match self.flag {
      None => {
        None
      }
      Some((t, xp)) => {
        tup.copy_from_slice(xp.as_ref());
        Some(t)
      }
    }
  }*/

  fn flag_tup(&mut self, _rel: CVar, _tup: &mut [SNum]) -> Option<TNum> {
    None
  }

  fn test_pos_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let xp = CTup2([x0, x1]);
      match self.pset.get(&xp) {
        None => {}
        Some(&t) => {
          return Some(t);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn test_neg_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let xp = CTup2([x0, x1]);
      match self.nset.get(&xp) {
        None => {}
        Some(&t) => {
          return Some(t);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn scan_pos(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup2::from(ubtup);
    let iter = self.pset.clone_iter_from(lbtup);
    let scan = Box::new(RScan2{ub, iter});
    scan
  }

  fn scan_neg(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup2::from(ubtup);
    let iter = self.nset.clone_iter_from(lbtup);
    let scan = Box::new(RScan2{ub, iter});
    scan
  }

  fn permscan_pos(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    self.scan_pos(_rel, lbtup, ubtup, _shm)
  }

  fn permscan_neg(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    self.scan_neg(_rel, lbtup, ubtup, _shm)
  }

  fn scan_par(&self, _rel: CVar, _shm: &STFrame) -> EScanBox {
    let ub = CTup2::ub();
    let iter = self.pset.merge_intersection(&self.nset, &mut |_, &lt, &rt| max(lt, rt)).clone_iter();
    let scan = Box::new(RScan2{ub, iter});
    scan
  }

  fn swap_pos_tup(&mut self, _rec: CVar, _rel: CVar, tup: &[SNum], _newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let mut xp = CTup2([x0, x1]).sort();
      let mut ret = None;
      loop {
        match self.pset.get(&xp) {
          None => {
            let t = shm.clk.fresh();
            self.plub = t;
            self.pidx.insert(x0, (t, xp));
            self.pidx.insert(x1, (t, xp));
            self.pset.insert(xp, t);
            swaptup.extend_from_slice(xp.as_ref());
            ret = Some(t);
          }
          Some(_) => {}
        }
        let xp_: &mut [SNum] = xp.as_mut();
        if next_permutation(xp_).is_none() {
          break;
        }
      }
      ret
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup(&mut self, _rec: CVar, _rel: CVar, tup: &[SNum], _newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let mut xp = CTup2([x0, x1]).sort();
      let mut ret = None;
      loop {
        match self.nset.get(&xp) {
          None => {
            let t = shm.clk.fresh();
            self.nlub = t;
            self.nidx.insert(x0, (t, xp));
            self.nidx.insert(x1, (t, xp));
            self.nset.insert(xp, t);
            swaptup.extend_from_slice(xp.as_ref());
            ret = Some(t);
          }
          Some(_) => {}
        }
        let xp_: &mut [SNum] = xp.as_mut();
        if next_permutation(xp_).is_none() {
          break;
        }
      }
      ret
    } else {
      unreachable!();
    }
  }

  fn swap_pos_tup_(&mut self, tlb: TNum, _rec: CVar, _rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[k0, k1] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let mut xp = CTup2([x0, x1]).sort();
      let mut fresh = None;
      let mut stale = None;
      loop {
        match self.pset.get(&xp) {
          None => {
            let t = shm.clk.fresh();
            self.plub = t;
            self.pidx.insert(x0, (t, xp));
            self.pidx.insert(x1, (t, xp));
            self.pset.insert(xp, t);
            //swaptup.extend_from_slice(xp.as_ref());
            fresh = Some(t);
          }
          Some(&t) => if t >= tlb {
            //swaptup.extend_from_slice(xp.as_ref());
            stale = Some(t);
          }
        }
        swaptup.extend_from_slice(xp.as_ref());
        let xp_: &mut [SNum] = xp.as_mut();
        if next_permutation(xp_).is_none() {
          break;
        }
      }
      _from_fresh_stale(fresh, stale)
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup_(&mut self, tlb: TNum, _rec: CVar, _rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[k0, k1] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let mut xp = CTup2([x0, x1]).sort();
      let mut fresh = None;
      let mut stale = None;
      loop {
        match self.nset.get(&xp) {
          None => {
            let t = shm.clk.fresh();
            self.nlub = t;
            self.nidx.insert(x0, (t, xp));
            self.nidx.insert(x1, (t, xp));
            self.nset.insert(xp, t);
            //swaptup.extend_from_slice(xp.as_ref());
            fresh = Some(t);
          }
          Some(&t) => if t >= tlb {
            //swaptup.extend_from_slice(xp.as_ref());
            stale = Some(t);
          }
        }
        swaptup.extend_from_slice(xp.as_ref());
        let xp_: &mut [SNum] = xp.as_mut();
        if next_permutation(xp_).is_none() {
          break;
        }
      }
      _from_fresh_stale(fresh, stale)
    } else {
      unreachable!();
    }
  }
}

pub struct RScan3 {
  ub:   CTup3,
  iter: IHTreapMapCloneIter<CTup3, TNum>,
}

impl EScan for RScan3 {
  fn next_tup(&mut self, tup: &mut [SNum], /*shm: &mut STFrame*/) -> TScanResult {
    match self.iter.next() {
      None => {
        End
      }
      Some((xp, t)) => if xp > self.ub {
        End
      } else {
        tup.copy_from_slice(xp.as_ref());
        Hit(t)
      }
    }
  }
}

#[derive(Clone, Default)]
pub struct Rel3 {
  chk:  TUSnapshot,
  attr: IHTreapMap<TNum, CVar>,
  plub: TNum,
  nlub: TNum,
  pidx: CUnionIter<(TNum, CTup3)>,
  //pdom: IHTreapSet<(TNum, CTup3)>,
  pset: IHTreapMap<CTup3, TNum>,
  ps2:  IHTreapMap<CTup3, IHTreapMap<CTup3, TNum>>,
  nidx: CUnionIter<(TNum, CTup3)>,
  //ndom: IHTreapSet<(TNum, CTup3)>,
  nset: IHTreapMap<CTup3, TNum>,
  ns2:  IHTreapMap<CTup3, IHTreapMap<CTup3, TNum>>,
  //flag: Option<(TNum, CTup3)>,
}

impl Rel3 {
  fn _patch(&mut self, _rel: CVar, shm: &mut STFrame) -> bool {
    //bench_patch_start();
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let mut nlub = self.nlub;
    let u_it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in u_it {
      for (_, np) in self.pidx.iter(nx) {
        let np_: &[CVar] = np.as_ref();
        let nx0 = np_[0];
        let nx1 = np_[1];
        let nx2 = np_[2];
        match self.pset.get(&np) {
          None => {}
          Some(&t) => if ut > t {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.pidx.insert(nx0, (t, np));
            self.pidx.insert(nx1, (t, np));
            self.pidx.insert(nx2, (t, np));
            self.pset.insert(np, t);
            for (perm, _) in self.ps2.clone_iter() {
              let np = np.perm(perm.as_ref());
              match self.ps2.get_mut(&perm) {
                None => unreachable!(),
                Some(pset) => {
                  pset.insert(np, t);
                }
              }
            }
          }
        }
      }
      for (ot, op) in self.pidx.iter(ox) {
        match self.pset.get(&op) {
          None => {}
          Some(&ot) => {
            let np = op.swap_var(ox, nx);
            let np_: &[CVar] = np.as_ref();
            let nx0 = np_[0];
            let nx1 = np_[1];
            let nx2 = np_[2];
            match self.pset.get(&np) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.pidx.insert(nx0, (t, np));
                self.pidx.insert(nx1, (t, np));
                self.pidx.insert(nx2, (t, np));
                self.pset.remove(&op);
                self.pset.insert(np, t);
                for (perm, _) in self.ps2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ps2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pset) => {
                      pset.remove(&op);
                      pset.insert(np, t);
                    }
                  }
                }
              }
              Some(&t) => if ut > t || ut > ot {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.pidx.insert(nx0, (t, np));
                self.pidx.insert(nx1, (t, np));
                self.pidx.insert(nx2, (t, np));
                self.pset.remove(&op);
                self.pset.insert(np, t);
                for (perm, _) in self.ps2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ps2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pset) => {
                      pset.remove(&op);
                      pset.insert(np, t);
                    }
                  }
                }
              }
            }
          }
        }
      }
      self.pidx.remove(ox);
      for (_, np) in self.nidx.iter(nx) {
        let np_: &[CVar] = np.as_ref();
        let nx0 = np_[0];
        let nx1 = np_[1];
        let nx2 = np_[2];
        match self.nset.get(&np) {
          None => {}
          Some(&t) => if ut > t {
            patch = true;
            let t = shm.clk.fresh();
            nlub = t;
            self.nidx.insert(nx0, (t, np));
            self.nidx.insert(nx1, (t, np));
            self.nidx.insert(nx2, (t, np));
            self.nset.insert(np, t);
            for (perm, _) in self.ns2.clone_iter() {
              let np = np.perm(perm.as_ref());
              match self.ns2.get_mut(&perm) {
                None => unreachable!(),
                Some(nset) => {
                  nset.insert(np, t);
                }
              }
            }
          }
        }
      }
      for (ot, op) in self.nidx.iter(ox) {
        match self.nset.get(&op) {
          None => {}
          Some(&ot) => {
            let np = op.swap_var(ox, nx);
            let np_: &[CVar] = np.as_ref();
            let nx0 = np_[0];
            let nx1 = np_[1];
            let nx2 = np_[2];
            match self.nset.get(&np) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                nlub = t;
                self.nidx.insert(nx0, (t, np));
                self.nidx.insert(nx1, (t, np));
                self.nidx.insert(nx2, (t, np));
                self.nset.remove(&op);
                self.nset.insert(np, t);
                for (perm, _) in self.ns2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ns2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(nset) => {
                      nset.remove(&op);
                      nset.insert(np, t);
                    }
                  }
                }
              }
              Some(&t) => if ut > t || ut > ot {
                patch = true;
                let t = shm.clk.fresh();
                nlub = t;
                self.nidx.insert(nx0, (t, np));
                self.nidx.insert(nx1, (t, np));
                self.nidx.insert(nx2, (t, np));
                self.nset.remove(&op);
                self.nset.insert(np, t);
                for (perm, _) in self.ns2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ns2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(nset) => {
                      nset.remove(&op);
                      nset.insert(np, t);
                    }
                  }
                }
              }
            }
          }
        }
      }
      self.nidx.remove(ox);
    }
    self.plub = plub;
    self.nlub = nlub;
    //bench_patch_stop();
    patch
  }
}

impl ERel for Rel3 {
  fn clone_ref(&self) -> ERelRef {
    Rc::new(self.clone())
  }

  fn arity(&self) -> usize {
    3
  }

  fn kind2(&self) -> (RelKind, RelKind2) {
    (RelKind::Rel, RelKind2::Exact)
  }

  fn pos_least_ub(&self, _shm: &STFrame) -> TNum {
    self.plub
  }

  fn neg_least_ub(&self, _shm: &STFrame) -> TNum {
    self.nlub
  }

  fn pos_tup_size(&self, _shm: &STFrame) -> u64 {
    self.pset.len() as u64
  }

  fn neg_tup_size(&self, _shm: &STFrame) -> u64 {
    self.nset.len() as u64
  }

  fn dump_tups(&self, rel: CVar, prefix: &str, _shm: &STFrame) {
    println!("{}Rel3::dump_tups: rel={} +{} -{}",
        prefix, rel.0, self.pset.len(), self.nset.len());
    for (xp, &t) in self.pset.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  + {} {:?}", prefix, t, xp_);
    }
    for (xp, &t) in self.nset.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  - {} {:?}", prefix, t, xp_);
    }
  }

  /*fn patch(&mut self, _rel: CVar, shm: &mut STFrame) {
    self._patch(&shm.cc, &mut shm.clk);
  }*/

  fn patchswap(&mut self, _rel: CVar, _newswap: &mut Vec<SNum>, shm: &mut STFrame) {
    self._patch(_rel, shm);
  }

  fn patch_swap(&mut self, _tlb: TNum, _rel: CVar, _newswap: &mut dyn ESwap, shm: &mut STFrame) {
    self._patch(_rel, shm);
  }

  /*fn flag_tup(&mut self, _rel: CVar, tup: &mut [SNum]) -> Option<TNum> {
    match self.flag {
      None => {
        None
      }
      Some((t, xp)) => {
        tup.copy_from_slice(xp.as_ref());
        Some(t)
      }
    }
  }*/

  fn flag_tup(&mut self, _rel: CVar, _tup: &mut [SNum]) -> Option<TNum> {
    None
  }

  fn test_pos_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let xp = CTup3([x0, x1, x2]);
      match self.pset.get(&xp) {
        None => {}
        Some(&t) => {
          return Some(t);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn test_neg_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let xp = CTup3([x0, x1, x2]);
      match self.nset.get(&xp) {
        None => {}
        Some(&t) => {
          return Some(t);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn scan_pos(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup3::from(ubtup);
    let iter = self.pset.clone_iter_from(lbtup);
    let scan = Box::new(RScan3{ub, iter});
    scan
  }

  fn scan_neg(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup3::from(ubtup);
    let iter = self.nset.clone_iter_from(lbtup);
    let scan = Box::new(RScan3{ub, iter});
    scan
  }

  fn permscan_pos(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    match self.ps2.get(perm) {
      None => {
        let mut pset = IHTreapMap::default();
        for (xp, &t) in self.pset.iter() {
          let xp = xp.perm(perm);
          pset.insert(xp, t);
        }
        self.ps2.insert(CTup3::from(perm), pset);
      }
      Some(_) => {}
    }
    match self.ps2.get(perm) {
      None => unreachable!(),
      Some(pset) => {
        let ub = CTup3::from(ubtup);
        let iter = pset.clone_iter_from(lbtup);
        let scan = Box::new(RScan3{ub, iter});
        scan
      }
    }
  }

  fn permscan_neg(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    match self.ns2.get(perm) {
      None => {
        let mut nset = IHTreapMap::default();
        for (xp, &t) in self.nset.iter() {
          let xp = xp.perm(perm);
          nset.insert(xp, t);
        }
        self.ns2.insert(CTup3::from(perm), nset);
      }
      Some(_) => {}
    }
    match self.ns2.get(perm) {
      None => unreachable!(),
      Some(nset) => {
        let ub = CTup3::from(ubtup);
        let iter = nset.clone_iter_from(lbtup);
        let scan = Box::new(RScan3{ub, iter});
        scan
      }
    }
  }

  fn scan_par(&self, _rel: CVar, _shm: &STFrame) -> EScanBox {
    let ub = CTup3::ub();
    let iter = self.pset.merge_intersection(&self.nset, &mut |_, &lt, &rt| max(lt, rt)).clone_iter();
    let scan = Box::new(RScan3{ub, iter});
    scan
  }

  fn swap_pos_tup(&mut self, _rec: CVar, _rel: CVar, tup: &[SNum], _newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let xp = CTup3([x0, x1, x2]);
      match self.pset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.pidx.insert(x0, (t, xp));
          self.pidx.insert(x1, (t, xp));
          self.pidx.insert(x2, (t, xp));
          //self.pdom.insert((t, xp));
          self.pset.insert(xp, t);
          swaptup.extend_from_slice(xp.as_ref());
          Some(t)
        }
        Some(_) => {
          None
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup(&mut self, _rec: CVar, _rel: CVar, tup: &[SNum], _newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let xp = CTup3([x0, x1, x2]);
      match self.nset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.nlub = t;
          self.nidx.insert(x0, (t, xp));
          self.nidx.insert(x1, (t, xp));
          self.nidx.insert(x2, (t, xp));
          //self.ndom.insert((t, xp));
          self.nset.insert(xp, t);
          swaptup.extend_from_slice(xp.as_ref());
          Some(t)
        }
        Some(_) => {
          None
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_pos_tup_(&mut self, tlb: TNum, _rec: CVar, _rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[k0, k1, k2] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let xp = CTup3([x0, x1, x2]);
      match self.pset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.pidx.insert(x0, (t, xp));
          self.pidx.insert(x1, (t, xp));
          self.pidx.insert(x2, (t, xp));
          //self.pdom.insert((t, xp));
          self.pset.insert(xp, t);
          swaptup.extend_from_slice(xp.as_ref());
          (Fresh, t)
        }
        Some(&t) => if t >= tlb {
          swaptup.extend_from_slice(xp.as_ref());
          (Stale, t)
        } else {
          (Noswap, 0)
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup_(&mut self, tlb: TNum, _rec: CVar, _rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[k0, k1, k2] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let xp = CTup3([x0, x1, x2]);
      match self.nset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.nlub = t;
          self.nidx.insert(x0, (t, xp));
          self.nidx.insert(x1, (t, xp));
          self.nidx.insert(x2, (t, xp));
          //self.ndom.insert((t, xp));
          self.nset.insert(xp, t);
          swaptup.extend_from_slice(xp.as_ref());
          (Fresh, t)
        }
        Some(&t) => if t >= tlb {
          swaptup.extend_from_slice(xp.as_ref());
          (Stale, t)
        } else {
          (Noswap, 0)
        }
      }
    } else {
      unreachable!();
    }
  }
}

#[derive(Clone, Default)]
pub struct SymmRel3 {
  chk:  TUSnapshot,
  attr: IHTreapMap<TNum, CVar>,
  plub: TNum,
  nlub: TNum,
  pidx: CUnionIter<(TNum, CTup3)>,
  pset: IHTreapMap<CTup3, TNum>,
  nidx: CUnionIter<(TNum, CTup3)>,
  nset: IHTreapMap<CTup3, TNum>,
  //flag: Option<(TNum, CTup3)>,
}

// TODO

impl SymmRel3 {
  fn _patch(&mut self, _rel: CVar, shm: &mut STFrame) -> bool {
    //bench_patch_start();
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let mut nlub = self.nlub;
    let u_it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in u_it {
      for (_, np) in self.pidx.iter(nx) {
        let np_: &[CVar] = np.as_ref();
        let nx0 = np_[0];
        let nx1 = np_[1];
        let nx2 = np_[2];
        match self.pset.get(&np) {
          None => {}
          Some(&t) => if ut > t {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.pidx.insert(nx0, (t, np));
            self.pidx.insert(nx1, (t, np));
            self.pidx.insert(nx2, (t, np));
            self.pset.insert(np, t);
          }
        }
      }
      for (ot, op) in self.pidx.iter(ox) {
        match self.pset.get(&op) {
          None => {}
          Some(&ot) => {
            let np = op.swap_var(ox, nx);
            let np_: &[CVar] = np.as_ref();
            let nx0 = np_[0];
            let nx1 = np_[1];
            let nx2 = np_[2];
            match self.pset.get(&np) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.pidx.insert(nx0, (t, np));
                self.pidx.insert(nx1, (t, np));
                self.pidx.insert(nx2, (t, np));
                self.pset.remove(&op);
                self.pset.insert(np, t);
              }
              Some(&t) => if ut > t || ut > ot {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.pidx.insert(nx0, (t, np));
                self.pidx.insert(nx1, (t, np));
                self.pidx.insert(nx2, (t, np));
                self.pset.remove(&op);
                self.pset.insert(np, t);
              }
            }
          }
        }
      }
      self.pidx.remove(ox);
      for (_, np) in self.nidx.iter(nx) {
        let np_: &[CVar] = np.as_ref();
        let nx0 = np_[0];
        let nx1 = np_[1];
        let nx2 = np_[2];
        match self.nset.get(&np) {
          None => {}
          Some(&t) => if ut > t {
            patch = true;
            let t = shm.clk.fresh();
            nlub = t;
            self.nidx.insert(nx0, (t, np));
            self.nidx.insert(nx1, (t, np));
            self.nidx.insert(nx2, (t, np));
            self.nset.insert(np, t);
          }
        }
      }
      for (ot, op) in self.nidx.iter(ox) {
        match self.nset.get(&op) {
          None => {}
          Some(&ot) => {
            let np = op.swap_var(ox, nx);
            let np_: &[CVar] = np.as_ref();
            let nx0 = np_[0];
            let nx1 = np_[1];
            let nx2 = np_[2];
            match self.nset.get(&np) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                nlub = t;
                self.nidx.insert(nx0, (t, np));
                self.nidx.insert(nx1, (t, np));
                self.nidx.insert(nx2, (t, np));
                self.nset.remove(&op);
                self.nset.insert(np, t);
              }
              Some(&t) => if ut > t || ut > ot {
                patch = true;
                let t = shm.clk.fresh();
                nlub = t;
                self.nidx.insert(nx0, (t, np));
                self.nidx.insert(nx1, (t, np));
                self.nidx.insert(nx2, (t, np));
                self.nset.remove(&op);
                self.nset.insert(np, t);
              }
            }
          }
        }
      }
      self.nidx.remove(ox);
    }
    self.plub = plub;
    self.nlub = nlub;
    //bench_patch_stop();
    patch
  }
}

impl ERel for SymmRel3 {
  fn clone_ref(&self) -> ERelRef {
    Rc::new(self.clone())
  }

  fn arity(&self) -> usize {
    3
  }

  fn kind2(&self) -> (RelKind, RelKind2) {
    (RelKind::Rel, RelKind2::Symm)
  }

  fn pos_least_ub(&self, _shm: &STFrame) -> TNum {
    self.plub
  }

  fn neg_least_ub(&self, _shm: &STFrame) -> TNum {
    self.nlub
  }

  fn pos_tup_size(&self, _shm: &STFrame) -> u64 {
    self.pset.len() as u64
  }

  fn neg_tup_size(&self, _shm: &STFrame) -> u64 {
    self.nset.len() as u64
  }

  fn dump_tups(&self, rel: CVar, prefix: &str, _shm: &STFrame) {
    println!("{}SymmRel3::dump_tups: rel={} +{} -{}",
        prefix, rel.0, self.pset.len(), self.nset.len());
    for (xp, &t) in self.pset.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  + {} {:?}", prefix, t, xp_);
    }
    for (xp, &t) in self.nset.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  - {} {:?}", prefix, t, xp_);
    }
  }

  /*fn patch(&mut self, _rel: CVar, clk: &mut TClk, shm: &mut STFrame) {
    self._patch(&shm.cc, clk);
  }*/

  fn patchswap(&mut self, _rel: CVar, _newswap: &mut Vec<SNum>, shm: &mut STFrame) {
    self._patch(_rel, shm);
  }

  fn patch_swap(&mut self, _tlb: TNum, _rel: CVar, _newswap: &mut dyn ESwap, shm: &mut STFrame) {
    self._patch(_rel, shm);
  }

  /*fn flag_tup(&mut self, _rel: CVar, tup: &mut [SNum]) -> Option<TNum> {
    match self.flag {
      None => {
        None
      }
      Some((t, xp)) => {
        tup.copy_from_slice(xp.as_ref());
        Some(t)
      }
    }
  }*/

  fn flag_tup(&mut self, _rel: CVar, _tup: &mut [SNum]) -> Option<TNum> {
    None
  }

  fn test_pos_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let xp = CTup3([x0, x1, x2]);
      match self.pset.get(&xp) {
        None => {}
        Some(&t) => {
          return Some(t);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn test_neg_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let xp = CTup3([x0, x1, x2]);
      match self.nset.get(&xp) {
        None => {}
        Some(&t) => {
          return Some(t);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn scan_pos(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup3::from(ubtup);
    let iter = self.pset.clone_iter_from(lbtup);
    let scan = Box::new(RScan3{ub, iter});
    scan
  }

  fn scan_neg(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup3::from(ubtup);
    let iter = self.nset.clone_iter_from(lbtup);
    let scan = Box::new(RScan3{ub, iter});
    scan
  }

  fn permscan_pos(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    self.scan_pos(_rel, lbtup, ubtup, _shm)
  }

  fn permscan_neg(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    self.scan_neg(_rel, lbtup, ubtup, _shm)
  }

  fn scan_par(&self, _rel: CVar, _shm: &STFrame) -> EScanBox {
    let ub = CTup3::ub();
    let iter = self.pset.merge_intersection(&self.nset, &mut |_, &lt, &rt| max(lt, rt)).clone_iter();
    let scan = Box::new(RScan3{ub, iter});
    scan
  }

  fn swap_pos_tup(&mut self, _rec: CVar, _rel: CVar, tup: &[SNum], _newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let mut xp = CTup3([x0, x1, x2]).sort();
      let mut ret = None;
      loop {
        match self.pset.get(&xp) {
          None => {
            let t = shm.clk.fresh();
            self.plub = t;
            self.pidx.insert(x0, (t, xp));
            self.pidx.insert(x1, (t, xp));
            self.pidx.insert(x2, (t, xp));
            self.pset.insert(xp, t);
            swaptup.extend_from_slice(xp.as_ref());
            ret = Some(t);
          }
          Some(_) => {}
        }
        let xp_: &mut [SNum] = xp.as_mut();
        if next_permutation(xp_).is_none() {
          break;
        }
      }
      ret
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup(&mut self, _rec: CVar, _rel: CVar, tup: &[SNum], _newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let mut xp = CTup3([x0, x1, x2]).sort();
      let mut ret = None;
      loop {
        match self.nset.get(&xp) {
          None => {
            let t = shm.clk.fresh();
            self.nlub = t;
            self.nidx.insert(x0, (t, xp));
            self.nidx.insert(x1, (t, xp));
            self.nidx.insert(x2, (t, xp));
            self.nset.insert(xp, t);
            swaptup.extend_from_slice(xp.as_ref());
            ret = Some(t);
          }
          Some(_) => {}
        }
        let xp_: &mut [SNum] = xp.as_mut();
        if next_permutation(xp_).is_none() {
          break;
        }
      }
      ret
    } else {
      unreachable!();
    }
  }

  fn swap_pos_tup_(&mut self, tlb: TNum, _rec: CVar, _rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[k0, k1, k2] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let mut xp = CTup3([x0, x1, x2]).sort();
      let mut fresh = None;
      let mut stale = None;
      loop {
        match self.pset.get(&xp) {
          None => {
            let t = shm.clk.fresh();
            self.plub = t;
            self.pidx.insert(x0, (t, xp));
            self.pidx.insert(x1, (t, xp));
            self.pidx.insert(x2, (t, xp));
            self.pset.insert(xp, t);
            //swaptup.extend_from_slice(xp.as_ref());
            fresh = Some(t);
          }
          Some(&t) => if t >= tlb {
            //swaptup.extend_from_slice(xp.as_ref());
            stale = Some(t);
          }
        }
        swaptup.extend_from_slice(xp.as_ref());
        let xp_: &mut [SNum] = xp.as_mut();
        if next_permutation(xp_).is_none() {
          break;
        }
      }
      _from_fresh_stale(fresh, stale)
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup_(&mut self, tlb: TNum, _rec: CVar, _rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[k0, k1, k2] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let mut xp = CTup3([x0, x1, x2]).sort();
      let mut fresh = None;
      let mut stale = None;
      loop {
        match self.nset.get(&xp) {
          None => {
            let t = shm.clk.fresh();
            self.nlub = t;
            self.nidx.insert(x0, (t, xp));
            self.nidx.insert(x1, (t, xp));
            self.nidx.insert(x2, (t, xp));
            self.nset.insert(xp, t);
            //swaptup.extend_from_slice(xp.as_ref());
            fresh = Some(t);
          }
          Some(&t) => if t >= tlb {
            //swaptup.extend_from_slice(xp.as_ref());
            stale = Some(t);
          }
        }
        swaptup.extend_from_slice(xp.as_ref());
        let xp_: &mut [SNum] = xp.as_mut();
        if next_permutation(xp_).is_none() {
          break;
        }
      }
      _from_fresh_stale(fresh, stale)
    } else {
      unreachable!();
    }
  }
}

pub struct RScan4 {
  ub:   CTup4,
  iter: IHTreapMapCloneIter<CTup4, TNum>,
}

impl EScan for RScan4 {
  fn next_tup(&mut self, tup: &mut [SNum], /*shm: &mut STFrame*/) -> TScanResult {
    match self.iter.next() {
      None => {
        End
      }
      Some((xp, t)) => if xp > self.ub {
        End
      } else {
        tup.copy_from_slice(xp.as_ref());
        Hit(t)
      }
    }
  }
}

#[derive(Clone, Default)]
pub struct Rel4 {
  chk:  TUSnapshot,
  attr: IHTreapMap<TNum, CVar>,
  plub: TNum,
  nlub: TNum,
  pidx: CUnionIter<(TNum, CTup4)>,
  //pdom: IHTreapSet<(TNum, CTup4)>,
  pset: IHTreapMap<CTup4, TNum>,
  ps2:  IHTreapMap<CTup4, IHTreapMap<CTup4, TNum>>,
  nidx: CUnionIter<(TNum, CTup4)>,
  //ndom: IHTreapSet<(TNum, CTup4)>,
  nset: IHTreapMap<CTup4, TNum>,
  ns2:  IHTreapMap<CTup4, IHTreapMap<CTup4, TNum>>,
  //flag: Option<(TNum, CTup4)>,
}

impl Rel4 {
  fn _patch(&mut self, _rel: CVar, shm: &mut STFrame) -> bool {
    //bench_patch_start();
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let mut nlub = self.nlub;
    let u_it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in u_it {
      for (_, np) in self.pidx.iter(nx) {
        let np_: &[CVar] = np.as_ref();
        let nx0 = np_[0];
        let nx1 = np_[1];
        let nx2 = np_[2];
        let nx3 = np_[3];
        match self.pset.get(&np) {
          None => {}
          Some(&t) => if ut > t {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.pidx.insert(nx0, (t, np));
            self.pidx.insert(nx1, (t, np));
            self.pidx.insert(nx2, (t, np));
            self.pidx.insert(nx3, (t, np));
            self.pset.insert(np, t);
            for (perm, _) in self.ps2.clone_iter() {
              let np = np.perm(perm.as_ref());
              match self.ps2.get_mut(&perm) {
                None => unreachable!(),
                Some(pset) => {
                  pset.insert(np, t);
                }
              }
            }
          }
        }
      }
      for (ot, op) in self.pidx.iter(ox) {
        match self.pset.get(&op) {
          None => {}
          Some(&ot) => {
            let np = op.swap_var(ox, nx);
            let np_: &[CVar] = np.as_ref();
            let nx0 = np_[0];
            let nx1 = np_[1];
            let nx2 = np_[2];
            let nx3 = np_[3];
            match self.pset.get(&np) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.pidx.insert(nx0, (t, np));
                self.pidx.insert(nx1, (t, np));
                self.pidx.insert(nx2, (t, np));
                self.pidx.insert(nx3, (t, np));
                self.pset.remove(&op);
                self.pset.insert(np, t);
                for (perm, _) in self.ps2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ps2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pset) => {
                      pset.remove(&op);
                      pset.insert(np, t);
                    }
                  }
                }
              }
              Some(&t) => if ut > t || ut > ot {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.pidx.insert(nx0, (t, np));
                self.pidx.insert(nx1, (t, np));
                self.pidx.insert(nx2, (t, np));
                self.pidx.insert(nx3, (t, np));
                self.pset.remove(&op);
                self.pset.insert(np, t);
                for (perm, _) in self.ps2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ps2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pset) => {
                      pset.remove(&op);
                      pset.insert(np, t);
                    }
                  }
                }
              }
            }
          }
        }
      }
      self.pidx.remove(ox);
      for (_, np) in self.nidx.iter(nx) {
        let np_: &[CVar] = np.as_ref();
        let nx0 = np_[0];
        let nx1 = np_[1];
        let nx2 = np_[2];
        let nx3 = np_[3];
        match self.nset.get(&np) {
          None => {}
          Some(&t) => if ut > t {
            patch = true;
            let t = shm.clk.fresh();
            nlub = t;
            self.nidx.insert(nx0, (t, np));
            self.nidx.insert(nx1, (t, np));
            self.nidx.insert(nx2, (t, np));
            self.nidx.insert(nx3, (t, np));
            self.nset.insert(np, t);
            for (perm, _) in self.ns2.clone_iter() {
              let np = np.perm(perm.as_ref());
              match self.ns2.get_mut(&perm) {
                None => unreachable!(),
                Some(nset) => {
                  nset.insert(np, t);
                }
              }
            }
          }
        }
      }
      for (ot, op) in self.nidx.iter(ox) {
        match self.nset.get(&op) {
          None => {}
          Some(&ot) => {
            let np = op.swap_var(ox, nx);
            let np_: &[CVar] = np.as_ref();
            let nx0 = np_[0];
            let nx1 = np_[1];
            let nx2 = np_[2];
            let nx3 = np_[3];
            match self.nset.get(&np) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                nlub = t;
                self.nidx.insert(nx0, (t, np));
                self.nidx.insert(nx1, (t, np));
                self.nidx.insert(nx2, (t, np));
                self.nidx.insert(nx3, (t, np));
                self.nset.remove(&op);
                self.nset.insert(np, t);
                for (perm, _) in self.ns2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ns2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(nset) => {
                      nset.remove(&op);
                      nset.insert(np, t);
                    }
                  }
                }
              }
              Some(&t) => if ut > t || ut > ot {
                patch = true;
                let t = shm.clk.fresh();
                nlub = t;
                self.nidx.insert(nx0, (t, np));
                self.nidx.insert(nx1, (t, np));
                self.nidx.insert(nx2, (t, np));
                self.nidx.insert(nx3, (t, np));
                self.nset.remove(&op);
                self.nset.insert(np, t);
                for (perm, _) in self.ns2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ns2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(nset) => {
                      nset.remove(&op);
                      nset.insert(np, t);
                    }
                  }
                }
              }
            }
          }
        }
      }
      self.nidx.remove(ox);
    }
    self.plub = plub;
    self.nlub = nlub;
    //bench_patch_stop();
    patch
  }
}

impl ERel for Rel4 {
  fn clone_ref(&self) -> ERelRef {
    Rc::new(self.clone())
  }

  fn arity(&self) -> usize {
    4
  }

  fn kind2(&self) -> (RelKind, RelKind2) {
    (RelKind::Rel, RelKind2::Exact)
  }

  fn pos_least_ub(&self, _shm: &STFrame) -> TNum {
    self.plub
  }

  fn neg_least_ub(&self, _shm: &STFrame) -> TNum {
    self.nlub
  }

  fn pos_tup_size(&self, _shm: &STFrame) -> u64 {
    self.pset.len() as u64
  }

  fn neg_tup_size(&self, _shm: &STFrame) -> u64 {
    self.nset.len() as u64
  }

  fn dump_tups(&self, rel: CVar, prefix: &str, _shm: &STFrame) {
    println!("{}Rel4::dump_tups: rel={} +{} -{}",
        prefix, rel.0, self.pset.len(), self.nset.len());
    for (xp, &t) in self.pset.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  + {} {:?}", prefix, t, xp_);
    }
    for (xp, &t) in self.nset.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  - {} {:?}", prefix, t, xp_);
    }
  }

  /*fn patch(&mut self, _rel: CVar, shm: &mut STFrame) {
    self._patch(&shm.cc, &mut shm.clk);
  }*/

  fn patchswap(&mut self, _rel: CVar, _newswap: &mut Vec<SNum>, shm: &mut STFrame) {
    self._patch(_rel, shm);
  }

  fn patch_swap(&mut self, _tlb: TNum, _rel: CVar, _newswap: &mut dyn ESwap, shm: &mut STFrame) {
    self._patch(_rel, shm);
  }

  /*fn flag_tup(&mut self, _rel: CVar, tup: &mut [SNum]) -> Option<TNum> {
    match self.flag {
      None => {
        None
      }
      Some((t, xp)) => {
        tup.copy_from_slice(xp.as_ref());
        Some(t)
      }
    }
  }*/

  fn flag_tup(&mut self, _rel: CVar, _tup: &mut [SNum]) -> Option<TNum> {
    None
  }

  fn test_pos_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2, k3] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let xp = CTup4([x0, x1, x2, x3]);
      match self.pset.get(&xp) {
        None => {}
        Some(&t) => {
          return Some(t);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn test_neg_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2, k3] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let xp = CTup4([x0, x1, x2, x3]);
      match self.nset.get(&xp) {
        None => {}
        Some(&t) => {
          return Some(t);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn scan_pos(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup4::from(ubtup);
    let iter = self.pset.clone_iter_from(lbtup);
    let scan = Box::new(RScan4{ub, iter});
    scan
  }

  fn scan_neg(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup4::from(ubtup);
    let iter = self.nset.clone_iter_from(lbtup);
    let scan = Box::new(RScan4{ub, iter});
    scan
  }

  fn permscan_pos(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    match self.ps2.get(perm) {
      None => {
        let mut pset = IHTreapMap::default();
        for (xp, &t) in self.pset.iter() {
          let xp = xp.perm(perm);
          pset.insert(xp, t);
        }
        self.ps2.insert(CTup4::from(perm), pset);
      }
      Some(_) => {}
    }
    match self.ps2.get(perm) {
      None => unreachable!(),
      Some(pset) => {
        let ub = CTup4::from(ubtup);
        let iter = pset.clone_iter_from(lbtup);
        let scan = Box::new(RScan4{ub, iter});
        scan
      }
    }
  }

  fn permscan_neg(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    match self.ns2.get(perm) {
      None => {
        let mut nset = IHTreapMap::default();
        for (xp, &t) in self.nset.iter() {
          let xp = xp.perm(perm);
          nset.insert(xp, t);
        }
        self.ns2.insert(CTup4::from(perm), nset);
      }
      Some(_) => {}
    }
    match self.ns2.get(perm) {
      None => unreachable!(),
      Some(nset) => {
        let ub = CTup4::from(ubtup);
        let iter = nset.clone_iter_from(lbtup);
        let scan = Box::new(RScan4{ub, iter});
        scan
      }
    }
  }

  fn scan_par(&self, _rel: CVar, _shm: &STFrame) -> EScanBox {
    let ub = CTup4::ub();
    let iter = self.pset.merge_intersection(&self.nset, &mut |_, &lt, &rt| max(lt, rt)).clone_iter();
    let scan = Box::new(RScan4{ub, iter});
    scan
  }

  fn swap_pos_tup(&mut self, _rec: CVar, _rel: CVar, tup: &[SNum], _newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2, k3] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let xp = CTup4([x0, x1, x2, x3]);
      match self.pset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.pidx.insert(x0, (t, xp));
          self.pidx.insert(x1, (t, xp));
          self.pidx.insert(x2, (t, xp));
          self.pidx.insert(x3, (t, xp));
          //self.pdom.insert((t, xp));
          self.pset.insert(xp, t);
          swaptup.extend_from_slice(xp.as_ref());
          Some(t)
        }
        Some(_) => {
          None
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup(&mut self, _rec: CVar, _rel: CVar, tup: &[SNum], _newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2, k3] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let xp = CTup4([x0, x1, x2, x3]);
      match self.nset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.nlub = t;
          self.nidx.insert(x0, (t, xp));
          self.nidx.insert(x1, (t, xp));
          self.nidx.insert(x2, (t, xp));
          self.nidx.insert(x3, (t, xp));
          //self.ndom.insert((t, xp));
          self.nset.insert(xp, t);
          swaptup.extend_from_slice(xp.as_ref());
          Some(t)
        }
        Some(_) => {
          None
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_pos_tup_(&mut self, tlb: TNum, _rec: CVar, _rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[k0, k1, k2, k3] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let xp = CTup4([x0, x1, x2, x3]);
      match self.pset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.pidx.insert(x0, (t, xp));
          self.pidx.insert(x1, (t, xp));
          self.pidx.insert(x2, (t, xp));
          self.pidx.insert(x3, (t, xp));
          //self.pdom.insert((t, xp));
          self.pset.insert(xp, t);
          swaptup.extend_from_slice(xp.as_ref());
          (Fresh, t)
        }
        Some(&t) => if t >= tlb {
          swaptup.extend_from_slice(xp.as_ref());
          (Stale, t)
        } else {
          (Noswap, 0)
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup_(&mut self, tlb: TNum, _rec: CVar, _rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[k0, k1, k2, k3] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let xp = CTup4([x0, x1, x2, x3]);
      match self.nset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.nlub = t;
          self.nidx.insert(x0, (t, xp));
          self.nidx.insert(x1, (t, xp));
          self.nidx.insert(x2, (t, xp));
          self.nidx.insert(x3, (t, xp));
          //self.ndom.insert((t, xp));
          self.nset.insert(xp, t);
          swaptup.extend_from_slice(xp.as_ref());
          (Fresh, t)
        }
        Some(&t) => if t >= tlb {
          swaptup.extend_from_slice(xp.as_ref());
          (Stale, t)
        } else {
          (Noswap, 0)
        }
      }
    } else {
      unreachable!();
    }
  }
}

pub struct RScan5 {
  ub:   CTup5,
  iter: IHTreapMapCloneIter<CTup5, TNum>,
}

impl EScan for RScan5 {
  fn next_tup(&mut self, tup: &mut [SNum], /*shm: &mut STFrame*/) -> TScanResult {
    match self.iter.next() {
      None => {
        End
      }
      Some((xp, t)) => if xp > self.ub {
        End
      } else {
        tup.copy_from_slice(xp.as_ref());
        Hit(t)
      }
    }
  }
}

#[derive(Clone, Default)]
pub struct Rel5 {
  chk:  TUSnapshot,
  attr: IHTreapMap<TNum, CVar>,
  plub: TNum,
  nlub: TNum,
  pidx: CUnionIter<(TNum, CTup5)>,
  //pdom: IHTreapSet<(TNum, CTup5)>,
  pset: IHTreapMap<CTup5, TNum>,
  ps2:  IHTreapMap<CTup5, IHTreapMap<CTup5, TNum>>,
  nidx: CUnionIter<(TNum, CTup5)>,
  //ndom: IHTreapSet<(TNum, CTup5)>,
  nset: IHTreapMap<CTup5, TNum>,
  ns2:  IHTreapMap<CTup5, IHTreapMap<CTup5, TNum>>,
  //flag: Option<(TNum, CTup5)>,
}

impl Rel5 {
  fn _patch(&mut self, _rel: CVar, shm: &mut STFrame) -> bool {
    //bench_patch_start();
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let mut nlub = self.nlub;
    let u_it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in u_it {
      for (_, np) in self.pidx.iter(nx) {
        let np_: &[CVar] = np.as_ref();
        let nx0 = np_[0];
        let nx1 = np_[1];
        let nx2 = np_[2];
        let nx3 = np_[3];
        let nx4 = np_[4];
        match self.pset.get(&np) {
          None => {}
          Some(&t) => if ut > t {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.pidx.insert(nx0, (t, np));
            self.pidx.insert(nx1, (t, np));
            self.pidx.insert(nx2, (t, np));
            self.pidx.insert(nx3, (t, np));
            self.pidx.insert(nx4, (t, np));
            self.pset.insert(np, t);
            for (perm, _) in self.ps2.clone_iter() {
              let np = np.perm(perm.as_ref());
              match self.ps2.get_mut(&perm) {
                None => unreachable!(),
                Some(pset) => {
                  pset.insert(np, t);
                }
              }
            }
          }
        }
      }
      for (ot, op) in self.pidx.iter(ox) {
        match self.pset.get(&op) {
          None => {}
          Some(&ot) => {
            let np = op.swap_var(ox, nx);
            let np_: &[CVar] = np.as_ref();
            let nx0 = np_[0];
            let nx1 = np_[1];
            let nx2 = np_[2];
            let nx3 = np_[3];
            let nx4 = np_[4];
            match self.pset.get(&np) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.pidx.insert(nx0, (t, np));
                self.pidx.insert(nx1, (t, np));
                self.pidx.insert(nx2, (t, np));
                self.pidx.insert(nx3, (t, np));
                self.pidx.insert(nx4, (t, np));
                self.pset.remove(&op);
                self.pset.insert(np, t);
                for (perm, _) in self.ps2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ps2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pset) => {
                      pset.remove(&op);
                      pset.insert(np, t);
                    }
                  }
                }
              }
              Some(&t) => if ut > t || ut > ot {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.pidx.insert(nx0, (t, np));
                self.pidx.insert(nx1, (t, np));
                self.pidx.insert(nx2, (t, np));
                self.pidx.insert(nx3, (t, np));
                self.pidx.insert(nx4, (t, np));
                self.pset.remove(&op);
                self.pset.insert(np, t);
                for (perm, _) in self.ps2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ps2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pset) => {
                      pset.remove(&op);
                      pset.insert(np, t);
                    }
                  }
                }
              }
            }
          }
        }
      }
      self.pidx.remove(ox);
      for (_, np) in self.nidx.iter(nx) {
        let np_: &[CVar] = np.as_ref();
        let nx0 = np_[0];
        let nx1 = np_[1];
        let nx2 = np_[2];
        let nx3 = np_[3];
        let nx4 = np_[4];
        match self.nset.get(&np) {
          None => {}
          Some(&t) => if ut > t {
            patch = true;
            let t = shm.clk.fresh();
            nlub = t;
            self.nidx.insert(nx0, (t, np));
            self.nidx.insert(nx1, (t, np));
            self.nidx.insert(nx2, (t, np));
            self.nidx.insert(nx3, (t, np));
            self.nidx.insert(nx4, (t, np));
            self.nset.insert(np, t);
            for (perm, _) in self.ns2.clone_iter() {
              let np = np.perm(perm.as_ref());
              match self.ns2.get_mut(&perm) {
                None => unreachable!(),
                Some(nset) => {
                  nset.insert(np, t);
                }
              }
            }
          }
        }
      }
      for (ot, op) in self.nidx.iter(ox) {
        match self.nset.get(&op) {
          None => {}
          Some(&ot) => {
            let np = op.swap_var(ox, nx);
            let np_: &[CVar] = np.as_ref();
            let nx0 = np_[0];
            let nx1 = np_[1];
            let nx2 = np_[2];
            let nx3 = np_[3];
            let nx4 = np_[4];
            match self.nset.get(&np) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                nlub = t;
                self.nidx.insert(nx0, (t, np));
                self.nidx.insert(nx1, (t, np));
                self.nidx.insert(nx2, (t, np));
                self.nidx.insert(nx3, (t, np));
                self.nidx.insert(nx4, (t, np));
                self.nset.remove(&op);
                self.nset.insert(np, t);
                for (perm, _) in self.ns2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ns2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(nset) => {
                      nset.remove(&op);
                      nset.insert(np, t);
                    }
                  }
                }
              }
              Some(&t) => if ut > t || ut > ot {
                patch = true;
                let t = shm.clk.fresh();
                nlub = t;
                self.nidx.insert(nx0, (t, np));
                self.nidx.insert(nx1, (t, np));
                self.nidx.insert(nx2, (t, np));
                self.nidx.insert(nx3, (t, np));
                self.nidx.insert(nx4, (t, np));
                self.nset.remove(&op);
                self.nset.insert(np, t);
                for (perm, _) in self.ns2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ns2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(nset) => {
                      nset.remove(&op);
                      nset.insert(np, t);
                    }
                  }
                }
              }
            }
          }
        }
      }
      self.nidx.remove(ox);
    }
    self.plub = plub;
    self.nlub = nlub;
    //bench_patch_stop();
    patch
  }
}

impl ERel for Rel5 {
  fn clone_ref(&self) -> ERelRef {
    Rc::new(self.clone())
  }

  fn arity(&self) -> usize {
    5
  }

  fn kind2(&self) -> (RelKind, RelKind2) {
    (RelKind::Rel, RelKind2::Exact)
  }

  fn pos_least_ub(&self, _shm: &STFrame) -> TNum {
    self.plub
  }

  fn neg_least_ub(&self, _shm: &STFrame) -> TNum {
    self.nlub
  }

  fn pos_tup_size(&self, _shm: &STFrame) -> u64 {
    self.pset.len() as u64
  }

  fn neg_tup_size(&self, _shm: &STFrame) -> u64 {
    self.nset.len() as u64
  }

  fn dump_tups(&self, rel: CVar, prefix: &str, _shm: &STFrame) {
    println!("{}Rel5::dump_tups: rel={} +{} -{}",
        prefix, rel.0, self.pset.len(), self.nset.len());
    for (xp, &t) in self.pset.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  + {} {:?}", prefix, t, xp_);
    }
    for (xp, &t) in self.nset.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  - {} {:?}", prefix, t, xp_);
    }
  }

  fn patchswap(&mut self, _rel: CVar, _newswap: &mut Vec<SNum>, shm: &mut STFrame) {
    self._patch(_rel, shm);
  }

  fn patch_swap(&mut self, _tlb: TNum, _rel: CVar, _newswap: &mut dyn ESwap, shm: &mut STFrame) {
    self._patch(_rel, shm);
  }

  fn test_pos_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2, k3, k4] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let (_, x4) = shm.cc.find(k4);
      let xp = CTup5([x0, x1, x2, x3, x4]);
      match self.pset.get(&xp) {
        None => {}
        Some(&t) => {
          return Some(t);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn test_neg_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2, k3, k4] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let (_, x4) = shm.cc.find(k4);
      let xp = CTup5([x0, x1, x2, x3, x4]);
      match self.nset.get(&xp) {
        None => {}
        Some(&t) => {
          return Some(t);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn scan_pos(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup5::from(ubtup);
    let iter = self.pset.clone_iter_from(lbtup);
    let scan = Box::new(RScan5{ub, iter});
    scan
  }

  fn scan_neg(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup5::from(ubtup);
    let iter = self.nset.clone_iter_from(lbtup);
    let scan = Box::new(RScan5{ub, iter});
    scan
  }

  fn permscan_pos(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    match self.ps2.get(perm) {
      None => {
        let mut pset = IHTreapMap::default();
        for (xp, &t) in self.pset.iter() {
          let xp = xp.perm(perm);
          pset.insert(xp, t);
        }
        self.ps2.insert(CTup5::from(perm), pset);
      }
      Some(_) => {}
    }
    match self.ps2.get(perm) {
      None => unreachable!(),
      Some(pset) => {
        let ub = CTup5::from(ubtup);
        let iter = pset.clone_iter_from(lbtup);
        let scan = Box::new(RScan5{ub, iter});
        scan
      }
    }
  }

  fn permscan_neg(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    match self.ns2.get(perm) {
      None => {
        let mut nset = IHTreapMap::default();
        for (xp, &t) in self.nset.iter() {
          let xp = xp.perm(perm);
          nset.insert(xp, t);
        }
        self.ns2.insert(CTup5::from(perm), nset);
      }
      Some(_) => {}
    }
    match self.ns2.get(perm) {
      None => unreachable!(),
      Some(nset) => {
        let ub = CTup5::from(ubtup);
        let iter = nset.clone_iter_from(lbtup);
        let scan = Box::new(RScan5{ub, iter});
        scan
      }
    }
  }

  fn scan_par(&self, _rel: CVar, _shm: &STFrame) -> EScanBox {
    let ub = CTup5::ub();
    let iter = self.pset.merge_intersection(&self.nset, &mut |_, &lt, &rt| max(lt, rt)).clone_iter();
    let scan = Box::new(RScan5{ub, iter});
    scan
  }

  fn swap_pos_tup(&mut self, _rec: CVar, _rel: CVar, tup: &[SNum], _newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2, k3, k4] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let (_, x4) = shm.cc.find(k4);
      let xp = CTup5([x0, x1, x2, x3, x4]);
      match self.pset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.pidx.insert(x0, (t, xp));
          self.pidx.insert(x1, (t, xp));
          self.pidx.insert(x2, (t, xp));
          self.pidx.insert(x3, (t, xp));
          self.pidx.insert(x4, (t, xp));
          //self.pdom.insert((t, xp));
          self.pset.insert(xp, t);
          swaptup.extend_from_slice(xp.as_ref());
          Some(t)
        }
        Some(_) => {
          None
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup(&mut self, _rec: CVar, _rel: CVar, tup: &[SNum], _newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2, k3, k4] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let (_, x4) = shm.cc.find(k4);
      let xp = CTup5([x0, x1, x2, x3, x4]);
      match self.nset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.nlub = t;
          self.nidx.insert(x0, (t, xp));
          self.nidx.insert(x1, (t, xp));
          self.nidx.insert(x2, (t, xp));
          self.nidx.insert(x3, (t, xp));
          self.nidx.insert(x4, (t, xp));
          //self.ndom.insert((t, xp));
          self.nset.insert(xp, t);
          swaptup.extend_from_slice(xp.as_ref());
          Some(t)
        }
        Some(_) => {
          None
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_pos_tup_(&mut self, tlb: TNum, _rec: CVar, _rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[k0, k1, k2, k3, k4] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let (_, x4) = shm.cc.find(k4);
      let xp = CTup5([x0, x1, x2, x3, x4]);
      match self.pset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.pidx.insert(x0, (t, xp));
          self.pidx.insert(x1, (t, xp));
          self.pidx.insert(x2, (t, xp));
          self.pidx.insert(x3, (t, xp));
          self.pidx.insert(x4, (t, xp));
          //self.pdom.insert((t, xp));
          self.pset.insert(xp, t);
          swaptup.extend_from_slice(xp.as_ref());
          (Fresh, t)
        }
        Some(&t) => if t >= tlb {
          swaptup.extend_from_slice(xp.as_ref());
          (Stale, t)
        } else {
          (Noswap, 0)
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup_(&mut self, tlb: TNum, _rec: CVar, _rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[k0, k1, k2, k3, k4] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let (_, x4) = shm.cc.find(k4);
      let xp = CTup5([x0, x1, x2, x3, x4]);
      match self.nset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.nlub = t;
          self.nidx.insert(x0, (t, xp));
          self.nidx.insert(x1, (t, xp));
          self.nidx.insert(x2, (t, xp));
          self.nidx.insert(x3, (t, xp));
          self.nidx.insert(x4, (t, xp));
          //self.ndom.insert((t, xp));
          self.nset.insert(xp, t);
          swaptup.extend_from_slice(xp.as_ref());
          (Fresh, t)
        }
        Some(&t) => if t >= tlb {
          swaptup.extend_from_slice(xp.as_ref());
          (Stale, t)
        } else {
          (Noswap, 0)
        }
      }
    } else {
      unreachable!();
    }
  }
}

pub struct RScan6 {
  ub:   CTup6,
  iter: IHTreapMapCloneIter<CTup6, TNum>,
}

impl EScan for RScan6 {
  fn next_tup(&mut self, tup: &mut [SNum], /*shm: &mut STFrame*/) -> TScanResult {
    match self.iter.next() {
      None => {
        End
      }
      Some((xp, t)) => if xp > self.ub {
        End
      } else {
        tup.copy_from_slice(xp.as_ref());
        Hit(t)
      }
    }
  }
}

#[derive(Clone, Default)]
pub struct Rel6 {
  chk:  TUSnapshot,
  attr: IHTreapMap<TNum, CVar>,
  plub: TNum,
  nlub: TNum,
  pidx: CUnionIter<(TNum, CTup6)>,
  //pdom: IHTreapSet<(TNum, CTup6)>,
  pset: IHTreapMap<CTup6, TNum>,
  ps2:  IHTreapMap<CTup6, IHTreapMap<CTup6, TNum>>,
  nidx: CUnionIter<(TNum, CTup6)>,
  //ndom: IHTreapSet<(TNum, CTup6)>,
  nset: IHTreapMap<CTup6, TNum>,
  ns2:  IHTreapMap<CTup6, IHTreapMap<CTup6, TNum>>,
  //flag: Option<(TNum, CTup6)>,
}

impl Rel6 {
  fn _patch(&mut self, _rel: CVar, shm: &mut STFrame) -> bool {
    //bench_patch_start();
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let mut nlub = self.nlub;
    let u_it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in u_it {
      for (_, np) in self.pidx.iter(nx) {
        let np_: &[CVar] = np.as_ref();
        let nx0 = np_[0];
        let nx1 = np_[1];
        let nx2 = np_[2];
        let nx3 = np_[3];
        let nx4 = np_[4];
        let nx5 = np_[5];
        match self.pset.get(&np) {
          None => {}
          Some(&t) => if ut > t {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.pidx.insert(nx0, (t, np));
            self.pidx.insert(nx1, (t, np));
            self.pidx.insert(nx2, (t, np));
            self.pidx.insert(nx3, (t, np));
            self.pidx.insert(nx4, (t, np));
            self.pidx.insert(nx5, (t, np));
            self.pset.insert(np, t);
            for (perm, _) in self.ps2.clone_iter() {
              let np = np.perm(perm.as_ref());
              match self.ps2.get_mut(&perm) {
                None => unreachable!(),
                Some(pset) => {
                  pset.insert(np, t);
                }
              }
            }
          }
        }
      }
      for (ot, op) in self.pidx.iter(ox) {
        match self.pset.get(&op) {
          None => {}
          Some(&ot) => {
            let np = op.swap_var(ox, nx);
            let np_: &[CVar] = np.as_ref();
            let nx0 = np_[0];
            let nx1 = np_[1];
            let nx2 = np_[2];
            let nx3 = np_[3];
            let nx4 = np_[4];
            let nx5 = np_[5];
            match self.pset.get(&np) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.pidx.insert(nx0, (t, np));
                self.pidx.insert(nx1, (t, np));
                self.pidx.insert(nx2, (t, np));
                self.pidx.insert(nx3, (t, np));
                self.pidx.insert(nx4, (t, np));
                self.pidx.insert(nx5, (t, np));
                self.pset.remove(&op);
                self.pset.insert(np, t);
                for (perm, _) in self.ps2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ps2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pset) => {
                      pset.remove(&op);
                      pset.insert(np, t);
                    }
                  }
                }
              }
              Some(&t) => if ut > t || ut > ot {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.pidx.insert(nx0, (t, np));
                self.pidx.insert(nx1, (t, np));
                self.pidx.insert(nx2, (t, np));
                self.pidx.insert(nx3, (t, np));
                self.pidx.insert(nx4, (t, np));
                self.pidx.insert(nx5, (t, np));
                self.pset.remove(&op);
                self.pset.insert(np, t);
                for (perm, _) in self.ps2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ps2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pset) => {
                      pset.remove(&op);
                      pset.insert(np, t);
                    }
                  }
                }
              }
            }
          }
        }
      }
      self.pidx.remove(ox);
      for (_, np) in self.nidx.iter(nx) {
        let np_: &[CVar] = np.as_ref();
        let nx0 = np_[0];
        let nx1 = np_[1];
        let nx2 = np_[2];
        let nx3 = np_[3];
        let nx4 = np_[4];
        let nx5 = np_[5];
        match self.nset.get(&np) {
          None => {}
          Some(&t) => if ut > t {
            patch = true;
            let t = shm.clk.fresh();
            nlub = t;
            self.nidx.insert(nx0, (t, np));
            self.nidx.insert(nx1, (t, np));
            self.nidx.insert(nx2, (t, np));
            self.nidx.insert(nx3, (t, np));
            self.nidx.insert(nx4, (t, np));
            self.nidx.insert(nx5, (t, np));
            self.nset.insert(np, t);
            for (perm, _) in self.ns2.clone_iter() {
              let np = np.perm(perm.as_ref());
              match self.ns2.get_mut(&perm) {
                None => unreachable!(),
                Some(nset) => {
                  nset.insert(np, t);
                }
              }
            }
          }
        }
      }
      for (ot, op) in self.nidx.iter(ox) {
        match self.nset.get(&op) {
          None => {}
          Some(&ot) => {
            let np = op.swap_var(ox, nx);
            let np_: &[CVar] = np.as_ref();
            let nx0 = np_[0];
            let nx1 = np_[1];
            let nx2 = np_[2];
            let nx3 = np_[3];
            let nx4 = np_[4];
            let nx5 = np_[5];
            match self.nset.get(&np) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                nlub = t;
                self.nidx.insert(nx0, (t, np));
                self.nidx.insert(nx1, (t, np));
                self.nidx.insert(nx2, (t, np));
                self.nidx.insert(nx3, (t, np));
                self.nidx.insert(nx4, (t, np));
                self.nidx.insert(nx5, (t, np));
                self.nset.remove(&op);
                self.nset.insert(np, t);
                for (perm, _) in self.ns2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ns2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(nset) => {
                      nset.remove(&op);
                      nset.insert(np, t);
                    }
                  }
                }
              }
              Some(&t) => if ut > t || ut > ot {
                patch = true;
                let t = shm.clk.fresh();
                nlub = t;
                self.nidx.insert(nx0, (t, np));
                self.nidx.insert(nx1, (t, np));
                self.nidx.insert(nx2, (t, np));
                self.nidx.insert(nx3, (t, np));
                self.nidx.insert(nx4, (t, np));
                self.nidx.insert(nx5, (t, np));
                self.nset.remove(&op);
                self.nset.insert(np, t);
                for (perm, _) in self.ns2.clone_iter() {
                  let op = op.perm(perm.as_ref());
                  let np = np.perm(perm.as_ref());
                  match self.ns2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(nset) => {
                      nset.remove(&op);
                      nset.insert(np, t);
                    }
                  }
                }
              }
            }
          }
        }
      }
      self.nidx.remove(ox);
    }
    self.plub = plub;
    self.nlub = nlub;
    //bench_patch_stop();
    patch
  }
}

impl ERel for Rel6 {
  fn clone_ref(&self) -> ERelRef {
    Rc::new(self.clone())
  }

  fn arity(&self) -> usize {
    6
  }

  fn kind2(&self) -> (RelKind, RelKind2) {
    (RelKind::Rel, RelKind2::Exact)
  }

  fn pos_least_ub(&self, _shm: &STFrame) -> TNum {
    self.plub
  }

  fn neg_least_ub(&self, _shm: &STFrame) -> TNum {
    self.nlub
  }

  fn pos_tup_size(&self, _shm: &STFrame) -> u64 {
    self.pset.len() as u64
  }

  fn neg_tup_size(&self, _shm: &STFrame) -> u64 {
    self.nset.len() as u64
  }

  fn dump_tups(&self, rel: CVar, prefix: &str, _shm: &STFrame) {
    println!("{}Rel6::dump_tups: rel={} +{} -{}",
        prefix, rel.0, self.pset.len(), self.nset.len());
    for (xp, &t) in self.pset.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  + {} {:?}", prefix, t, xp_);
    }
    for (xp, &t) in self.nset.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  - {} {:?}", prefix, t, xp_);
    }
  }

  /*fn patch(&mut self, _rel: CVar, shm: &mut STFrame) {
    self._patch(&shm.cc, &mut shm.clk);
  }*/

  fn patchswap(&mut self, _rel: CVar, _newswap: &mut Vec<SNum>, shm: &mut STFrame) {
    self._patch(_rel, shm);
  }

  fn patch_swap(&mut self, _tlb: TNum, _rel: CVar, _newswap: &mut dyn ESwap, shm: &mut STFrame) {
    self._patch(_rel, shm);
  }

  /*fn flag_tup(&mut self, _rel: CVar, tup: &mut [SNum]) -> Option<TNum> {
    match self.flag {
      None => {
        None
      }
      Some((t, xp)) => {
        tup.copy_from_slice(xp.as_ref());
        Some(t)
      }
    }
  }*/

  fn flag_tup(&mut self, _rel: CVar, _tup: &mut [SNum]) -> Option<TNum> {
    None
  }

  fn test_pos_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2, k3, k4, k5] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let (_, x4) = shm.cc.find(k4);
      let (_, x5) = shm.cc.find(k5);
      let xp = CTup6([x0, x1, x2, x3, x4, x5]);
      match self.pset.get(&xp) {
        None => {}
        Some(&t) => {
          return Some(t);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn test_neg_tup(&mut self, _rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2, k3, k4, k5] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let (_, x4) = shm.cc.find(k4);
      let (_, x5) = shm.cc.find(k5);
      let xp = CTup6([x0, x1, x2, x3, x4, x5]);
      match self.nset.get(&xp) {
        None => {}
        Some(&t) => {
          return Some(t);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn scan_pos(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup6::from(ubtup);
    let iter = self.pset.clone_iter_from(lbtup);
    let scan = Box::new(RScan6{ub, iter});
    scan
  }

  fn scan_neg(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup6::from(ubtup);
    let iter = self.nset.clone_iter_from(lbtup);
    let scan = Box::new(RScan6{ub, iter});
    scan
  }

  fn permscan_pos(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    match self.ps2.get(perm) {
      None => {
        let mut pset = IHTreapMap::default();
        for (xp, &t) in self.pset.iter() {
          let xp = xp.perm(perm);
          pset.insert(xp, t);
        }
        self.ps2.insert(CTup6::from(perm), pset);
      }
      Some(_) => {}
    }
    match self.ps2.get(perm) {
      None => unreachable!(),
      Some(pset) => {
        let ub = CTup6::from(ubtup);
        let iter = pset.clone_iter_from(lbtup);
        let scan = Box::new(RScan6{ub, iter});
        scan
      }
    }
  }

  fn permscan_neg(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    match self.ns2.get(perm) {
      None => {
        let mut nset = IHTreapMap::default();
        for (xp, &t) in self.nset.iter() {
          let xp = xp.perm(perm);
          nset.insert(xp, t);
        }
        self.ns2.insert(CTup6::from(perm), nset);
      }
      Some(_) => {}
    }
    match self.ns2.get(perm) {
      None => unreachable!(),
      Some(nset) => {
        let ub = CTup6::from(ubtup);
        let iter = nset.clone_iter_from(lbtup);
        let scan = Box::new(RScan6{ub, iter});
        scan
      }
    }
  }

  fn scan_par(&self, _rel: CVar, _shm: &STFrame) -> EScanBox {
    let ub = CTup6::ub();
    let iter = self.pset.merge_intersection(&self.nset, &mut |_, &lt, &rt| max(lt, rt)).clone_iter();
    let scan = Box::new(RScan6{ub, iter});
    scan
  }

  fn swap_pos_tup(&mut self, _rec: CVar, _rel: CVar, tup: &[SNum], _newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2, k3, k4, k5] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let (_, x4) = shm.cc.find(k4);
      let (_, x5) = shm.cc.find(k5);
      let xp = CTup6([x0, x1, x2, x3, x4, x5]);
      match self.pset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.pidx.insert(x0, (t, xp));
          self.pidx.insert(x1, (t, xp));
          self.pidx.insert(x2, (t, xp));
          self.pidx.insert(x3, (t, xp));
          self.pidx.insert(x4, (t, xp));
          self.pidx.insert(x5, (t, xp));
          //self.pdom.insert((t, xp));
          self.pset.insert(xp, t);
          swaptup.extend_from_slice(xp.as_ref());
          Some(t)
        }
        Some(_) => {
          None
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup(&mut self, _rec: CVar, _rel: CVar, tup: &[SNum], _newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[k0, k1, k2, k3, k4, k5] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(&shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let (_, x4) = shm.cc.find(k4);
      let (_, x5) = shm.cc.find(k5);
      let xp = CTup6([x0, x1, x2, x3, x4, x5]);
      match self.nset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.nlub = t;
          self.nidx.insert(x0, (t, xp));
          self.nidx.insert(x1, (t, xp));
          self.nidx.insert(x2, (t, xp));
          self.nidx.insert(x3, (t, xp));
          self.nidx.insert(x4, (t, xp));
          self.nidx.insert(x5, (t, xp));
          //self.ndom.insert((t, xp));
          self.nset.insert(xp, t);
          swaptup.extend_from_slice(xp.as_ref());
          Some(t)
        }
        Some(_) => {
          None
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_pos_tup_(&mut self, tlb: TNum, _rec: CVar, _rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[k0, k1, k2, k3, k4, k5] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let (_, x4) = shm.cc.find(k4);
      let (_, x5) = shm.cc.find(k5);
      let xp = CTup6([x0, x1, x2, x3, x4, x5]);
      match self.pset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.pidx.insert(x0, (t, xp));
          self.pidx.insert(x1, (t, xp));
          self.pidx.insert(x2, (t, xp));
          self.pidx.insert(x3, (t, xp));
          self.pidx.insert(x4, (t, xp));
          self.pidx.insert(x5, (t, xp));
          //self.pdom.insert((t, xp));
          self.pset.insert(xp, t);
          swaptup.extend_from_slice(xp.as_ref());
          (Fresh, t)
        }
        Some(&t) => if t >= tlb {
          swaptup.extend_from_slice(xp.as_ref());
          (Stale, t)
        } else {
          (Noswap, 0)
        }
      }
    } else {
      unreachable!();
    }
  }

  fn swap_neg_tup_(&mut self, tlb: TNum, _rec: CVar, _rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, _newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[k0, k1, k2, k3, k4, k5] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, x0) = shm.cc.find(k0);
      let (_, x1) = shm.cc.find(k1);
      let (_, x2) = shm.cc.find(k2);
      let (_, x3) = shm.cc.find(k3);
      let (_, x4) = shm.cc.find(k4);
      let (_, x5) = shm.cc.find(k5);
      let xp = CTup6([x0, x1, x2, x3, x4, x5]);
      match self.nset.get(&xp) {
        None => {
          let t = shm.clk.fresh();
          self.nlub = t;
          self.nidx.insert(x0, (t, xp));
          self.nidx.insert(x1, (t, xp));
          self.nidx.insert(x2, (t, xp));
          self.nidx.insert(x3, (t, xp));
          self.nidx.insert(x4, (t, xp));
          self.nidx.insert(x5, (t, xp));
          //self.ndom.insert((t, xp));
          self.nset.insert(xp, t);
          swaptup.extend_from_slice(xp.as_ref());
          (Fresh, t)
        }
        Some(&t) => if t >= tlb {
          swaptup.extend_from_slice(xp.as_ref());
          (Stale, t)
        } else {
          (Noswap, 0)
        }
      }
    } else {
      unreachable!();
    }
  }
}

pub struct EmpScan {
}

impl EScan for EmpScan {
  fn next_tup(&mut self, _tup: &mut [SNum], /*_shm: &mut STFrame*/) -> TScanResult {
    End
  }
}

pub struct FScan1 {
  ub:   CVar,
  iter: IHTreapMapCloneIter<CVar, (CVar, TNum)>,
}

impl EScan for FScan1 {
  fn next_tup(&mut self, tup: &mut [SNum], /*shm: &mut STFrame*/) -> TScanResult {
    match self.iter.next() {
      None => {
        End
      }
      Some((x, (y, t))) => if x > self.ub {
        End
      } else {
        tup[0] = x.0;
        tup[1] = y.0;
        Hit(t)
      }
    }
  }
}

#[derive(Clone, Default)]
pub struct Fun1 {
  chk:  TUSnapshot,
  attr: IHTreapMap<TNum, CVar>,
  plub: TNum,
  idx:  CUnionIter<(TNum, CVar, CVar)>,
  //idx:  IHTreapMap<CVar, IHTreapSet<(TNum, CVar, CVar)>>,
  //idx:  CUnionIter_<(TNum, CVar, CVar)>,
  //dom:  IHTreapSet<(TNum, CVar)>,
  pmap: IHTreapMap<CVar, (CVar, TNum)>,
  //ndom: IHTreapSet<(TNum, CVar, CVar)>,
  //nset: IHTreapMap<(CVar, CVar), TNum>,
}

impl Fun1 {
  fn _patchswap(&mut self, rel: CVar, newswap: &mut Vec<SNum>, shm: &mut STFrame) -> bool {
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let u_it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in u_it {
      for (_, olx, orx) in self.idx.iter(nx) {
        let nlx = swap_var(olx, ox, nx);
        let nrx = swap_var(orx, ox, nx);
        let (_, rx) = shm.cc.find(nrx);
        match self.pmap.get(&nlx) {
          None => {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.idx.insert(nlx, (t, nlx, rx));
            self.idx.insert(rx, (t, nlx, rx));
            self.pmap.remove(&olx);
            self.pmap.insert(nlx, (rx, t));
          }
          Some(&(oqrx, t)) => {
            let (_, qrx) = shm.cc.find(oqrx);
            if ut > t {
              patch = true;
              let t = shm.clk.fresh();
              plub = t;
              self.idx.insert(nlx, (t, nlx, qrx));
              self.idx.insert(qrx, (t, nlx, qrx));
              self.pmap.remove(&olx);
              self.pmap.insert(nlx, (qrx, t));
            }
            if qrx != rx {
              newswap.push(shm._pseudo_var(rel));
              newswap.push(shm.evar.0);
              newswap.push(qrx.0);
              newswap.push(rx.0);
            }
          }
        }
      }
      for (_, olx, orx) in self.idx.iter(ox) {
        match self.pmap.get(&olx) {
          None => {}
          Some(&(_, ot)) => {
            let nlx = swap_var(olx, ox, nx);
            let nrx = swap_var(orx, ox, nx);
            let (_, rx) = shm.cc.find(nrx);
            match self.pmap.get(&nlx) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.idx.insert(nlx, (t, nlx, rx));
                self.idx.insert(rx, (t, nlx, rx));
                self.pmap.remove(&olx);
                self.pmap.insert(nlx, (rx, t));
              }
              Some(&(oqrx, t)) => {
                let (_, qrx) = shm.cc.find(oqrx);
                if ut > t || ut > ot {
                  patch = true;
                  let t = shm.clk.fresh();
                  plub = t;
                  self.idx.insert(nlx, (t, nlx, qrx));
                  self.idx.insert(qrx, (t, nlx, qrx));
                  self.pmap.remove(&olx);
                  self.pmap.insert(nlx, (qrx, t));
                }
                if qrx != rx {
                  newswap.push(shm._pseudo_var(rel));
                  newswap.push(shm.evar.0);
                  newswap.push(qrx.0);
                  newswap.push(rx.0);
                }
              }
            }
          }
        }
      }
      self.idx.remove(ox);
    }
    self.plub = plub;
    patch
  }

  fn _patch_swap(&mut self, tlb: TNum, rel: CVar, newswap: &mut dyn ESwap, shm: &mut STFrame) -> bool {
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let u_it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    /*let stage_tlb = shm._snapshot().next_glb();*/
    for ((ut, ox), nx) in u_it {
      for (_, olx, orx) in self.idx.iter(nx) {
        let (_, nlx) = shm.cc.find(olx);
        let (_, rx) = shm.cc.find(orx);
        match self.pmap.get(&nlx) {
          None => {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.idx.insert(nlx, (t, nlx, rx));
            self.idx.insert(rx, (t, nlx, rx));
            self.pmap.remove(&olx);
            self.pmap.insert(nlx, (rx, t));
            newswap.patch_tup(tlb, rel.0, &[olx.0], &[orx.0], &[nlx.0], &[rx.0]);
          }
          Some(&(oqrx, t)) => {
            let (_, qrx) = shm.cc.find(oqrx);
            if ut > t {
              patch = true;
              let t = shm.clk.fresh();
              plub = t;
              self.idx.insert(nlx, (t, nlx, qrx));
              self.idx.insert(qrx, (t, nlx, qrx));
              self.pmap.remove(&olx);
              self.pmap.insert(nlx, (qrx, t));
              newswap.patch_tup(tlb, rel.0, &[olx.0], &[orx.0], &[nlx.0], &[rx.0]);
            }
            if qrx != rx {
              newswap.stage_tup(
                  tlb,
                  SwapEvent::Pat(shm.pseudo_var(rel), rel.0, &[nlx.0], &[qrx.0, rx.0]),
                  shm.evar.0,
                  &[qrx.0, rx.0],
              );
            }
          }
        }
      }
      for (_, olx, orx) in self.idx.iter(ox) {
        match self.pmap.get(&olx) {
          None => {}
          Some(&(_, ot)) => {
            let (_, nlx) = shm.cc.find(olx);
            let (_, rx) = shm.cc.find(orx);
            match self.pmap.get(&nlx) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.idx.insert(nlx, (t, nlx, rx));
                self.idx.insert(rx, (t, nlx, rx));
                self.pmap.remove(&olx);
                self.pmap.insert(nlx, (rx, t));
                newswap.patch_tup(tlb, rel.0, &[olx.0], &[orx.0], &[nlx.0], &[rx.0]);
              }
              Some(&(oqrx, t)) => {
                let (_, qrx) = shm.cc.find(oqrx);
                if ut > t || ut > ot {
                  patch = true;
                  let t = shm.clk.fresh();
                  plub = t;
                  self.idx.insert(nlx, (t, nlx, qrx));
                  self.idx.insert(qrx, (t, nlx, qrx));
                  self.pmap.remove(&olx);
                  self.pmap.insert(nlx, (qrx, t));
                  newswap.patch_tup(tlb, rel.0, &[olx.0], &[orx.0], &[nlx.0], &[rx.0]);
                }
                if qrx != rx {
                  newswap.stage_tup(
                      tlb,
                      SwapEvent::Pat(shm.pseudo_var(rel), rel.0, &[nlx.0], &[qrx.0, rx.0]),
                      shm.evar.0,
                      &[qrx.0, rx.0],
                  );
                }
              }
            }
          }
        }
      }
      self.idx.remove(ox);
    }
    self.plub = plub;
    patch
  }
}

impl ERel for Fun1 {
  fn clone_ref(&self) -> ERelRef {
    Rc::new(self.clone())
  }

  /*fn anycast_ref(&self) -> &dyn Any {
    self
  }*/

  fn arity(&self) -> usize {
    2
  }

  fn kind2(&self) -> (RelKind, RelKind2) {
    (RelKind::Fun, RelKind2::Exact)
  }

  fn fun_arity(&self) -> Option<(usize, usize)> {
    Some((1, 1))
  }

  fn pos_least_ub(&self, _shm: &STFrame) -> TNum {
    self.plub
  }

  fn neg_least_ub(&self, _shm: &STFrame) -> TNum {
    0
  }

  fn pos_tup_size(&self, _shm: &STFrame) -> u64 {
    self.pmap.len() as u64
  }

  fn neg_tup_size(&self, _shm: &STFrame) -> u64 {
    //self.nset.len() as u64
    0
  }

  fn dump_tups(&self, rel: CVar, prefix: &str, _shm: &STFrame) {
    println!("{}Fun1::dump_tups: rel={} +{}",
        prefix, rel.0, self.pmap.len());
    for (&x, &(y, t)) in self.pmap.iter() {
      println!("{}  + {} [{}] -> {}", prefix, t, x.0, y.0);
    }
  }

  /*fn patchdiff(&self, rel: CVar, older: &dyn ERel, shm: &mut STFrame) -> (usize, usize) {
    if let Some(older) = older.anycast_ref().downcast_ref::<Fun1>() {
      let mut patch_pmap = IHTreapMap::default();
      for (&kx, &(ky, t)) in older.pmap.iter() {
        let (_, x) = shm.cc.find(kx);
        let (_, y) = shm.cc.find(ky);
        patch_pmap.insert(x, (y, t));
      }
      (max(patch_pmap.len(), self.pmap.len()) - patch_pmap.len(),
       0)
    } else {
      panic!("bug: Fun1::patchdiff: mismatched type");
    }
  }*/

  /*fn patch(&mut self, rel: CVar, clk: &mut TClk, shm: &mut STFrame) {
    self._patch(rel, &mut shm.cc, clk);
  }*/

  fn patchswap(&mut self, rel: CVar, newswap: &mut Vec<SNum>, shm: &mut STFrame) {
    self._patchswap(rel, newswap, shm);
  }

  fn patch_swap(&mut self, tlb: TNum, rel: CVar, newswap: &mut dyn ESwap, shm: &mut STFrame) {
    self._patch_swap(tlb, rel, newswap, shm);
  }

  fn flag_tup(&mut self, _rel: CVar, _tup: &mut [SNum]) -> Option<TNum> {
    None
  }

  fn test_pos_tup(&mut self, rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[lk, rk] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(rel, &mut shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx) = shm.cc.find(lk);
      match self.pmap.get(&lx) {
        None => {}
        Some(&(rx, rt)) => {
          let (_, rq) = shm.cc.find(rk);
          if rx == rq {
            return Some(rt);
          }
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn scan_pos(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let lb = CVar(lbtup[0]);
    let ub = CVar(ubtup[0]);
    let iter = self.pmap.clone_iter_from(&lb);
    let scan = Box::new(FScan1{ub, iter});
    scan
  }

  fn permscan_pos(&mut self, _rel: CVar, _perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    self.scan_pos(_rel, lbtup, ubtup, _shm)
  }

  fn scan_par(&self, _rel: CVar, _shm: &STFrame) -> EScanBox {
    Box::new(EmpScan{})
  }

  fn swap_pos_tup(&mut self, rec: CVar, rel: CVar, tup: &[SNum], newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[lk, rk] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(rel, &mut shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx) = shm.cc.find(lk);
      let (_, rx) = shm.cc.find(rk);
      match self.pmap.get(&lx) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.idx.insert(lx, (t, lx, rx));
          self.idx.insert(rx, (t, lx, rx));
          //self.attr.insert(t, rec);
          //self.dom.insert((t, lx));
          self.pmap.insert(lx, (rx, t));
          swaptup.push(lx.0);
          swaptup.push(rx.0);
          return Some(t);
        }
        Some(&(orx, t)) => if orx != rx {
          newswap.push(shm._pseudo_var(rel));
          newswap.push(shm.evar.0);
          newswap.push(orx.0);
          newswap.push(rx.0);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn swap_pos_tup_(&mut self, tlb: TNum, rec: CVar, rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[lk, rk] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx) = shm.cc.find(lk);
      let (_, rx) = shm.cc.find(rk);
      match self.pmap.get(&lx) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.idx.insert(lx, (t, lx, rx));
          self.idx.insert(rx, (t, lx, rx));
          //self.attr.insert(t, rec);
          //self.dom.insert((t, lx));
          self.pmap.insert(lx, (rx, t));
          swaptup.push(lx.0);
          swaptup.push(rx.0);
          (Fresh, t)
        }
        Some(&(orx, t)) => {
          if orx != rx {
            newswap.stage_tup(
                tlb,
                SwapEvent::Pat(shm.pseudo_var(rel), rel.0, &[lx.0], &[orx.0, rx.0]),
                shm.evar.0,
                &[orx.0, rx.0],
            );
            // FIXME
            swaptup.push(lx.0);
            swaptup.push(rx.0);
            (Merge, t)
          } else if t >= tlb {
            swaptup.push(lx.0);
            swaptup.push(rx.0);
            (Stale, t)
          } else {
            (Noswap, 0)
          }
        }
      }
    } else {
      unreachable!();
    }
  }
}

pub struct FScan2 {
  ub:   CTup2,
  iter: IHTreapMapCloneIter<CTup2, (TNum, CVar)>,
  //iter: IHTreapMapCloneIter<CTup2, (CVar, TNum)>,
}

impl EScan for FScan2 {
  fn next_tup(&mut self, tup: &mut [SNum], /*shm: &mut STFrame*/) -> TScanResult {
    match self.iter.next() {
      None => {
        End
      }
      Some((xp, (t, y))) => if xp > self.ub {
      //Some((xp, (y, t))) => if xp > self.ub {
        End
      } else {
        tup[ .. 2].copy_from_slice(xp.as_ref());
        tup[2] = y.0;
        Hit(t)
      }
    }
  }
}

#[derive(Clone, Default)]
pub struct Fun2 {
  chk:  TUSnapshot,
  attr: IHTreapMap<TNum, CVar>,
  plub: TNum,
  //idx:  CUnionIter<(TNum, CTup2)>,
  idx:  CUnionIter<(TNum, CTup2, CVar)>,
  //idx:  CUnionIter_<(TNum, CTup2, CVar)>,
  //idx:  IHTreapMap<CVar, IHTreapSet<(TNum, CTup2, CVar)>>,
  //dom:  IHTreapSet<(TNum, CTup2)>,
  pmap: IHTreapMap<CTup2, (TNum, CVar)>,
  pm2:  IHTreapMap<CTup2, IHTreapMap<CTup2, (TNum, CVar)>>,
  //prng: IHTreapMap<CVar, TNum>,
  //ndom: IHTreapSet<(TNum, CTup2, CVar)>,
  //nset: IHTreapMap<(CTup2, CVar), TNum>,
}

impl Fun2 {
  fn _patchswap(&mut self, rel: CVar, newswap: &mut Vec<SNum>, shm: &mut STFrame) -> bool {
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in it {
      for (_, olp, orx) in self.idx.iter(nx) {
        let nlp = olp.swap_var(ox, nx);
        let nlp_: &[CVar] = nlp.as_ref();
        let nlx0 = nlp_[0];
        let nlx1 = nlp_[1];
        let nrx = swap_var(orx, ox, nx);
        let (_, rx) = shm.cc.find(nrx);
        match self.pmap.get(&nlp) {
          None => {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.idx.insert(nlx0, (t, nlp, rx));
            self.idx.insert(nlx1, (t, nlp, rx));
            self.idx.insert(rx, (t, nlp, rx));
            self.pmap.remove(&olp);
            self.pmap.insert(nlp, (t, rx));
            for (perm, _) in self.pm2.clone_iter() {
              let olp = olp.perm(perm.as_ref());
              let nlp = nlp.perm(perm.as_ref());
              match self.pm2.get_mut(&perm) {
                None => unreachable!(),
                Some(pmap) => {
                  pmap.remove(&olp);
                  pmap.insert(nlp, (t, rx));
                }
              }
            }
          }
          Some(&(t, oqrx)) => {
            let (_, qrx) = shm.cc.find(oqrx);
            if ut > t {
              patch = true;
              let t = shm.clk.fresh();
              plub = t;
              self.idx.insert(nlx0, (t, nlp, qrx));
              self.idx.insert(nlx1, (t, nlp, qrx));
              self.idx.insert(qrx, (t, nlp, qrx));
              self.pmap.remove(&olp);
              self.pmap.insert(nlp, (t, qrx));
              for (perm, _) in self.pm2.clone_iter() {
                let olp = olp.perm(perm.as_ref());
                let nlp = nlp.perm(perm.as_ref());
                match self.pm2.get_mut(&perm) {
                  None => unreachable!(),
                  Some(pmap) => {
                    pmap.remove(&olp);
                    pmap.insert(nlp, (t, qrx));
                  }
                }
              }
            }
            if qrx != rx {
              newswap.push(shm._pseudo_var(rel));
              newswap.push(shm.evar.0);
              newswap.push(qrx.0);
              newswap.push(rx.0);
            }
          }
        }
      }
      for (_, olp, orx) in self.idx.iter(ox) {
        match self.pmap.get(&olp) {
          None => {}
          Some(&(ot, _)) => {
            let nlp = olp.swap_var(ox, nx);
            let nlp_: &[CVar] = nlp.as_ref();
            let nlx0 = nlp_[0];
            let nlx1 = nlp_[1];
            let nrx = swap_var(orx, ox, nx);
            let (_, rx) = shm.cc.find(nrx);
            match self.pmap.get(&nlp) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.idx.insert(nlx0, (t, nlp, rx));
                self.idx.insert(nlx1, (t, nlp, rx));
                self.idx.insert(rx, (t, nlp, rx));
                self.pmap.remove(&olp);
                self.pmap.insert(nlp, (t, rx));
                for (perm, _) in self.pm2.clone_iter() {
                  let olp = olp.perm(perm.as_ref());
                  let nlp = nlp.perm(perm.as_ref());
                  match self.pm2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pmap) => {
                      pmap.remove(&olp);
                      pmap.insert(nlp, (t, rx));
                    }
                  }
                }
              }
              Some(&(t, oqrx)) => {
                let (_, qrx) = shm.cc.find(oqrx);
                if ut > t || ut > ot {
                  patch = true;
                  let t = shm.clk.fresh();
                  plub = t;
                  self.idx.insert(nlx0, (t, nlp, qrx));
                  self.idx.insert(nlx1, (t, nlp, qrx));
                  self.idx.insert(qrx, (t, nlp, qrx));
                  self.pmap.remove(&olp);
                  self.pmap.insert(nlp, (t, qrx));
                  for (perm, _) in self.pm2.clone_iter() {
                    let olp = olp.perm(perm.as_ref());
                    let nlp = nlp.perm(perm.as_ref());
                    match self.pm2.get_mut(&perm) {
                      None => unreachable!(),
                      Some(pmap) => {
                        pmap.remove(&olp);
                        pmap.insert(nlp, (t, qrx));
                      }
                    }
                  }
                }
                if qrx != rx {
                  newswap.push(shm._pseudo_var(rel));
                  newswap.push(shm.evar.0);
                  newswap.push(qrx.0);
                  newswap.push(rx.0);
                }
              }
            }
          }
        }
      }
      self.idx.remove(ox);
    }
    self.plub = plub;
    patch
  }

  fn _patch_swap(&mut self, tlb: TNum, rel: CVar, newswap: &mut dyn ESwap, shm: &mut STFrame) -> bool {
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in it {
      for (_, olp, orx) in self.idx.iter(nx) {
        let nlp = shm.cc.tfind(olp);
        let nlp_: &[CVar] = nlp.as_ref();
        let nlx0 = nlp_[0];
        let nlx1 = nlp_[1];
        let (_, rx) = shm.cc.find(orx);
        match self.pmap.get(&nlp) {
          None => {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.idx.insert(nlx0, (t, nlp, rx));
            self.idx.insert(nlx1, (t, nlp, rx));
            self.idx.insert(rx, (t, nlp, rx));
            self.pmap.remove(&olp);
            self.pmap.insert(nlp, (t, rx));
            for (perm, _) in self.pm2.clone_iter() {
              let olp = olp.perm(perm.as_ref());
              let nlp = nlp.perm(perm.as_ref());
              match self.pm2.get_mut(&perm) {
                None => unreachable!(),
                Some(pmap) => {
                  pmap.remove(&olp);
                  pmap.insert(nlp, (t, rx));
                }
              }
            }
            newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
          }
          Some(&(t, oqrx)) => {
            let (_, qrx) = shm.cc.find(oqrx);
            if ut > t {
              patch = true;
              let t = shm.clk.fresh();
              plub = t;
              self.idx.insert(nlx0, (t, nlp, qrx));
              self.idx.insert(nlx1, (t, nlp, qrx));
              self.idx.insert(qrx, (t, nlp, qrx));
              self.pmap.remove(&olp);
              self.pmap.insert(nlp, (t, qrx));
              for (perm, _) in self.pm2.clone_iter() {
                let olp = olp.perm(perm.as_ref());
                let nlp = nlp.perm(perm.as_ref());
                match self.pm2.get_mut(&perm) {
                  None => unreachable!(),
                  Some(pmap) => {
                    pmap.remove(&olp);
                    pmap.insert(nlp, (t, qrx));
                  }
                }
              }
              newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
            }
            if qrx != rx {
              newswap.stage_tup(
                  tlb,
                  SwapEvent::Pat(shm.pseudo_var(rel), rel.0, nlp.as_ref(), &[qrx.0, rx.0]),
                  shm.evar.0,
                  &[qrx.0, rx.0],
              );
            }
          }
        }
      }
      for (_, olp, orx) in self.idx.iter(ox) {
        match self.pmap.get(&olp) {
          None => {}
          Some(&(ot, _)) => {
            let nlp = shm.cc.tfind(olp);
            let nlp_: &[CVar] = nlp.as_ref();
            let nlx0 = nlp_[0];
            let nlx1 = nlp_[1];
            let (_, rx) = shm.cc.find(orx);
            match self.pmap.get(&nlp) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.idx.insert(nlx0, (t, nlp, rx));
                self.idx.insert(nlx1, (t, nlp, rx));
                self.idx.insert(rx, (t, nlp, rx));
                self.pmap.remove(&olp);
                self.pmap.insert(nlp, (t, rx));
                for (perm, _) in self.pm2.clone_iter() {
                  let olp = olp.perm(perm.as_ref());
                  let nlp = nlp.perm(perm.as_ref());
                  match self.pm2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pmap) => {
                      pmap.remove(&olp);
                      pmap.insert(nlp, (t, rx));
                    }
                  }
                }
                newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
              }
              Some(&(t, oqrx)) => {
                let (_, qrx) = shm.cc.find(oqrx);
                if ut > t || ut > ot {
                  patch = true;
                  let t = shm.clk.fresh();
                  plub = t;
                  self.idx.insert(nlx0, (t, nlp, qrx));
                  self.idx.insert(nlx1, (t, nlp, qrx));
                  self.idx.insert(qrx, (t, nlp, qrx));
                  self.pmap.remove(&olp);
                  self.pmap.insert(nlp, (t, qrx));
                  for (perm, _) in self.pm2.clone_iter() {
                    let olp = olp.perm(perm.as_ref());
                    let nlp = nlp.perm(perm.as_ref());
                    match self.pm2.get_mut(&perm) {
                      None => unreachable!(),
                      Some(pmap) => {
                        pmap.remove(&olp);
                        pmap.insert(nlp, (t, qrx));
                      }
                    }
                  }
                  newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
                }
                if qrx != rx {
                  newswap.stage_tup(
                      tlb,
                      SwapEvent::Pat(shm.pseudo_var(rel), rel.0, nlp.as_ref(), &[qrx.0, rx.0]),
                      shm.evar.0,
                      &[qrx.0, rx.0],
                  );
                }
              }
            }
          }
        }
      }
      self.idx.remove(ox);
    }
    self.plub = plub;
    patch
  }
}

impl ERel for Fun2 {
  fn clone_ref(&self) -> ERelRef {
    Rc::new(self.clone())
  }

  fn arity(&self) -> usize {
    3
  }

  fn kind2(&self) -> (RelKind, RelKind2) {
    (RelKind::Fun, RelKind2::Exact)
  }

  fn fun_arity(&self) -> Option<(usize, usize)> {
    Some((2, 1))
  }

  fn pos_least_ub(&self, _shm: &STFrame) -> TNum {
    self.plub
  }

  fn neg_least_ub(&self, _shm: &STFrame) -> TNum {
    0
  }

  fn pos_tup_size(&self, _shm: &STFrame) -> u64 {
    self.pmap.len() as u64
  }

  fn neg_tup_size(&self, _shm: &STFrame) -> u64 {
    //self.nset.len() as u64
    0
  }

  fn dump_tups(&self, rel: CVar, prefix: &str, _shm: &STFrame) {
    println!("{}Fun2::dump_tups: rel={} +{}",
        prefix, rel.0, self.pmap.len());
    for (xp, &(t, y)) in self.pmap.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  + {} {:?} -> {}", prefix, t, xp_, y.0);
    }
  }

  /*fn patch(&mut self, rel: CVar, clk: &mut TClk, shm: &mut STFrame) {
    self._patch(rel, &mut shm.cc, clk);
  }*/

  fn patchswap(&mut self, rel: CVar, newswap: &mut Vec<SNum>, shm: &mut STFrame) {
    self._patchswap(rel, newswap, shm);
  }

  fn patch_swap(&mut self, tlb: TNum, rel: CVar, newswap: &mut dyn ESwap, shm: &mut STFrame) {
    self._patch_swap(tlb, rel, newswap, shm);
  }

  fn flag_tup(&mut self, _rel: CVar, _tup: &mut [SNum]) -> Option<TNum> {
    None
  }

  fn test_pos_tup(&mut self, rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[lk0, lk1, rk] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(rel, &mut shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let lxp = CTup2([lx0, lx1]);
      match self.pmap.get(&lxp) {
        None => {}
        Some(&(rt, rx)) => {
          let (_, rq) = shm.cc.find(rk);
          if rx == rq {
            return Some(rt);
          }
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn scan_pos(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup2::from(&ubtup[ .. 2]);
    let iter = self.pmap.clone_iter_from(&lbtup[ .. 2]);
    let scan = Box::new(FScan2{ub, iter});
    scan
  }

  fn permscan_pos(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    match self.pm2.get(perm) {
      None => {
        let mut pmap = IHTreapMap::default();
        for (xp, &t) in self.pmap.iter() {
          let xp = xp.perm(perm);
          pmap.insert(xp, t);
        }
        self.pm2.insert(CTup2::from(perm), pmap);
      }
      Some(_) => {}
    }
    match self.pm2.get(perm) {
      None => unreachable!(),
      Some(pmap) => {
        let ub = CTup2::from(&ubtup[ .. 2]);
        let iter = pmap.clone_iter_from(&lbtup[ .. 2]);
        let scan = Box::new(FScan2{ub, iter});
        scan
      }
    }
  }

  fn scan_par(&self, _rel: CVar, _shm: &STFrame) -> EScanBox {
    Box::new(EmpScan{})
  }

  fn swap_pos_tup(&mut self, rec: CVar, rel: CVar, tup: &[SNum], newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[lk0, lk1, rk] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(rel, &mut shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let (_, rx) = shm.cc.find(rk);
      let lxp = CTup2([lx0, lx1]);
      match self.pmap.get(&lxp) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.idx.insert(lx0, (t, lxp, rx));
          self.idx.insert(lx1, (t, lxp, rx));
          self.idx.insert(rx, (t, lxp, rx));
          //self.dom.insert((t, lxp));
          self.pmap.insert(lxp, (t, rx));
          for (perm, _) in self.pm2.clone_iter() {
            let lxp = lxp.perm(perm.as_ref());
            match self.pm2.get_mut(&perm) {
              None => unreachable!(),
              Some(pmap) => {
                pmap.insert(lxp, (t, rx));
              }
            }
          }
          swaptup.extend_from_slice(lxp.as_ref());
          swaptup.push(rx.0);
          return Some(t);
        }
        Some(&(t, orx)) => if orx != rx {
          newswap.push(shm._pseudo_var(rel));
          newswap.push(shm.evar.0);
          newswap.push(orx.0);
          newswap.push(rx.0);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn swap_pos_tup_(&mut self, tlb: TNum, rec: CVar, rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[lk0, lk1, rk] = as_cvars(tup) {
      //assert!(self.chk.is_ulive(&shm.cc));
      if !self.chk.is_ulive(&shm.cc) {
        println!("TRACE: Fun2::swap_pos_tup_: rec={} rel={} tup={:?} chk.tu={} cc.tu={}",
            rec.0, rel.0, tup,
            self.chk.tu, shm.cc.tu);
        panic!("BUG");
      }
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let (_, rx) = shm.cc.find(rk);
      let lxp = CTup2([lx0, lx1]);
      match self.pmap.get(&lxp) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.idx.insert(lx0, (t, lxp, rx));
          self.idx.insert(lx1, (t, lxp, rx));
          self.idx.insert(rx, (t, lxp, rx));
          //self.dom.insert((t, lxp));
          self.pmap.insert(lxp, (t, rx));
          for (perm, _) in self.pm2.clone_iter() {
            let lxp = lxp.perm(perm.as_ref());
            match self.pm2.get_mut(&perm) {
              None => unreachable!(),
              Some(pmap) => {
                pmap.insert(lxp, (t, rx));
              }
            }
          }
          swaptup.extend_from_slice(lxp.as_ref());
          swaptup.push(rx.0);
          (Fresh, t)
        }
        Some(&(t, orx)) => {
          if orx != rx {
            newswap.stage_tup(
                tlb,
                SwapEvent::Pat(shm.pseudo_var(rel), rel.0, lxp.as_ref(), &[orx.0, rx.0]),
                shm.evar.0,
                &[orx.0, rx.0],
            );
            swaptup.extend_from_slice(lxp.as_ref());
            swaptup.push(rx.0);
            (Merge, t)
          } else if t >= tlb {
            swaptup.extend_from_slice(lxp.as_ref());
            swaptup.push(rx.0);
            (Stale, t)
          } else {
            (Noswap, 0)
          }
        }
      }
    } else {
      unreachable!();
    }
  }
}

#[derive(Clone, Default)]
pub struct SymmFun2 {
  chk:  TUSnapshot,
  attr: IHTreapMap<TNum, CVar>,
  plub: TNum,
  //idx:  CUnionIter<(TNum, CTup2)>,
  idx:  CUnionIter<(TNum, CTup2, CVar)>,
  //idx:  IHTreapMap<CVar, IHTreapSet<(TNum, CTup2, CVar)>>,
  //idx:  CUnionIter_<(TNum, CTup2, CVar)>,
  //dom:  IHTreapSet<(TNum, CTup2)>,
  pmap: IHTreapMap<CTup2, (TNum, CVar)>,
}

impl SymmFun2 {
  fn _patchswap(&mut self, rel: CVar, newswap: &mut Vec<SNum>, shm: &mut STFrame) -> bool {
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in it {
      for (_, olp, orx) in self.idx.iter(nx) {
        let nlp = olp.swap_var(ox, nx);
        let nlp_: &[CVar] = nlp.as_ref();
        let nlx0 = nlp_[0];
        let nlx1 = nlp_[1];
        let nrx = swap_var(orx, ox, nx);
        let (_, rx) = shm.cc.find(nrx);
        match self.pmap.get(&nlp) {
          None => {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.idx.insert(nlx0, (t, nlp, rx));
            self.idx.insert(nlx1, (t, nlp, rx));
            self.idx.insert(rx, (t, nlp, rx));
            self.pmap.remove(&olp);
            self.pmap.insert(nlp, (t, rx));
          }
          Some(&(t, oqrx)) => {
            let (_, qrx) = shm.cc.find(oqrx);
            if ut > t {
              patch = true;
              let t = shm.clk.fresh();
              plub = t;
              self.idx.insert(nlx0, (t, nlp, qrx));
              self.idx.insert(nlx1, (t, nlp, qrx));
              self.idx.insert(qrx, (t, nlp, qrx));
              self.pmap.remove(&olp);
              self.pmap.insert(nlp, (t, qrx));
            }
            if qrx != rx {
              newswap.push(shm._pseudo_var(rel));
              newswap.push(shm.evar.0);
              newswap.push(qrx.0);
              newswap.push(rx.0);
            }
          }
        }
      }
      for (_, olp, orx) in self.idx.iter(ox) {
        match self.pmap.get(&olp) {
          None => {}
          Some(&(ot, _)) => {
            let nlp = olp.swap_var(ox, nx);
            let nlp_: &[CVar] = nlp.as_ref();
            let nlx0 = nlp_[0];
            let nlx1 = nlp_[1];
            let nrx = swap_var(orx, ox, nx);
            let (_, rx) = shm.cc.find(nrx);
            match self.pmap.get(&nlp) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.idx.insert(nlx0, (t, nlp, rx));
                self.idx.insert(nlx1, (t, nlp, rx));
                self.idx.insert(rx, (t, nlp, rx));
                self.pmap.remove(&olp);
                self.pmap.insert(nlp, (t, rx));
              }
              Some(&(t, oqrx)) => {
                let (_, qrx) = shm.cc.find(oqrx);
                if ut > t || ut > ot {
                  patch = true;
                  let t = shm.clk.fresh();
                  plub = t;
                  self.idx.insert(nlx0, (t, nlp, qrx));
                  self.idx.insert(nlx1, (t, nlp, qrx));
                  self.idx.insert(qrx, (t, nlp, qrx));
                  self.pmap.remove(&olp);
                  self.pmap.insert(nlp, (t, qrx));
                }
                if qrx != rx {
                  newswap.push(shm._pseudo_var(rel));
                  newswap.push(shm.evar.0);
                  newswap.push(qrx.0);
                  newswap.push(rx.0);
                }
              }
            }
          }
        }
      }
      self.idx.remove(ox);
    }
    self.plub = plub;
    patch
  }

  fn _patch_swap(&mut self, tlb: TNum, rel: CVar, newswap: &mut dyn ESwap, shm: &mut STFrame) -> bool {
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in it {
      for (_, olp, orx) in self.idx.iter(nx) {
        let nlp = shm.cc.tfind(olp);
        let nlp_: &[CVar] = nlp.as_ref();
        let nlx0 = nlp_[0];
        let nlx1 = nlp_[1];
        let (_, rx) = shm.cc.find(orx);
        match self.pmap.get(&nlp) {
          None => {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.idx.insert(nlx0, (t, nlp, rx));
            self.idx.insert(nlx1, (t, nlp, rx));
            self.idx.insert(rx, (t, nlp, rx));
            self.pmap.remove(&olp);
            self.pmap.insert(nlp, (t, rx));
            newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
          }
          Some(&(t, oqrx)) => {
            let (_, qrx) = shm.cc.find(oqrx);
            if ut > t {
              patch = true;
              let t = shm.clk.fresh();
              plub = t;
              self.idx.insert(nlx0, (t, nlp, qrx));
              self.idx.insert(nlx1, (t, nlp, qrx));
              self.idx.insert(qrx, (t, nlp, qrx));
              self.pmap.remove(&olp);
              self.pmap.insert(nlp, (t, qrx));
              newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
            }
            if qrx != rx {
              newswap.stage_tup(
                  tlb,
                  SwapEvent::Pat(shm.pseudo_var(rel), rel.0, nlp.as_ref(), &[qrx.0, rx.0]),
                  shm.evar.0,
                  &[qrx.0, rx.0],
              );
            }
          }
        }
      }
      for (_, olp, orx) in self.idx.iter(ox) {
        match self.pmap.get(&olp) {
          None => {}
          Some(&(ot, _)) => {
            let nlp = shm.cc.tfind(olp);
            let nlp_: &[CVar] = nlp.as_ref();
            let nlx0 = nlp_[0];
            let nlx1 = nlp_[1];
            let (_, rx) = shm.cc.find(orx);
            match self.pmap.get(&nlp) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.idx.insert(nlx0, (t, nlp, rx));
                self.idx.insert(nlx1, (t, nlp, rx));
                self.idx.insert(rx, (t, nlp, rx));
                self.pmap.remove(&olp);
                self.pmap.insert(nlp, (t, rx));
                newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
              }
              Some(&(t, oqrx)) => {
                let (_, qrx) = shm.cc.find(oqrx);
                if ut > t || ut > ot {
                  patch = true;
                  let t = shm.clk.fresh();
                  plub = t;
                  self.idx.insert(nlx0, (t, nlp, qrx));
                  self.idx.insert(nlx1, (t, nlp, qrx));
                  self.idx.insert(qrx, (t, nlp, qrx));
                  self.pmap.remove(&olp);
                  self.pmap.insert(nlp, (t, qrx));
                  newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
                }
                if qrx != rx {
                  newswap.stage_tup(
                      tlb,
                      SwapEvent::Pat(shm.pseudo_var(rel), rel.0, nlp.as_ref(), &[qrx.0, rx.0]),
                      shm.evar.0,
                      &[qrx.0, rx.0],
                  );
                }
              }
            }
          }
        }
      }
      self.idx.remove(ox);
    }
    self.plub = plub;
    patch
  }
}

impl ERel for SymmFun2 {
  fn clone_ref(&self) -> ERelRef {
    Rc::new(self.clone())
  }

  fn arity(&self) -> usize {
    3
  }

  fn kind2(&self) -> (RelKind, RelKind2) {
    (RelKind::Fun, RelKind2::LSymmF)
  }

  fn fun_arity(&self) -> Option<(usize, usize)> {
    Some((2, 1))
  }

  fn pos_least_ub(&self, _shm: &STFrame) -> TNum {
    self.plub
  }

  fn neg_least_ub(&self, _shm: &STFrame) -> TNum {
    0
  }

  fn pos_tup_size(&self, _shm: &STFrame) -> u64 {
    self.pmap.len() as u64
  }

  fn neg_tup_size(&self, _shm: &STFrame) -> u64 {
    0
  }

  fn dump_tups(&self, rel: CVar, prefix: &str, _shm: &STFrame) {
    println!("{}SymmFun2::dump_tups: rel={} +{}",
        prefix, rel.0, self.pmap.len());
    for (xp, &(t, y)) in self.pmap.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  + {} {:?} -> {}", prefix, t, xp_, y.0);
    }
  }

  /*fn patch(&mut self, rel: CVar, clk: &mut TClk, shm: &mut STFrame) {
    self._patch(rel, &mut shm.cc, clk);
  }*/

  fn patchswap(&mut self, rel: CVar, newswap: &mut Vec<SNum>, shm: &mut STFrame) {
    self._patchswap(rel, newswap, shm);
  }

  fn patch_swap(&mut self, tlb: TNum, rel: CVar, newswap: &mut dyn ESwap, shm: &mut STFrame) {
    self._patch_swap(tlb, rel, newswap, shm);
  }

  fn flag_tup(&mut self, _rel: CVar, _tup: &mut [SNum]) -> Option<TNum> {
    None
  }

  fn test_pos_tup(&mut self, rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[lk0, lk1, rk] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(rel, &mut shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let lxp = CTup2([lx0, lx1]);
      match self.pmap.get(&lxp) {
        None => {}
        Some(&(rt, rx)) => {
          let (_, rq) = shm.cc.find(rk);
          if rx == rq {
            return Some(rt);
          }
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn scan_pos(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup2::from(&ubtup[ .. 2]);
    let iter = self.pmap.clone_iter_from(&lbtup[ .. 2]);
    let scan = Box::new(FScan2{ub, iter});
    scan
  }

  fn permscan_pos(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    self.scan_pos(_rel, lbtup, ubtup, _shm)
  }

  fn scan_par(&self, _rel: CVar, _shm: &STFrame) -> EScanBox {
    Box::new(EmpScan{})
  }

  fn swap_pos_tup(&mut self, rec: CVar, rel: CVar, tup: &[SNum], newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[lk0, lk1, rk] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(rel, &mut shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let (_, rx) = shm.cc.find(rk);
      let mut lxp = CTup2([lx0, lx1]).sort();
      let mut ret = None;
      loop {
        match self.pmap.get(&lxp) {
          None => {
            let t = shm.clk.fresh();
            self.plub = t;
            self.idx.insert(lx0, (t, lxp, rx));
            self.idx.insert(lx1, (t, lxp, rx));
            self.idx.insert(rx, (t, lxp, rx));
            self.pmap.insert(lxp, (t, rx));
            swaptup.extend_from_slice(lxp.as_ref());
            swaptup.push(rx.0);
            ret = Some(t);
          }
          Some(&(t, orx)) => if orx != rx {
            newswap.push(shm._pseudo_var(rel));
            newswap.push(shm.evar.0);
            newswap.push(orx.0);
            newswap.push(rx.0);
          }
        }
        let lxp_: &mut [SNum] = lxp.as_mut();
        if next_permutation(lxp_).is_none() {
          break;
        }
      }
      ret
    } else {
      unreachable!();
    }
  }

  fn swap_pos_tup_(&mut self, tlb: TNum, rec: CVar, rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[lk0, lk1, rk] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let (_, rx) = shm.cc.find(rk);
      let mut lxp = CTup2([lx0, lx1]).sort();
      let mut merge = None;
      let mut fresh = None;
      let mut stale = None;
      loop {
        match self.pmap.get(&lxp) {
          None => {
            let t = shm.clk.fresh();
            self.plub = t;
            self.idx.insert(lx0, (t, lxp, rx));
            self.idx.insert(lx1, (t, lxp, rx));
            self.idx.insert(rx, (t, lxp, rx));
            self.pmap.insert(lxp, (t, rx));
            //swaptup.extend_from_slice(lxp.as_ref());
            //swaptup.push(rx.0);
            fresh = Some(t);
          }
          Some(&(t, orx)) => {
            if orx != rx {
              newswap.stage_tup(
                  tlb,
                  SwapEvent::Pat(shm.pseudo_var(rel), rel.0, lxp.as_ref(), &[orx.0, rx.0]),
                  shm.evar.0,
                  &[orx.0, rx.0],
              );
              //swaptup.extend_from_slice(lxp.as_ref());
              //swaptup.push(rx.0);
              merge = Some(t);
            } else if t >= tlb {
              //swaptup.extend_from_slice(lxp.as_ref());
              //swaptup.push(rx.0);
              stale = Some(t);
            }
          }
        }
        swaptup.extend_from_slice(lxp.as_ref());
        swaptup.push(rx.0);
        let lxp_: &mut [SNum] = lxp.as_mut();
        if next_permutation(lxp_).is_none() {
          break;
        }
      }
      _from_merge_fresh_stale(merge, fresh, stale)
    } else {
      unreachable!();
    }
  }
}

pub struct FScan3 {
  ub:   CTup3,
  iter: IHTreapMapCloneIter<CTup3, (TNum, CVar)>,
  //iter: IHTreapMapCloneIter<CTup3, (CVar, TNum)>,
}

impl EScan for FScan3 {
  fn next_tup(&mut self, tup: &mut [SNum], /*shm: &mut STFrame*/) -> TScanResult {
    match self.iter.next() {
      None => {
        End
      }
      Some((xp, (t, y))) => if xp > self.ub {
      //Some((xp, (y, t))) => if xp > self.ub {
        End
      } else {
        tup[ .. 3].copy_from_slice(xp.as_ref());
        tup[3] = y.0;
        Hit(t)
      }
    }
  }
}

#[derive(Clone, Default)]
pub struct Fun3 {
  chk:  TUSnapshot,
  attr: IHTreapMap<TNum, CVar>,
  plub: TNum,
  //idx:  CUnionIter<(TNum, CTup3)>,
  idx:  CUnionIter<(TNum, CTup3, CVar)>,
  //idx:  IHTreapMap<CVar, IHTreapSet<(TNum, CTup3, CVar)>>,
  //idx:  CUnionIter_<(TNum, CTup3, CVar)>,
  //dom:  IHTreapSet<(TNum, CTup3)>,
  pmap: IHTreapMap<CTup3, (TNum, CVar)>,
  pm2:  IHTreapMap<CTup3, IHTreapMap<CTup3, (TNum, CVar)>>,
  //ndom: IHTreapSet<(TNum, CTup3, CVar)>,
  //nset: IHTreapMap<(CTup3, CVar), TNum>,
}

impl Fun3 {
  fn _patchswap(&mut self, rel: CVar, newswap: &mut Vec<SNum>, shm: &mut STFrame) -> bool {
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in it {
      for (_, olp, orx) in self.idx.iter(nx) {
        let nlp = olp.swap_var(ox, nx);
        let nlp_: &[CVar] = nlp.as_ref();
        let nlx0 = nlp_[0];
        let nlx1 = nlp_[1];
        let nlx2 = nlp_[2];
        let nrx = swap_var(orx, ox, nx);
        let (_, rx) = shm.cc.find(nrx);
        match self.pmap.get(&nlp) {
          None => {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.idx.insert(nlx0, (t, nlp, rx));
            self.idx.insert(nlx1, (t, nlp, rx));
            self.idx.insert(nlx2, (t, nlp, rx));
            self.idx.insert(rx, (t, nlp, rx));
            self.pmap.remove(&olp);
            self.pmap.insert(nlp, (t, rx));
            for (perm, _) in self.pm2.clone_iter() {
              let olp = olp.perm(perm.as_ref());
              let nlp = nlp.perm(perm.as_ref());
              match self.pm2.get_mut(&perm) {
                None => unreachable!(),
                Some(pmap) => {
                  pmap.remove(&olp);
                  pmap.insert(nlp, (t, rx));
                }
              }
            }
          }
          Some(&(t, oqrx)) => {
            let (_, qrx) = shm.cc.find(oqrx);
            if ut > t {
              patch = true;
              let t = shm.clk.fresh();
              plub = t;
              self.idx.insert(nlx0, (t, nlp, qrx));
              self.idx.insert(nlx1, (t, nlp, qrx));
              self.idx.insert(nlx2, (t, nlp, qrx));
              self.idx.insert(qrx, (t, nlp, qrx));
              self.pmap.remove(&olp);
              self.pmap.insert(nlp, (t, qrx));
              for (perm, _) in self.pm2.clone_iter() {
                let olp = olp.perm(perm.as_ref());
                let nlp = nlp.perm(perm.as_ref());
                match self.pm2.get_mut(&perm) {
                  None => unreachable!(),
                  Some(pmap) => {
                    pmap.remove(&olp);
                    pmap.insert(nlp, (t, qrx));
                  }
                }
              }
            }
            if qrx != rx {
              newswap.push(shm._pseudo_var(rel));
              newswap.push(shm.evar.0);
              newswap.push(qrx.0);
              newswap.push(rx.0);
            }
          }
        }
      }
      for (_, olp, orx) in self.idx.iter(ox) {
        match self.pmap.get(&olp) {
          None => {}
          Some(&(ot, _)) => {
            let nlp = olp.swap_var(ox, nx);
            let nlp_: &[CVar] = nlp.as_ref();
            let nlx0 = nlp_[0];
            let nlx1 = nlp_[1];
            let nlx2 = nlp_[2];
            let nrx = swap_var(orx, ox, nx);
            let (_, rx) = shm.cc.find(nrx);
            match self.pmap.get(&nlp) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.idx.insert(nlx0, (t, nlp, rx));
                self.idx.insert(nlx1, (t, nlp, rx));
                self.idx.insert(nlx2, (t, nlp, rx));
                self.idx.insert(rx, (t, nlp, rx));
                self.pmap.remove(&olp);
                self.pmap.insert(nlp, (t, rx));
                for (perm, _) in self.pm2.clone_iter() {
                  let olp = olp.perm(perm.as_ref());
                  let nlp = nlp.perm(perm.as_ref());
                  match self.pm2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pmap) => {
                      pmap.remove(&olp);
                      pmap.insert(nlp, (t, rx));
                    }
                  }
                }
              }
              Some(&(t, oqrx)) => {
                let (_, qrx) = shm.cc.find(oqrx);
                if ut > t || ut > ot {
                  patch = true;
                  let t = shm.clk.fresh();
                  plub = t;
                  self.idx.insert(nlx0, (t, nlp, qrx));
                  self.idx.insert(nlx1, (t, nlp, qrx));
                  self.idx.insert(nlx2, (t, nlp, qrx));
                  self.idx.insert(qrx, (t, nlp, qrx));
                  self.pmap.remove(&olp);
                  self.pmap.insert(nlp, (t, qrx));
                  for (perm, _) in self.pm2.clone_iter() {
                    let olp = olp.perm(perm.as_ref());
                    let nlp = nlp.perm(perm.as_ref());
                    match self.pm2.get_mut(&perm) {
                      None => unreachable!(),
                      Some(pmap) => {
                        pmap.remove(&olp);
                        pmap.insert(nlp, (t, qrx));
                      }
                    }
                  }
                }
                if qrx != rx {
                  newswap.push(shm._pseudo_var(rel));
                  newswap.push(shm.evar.0);
                  newswap.push(qrx.0);
                  newswap.push(rx.0);
                }
              }
            }
          }
        }
      }
      self.idx.remove(ox);
    }
    self.plub = plub;
    patch
  }

  fn _patch_swap(&mut self, tlb: TNum, rel: CVar, newswap: &mut dyn ESwap, shm: &mut STFrame) -> bool {
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in it {
      for (_, olp, orx) in self.idx.iter(nx) {
        let nlp = shm.cc.tfind(olp);
        let nlp_: &[CVar] = nlp.as_ref();
        let nlx0 = nlp_[0];
        let nlx1 = nlp_[1];
        let nlx2 = nlp_[2];
        let (_, rx) = shm.cc.find(orx);
        match self.pmap.get(&nlp) {
          None => {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.idx.insert(nlx0, (t, nlp, rx));
            self.idx.insert(nlx1, (t, nlp, rx));
            self.idx.insert(nlx2, (t, nlp, rx));
            self.idx.insert(rx, (t, nlp, rx));
            self.pmap.remove(&olp);
            self.pmap.insert(nlp, (t, rx));
            for (perm, _) in self.pm2.clone_iter() {
              let olp = olp.perm(perm.as_ref());
              let nlp = nlp.perm(perm.as_ref());
              match self.pm2.get_mut(&perm) {
                None => unreachable!(),
                Some(pmap) => {
                  pmap.remove(&olp);
                  pmap.insert(nlp, (t, rx));
                }
              }
            }
            newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
          }
          Some(&(t, oqrx)) => {
            let (_, qrx) = shm.cc.find(oqrx);
            if ut > t {
              patch = true;
              let t = shm.clk.fresh();
              plub = t;
              self.idx.insert(nlx0, (t, nlp, qrx));
              self.idx.insert(nlx1, (t, nlp, qrx));
              self.idx.insert(nlx2, (t, nlp, qrx));
              self.idx.insert(qrx, (t, nlp, qrx));
              self.pmap.remove(&olp);
              self.pmap.insert(nlp, (t, qrx));
              for (perm, _) in self.pm2.clone_iter() {
                let olp = olp.perm(perm.as_ref());
                let nlp = nlp.perm(perm.as_ref());
                match self.pm2.get_mut(&perm) {
                  None => unreachable!(),
                  Some(pmap) => {
                    pmap.remove(&olp);
                    pmap.insert(nlp, (t, qrx));
                  }
                }
              }
              newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
            }
            if qrx != rx {
              newswap.stage_tup(
                  tlb,
                  SwapEvent::Pat(shm.pseudo_var(rel), rel.0, nlp.as_ref(), &[qrx.0, rx.0]),
                  shm.evar.0,
                  &[qrx.0, rx.0],
              );
            }
          }
        }
      }
      for (_, olp, orx) in self.idx.iter(ox) {
        match self.pmap.get(&olp) {
          None => {}
          Some(&(ot, _)) => {
            let nlp = shm.cc.tfind(olp);
            let nlp_: &[CVar] = nlp.as_ref();
            let nlx0 = nlp_[0];
            let nlx1 = nlp_[1];
            let nlx2 = nlp_[2];
            let (_, rx) = shm.cc.find(orx);
            match self.pmap.get(&nlp) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.idx.insert(nlx0, (t, nlp, rx));
                self.idx.insert(nlx1, (t, nlp, rx));
                self.idx.insert(nlx2, (t, nlp, rx));
                self.idx.insert(rx, (t, nlp, rx));
                self.pmap.remove(&olp);
                self.pmap.insert(nlp, (t, rx));
                for (perm, _) in self.pm2.clone_iter() {
                  let olp = olp.perm(perm.as_ref());
                  let nlp = nlp.perm(perm.as_ref());
                  match self.pm2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pmap) => {
                      pmap.remove(&olp);
                      pmap.insert(nlp, (t, rx));
                    }
                  }
                }
                newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
              }
              Some(&(t, oqrx)) => {
                let (_, qrx) = shm.cc.find(oqrx);
                if ut > t || ut > ot {
                  patch = true;
                  let t = shm.clk.fresh();
                  plub = t;
                  self.idx.insert(nlx0, (t, nlp, qrx));
                  self.idx.insert(nlx1, (t, nlp, qrx));
                  self.idx.insert(nlx2, (t, nlp, qrx));
                  self.idx.insert(qrx, (t, nlp, qrx));
                  self.pmap.remove(&olp);
                  self.pmap.insert(nlp, (t, qrx));
                  for (perm, _) in self.pm2.clone_iter() {
                    let olp = olp.perm(perm.as_ref());
                    let nlp = nlp.perm(perm.as_ref());
                    match self.pm2.get_mut(&perm) {
                      None => unreachable!(),
                      Some(pmap) => {
                        pmap.remove(&olp);
                        pmap.insert(nlp, (t, qrx));
                      }
                    }
                  }
                  newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
                }
                if qrx != rx {
                  newswap.stage_tup(
                      tlb,
                      SwapEvent::Pat(shm.pseudo_var(rel), rel.0, nlp.as_ref(), &[qrx.0, rx.0]),
                      shm.evar.0,
                      &[qrx.0, rx.0],
                  );
                }
              }
            }
          }
        }
      }
      self.idx.remove(ox);
    }
    self.plub = plub;
    patch
  }
}

impl ERel for Fun3 {
  fn clone_ref(&self) -> ERelRef {
    Rc::new(self.clone())
  }

  /*fn anycast_ref(&self) -> &dyn Any {
    self
  }*/

  fn arity(&self) -> usize {
    4
  }

  fn kind2(&self) -> (RelKind, RelKind2) {
    (RelKind::Fun, RelKind2::Exact)
  }

  fn fun_arity(&self) -> Option<(usize, usize)> {
    Some((3, 1))
  }

  fn pos_least_ub(&self, _shm: &STFrame) -> TNum {
    self.plub
  }

  fn neg_least_ub(&self, _shm: &STFrame) -> TNum {
    0
  }

  fn pos_tup_size(&self, _shm: &STFrame) -> u64 {
    self.pmap.len() as u64
  }

  fn neg_tup_size(&self, _shm: &STFrame) -> u64 {
    //self.nset.len() as u64
    0
  }

  fn dump_tups(&self, rel: CVar, prefix: &str, _shm: &STFrame) {
    println!("{}Fun3::dump_tups: rel={} +{}",
        prefix, rel.0, self.pmap.len());
    for (xp, &(t, y)) in self.pmap.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  + {} {:?} -> {}", prefix, t, xp_, y.0);
    }
  }

  /*fn patchdiff(&self, rel: CVar, older: &dyn ERel, shm: &mut STFrame) -> (usize, usize) {
    if let Some(older) = older.anycast_ref().downcast_ref::<Fun3>() {
      let mut patch_pmap = IHTreapMap::default();
      for (&kxp, &(t, ky)) in older.pmap.iter() {
        let kxp_: &[CVar] = kxp.as_ref();
        let (_, x0) = shm.cc.find(kxp_[0]);
        let (_, x1) = shm.cc.find(kxp_[1]);
        let (_, x2) = shm.cc.find(kxp_[2]);
        let xp = CTup3::from([x0, x1, x2]);
        let (_, y) = shm.cc.find(ky);
        patch_pmap.insert(xp, (t, y));
      }
      (max(patch_pmap.len(), self.pmap.len()) - patch_pmap.len(),
       0)
    } else {
      panic!("bug: Fun3::patchdiff: mismatched type");
    }
  }*/

  /*fn patch(&mut self, rel: CVar, clk: &mut TClk, shm: &mut STFrame) {
    self._patch(rel, &mut shm.cc, clk);
  }*/

  fn patchswap(&mut self, rel: CVar, newswap: &mut Vec<SNum>, shm: &mut STFrame) {
    self._patchswap(rel, newswap, shm);
  }

  fn patch_swap(&mut self, tlb: TNum, rel: CVar, newswap: &mut dyn ESwap, shm: &mut STFrame) {
    self._patch_swap(tlb, rel, newswap, shm);
  }

  fn flag_tup(&mut self, _rel: CVar, _tup: &mut [SNum]) -> Option<TNum> {
    None
  }

  fn test_pos_tup(&mut self, rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[lk0, lk1, lk2, rk] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(rel, &mut shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let (_, lx2) = shm.cc.find(lk2);
      let lxp = CTup3([lx0, lx1, lx2]);
      match self.pmap.get(&lxp) {
        None => {}
        Some(&(rt, rx)) => {
          let (_, rq) = shm.cc.find(rk);
          if rx == rq {
            return Some(rt);
          }
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn scan_pos(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup3::from(&ubtup[ .. 3]);
    let iter = self.pmap.clone_iter_from(&lbtup[ .. 3]);
    let scan = Box::new(FScan3{ub, iter});
    scan
  }

  fn permscan_pos(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    match self.pm2.get(perm) {
      None => {
        let mut pmap = IHTreapMap::default();
        for (xp, &t) in self.pmap.iter() {
          let xp = xp.perm(perm);
          pmap.insert(xp, t);
        }
        self.pm2.insert(CTup3::from(perm), pmap);
      }
      Some(_) => {}
    }
    match self.pm2.get(perm) {
      None => unreachable!(),
      Some(pmap) => {
        let ub = CTup3::from(&ubtup[ .. 3]);
        let iter = pmap.clone_iter_from(&lbtup[ .. 3]);
        let scan = Box::new(FScan3{ub, iter});
        scan
      }
    }
  }

  fn scan_par(&self, _rel: CVar, _shm: &STFrame) -> EScanBox {
    Box::new(EmpScan{})
  }

  fn swap_pos_tup(&mut self, rec: CVar, rel: CVar, tup: &[SNum], newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[lk0, lk1, lk2, rk] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(rel, &mut shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let (_, lx2) = shm.cc.find(lk2);
      let (_, rx) = shm.cc.find(rk);
      let lxp = CTup3([lx0, lx1, lx2]);
      match self.pmap.get(&lxp) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.idx.insert(lx0, (t, lxp, rx));
          self.idx.insert(lx1, (t, lxp, rx));
          self.idx.insert(lx2, (t, lxp, rx));
          self.idx.insert(rx, (t, lxp, rx));
          //self.dom.insert((t, lxp));
          self.pmap.insert(lxp, (t, rx));
          for (perm, _) in self.pm2.clone_iter() {
            let lxp = lxp.perm(perm.as_ref());
            match self.pm2.get_mut(&perm) {
              None => unreachable!(),
              Some(pmap) => {
                pmap.insert(lxp, (t, rx));
              }
            }
          }
          swaptup.extend_from_slice(lxp.as_ref());
          swaptup.push(rx.0);
          return Some(t);
        }
        Some(&(t, orx)) => if orx != rx {
          newswap.push(shm._pseudo_var(rel));
          newswap.push(shm.evar.0);
          newswap.push(orx.0);
          newswap.push(rx.0);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn swap_pos_tup_(&mut self, tlb: TNum, rec: CVar, rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[lk0, lk1, lk2, rk] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let (_, lx2) = shm.cc.find(lk2);
      let (_, rx) = shm.cc.find(rk);
      let lxp = CTup3([lx0, lx1, lx2]);
      match self.pmap.get(&lxp) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.idx.insert(lx0, (t, lxp, rx));
          self.idx.insert(lx1, (t, lxp, rx));
          self.idx.insert(lx2, (t, lxp, rx));
          self.idx.insert(rx, (t, lxp, rx));
          //self.dom.insert((t, lxp));
          self.pmap.insert(lxp, (t, rx));
          for (perm, _) in self.pm2.clone_iter() {
            let lxp = lxp.perm(perm.as_ref());
            match self.pm2.get_mut(&perm) {
              None => unreachable!(),
              Some(pmap) => {
                pmap.insert(lxp, (t, rx));
              }
            }
          }
          swaptup.extend_from_slice(lxp.as_ref());
          swaptup.push(rx.0);
          (Fresh, t)
        }
        Some(&(t, orx)) => {
          if orx != rx {
            newswap.stage_tup(
                tlb,
                SwapEvent::Pat(shm.pseudo_var(rel), rel.0, lxp.as_ref(), &[orx.0, rx.0]),
                shm.evar.0,
                &[orx.0, rx.0],
            );
            swaptup.extend_from_slice(lxp.as_ref());
            swaptup.push(rx.0);
            (Merge, t)
          } else if t >= tlb {
            swaptup.extend_from_slice(lxp.as_ref());
            swaptup.push(rx.0);
            (Stale, t)
          } else {
            (Noswap, 0)
          }
        }
      }
    } else {
      unreachable!();
    }
  }
}

#[derive(Clone, Default)]
pub struct SymmFun3 {
  chk:  TUSnapshot,
  attr: IHTreapMap<TNum, CVar>,
  plub: TNum,
  //idx:  CUnionIter<(TNum, CTup3)>,
  idx:  CUnionIter<(TNum, CTup3, CVar)>,
  //idx:  IHTreapMap<CVar, IHTreapSet<(TNum, CTup3, CVar)>>,
  //idx:  CUnionIter_<(TNum, CTup3, CVar)>,
  //dom:  IHTreapSet<(TNum, CTup3)>,
  pmap: IHTreapMap<CTup3, (TNum, CVar)>,
}

impl SymmFun3 {
  fn _patchswap(&mut self, rel: CVar, newswap: &mut Vec<SNum>, shm: &mut STFrame) -> bool {
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in it {
      for (_, olp, orx) in self.idx.iter(nx) {
        let nlp = olp.swap_var(ox, nx);
        let nlp_: &[CVar] = nlp.as_ref();
        let nlx0 = nlp_[0];
        let nlx1 = nlp_[1];
        let nlx2 = nlp_[2];
        let nrx = swap_var(orx, ox, nx);
        let (_, rx) = shm.cc.find(nrx);
        match self.pmap.get(&nlp) {
          None => {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.idx.insert(nlx0, (t, nlp, rx));
            self.idx.insert(nlx1, (t, nlp, rx));
            self.idx.insert(nlx2, (t, nlp, rx));
            self.idx.insert(rx, (t, nlp, rx));
            self.pmap.remove(&olp);
            self.pmap.insert(nlp, (t, rx));
          }
          Some(&(t, oqrx)) => {
            let (_, qrx) = shm.cc.find(oqrx);
            if ut > t {
              patch = true;
              let t = shm.clk.fresh();
              plub = t;
              self.idx.insert(nlx0, (t, nlp, qrx));
              self.idx.insert(nlx1, (t, nlp, qrx));
              self.idx.insert(nlx2, (t, nlp, qrx));
              self.idx.insert(qrx, (t, nlp, qrx));
              self.pmap.remove(&olp);
              self.pmap.insert(nlp, (t, qrx));
            }
            if qrx != rx {
              newswap.push(shm._pseudo_var(rel));
              newswap.push(shm.evar.0);
              newswap.push(qrx.0);
              newswap.push(rx.0);
            }
          }
        }
      }
      for (_, olp, orx) in self.idx.iter(ox) {
        match self.pmap.get(&olp) {
          None => {}
          Some(&(ot, _)) => {
            let nlp = olp.swap_var(ox, nx);
            let nlp_: &[CVar] = nlp.as_ref();
            let nlx0 = nlp_[0];
            let nlx1 = nlp_[1];
            let nlx2 = nlp_[2];
            let nrx = swap_var(orx, ox, nx);
            let (_, rx) = shm.cc.find(nrx);
            match self.pmap.get(&nlp) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.idx.insert(nlx0, (t, nlp, rx));
                self.idx.insert(nlx1, (t, nlp, rx));
                self.idx.insert(nlx2, (t, nlp, rx));
                self.idx.insert(rx, (t, nlp, rx));
                self.pmap.remove(&olp);
                self.pmap.insert(nlp, (t, rx));
              }
              Some(&(t, oqrx)) => {
                let (_, qrx) = shm.cc.find(oqrx);
                if ut > t || ut > ot {
                  patch = true;
                  let t = shm.clk.fresh();
                  plub = t;
                  self.idx.insert(nlx0, (t, nlp, qrx));
                  self.idx.insert(nlx1, (t, nlp, qrx));
                  self.idx.insert(nlx2, (t, nlp, qrx));
                  self.idx.insert(qrx, (t, nlp, qrx));
                  self.pmap.remove(&olp);
                  self.pmap.insert(nlp, (t, qrx));
                }
                if qrx != rx {
                  newswap.push(shm._pseudo_var(rel));
                  newswap.push(shm.evar.0);
                  newswap.push(qrx.0);
                  newswap.push(rx.0);
                }
              }
            }
          }
        }
      }
      self.idx.remove(ox);
    }
    self.plub = plub;
    patch
  }

  fn _patch_swap(&mut self, tlb: TNum, rel: CVar, newswap: &mut dyn ESwap, shm: &mut STFrame) -> bool {
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in it {
      for (_, olp, orx) in self.idx.iter(nx) {
        let nlp = shm.cc.tfind(olp);
        let nlp_: &[CVar] = nlp.as_ref();
        let nlx0 = nlp_[0];
        let nlx1 = nlp_[1];
        let nlx2 = nlp_[2];
        let (_, rx) = shm.cc.find(orx);
        match self.pmap.get(&nlp) {
          None => {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.idx.insert(nlx0, (t, nlp, rx));
            self.idx.insert(nlx1, (t, nlp, rx));
            self.idx.insert(nlx2, (t, nlp, rx));
            self.idx.insert(rx, (t, nlp, rx));
            self.pmap.remove(&olp);
            self.pmap.insert(nlp, (t, rx));
            newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
          }
          Some(&(t, oqrx)) => {
            let (_, qrx) = shm.cc.find(oqrx);
            if ut > t {
              patch = true;
              let t = shm.clk.fresh();
              plub = t;
              self.idx.insert(nlx0, (t, nlp, qrx));
              self.idx.insert(nlx1, (t, nlp, qrx));
              self.idx.insert(nlx2, (t, nlp, qrx));
              self.idx.insert(qrx, (t, nlp, qrx));
              self.pmap.remove(&olp);
              self.pmap.insert(nlp, (t, qrx));
              newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
            }
            if qrx != rx {
              newswap.stage_tup(
                  tlb,
                  SwapEvent::Pat(shm.pseudo_var(rel), rel.0, nlp.as_ref(), &[qrx.0, rx.0]),
                  shm.evar.0,
                  &[qrx.0, rx.0],
              );
            }
          }
        }
      }
      for (_, olp, orx) in self.idx.iter(ox) {
        match self.pmap.get(&olp) {
          None => {}
          Some(&(ot, _)) => {
            let nlp = shm.cc.tfind(olp);
            let nlp_: &[CVar] = nlp.as_ref();
            let nlx0 = nlp_[0];
            let nlx1 = nlp_[1];
            let nlx2 = nlp_[2];
            let (_, rx) = shm.cc.find(orx);
            match self.pmap.get(&nlp) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.idx.insert(nlx0, (t, nlp, rx));
                self.idx.insert(nlx1, (t, nlp, rx));
                self.idx.insert(nlx2, (t, nlp, rx));
                self.idx.insert(rx, (t, nlp, rx));
                self.pmap.remove(&olp);
                self.pmap.insert(nlp, (t, rx));
                newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
              }
              Some(&(t, oqrx)) => {
                let (_, qrx) = shm.cc.find(oqrx);
                if ut > t || ut > ot {
                  patch = true;
                  let t = shm.clk.fresh();
                  plub = t;
                  self.idx.insert(nlx0, (t, nlp, qrx));
                  self.idx.insert(nlx1, (t, nlp, qrx));
                  self.idx.insert(nlx2, (t, nlp, qrx));
                  self.idx.insert(qrx, (t, nlp, qrx));
                  self.pmap.remove(&olp);
                  self.pmap.insert(nlp, (t, qrx));
                  newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
                }
                if qrx != rx {
                  newswap.stage_tup(
                      tlb,
                      SwapEvent::Pat(shm.pseudo_var(rel), rel.0, nlp.as_ref(), &[qrx.0, rx.0]),
                      shm.evar.0,
                      &[qrx.0, rx.0],
                  );
                }
              }
            }
          }
        }
      }
      self.idx.remove(ox);
    }
    self.plub = plub;
    patch
  }
}

impl ERel for SymmFun3 {
  fn clone_ref(&self) -> ERelRef {
    Rc::new(self.clone())
  }

  fn arity(&self) -> usize {
    4
  }

  fn kind2(&self) -> (RelKind, RelKind2) {
    (RelKind::Fun, RelKind2::LSymmF)
  }

  fn fun_arity(&self) -> Option<(usize, usize)> {
    Some((3, 1))
  }

  fn pos_least_ub(&self, _shm: &STFrame) -> TNum {
    self.plub
  }

  fn neg_least_ub(&self, _shm: &STFrame) -> TNum {
    0
  }

  fn pos_tup_size(&self, _shm: &STFrame) -> u64 {
    self.pmap.len() as u64
  }

  fn neg_tup_size(&self, _shm: &STFrame) -> u64 {
    0
  }

  fn dump_tups(&self, rel: CVar, prefix: &str, _shm: &STFrame) {
    println!("{}SymmFun3::dump_tups: rel={} +{}",
        prefix, rel.0, self.pmap.len());
    for (xp, &(t, y)) in self.pmap.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  + {} {:?} -> {}", prefix, t, xp_, y.0);
    }
  }

  /*fn patch(&mut self, rel: CVar, clk: &mut TClk, shm: &mut STFrame) {
    self._patch(rel, &mut shm.cc, clk);
  }*/

  fn patchswap(&mut self, rel: CVar, newswap: &mut Vec<SNum>, shm: &mut STFrame) {
    self._patchswap(rel, newswap, shm);
  }

  fn patch_swap(&mut self, tlb: TNum, rel: CVar, newswap: &mut dyn ESwap, shm: &mut STFrame) {
    self._patch_swap(tlb, rel, newswap, shm);
  }

  fn flag_tup(&mut self, _rel: CVar, _tup: &mut [SNum]) -> Option<TNum> {
    None
  }

  fn test_pos_tup(&mut self, rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[lk0, lk1, lk2, rk] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(rel, &mut shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let (_, lx2) = shm.cc.find(lk2);
      let lxp = CTup3([lx0, lx1, lx2]);
      match self.pmap.get(&lxp) {
        None => {}
        Some(&(rt, rx)) => {
          let (_, rq) = shm.cc.find(rk);
          if rx == rq {
            return Some(rt);
          }
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn scan_pos(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup3::from(&ubtup[ .. 3]);
    let iter = self.pmap.clone_iter_from(&lbtup[ .. 3]);
    let scan = Box::new(FScan3{ub, iter});
    scan
  }

  fn permscan_pos(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    self.scan_pos(_rel, lbtup, ubtup, _shm)
  }

  fn scan_par(&self, _rel: CVar, _shm: &STFrame) -> EScanBox {
    Box::new(EmpScan{})
  }

  fn swap_pos_tup(&mut self, rec: CVar, rel: CVar, tup: &[SNum], newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[lk0, lk1, lk2, rk] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(rel, &mut shm.cc, clk);
      }*/
      if !self.chk.is_ulive(&shm.cc) {
        panic!("bug: SymmFun3:swap_pos_tup: liveness failure: {} vs {} rec={} rel={} tup={:?}",
            self.chk.tu, shm.cc.tu, rec.0, rel.0, tup);
      }
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let (_, lx2) = shm.cc.find(lk2);
      let (_, rx) = shm.cc.find(rk);
      let mut lxp = CTup3([lx0, lx1, lx2]).sort();
      let mut ret = None;
      loop {
        match self.pmap.get(&lxp) {
          None => {
            let t = shm.clk.fresh();
            self.plub = t;
            self.idx.insert(lx0, (t, lxp, rx));
            self.idx.insert(lx1, (t, lxp, rx));
            self.idx.insert(lx2, (t, lxp, rx));
            self.idx.insert(rx, (t, lxp, rx));
            self.pmap.insert(lxp, (t, rx));
            swaptup.extend_from_slice(lxp.as_ref());
            swaptup.push(rx.0);
            ret = Some(t);
          }
          Some(&(t, orx)) => if orx != rx {
            newswap.push(shm._pseudo_var(rel));
            newswap.push(shm.evar.0);
            newswap.push(orx.0);
            newswap.push(rx.0);
          }
        }
        let lxp_: &mut [SNum] = lxp.as_mut();
        if next_permutation(lxp_).is_none() {
          break;
        }
      }
      ret
    } else {
      unreachable!();
    }
  }

  fn swap_pos_tup_(&mut self, tlb: TNum, rec: CVar, rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[lk0, lk1, lk2, rk] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let (_, lx2) = shm.cc.find(lk2);
      let (_, rx) = shm.cc.find(rk);
      let mut lxp = CTup3([lx0, lx1, lx2]).sort();
      let mut merge = None;
      let mut fresh = None;
      let mut stale = None;
      loop {
        match self.pmap.get(&lxp) {
          None => {
            let t = shm.clk.fresh();
            self.plub = t;
            self.idx.insert(lx0, (t, lxp, rx));
            self.idx.insert(lx1, (t, lxp, rx));
            self.idx.insert(lx2, (t, lxp, rx));
            self.idx.insert(rx, (t, lxp, rx));
            self.pmap.insert(lxp, (t, rx));
            //swaptup.extend_from_slice(lxp.as_ref());
            //swaptup.push(rx.0);
            fresh = Some(t);
          }
          Some(&(t, orx)) => {
            if orx != rx {
              newswap.stage_tup(
                  tlb,
                  SwapEvent::Pat(shm.pseudo_var(rel), rel.0, lxp.as_ref(), &[orx.0, rx.0]),
                  shm.evar.0,
                  &[orx.0, rx.0],
              );
              //swaptup.extend_from_slice(lxp.as_ref());
              //swaptup.push(rx.0);
              merge = Some(t);
            } else if t >= tlb {
              //swaptup.extend_from_slice(lxp.as_ref());
              //swaptup.push(rx.0);
              stale = Some(t);
            }
          }
        }
        swaptup.extend_from_slice(lxp.as_ref());
        swaptup.push(rx.0);
        let lxp_: &mut [SNum] = lxp.as_mut();
        if next_permutation(lxp_).is_none() {
          break;
        }
      }
      _from_merge_fresh_stale(merge, fresh, stale)
    } else {
      unreachable!();
    }
  }
}

pub struct FScan4 {
  ub:   CTup4,
  iter: IHTreapMapCloneIter<CTup4, (TNum, CVar)>,
  //iter: IHTreapMapCloneIter<CTup4, (CVar, TNum)>,
}

impl EScan for FScan4 {
  fn next_tup(&mut self, tup: &mut [SNum], /*shm: &mut STFrame*/) -> TScanResult {
    match self.iter.next() {
      None => {
        End
      }
      Some((xp, (t, y))) => if xp > self.ub {
      //Some((xp, (y, t))) => if xp > self.ub {
        End
      } else {
        tup[ .. 4].copy_from_slice(xp.as_ref());
        tup[4] = y.0;
        Hit(t)
      }
    }
  }
}

#[derive(Clone, Default)]
pub struct Fun4 {
  chk:  TUSnapshot,
  attr: IHTreapMap<TNum, CVar>,
  plub: TNum,
  //idx:  CUnionIter<(TNum, CTup4)>,
  idx:  CUnionIter<(TNum, CTup4, CVar)>,
  //idx:  IHTreapMap<CVar, IHTreapSet<(TNum, CTup4, CVar)>>,
  //idx:  CUnionIter_<(TNum, CTup4, CVar)>,
  //dom:  IHTreapSet<(TNum, CTup4)>,
  pmap: IHTreapMap<CTup4, (TNum, CVar)>,
  pm2:  IHTreapMap<CTup4, IHTreapMap<CTup4, (TNum, CVar)>>,
  //ndom: IHTreapSet<(TNum, CTup4, CVar)>,
  //nset: IHTreapMap<(CTup4, CVar), TNum>,
}

impl Fun4 {
  fn _patchswap(&mut self, rel: CVar, newswap: &mut Vec<SNum>, shm: &mut STFrame) -> bool {
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in it {
      for (_, olp, orx) in self.idx.iter(nx) {
        let nlp = olp.swap_var(ox, nx);
        let nlp_: &[CVar] = nlp.as_ref();
        let nlx0 = nlp_[0];
        let nlx1 = nlp_[1];
        let nlx2 = nlp_[2];
        let nlx3 = nlp_[3];
        let nrx = swap_var(orx, ox, nx);
        let (_, rx) = shm.cc.find(nrx);
        match self.pmap.get(&nlp) {
          None => {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.idx.insert(nlx0, (t, nlp, rx));
            self.idx.insert(nlx1, (t, nlp, rx));
            self.idx.insert(nlx2, (t, nlp, rx));
            self.idx.insert(nlx3, (t, nlp, rx));
            self.idx.insert(rx, (t, nlp, rx));
            self.pmap.remove(&olp);
            self.pmap.insert(nlp, (t, rx));
            for (perm, _) in self.pm2.clone_iter() {
              let olp = olp.perm(perm.as_ref());
              let nlp = nlp.perm(perm.as_ref());
              match self.pm2.get_mut(&perm) {
                None => unreachable!(),
                Some(pmap) => {
                  pmap.remove(&olp);
                  pmap.insert(nlp, (t, rx));
                }
              }
            }
          }
          Some(&(t, oqrx)) => {
            let (_, qrx) = shm.cc.find(oqrx);
            if ut > t {
              patch = true;
              let t = shm.clk.fresh();
              plub = t;
              self.idx.insert(nlx0, (t, nlp, qrx));
              self.idx.insert(nlx1, (t, nlp, qrx));
              self.idx.insert(nlx2, (t, nlp, qrx));
              self.idx.insert(nlx3, (t, nlp, qrx));
              self.idx.insert(qrx, (t, nlp, qrx));
              self.pmap.remove(&olp);
              self.pmap.insert(nlp, (t, qrx));
              for (perm, _) in self.pm2.clone_iter() {
                let olp = olp.perm(perm.as_ref());
                let nlp = nlp.perm(perm.as_ref());
                match self.pm2.get_mut(&perm) {
                  None => unreachable!(),
                  Some(pmap) => {
                    pmap.remove(&olp);
                    pmap.insert(nlp, (t, qrx));
                  }
                }
              }
            }
            if qrx != rx {
              newswap.push(shm._pseudo_var(rel));
              newswap.push(shm.evar.0);
              newswap.push(qrx.0);
              newswap.push(rx.0);
            }
          }
        }
      }
      for (_, olp, orx) in self.idx.iter(ox) {
        match self.pmap.get(&olp) {
          None => {}
          Some(&(ot, _)) => {
            let nlp = olp.swap_var(ox, nx);
            let nlp_: &[CVar] = nlp.as_ref();
            let nlx0 = nlp_[0];
            let nlx1 = nlp_[1];
            let nlx2 = nlp_[2];
            let nlx3 = nlp_[3];
            let nrx = swap_var(orx, ox, nx);
            let (_, rx) = shm.cc.find(nrx);
            match self.pmap.get(&nlp) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.idx.insert(nlx0, (t, nlp, rx));
                self.idx.insert(nlx1, (t, nlp, rx));
                self.idx.insert(nlx2, (t, nlp, rx));
                self.idx.insert(nlx3, (t, nlp, rx));
                self.idx.insert(rx, (t, nlp, rx));
                self.pmap.remove(&olp);
                self.pmap.insert(nlp, (t, rx));
                for (perm, _) in self.pm2.clone_iter() {
                  let olp = olp.perm(perm.as_ref());
                  let nlp = nlp.perm(perm.as_ref());
                  match self.pm2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pmap) => {
                      pmap.remove(&olp);
                      pmap.insert(nlp, (t, rx));
                    }
                  }
                }
              }
              Some(&(t, oqrx)) => {
                let (_, qrx) = shm.cc.find(oqrx);
                if ut > t || ut > ot {
                  patch = true;
                  let t = shm.clk.fresh();
                  plub = t;
                  self.idx.insert(nlx0, (t, nlp, qrx));
                  self.idx.insert(nlx1, (t, nlp, qrx));
                  self.idx.insert(nlx2, (t, nlp, qrx));
                  self.idx.insert(nlx3, (t, nlp, qrx));
                  self.idx.insert(qrx, (t, nlp, qrx));
                  self.pmap.remove(&olp);
                  self.pmap.insert(nlp, (t, qrx));
                  for (perm, _) in self.pm2.clone_iter() {
                    let olp = olp.perm(perm.as_ref());
                    let nlp = nlp.perm(perm.as_ref());
                    match self.pm2.get_mut(&perm) {
                      None => unreachable!(),
                      Some(pmap) => {
                        pmap.remove(&olp);
                        pmap.insert(nlp, (t, qrx));
                      }
                    }
                  }
                }
                if qrx != rx {
                  newswap.push(shm._pseudo_var(rel));
                  newswap.push(shm.evar.0);
                  newswap.push(qrx.0);
                  newswap.push(rx.0);
                }
              }
            }
          }
        }
      }
      self.idx.remove(ox);
    }
    self.plub = plub;
    patch
  }

  fn _patch_swap(&mut self, tlb: TNum, rel: CVar, newswap: &mut dyn ESwap, shm: &mut STFrame) -> bool {
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in it {
      for (_, olp, orx) in self.idx.iter(nx) {
        let nlp = shm.cc.tfind(olp);
        let nlp_: &[CVar] = nlp.as_ref();
        let nlx0 = nlp_[0];
        let nlx1 = nlp_[1];
        let nlx2 = nlp_[2];
        let nlx3 = nlp_[3];
        let (_, rx) = shm.cc.find(orx);
        match self.pmap.get(&nlp) {
          None => {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.idx.insert(nlx0, (t, nlp, rx));
            self.idx.insert(nlx1, (t, nlp, rx));
            self.idx.insert(nlx2, (t, nlp, rx));
            self.idx.insert(nlx3, (t, nlp, rx));
            self.idx.insert(rx, (t, nlp, rx));
            self.pmap.remove(&olp);
            self.pmap.insert(nlp, (t, rx));
            for (perm, _) in self.pm2.clone_iter() {
              let olp = olp.perm(perm.as_ref());
              let nlp = nlp.perm(perm.as_ref());
              match self.pm2.get_mut(&perm) {
                None => unreachable!(),
                Some(pmap) => {
                  pmap.remove(&olp);
                  pmap.insert(nlp, (t, rx));
                }
              }
            }
            newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
          }
          Some(&(t, oqrx)) => {
            let (_, qrx) = shm.cc.find(oqrx);
            if ut > t {
              patch = true;
              let t = shm.clk.fresh();
              plub = t;
              self.idx.insert(nlx0, (t, nlp, qrx));
              self.idx.insert(nlx1, (t, nlp, qrx));
              self.idx.insert(nlx2, (t, nlp, qrx));
              self.idx.insert(nlx3, (t, nlp, qrx));
              self.idx.insert(qrx, (t, nlp, qrx));
              self.pmap.remove(&olp);
              self.pmap.insert(nlp, (t, qrx));
              for (perm, _) in self.pm2.clone_iter() {
                let olp = olp.perm(perm.as_ref());
                let nlp = nlp.perm(perm.as_ref());
                match self.pm2.get_mut(&perm) {
                  None => unreachable!(),
                  Some(pmap) => {
                    pmap.remove(&olp);
                    pmap.insert(nlp, (t, qrx));
                  }
                }
              }
              newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
            }
            if qrx != rx {
              newswap.stage_tup(
                  tlb,
                  SwapEvent::Pat(shm.pseudo_var(rel), rel.0, nlp.as_ref(), &[qrx.0, rx.0]),
                  shm.evar.0,
                  &[qrx.0, rx.0],
              );
            }
          }
        }
      }
      for (_, olp, orx) in self.idx.iter(ox) {
        match self.pmap.get(&olp) {
          None => {}
          Some(&(ot, _)) => {
            let nlp = shm.cc.tfind(olp);
            let nlp_: &[CVar] = nlp.as_ref();
            let nlx0 = nlp_[0];
            let nlx1 = nlp_[1];
            let nlx2 = nlp_[2];
            let nlx3 = nlp_[3];
            let (_, rx) = shm.cc.find(orx);
            match self.pmap.get(&nlp) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.idx.insert(nlx0, (t, nlp, rx));
                self.idx.insert(nlx1, (t, nlp, rx));
                self.idx.insert(nlx2, (t, nlp, rx));
                self.idx.insert(nlx3, (t, nlp, rx));
                self.idx.insert(rx, (t, nlp, rx));
                self.pmap.remove(&olp);
                self.pmap.insert(nlp, (t, rx));
                for (perm, _) in self.pm2.clone_iter() {
                  let olp = olp.perm(perm.as_ref());
                  let nlp = nlp.perm(perm.as_ref());
                  match self.pm2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pmap) => {
                      pmap.remove(&olp);
                      pmap.insert(nlp, (t, rx));
                    }
                  }
                }
                newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
              }
              Some(&(t, oqrx)) => {
                let (_, qrx) = shm.cc.find(oqrx);
                if ut > t || ut > ot {
                  patch = true;
                  let t = shm.clk.fresh();
                  plub = t;
                  self.idx.insert(nlx0, (t, nlp, qrx));
                  self.idx.insert(nlx1, (t, nlp, qrx));
                  self.idx.insert(nlx2, (t, nlp, qrx));
                  self.idx.insert(nlx3, (t, nlp, qrx));
                  self.idx.insert(qrx, (t, nlp, qrx));
                  self.pmap.remove(&olp);
                  self.pmap.insert(nlp, (t, qrx));
                  for (perm, _) in self.pm2.clone_iter() {
                    let olp = olp.perm(perm.as_ref());
                    let nlp = nlp.perm(perm.as_ref());
                    match self.pm2.get_mut(&perm) {
                      None => unreachable!(),
                      Some(pmap) => {
                        pmap.remove(&olp);
                        pmap.insert(nlp, (t, qrx));
                      }
                    }
                  }
                  newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
                }
                if qrx != rx {
                  newswap.stage_tup(
                      tlb,
                      SwapEvent::Pat(shm.pseudo_var(rel), rel.0, nlp.as_ref(), &[qrx.0, rx.0]),
                      shm.evar.0,
                      &[qrx.0, rx.0],
                  );
                }
              }
            }
          }
        }
      }
      self.idx.remove(ox);
    }
    self.plub = plub;
    patch
  }
}

impl ERel for Fun4 {
  fn clone_ref(&self) -> ERelRef {
    Rc::new(self.clone())
  }

  fn arity(&self) -> usize {
    5
  }

  fn kind2(&self) -> (RelKind, RelKind2) {
    (RelKind::Fun, RelKind2::Exact)
  }

  fn fun_arity(&self) -> Option<(usize, usize)> {
    Some((4, 1))
  }

  fn pos_least_ub(&self, _shm: &STFrame) -> TNum {
    self.plub
  }

  fn neg_least_ub(&self, _shm: &STFrame) -> TNum {
    0
  }

  fn pos_tup_size(&self, _shm: &STFrame) -> u64 {
    self.pmap.len() as u64
  }

  fn neg_tup_size(&self, _shm: &STFrame) -> u64 {
    //self.nset.len() as u64
    0
  }

  /*fn patch(&mut self, rel: CVar, clk: &mut TClk, shm: &mut STFrame) {
    self._patch(rel, &mut shm.cc, clk);
  }*/

  fn patchswap(&mut self, rel: CVar, newswap: &mut Vec<SNum>, shm: &mut STFrame) {
    self._patchswap(rel, newswap, shm);
  }

  fn patch_swap(&mut self, tlb: TNum, rel: CVar, newswap: &mut dyn ESwap, shm: &mut STFrame) {
    self._patch_swap(tlb, rel, newswap, shm);
  }

  fn flag_tup(&mut self, _rel: CVar, _tup: &mut [SNum]) -> Option<TNum> {
    None
  }

  fn test_pos_tup(&mut self, rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[lk0, lk1, lk2, lk3, rk] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(rel, &mut shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let (_, lx2) = shm.cc.find(lk2);
      let (_, lx3) = shm.cc.find(lk3);
      let lxp = CTup4([lx0, lx1, lx2, lx3]);
      match self.pmap.get(&lxp) {
        None => {}
        Some(&(rt, rx)) => {
          let (_, rq) = shm.cc.find(rk);
          if rx == rq {
            return Some(rt);
          }
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn scan_pos(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup4::from(&ubtup[ .. 4]);
    let iter = self.pmap.clone_iter_from(&lbtup[ .. 4]);
    let scan = Box::new(FScan4{ub, iter});
    scan
  }

  fn permscan_pos(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    match self.pm2.get(perm) {
      None => {
        let mut pmap = IHTreapMap::default();
        for (xp, &t) in self.pmap.iter() {
          let xp = xp.perm(perm);
          pmap.insert(xp, t);
        }
        self.pm2.insert(CTup4::from(perm), pmap);
      }
      Some(_) => {}
    }
    match self.pm2.get(perm) {
      None => unreachable!(),
      Some(pmap) => {
        let ub = CTup4::from(&ubtup[ .. 4]);
        let iter = pmap.clone_iter_from(&lbtup[ .. 4]);
        let scan = Box::new(FScan4{ub, iter});
        scan
      }
    }
  }

  fn scan_par(&self, _rel: CVar, _shm: &STFrame) -> EScanBox {
    Box::new(EmpScan{})
  }

  fn swap_pos_tup(&mut self, rec: CVar, rel: CVar, tup: &[SNum], newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[lk0, lk1, lk2, lk3, rk] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(rel, &mut shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let (_, lx2) = shm.cc.find(lk2);
      let (_, lx3) = shm.cc.find(lk3);
      let (_, rx) = shm.cc.find(rk);
      let lxp = CTup4([lx0, lx1, lx2, lx3]);
      match self.pmap.get(&lxp) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.idx.insert(lx0, (t, lxp, rx));
          self.idx.insert(lx1, (t, lxp, rx));
          self.idx.insert(lx2, (t, lxp, rx));
          self.idx.insert(lx3, (t, lxp, rx));
          self.idx.insert(rx, (t, lxp, rx));
          //self.dom.insert((t, lxp));
          self.pmap.insert(lxp, (t, rx));
          for (perm, _) in self.pm2.clone_iter() {
            let lxp = lxp.perm(perm.as_ref());
            match self.pm2.get_mut(&perm) {
              None => unreachable!(),
              Some(pmap) => {
                pmap.insert(lxp, (t, rx));
              }
            }
          }
          swaptup.extend_from_slice(lxp.as_ref());
          swaptup.push(rx.0);
          return Some(t);
        }
        Some(&(t, orx)) => if orx != rx {
          newswap.push(shm._pseudo_var(rel));
          newswap.push(shm.evar.0);
          newswap.push(orx.0);
          newswap.push(rx.0);
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn swap_pos_tup_(&mut self, tlb: TNum, rec: CVar, rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[lk0, lk1, lk2, lk3, rk] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let (_, lx2) = shm.cc.find(lk2);
      let (_, lx3) = shm.cc.find(lk3);
      let (_, rx) = shm.cc.find(rk);
      let lxp = CTup4([lx0, lx1, lx2, lx3]);
      match self.pmap.get(&lxp) {
        None => {
          let t = shm.clk.fresh();
          self.plub = t;
          self.idx.insert(lx0, (t, lxp, rx));
          self.idx.insert(lx1, (t, lxp, rx));
          self.idx.insert(lx2, (t, lxp, rx));
          self.idx.insert(lx3, (t, lxp, rx));
          self.idx.insert(rx, (t, lxp, rx));
          //self.dom.insert((t, lxp));
          self.pmap.insert(lxp, (t, rx));
          for (perm, _) in self.pm2.clone_iter() {
            let lxp = lxp.perm(perm.as_ref());
            match self.pm2.get_mut(&perm) {
              None => unreachable!(),
              Some(pmap) => {
                pmap.insert(lxp, (t, rx));
              }
            }
          }
          swaptup.extend_from_slice(lxp.as_ref());
          swaptup.push(rx.0);
          (Fresh, t)
        }
        Some(&(t, orx)) => {
          if orx != rx {
            newswap.stage_tup(
                tlb,
                SwapEvent::Pat(shm.pseudo_var(rel), rel.0, lxp.as_ref(), &[orx.0, rx.0]),
                shm.evar.0,
                &[orx.0, rx.0],
            );
            swaptup.extend_from_slice(lxp.as_ref());
            swaptup.push(rx.0);
            (Merge, t)
          } else if t >= tlb {
            swaptup.extend_from_slice(lxp.as_ref());
            swaptup.push(rx.0);
            (Stale, t)
          } else {
            (Noswap, 0)
          }
        }
      }
    } else {
      unreachable!();
    }
  }
}

#[derive(Clone, Default)]
pub struct CyclFun4 {
  chk:  TUSnapshot,
  attr: IHTreapMap<TNum, CVar>,
  plub: TNum,
  //idx:  CUnionIter<(TNum, CTup4)>,
  idx:  CUnionIter<(TNum, CTup4, CVar)>,
  //idx:  IHTreapMap<CVar, IHTreapSet<(TNum, CTup4, CVar)>>,
  //idx:  CUnionIter_<(TNum, CTup4, CVar)>,
  pmap: IHTreapMap<CTup4, (TNum, CVar)>,
  pm2:  IHTreapMap<CTup4, IHTreapMap<CTup4, (TNum, CVar)>>,
}

impl CyclFun4 {
  fn _patchswap(&mut self, rel: CVar, newswap: &mut Vec<SNum>, shm: &mut STFrame) -> bool {
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in it {
      for (_, olp, orx) in self.idx.iter(nx) {
        let nlp = olp.swap_var(ox, nx);
        let nlp_: &[CVar] = nlp.as_ref();
        let nlx0 = nlp_[0];
        let nlx1 = nlp_[1];
        let nlx2 = nlp_[2];
        let nlx3 = nlp_[3];
        let nrx = swap_var(orx, ox, nx);
        let (_, rx) = shm.cc.find(nrx);
        match self.pmap.get(&nlp) {
          None => {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.idx.insert(nlx0, (t, nlp, rx));
            self.idx.insert(nlx1, (t, nlp, rx));
            self.idx.insert(nlx2, (t, nlp, rx));
            self.idx.insert(nlx3, (t, nlp, rx));
            self.idx.insert(rx, (t, nlp, rx));
            self.pmap.remove(&olp);
            self.pmap.insert(nlp, (t, rx));
            for (perm, _) in self.pm2.clone_iter() {
              let olp = olp.perm(perm.as_ref());
              let nlp = nlp.perm(perm.as_ref());
              match self.pm2.get_mut(&perm) {
                None => unreachable!(),
                Some(pmap) => {
                  pmap.remove(&olp);
                  pmap.insert(nlp, (t, rx));
                }
              }
            }
          }
          Some(&(t, oqrx)) => {
            let (_, qrx) = shm.cc.find(oqrx);
            if ut > t {
              patch = true;
              let t = shm.clk.fresh();
              plub = t;
              self.idx.insert(nlx0, (t, nlp, qrx));
              self.idx.insert(nlx1, (t, nlp, qrx));
              self.idx.insert(nlx2, (t, nlp, qrx));
              self.idx.insert(nlx3, (t, nlp, qrx));
              self.idx.insert(qrx, (t, nlp, qrx));
              self.pmap.remove(&olp);
              self.pmap.insert(nlp, (t, qrx));
              for (perm, _) in self.pm2.clone_iter() {
                let olp = olp.perm(perm.as_ref());
                let nlp = nlp.perm(perm.as_ref());
                match self.pm2.get_mut(&perm) {
                  None => unreachable!(),
                  Some(pmap) => {
                    pmap.remove(&olp);
                    pmap.insert(nlp, (t, qrx));
                  }
                }
              }
            }
            if qrx != rx {
              newswap.push(shm._pseudo_var(rel));
              newswap.push(shm.evar.0);
              newswap.push(qrx.0);
              newswap.push(rx.0);
            }
          }
        }
      }
      for (_, olp, orx) in self.idx.iter(ox) {
        match self.pmap.get(&olp) {
          None => {}
          Some(&(ot, _)) => {
            let nlp = olp.swap_var(ox, nx);
            let nlp_: &[CVar] = nlp.as_ref();
            let nlx0 = nlp_[0];
            let nlx1 = nlp_[1];
            let nlx2 = nlp_[2];
            let nlx3 = nlp_[3];
            let nrx = swap_var(orx, ox, nx);
            let (_, rx) = shm.cc.find(nrx);
            match self.pmap.get(&nlp) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.idx.insert(nlx0, (t, nlp, rx));
                self.idx.insert(nlx1, (t, nlp, rx));
                self.idx.insert(nlx2, (t, nlp, rx));
                self.idx.insert(nlx3, (t, nlp, rx));
                self.idx.insert(rx, (t, nlp, rx));
                self.pmap.remove(&olp);
                self.pmap.insert(nlp, (t, rx));
                for (perm, _) in self.pm2.clone_iter() {
                  let olp = olp.perm(perm.as_ref());
                  let nlp = nlp.perm(perm.as_ref());
                  match self.pm2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pmap) => {
                      pmap.remove(&olp);
                      pmap.insert(nlp, (t, rx));
                    }
                  }
                }
              }
              Some(&(t, oqrx)) => {
                let (_, qrx) = shm.cc.find(oqrx);
                if ut > t || ut > ot {
                  patch = true;
                  let t = shm.clk.fresh();
                  plub = t;
                  self.idx.insert(nlx0, (t, nlp, qrx));
                  self.idx.insert(nlx1, (t, nlp, qrx));
                  self.idx.insert(nlx2, (t, nlp, qrx));
                  self.idx.insert(nlx3, (t, nlp, qrx));
                  self.idx.insert(qrx, (t, nlp, qrx));
                  self.pmap.remove(&olp);
                  self.pmap.insert(nlp, (t, qrx));
                  for (perm, _) in self.pm2.clone_iter() {
                    let olp = olp.perm(perm.as_ref());
                    let nlp = nlp.perm(perm.as_ref());
                    match self.pm2.get_mut(&perm) {
                      None => unreachable!(),
                      Some(pmap) => {
                        pmap.remove(&olp);
                        pmap.insert(nlp, (t, qrx));
                      }
                    }
                  }
                }
                if qrx != rx {
                  newswap.push(shm._pseudo_var(rel));
                  newswap.push(shm.evar.0);
                  newswap.push(qrx.0);
                  newswap.push(rx.0);
                }
              }
            }
          }
        }
      }
      self.idx.remove(ox);
    }
    self.plub = plub;
    patch
  }

  fn _patch_swap(&mut self, tlb: TNum, rel: CVar, newswap: &mut dyn ESwap, shm: &mut STFrame) -> bool {
    if self.chk.is_ulive(&shm.cc) {
      return false;
    }
    let mut patch = false;
    let mut plub = self.plub;
    let it = shm.cc.usnapdiff(&self.chk);
    self.chk = shm.cc.usnapshot();
    for ((ut, ox), nx) in it {
      for (_, olp, orx) in self.idx.iter(nx) {
        let nlp = shm.cc.tfind(olp);
        let nlp_: &[CVar] = nlp.as_ref();
        let nlx0 = nlp_[0];
        let nlx1 = nlp_[1];
        let nlx2 = nlp_[2];
        let nlx3 = nlp_[3];
        let (_, rx) = shm.cc.find(orx);
        match self.pmap.get(&nlp) {
          None => {
            patch = true;
            let t = shm.clk.fresh();
            plub = t;
            self.idx.insert(nlx0, (t, nlp, rx));
            self.idx.insert(nlx1, (t, nlp, rx));
            self.idx.insert(nlx2, (t, nlp, rx));
            self.idx.insert(nlx3, (t, nlp, rx));
            self.idx.insert(rx, (t, nlp, rx));
            self.pmap.remove(&olp);
            self.pmap.insert(nlp, (t, rx));
            for (perm, _) in self.pm2.clone_iter() {
              let olp = olp.perm(perm.as_ref());
              let nlp = nlp.perm(perm.as_ref());
              match self.pm2.get_mut(&perm) {
                None => unreachable!(),
                Some(pmap) => {
                  pmap.remove(&olp);
                  pmap.insert(nlp, (t, rx));
                }
              }
            }
            newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
          }
          Some(&(t, oqrx)) => {
            let (_, qrx) = shm.cc.find(oqrx);
            if ut > t {
              patch = true;
              let t = shm.clk.fresh();
              plub = t;
              self.idx.insert(nlx0, (t, nlp, qrx));
              self.idx.insert(nlx1, (t, nlp, qrx));
              self.idx.insert(nlx2, (t, nlp, qrx));
              self.idx.insert(nlx3, (t, nlp, qrx));
              self.idx.insert(qrx, (t, nlp, qrx));
              self.pmap.remove(&olp);
              self.pmap.insert(nlp, (t, qrx));
              for (perm, _) in self.pm2.clone_iter() {
                let olp = olp.perm(perm.as_ref());
                let nlp = nlp.perm(perm.as_ref());
                match self.pm2.get_mut(&perm) {
                  None => unreachable!(),
                  Some(pmap) => {
                    pmap.remove(&olp);
                    pmap.insert(nlp, (t, qrx));
                  }
                }
              }
              newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
            }
            if qrx != rx {
              newswap.stage_tup(
                  tlb,
                  SwapEvent::Pat(shm.pseudo_var(rel), rel.0, nlp.as_ref(), &[qrx.0, rx.0]),
                  shm.evar.0,
                  &[qrx.0, rx.0],
              );
            }
          }
        }
      }
      for (_, olp, orx) in self.idx.iter(ox) {
        match self.pmap.get(&olp) {
          None => {}
          Some(&(ot, _)) => {
            let nlp = shm.cc.tfind(olp);
            let nlp_: &[CVar] = nlp.as_ref();
            let nlx0 = nlp_[0];
            let nlx1 = nlp_[1];
            let nlx2 = nlp_[2];
            let nlx3 = nlp_[3];
            let (_, rx) = shm.cc.find(orx);
            match self.pmap.get(&nlp) {
              None => {
                patch = true;
                let t = shm.clk.fresh();
                plub = t;
                self.idx.insert(nlx0, (t, nlp, rx));
                self.idx.insert(nlx1, (t, nlp, rx));
                self.idx.insert(nlx2, (t, nlp, rx));
                self.idx.insert(nlx3, (t, nlp, rx));
                self.idx.insert(rx, (t, nlp, rx));
                self.pmap.remove(&olp);
                self.pmap.insert(nlp, (t, rx));
                for (perm, _) in self.pm2.clone_iter() {
                  let olp = olp.perm(perm.as_ref());
                  let nlp = nlp.perm(perm.as_ref());
                  match self.pm2.get_mut(&perm) {
                    None => unreachable!(),
                    Some(pmap) => {
                      pmap.remove(&olp);
                      pmap.insert(nlp, (t, rx));
                    }
                  }
                }
                newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
              }
              Some(&(t, oqrx)) => {
                let (_, qrx) = shm.cc.find(oqrx);
                if ut > t || ut > ot {
                  patch = true;
                  let t = shm.clk.fresh();
                  plub = t;
                  self.idx.insert(nlx0, (t, nlp, qrx));
                  self.idx.insert(nlx1, (t, nlp, qrx));
                  self.idx.insert(nlx2, (t, nlp, qrx));
                  self.idx.insert(nlx3, (t, nlp, qrx));
                  self.idx.insert(qrx, (t, nlp, qrx));
                  self.pmap.remove(&olp);
                  self.pmap.insert(nlp, (t, qrx));
                  for (perm, _) in self.pm2.clone_iter() {
                    let olp = olp.perm(perm.as_ref());
                    let nlp = nlp.perm(perm.as_ref());
                    match self.pm2.get_mut(&perm) {
                      None => unreachable!(),
                      Some(pmap) => {
                        pmap.remove(&olp);
                        pmap.insert(nlp, (t, qrx));
                      }
                    }
                  }
                  newswap.patch_tup(tlb, rel.0, olp.as_ref(), &[orx.0], nlp.as_ref(), &[rx.0]);
                }
                if qrx != rx {
                  newswap.stage_tup(
                      tlb,
                      SwapEvent::Pat(shm.pseudo_var(rel), rel.0, nlp.as_ref(), &[qrx.0, rx.0]),
                      shm.evar.0,
                      &[qrx.0, rx.0],
                  );
                }
              }
            }
          }
        }
      }
      self.idx.remove(ox);
    }
    self.plub = plub;
    patch
  }
}

impl ERel for CyclFun4 {
  fn clone_ref(&self) -> ERelRef {
    Rc::new(self.clone())
  }

  fn arity(&self) -> usize {
    5
  }

  fn kind2(&self) -> (RelKind, RelKind2) {
    (RelKind::Fun, RelKind2::LCyclF)
  }

  fn fun_arity(&self) -> Option<(usize, usize)> {
    Some((4, 1))
  }

  fn pos_least_ub(&self, _shm: &STFrame) -> TNum {
    self.plub
  }

  fn neg_least_ub(&self, _shm: &STFrame) -> TNum {
    0
  }

  fn pos_tup_size(&self, _shm: &STFrame) -> u64 {
    self.pmap.len() as u64
  }

  fn neg_tup_size(&self, _shm: &STFrame) -> u64 {
    0
  }

  fn dump_tups(&self, rel: CVar, prefix: &str, _shm: &STFrame) {
    println!("{}CyclFun4::dump_tups: rel={} +{}",
        prefix, rel.0, self.pmap.len());
    for (xp, &(t, y)) in self.pmap.iter() {
      let xp_: &[SNum] = xp.as_ref();
      println!("{}  + {} {:?} -> {}", prefix, t, xp_, y.0);
    }
  }

  /*fn patch(&mut self, rel: CVar, clk: &mut TClk, shm: &mut STFrame) {
    self._patch(rel, &mut shm.cc, clk);
  }*/

  fn patchswap(&mut self, rel: CVar, newswap: &mut Vec<SNum>, shm: &mut STFrame) {
    self._patchswap(rel, newswap, shm);
  }

  fn patch_swap(&mut self, tlb: TNum, rel: CVar, newswap: &mut dyn ESwap, shm: &mut STFrame) {
    self._patch_swap(tlb, rel, newswap, shm);
  }

  fn flag_tup(&mut self, _rel: CVar, _tup: &mut [SNum]) -> Option<TNum> {
    None
  }

  fn test_pos_tup(&mut self, rel: CVar, tup: &[SNum], shm: &mut STFrame) -> Option<TNum> {
    if let &[lk0, lk1, lk2, lk3, rk] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(rel, &mut shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let (_, lx2) = shm.cc.find(lk2);
      let (_, lx3) = shm.cc.find(lk3);
      let lxp = CTup4([lx0, lx1, lx2, lx3]);
      match self.pmap.get(&lxp) {
        None => {}
        Some(&(rt, rx)) => {
          let (_, rq) = shm.cc.find(rk);
          if rx == rq {
            return Some(rt);
          }
        }
      }
      None
    } else {
      unreachable!();
    }
  }

  fn scan_pos(&mut self, _rel: CVar, lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    let ub = CTup4::from(&ubtup[ .. 4]);
    let iter = self.pmap.clone_iter_from(&lbtup[ .. 4]);
    let scan = Box::new(FScan4{ub, iter});
    scan
  }

  fn permscan_pos(&mut self, _rel: CVar, perm: &[SNum], lbtup: &[SNum], ubtup: &[SNum], _shm: &mut STFrame) -> EScanBox {
    match self.pm2.get(perm) {
      None => {
        let mut pmap = IHTreapMap::default();
        for (xp, &t) in self.pmap.iter() {
          let xp = xp.perm(perm);
          pmap.insert(xp, t);
        }
        self.pm2.insert(CTup4::from(perm), pmap);
      }
      Some(_) => {}
    }
    match self.pm2.get(perm) {
      None => unreachable!(),
      Some(pmap) => {
        let ub = CTup4::from(&ubtup[ .. 4]);
        let iter = pmap.clone_iter_from(&lbtup[ .. 4]);
        let scan = Box::new(FScan4{ub, iter});
        scan
      }
    }
  }

  fn scan_par(&self, _rel: CVar, _shm: &STFrame) -> EScanBox {
    Box::new(EmpScan{})
  }

  fn swap_pos_tup(&mut self, rec: CVar, rel: CVar, tup: &[SNum], newswap: &mut Vec<SNum>, swaptup: &mut Vec<SNum>, shm: &mut STFrame) -> Option<TNum> {
    if let &[lk0, lk1, lk2, lk3, rk] = as_cvars(tup) {
      /*if !self.chk.is_ulive(&shm.cc) {
        self._patch(rel, &mut shm.cc, clk);
      }*/
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let (_, lx2) = shm.cc.find(lk2);
      let (_, lx3) = shm.cc.find(lk3);
      let (_, rx) = shm.cc.find(rk);
      let mut lxp = CTup4([lx0, lx1, lx2, lx3]);
      let mut ret = None;
      for i in 0 .. 4 {
        match self.pmap.get(&lxp) {
          None => {
            let t = shm.clk.fresh();
            self.plub = t;
            self.idx.insert(lx0, (t, lxp, rx));
            self.idx.insert(lx1, (t, lxp, rx));
            self.idx.insert(lx2, (t, lxp, rx));
            self.idx.insert(lx3, (t, lxp, rx));
            self.idx.insert(rx, (t, lxp, rx));
            self.pmap.insert(lxp, (t, rx));
            for (perm, _) in self.pm2.clone_iter() {
              let lxp = lxp.perm(perm.as_ref());
              match self.pm2.get_mut(&perm) {
                None => unreachable!(),
                Some(pmap) => {
                  pmap.insert(lxp, (t, rx));
                }
              }
            }
            swaptup.extend_from_slice(lxp.as_ref());
            swaptup.push(rx.0);
            ret = Some(t);
          }
          Some(&(t, orx)) => if orx != rx {
            newswap.push(shm._pseudo_var(rel));
            newswap.push(shm.evar.0);
            newswap.push(orx.0);
            newswap.push(rx.0);
          }
        }
        if i == 0 && lxp.count_var(lx0) == lxp.len() {
          break;
        }
        let lxp_: &mut [SNum] = lxp.as_mut();
        rotate(lxp_);
      }
      ret
    } else {
      unreachable!();
    }
  }

  fn swap_pos_tup_(&mut self, tlb: TNum, rec: CVar, rel: CVar, tup: &[SNum], swaptup: &mut Vec<SNum>, newswap: &mut dyn ESwap, shm: &mut STFrame) -> TSwapResult {
    if let &[lk0, lk1, lk2, lk3, rk] = as_cvars(tup) {
      assert!(self.chk.is_ulive(&shm.cc));
      let (_, lx0) = shm.cc.find(lk0);
      let (_, lx1) = shm.cc.find(lk1);
      let (_, lx2) = shm.cc.find(lk2);
      let (_, lx3) = shm.cc.find(lk3);
      let (_, rx) = shm.cc.find(rk);
      let mut lxp = CTup4([lx0, lx1, lx2, lx3]).rotate_lo();
      let mut merge = None;
      let mut fresh = None;
      let mut stale = None;
      for i in 0 .. 4 {
        match self.pmap.get(&lxp) {
          None => {
            let t = shm.clk.fresh();
            self.plub = t;
            self.idx.insert(lx0, (t, lxp, rx));
            self.idx.insert(lx1, (t, lxp, rx));
            self.idx.insert(lx2, (t, lxp, rx));
            self.idx.insert(lx3, (t, lxp, rx));
            self.idx.insert(rx, (t, lxp, rx));
            self.pmap.insert(lxp, (t, rx));
            for (perm, _) in self.pm2.clone_iter() {
              let lxp = lxp.perm(perm.as_ref());
              match self.pm2.get_mut(&perm) {
                None => unreachable!(),
                Some(pmap) => {
                  pmap.insert(lxp, (t, rx));
                }
              }
            }
            //swaptup.extend_from_slice(lxp.as_ref());
            //swaptup.push(rx.0);
            fresh = Some(t);
          }
          Some(&(t, orx)) => {
            if orx != rx {
              newswap.stage_tup(
                  tlb,
                  SwapEvent::Pat(shm.pseudo_var(rel), rel.0, lxp.as_ref(), &[orx.0, rx.0]),
                  shm.evar.0,
                  &[orx.0, rx.0],
              );
              //swaptup.extend_from_slice(lxp.as_ref());
              //swaptup.push(rx.0);
              merge = Some(t);
            } else if t >= tlb {
              //swaptup.extend_from_slice(lxp.as_ref());
              //swaptup.push(rx.0);
              stale = Some(t);
            }
          }
        }
        swaptup.extend_from_slice(lxp.as_ref());
        swaptup.push(rx.0);
        if i == 0 && lxp.count_var(lx0) == lxp.len() {
          break;
        }
        let lxp_: &mut [SNum] = lxp.as_mut();
        rotate(lxp_);
      }
      _from_merge_fresh_stale(merge, fresh, stale)
    } else {
      unreachable!();
    }
  }
}
