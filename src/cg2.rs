use crate::algo::*;
use crate::framework::{CVar, SNum};
use crate::framework2::*;
use crate::ir::{*, IRelSchema::*};
use crate::log::*;

use std::collections::{VecDeque};
use std::sync::{Arc as Rc};

#[derive(Default)]
struct YFrame {
  pseudo:   BTreeMap<CVar, CVar>,
  //shadow:   BTreeMap<SNum, SNum>,
  shadow:   BTreeMap<SNum, (CVar, SNum)>,
  tmp_rel:  BTreeMap<SNum, SNum>,
  tmp_rec:  BTreeMap<YKey, (CVar, YRec, YKeyInfo)>,
  //snk_rec:  BTreeMap<YKey, (CVar, YRec)>,
  primrec:  Vec<(CVar, YRec, YKeyInfo)>,
  freerec:  Vec<(CVar, YRec)>,
}

impl YFrame {
  fn _emit_rels(&self, rels: &mut IHTreapMap<CVar, ERelRef>) {
    // TODO
    for (&primrel, &(_, shadrel)) in self.shadow.iter() {
      let ar = match rels.get(&CVar(primrel)) {
        None => panic!("bug: cg2: YFrame::_emit_rels: unk rel={}", primrel),
        Some(rel) => rel.arity()
      };
      let rel: ERelRef = match ar {
        1 => Rc::new(Rel1::default()),
        2 => Rc::new(Rel2::default()),
        3 => Rc::new(Rel3::default()),
        4 => Rc::new(Rel4::default()),
        5 => Rc::new(Rel5::default()),
        6 => Rc::new(Rel6::default()),
        _ => panic!("bug: cg2: YFrame::_emit_rels: ar={}", ar)
      };
      if log_debug() {
        println!("DEBUG: cg2: YFrame::_emit_rels: prim={} shad={}", primrel, shadrel);
      }
      rels.insert(CVar(shadrel), rel);
    }
    //for (&primrel, &tmp_rel) in self.tmp_rel.iter() {
    for (&tmp_rel, &primrel) in self.tmp_rel.iter() {
      let ar = match rels.get(&CVar(primrel)) {
        None => panic!("bug: cg2: YFrame::_emit_rels: unk rel={}", primrel),
        Some(rel) => rel.arity()
      };
      let rel: ERelRef = match ar {
        1 => Rc::new(Rel1::default()),
        2 => Rc::new(Rel2::default()),
        3 => Rc::new(Rel3::default()),
        4 => Rc::new(Rel4::default()),
        5 => Rc::new(Rel5::default()),
        6 => Rc::new(Rel6::default()),
        _ => panic!("bug: cg2: YFrame::_emit_rels: ar={}", ar)
      };
      if log_debug() {
        println!("DEBUG: cg2: YFrame::_emit_rels: prim={} tmp={}", primrel, tmp_rel);
      }
      rels.insert(CVar(tmp_rel), rel);
    }
  }

  fn _emit_recs_1(&self, rels: &IHTreapMap<CVar, ERelRef>, urec: &mut HTreapMap<CVar, TRec1>, drec: &mut HTreapMap<CVar, TRec1>, shm: &mut STFrame) {
    // TODO
    for &(rec_var, ref rec) in self.freerec.iter() {
      let rec = rec._emit_rec_1();
      if log_debug() {
        println!("DEBUG: cg2: YFrame::_emit_recs_1: free rec={}", rec_var.0);
      }
      urec.insert(rec_var, rec);
    }
    for &(rec_var, ref rec, ref recinfo) in self.primrec.iter() {
      if !rec.dsub.is_empty() {
        let rec = rec._emit_rec_1_(recinfo);
        if log_debug() {
          println!("DEBUG: cg2: YFrame::_emit_recs_1: def rec={}", rec_var.0);
        }
        drec.insert(rec_var, rec);
      } else {
        let rec = rec._emit_rec_1_(recinfo);
        if log_debug() {
          println!("DEBUG: cg2: YFrame::_emit_recs_1: nul rec={}", rec_var.0);
        }
        urec.insert(rec_var, rec);
      }
    }
    for (&rel_var, &pseudo_var) in self.pseudo.iter() {
      shm.pseu.insert(rel_var, pseudo_var);
      shm.rpsu.insert(pseudo_var, rel_var);
    }
    /*for (_, &(rec_var, ref rec)) in self.snk_rec.iter() {
      if !rec.dsub.is_empty() {
        let rec = rec._emit_rec_1();
        drec.insert(rec_var, rec);
      } else {
        let rec = rec._emit_rec_1();
        urec.insert(rec_var, rec);
      }
    }*/
    for (_, &(rec_var, ref rec, ref recinfo)) in self.tmp_rec.iter() {
      if !rec.dsub.is_empty() {
        panic!("bug: cg2: YFrame::_emit_recs_1");
      } else {
        let rec = rec._emit_rec_1_(recinfo);
        if log_debug() {
          println!("DEBUG: cg2: YFrame::_emit_recs_1: tmp rec={}", rec_var.0);
        }
        urec.insert(rec_var, rec);
      }
    }
    // TODO: shadow recs.
    for (&primrel, &(shad_rec, shadrel)) in self.shadow.iter() {
      let ar = match rels.get(&CVar(primrel)) {
        None => panic!("bug: cg2: YFrame::_emit_recs_1"),
        Some(rel) => rel.arity()
      };
      let mut usub = Vec::with_capacity(ar as usize);
      for k in 0 .. ar {
        usub.push(-(k as SNum + 1));
      }
      let dsub = Vec::new();
      let lkey = YKey{
        rel:    vec![primrel],
        off:    vec![0],
        // FIXME
        lary:   vec![ar as u32 - 1],
        rary:   vec![1],
        pat:    usub.clone(),
      };
      let mut tups = BTreeSet::new();
      tups.insert(YTup{
        rel:    shadrel,
        pat:    usub.clone(),
      });
      let rkey = YRKey{tups};
      let rec = YRec{
        usub,
        dsub,
        lkey,
        rkey,
      };
      let rec = rec._emit_rec_1();
      if log_debug() {
        println!("DEBUG: cg2: YFrame::_emit_recs_1: shad rel={} shadrel={} rec={}", primrel, shadrel, shad_rec.0);
      }
      urec.insert(shad_rec, rec);
    }
  }
}

#[derive(Clone, Default)]
struct YRec {
  usub: Vec<SNum>,
  dsub: Vec<SNum>,
  lkey: YKey,
  rkey: YRKey,
}

impl YRec {
  //fn _emit_rec_1_(&self, nod: &[BTreeSet<u32>]) -> TRec1 {
  fn _emit_rec_1_(&self, recinfo: &YKeyInfo) -> TRec1 {
    // TODO
    let mut emit = TRec1::default();
    let mut free: BTreeMap<SNum, i8> = BTreeMap::new();
    emit.uvlen = self.usub.len() as u8;
    emit.dvlen = self.dsub.len() as u8;
    emit.xvlen = 0;
    emit.antelen = self.lkey.rel.len() as u8;
    emit.conslen = self.rkey.tups.len() as u8;
    emit.useset = recinfo.use_.clone();
    emit.defset = recinfo.def.clone();
    // FIXME
    let mut nod_rel_ct = 0;
    emit.node.push(recinfo.nod.len() as _);
    for nod in recinfo.nod.iter() {
      nod_rel_ct += nod.len();
      emit.node.push(nod.len() as _);
      for &r in nod.iter() {
        emit.node.push(r as _);
      }
    }
    if self.lkey.rel.len() != nod_rel_ct {
      println!("TRACE: cg2: YRec::_emit_rec_1_: lkey.rel={:?} nod_rel_ct={}",
          self.lkey.rel, nod_rel_ct);
      println!("TRACE: cg2: YRec::_emit_rec_1_: possible double def?");
      panic!("BUG");
    }
    for r in 0 .. self.lkey.rel.len() {
      let rel = self.lkey.rel[r];
      if rel < 0 {
        emit.data.push(-1);
      } else {
        emit.data.push(1);
      }
      let rel_var = rel.abs();
      let rel_pos = match free.get(&rel_var) {
        None => {
          assert!(free.len() < 127);
          let rel_pos = free.len() as i8;
          free.insert(rel_var, rel_pos);
          rel_pos
        }
        Some(&rel_pos) => rel_pos
      };
      emit.data.push(rel_pos);
      let o = self.lkey.off[r];
      let la = self.lkey.lary[r];
      let ra = self.lkey.rary[r];
      for i in o as usize .. (o + la + ra) as usize {
        let p = self.lkey.pat[i];
        if p < 0 {
          emit.data.push(p as i8);
        } else if p > 0 {
          let pos = match free.get(&p) {
            None => {
              assert!(free.len() < 127);
              let pos = free.len() as i8;
              free.insert(p, pos);
              pos
            }
            Some(&pos) => pos
          };
          assert!(pos >= 0);
          emit.data.push(pos);
        } else {
          panic!("bug: YRec::_emit_rec_1");
        }
      }
    }
    for tup in self.rkey.tups.iter() {
      if tup.rel < 0 {
        emit.data.push(-1);
      } else {
        emit.data.push(1);
      }
      let rel_var = tup.rel.abs();
      let rel_pos = match free.get(&rel_var) {
        None => {
          assert!(free.len() < 127);
          let rel_pos = free.len() as i8;
          free.insert(rel_var, rel_pos);
          rel_pos
        }
        Some(&rel_pos) => rel_pos
      };
      emit.data.push(rel_pos);
      // TODO
      for &p in tup.pat.iter() {
        if p < 0 {
          emit.data.push(p as i8);
        } else if p > 0 {
          let pos = match free.get(&p) {
            None => {
              assert!(free.len() < 127);
              let pos = free.len() as i8;
              free.insert(p, pos);
              pos
            }
            Some(&pos) => pos
          };
          assert!(pos >= 0);
          emit.data.push(pos);
        } else {
          panic!("bug: YRec::_emit_rec_1");
        }
      }
    }
    let mut free_var: BTreeMap<i8, SNum> = BTreeMap::new();
    for (&rel_var, &rel_pos) in free.iter() {
      free_var.insert(rel_pos, rel_var);
    }
    assert_eq!(free.len(), free_var.len());
    for (&rel_pos, &rel_var) in free_var.iter() {
      assert_eq!(rel_pos as usize, emit.freevar.len());
      assert!(rel_var > 0);
      emit.freevar.push(rel_var);
    }
    emit
  }

  fn _emit_rec_1(&self) -> TRec1 {
    // TODO
    let mut emit = TRec1::default();
    let mut free: BTreeMap<SNum, i8> = BTreeMap::new();
    emit.uvlen = self.usub.len() as u8;
    emit.dvlen = self.dsub.len() as u8;
    emit.xvlen = 0;
    emit.antelen = self.lkey.rel.len() as u8;
    emit.conslen = self.rkey.tups.len() as u8;
    // FIXME
    emit.node.push(1);
    emit.node.push(emit.antelen);
    for r in 0 .. emit.antelen {
      emit.node.push(r);
    }
    for r in 0 .. self.lkey.rel.len() {
      let rel = self.lkey.rel[r];
      if rel < 0 {
        emit.data.push(-1);
      } else {
        emit.data.push(1);
      }
      let rel_var = rel.abs();
      let rel_pos = match free.get(&rel_var) {
        None => {
          assert!(free.len() <= 127);
          let rel_pos = free.len() as i8;
          free.insert(rel_var, rel_pos);
          rel_pos
        }
        Some(&rel_pos) => rel_pos
      };
      emit.data.push(rel_pos);
      let o = self.lkey.off[r];
      let la = self.lkey.lary[r];
      let ra = self.lkey.rary[r];
      for i in o as usize .. (o + la + ra) as usize {
        let p = self.lkey.pat[i];
        if p < 0 {
          emit.data.push(p as i8);
        } else if p > 0 {
          let pos = match free.get(&p) {
            None => {
              assert!(free.len() <= 127);
              let pos = free.len() as i8;
              free.insert(p, pos);
              pos
            }
            Some(&pos) => pos
          };
          assert!(pos >= 0);
          emit.data.push(pos);
        } else {
          panic!("bug: YRec::_emit_rec_1");
        }
      }
    }
    for tup in self.rkey.tups.iter() {
      if tup.rel < 0 {
        emit.data.push(-1);
      } else {
        emit.data.push(1);
      }
      let rel_var = tup.rel.abs();
      let rel_pos = match free.get(&rel_var) {
        None => {
          assert!(free.len() <= 127);
          let rel_pos = free.len() as i8;
          free.insert(rel_var, rel_pos);
          rel_pos
        }
        Some(&rel_pos) => rel_pos
      };
      emit.data.push(rel_pos);
      // TODO
      for &p in tup.pat.iter() {
        if p < 0 {
          emit.data.push(p as i8);
        } else if p > 0 {
          let pos = match free.get(&p) {
            None => {
              assert!(free.len() <= 127);
              let pos = free.len() as i8;
              free.insert(p, pos);
              pos
            }
            Some(&pos) => pos
          };
          assert!(pos >= 0);
          emit.data.push(pos);
        } else {
          panic!("bug: YRec::_emit_rec_1");
        }
      }
    }
    let mut free_var: BTreeMap<i8, SNum> = BTreeMap::new();
    for (&rel_var, &rel_pos) in free.iter() {
      free_var.insert(rel_pos, rel_var);
    }
    assert_eq!(free.len(), free_var.len());
    for (&rel_pos, &rel_var) in free_var.iter() {
      assert_eq!(rel_pos as usize, emit.freevar.len());
      emit.freevar.push(rel_var);
    }
    emit
  }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct YTup {
  rel:  SNum,
  pat:  Vec<SNum>,
}

#[derive(Clone, Default)]
struct YRKey {
  tups: BTreeSet<YTup>,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
struct YKey {
  rel:  Vec<SNum>,
  off:  Vec<u32>,
  lary: Vec<u32>,
  rary: Vec<u32>,
  pat:  Vec<SNum>,
}

#[derive(Default)]
struct YStatInfo {
  use_: BTreeMap<SNum, BTreeSet<u32>>,
  def:  BTreeMap<SNum, u32>,
  fwd:  BTreeMap<u32, BTreeSet<u32>>,
  bwd:  BTreeMap<u32, BTreeSet<u32>>,
  far:  BTreeMap<u32, u32>,
  bar:  BTreeMap<u32, u32>,
  src:  BTreeSet<u32>,
  snk:  BTreeSet<u32>,
}

impl YStatInfo {
  fn _reset(&mut self) {
    self.use_.clear();
    self.def.clear();
    self.fwd.clear();
    self.bwd.clear();
    self.far.clear();
    self.bar.clear();
    self.src.clear();
    self.snk.clear();
  }

  fn _fill_use_def(&mut self, qrec: &YRec) {
    for r in 0 .. qrec.lkey.rel.len() {
      let o = qrec.lkey.off[r];
      let la = qrec.lkey.lary[r];
      let ra = qrec.lkey.rary[r];
      for i in o as usize .. (o + la) as usize {
        let arg = qrec.lkey.pat[i];
        match self.use_.get_mut(&arg) {
          None => {
            let mut rels = BTreeSet::new();
            rels.insert(r as _);
            self.use_.insert(arg, rels);
          }
          Some(rels) => {
            rels.insert(r as _);
          }
        }
      }
      for i in (o + la) as usize .. (o + la + ra) as usize {
        let arg = qrec.lkey.pat[i];
        match self.def.get(&arg) {
          None => {
            self.def.insert(arg, r as _);
          }
          Some(&def0) => {
            panic!("bug: cg2: YStatInfo: double def: arg={} def0={} def1={}",
                arg, def0, r);
          }
        }
      }
    }
  }

  fn _fill_fwd_bwd(&mut self, qrec: &YRec) {
    for r in 0 .. qrec.lkey.rel.len() {
      let o = qrec.lkey.off[r];
      let la = qrec.lkey.lary[r];
      let ra = qrec.lkey.rary[r];
      let mut src = true;
      for i in o as usize .. (o + la) as usize {
        let arg = qrec.lkey.pat[i];
        match self.def.get(&arg) {
          None => {}
          Some(&def) => {
            src = false;
            match self.bwd.get_mut(&(r as _)) {
              None => {
                let mut rels = BTreeSet::new();
                rels.insert(def);
                self.bwd.insert(r as _, rels);
              }
              Some(rels) => {
                rels.insert(def);
              }
            }
          }
        }
      }
      if src {
        self.src.insert(r as _);
      }
      for i in (o + la) as usize .. (o + la + ra) as usize {
        let arg = qrec.lkey.pat[i];
        match self.use_.get(&arg) {
          None => {}
          Some(rels) => {
            for &r2 in rels.iter() {
              match self.fwd.get_mut(&(r as _)) {
                None => {
                  let mut rels = BTreeSet::new();
                  rels.insert(r2);
                  self.fwd.insert(r as _, rels);
                }
                Some(rels) => {
                  rels.insert(r2);
                }
              }
            }
          }
        }
      }
    }
    for r in 0 .. qrec.lkey.rel.len() {
      let r = r as _;
      match self.fwd.get(&r) {
        None => {}
        Some(rels) => {
          self.far.insert(r, rels.len() as u32);
        }
      }
      match self.bwd.get(&r) {
        None => {}
        Some(rels) => {
          self.bar.insert(r, rels.len() as u32);
        }
      }
    }
  }
}

#[derive(Default)]
struct YNodeInfo {
  nqueue:   VecDeque<BTreeSet<u32>>,
  //nuse:     BTreeMap<SNum, BTreeSet<u32>>,
  nvisit:   BTreeMap<u32, u32>,
  //nvisit:   BTreeSet<u32>,
  //nsub:     BTreeSet<SNum>,
  nod:      Vec<BTreeSet<u32>>,
  queue:    VecDeque<u32>,
  visit:    BTreeMap<u32, u32>,
  // TODO
  tmp:      BTreeMap<u32, SNum>,
  snk_req:  BTreeSet<SNum>,
  snk_map:  BTreeMap<SNum, BTreeSet<Vec<SNum>>>,
  snk_set:  BTreeSet<Vec<SNum>>,
  snk_edge: Vec<Vec<SNum>>,
  /*nod:  BTreeMap<u32, BTreeSet<u32>>,
  unod: BTreeMap<u32, BTreeSet<u32>>,
  dnod: BTreeMap<u32, BTreeSet<u32>>,
  nfwd: BTreeMap<u32, BTreeSet<u32>>,
  nbwd: BTreeMap<u32, BTreeSet<u32>>,*/
}

impl YNodeInfo {
  fn _reset(&mut self) {
    // TODO
    self.nqueue.clear();
    self.nvisit.clear();
    self.nod.clear();
    self.queue.clear();
    self.visit.clear();
    self.tmp.clear();
    self.snk_req.clear();
    self.snk_map.clear();
    self.snk_set.clear();
    self.snk_edge.clear();
  }
}

#[derive(Clone, Default)]
struct YKeyInfo {
  use_: BTreeMap<SNum, BTreeSet<u32>>,
  def:  BTreeMap<SNum, u32>,
  nod:  Vec<BTreeSet<u32>>,
}

impl YKeyInfo {
  fn from(stat: &YStatInfo, node: &YNodeInfo) -> YKeyInfo {
    YKeyInfo{
      use_: stat.use_.clone(),
      def:  stat.def.clone(),
      nod:  node.nod.clone(),
    }
  }
}

fn _postgen_rel(rel_var: CVar, rel: &ERelRef, yfm: &mut YFrame, shm: &mut STFrame) {
  match rel.fun_arity() {
    None => {}
    Some(_) => {
      let pseudo_var = shm.cc.fresh(TAttr::Top, &mut shm.univ, &mut shm.clk);
      yfm.pseudo.insert(rel_var, pseudo_var);
    }
  }
}

fn _recinfo(qrec: &YRec, stat: &mut YStatInfo, node: &mut YNodeInfo) {
  stat._reset();
  node._reset();
  stat._fill_use_def(qrec);
  stat._fill_fwd_bwd(qrec);
  node.nqueue.push_back(stat.src.clone());
  let mut this_nod = BTreeSet::new();
  let mut next_nod = BTreeSet::new();
  let mut last_nod = BTreeSet::new();
  loop {
    // TODO
    if !this_nod.is_empty() {
      node.nod.push(this_nod);
      this_nod = BTreeSet::new();
    }
    let nod = match node.nqueue.pop_front() {
      None => break,
      Some(n) => n
    };
    /*for &r in nod.iter() {
      let o = qrec.off[r as usize];
      let la = qrec.lary[r as usize];
      //let ra = qrec.rary[r as usize];
      for &p in qrec.pat[o as usize .. (o + la) as usize].iter() {
        match node.nuse.get_mut(&p) {
          None => {
            let mut rs = BTreeSet::new();
            rs.insert(r);
            node.nuse.insert(p, rs);
          }
          Some(rs) => {
            rs.insert(r);
          }
        }
      }
    }*/
    for &r in nod.iter() {
      let mut eq_rel = false;
      let rel = qrec.lkey.rel[r as usize];
      if rel == 1 || rel == -1 {
        eq_rel = true;
      }
      match stat.fwd.get(&r) {
        None => {}
        Some(fwd_rels) => {
          for &f in fwd_rels.iter() {
            let fv_ct = match node.nvisit.get_mut(&f) {
              None => {
                node.nvisit.insert(f, 1);
                1
              }
              Some(v_ct) => {
                *v_ct += 1;
                *v_ct
              }
            };
            match stat.bar.get(&f) {
              None => panic!("bug"),
              Some(&bar) => if fv_ct > bar {
                panic!("bug");
              } else if fv_ct == bar {
                // TODO
                next_nod.insert(f);
              }
            }
          }
        }
      }
      if !next_nod.is_empty() {
        node.nqueue.push_back(next_nod);
        next_nod = BTreeSet::new();
      }
      if eq_rel {
        last_nod.insert(r);
      } else {
        this_nod.insert(r);
      }
    }
  }
  if !last_nod.is_empty() {
    node.nod.push(last_nod);
  }
}

fn _gen_rec(qrec_var: SNum, qrec: &YRec, stat: &mut YStatInfo, node: &mut YNodeInfo, yfm: &mut YFrame, shm: &mut STFrame) {
  if log_debug() {
    println!("DEBUG: cg2: _gen_rec: rec={} uv={} dv={} lkey={} rkey={}",
        qrec_var,
        qrec.usub.len(), qrec.dsub.len(),
        qrec.lkey.rel.len(), qrec.rkey.tups.len(),
    );
  }
  if qrec.usub.is_empty() && qrec.dsub.is_empty() {
    // TODO
    yfm.freerec.push((CVar(qrec_var), qrec.clone()));
    return;
  }
  _recinfo(qrec, stat, node);
  //yfm.primrec.push((CVar(qrec_var), qrec.clone(), node.nod.clone()));
  let recinfo = YKeyInfo::from(&stat, &node);
  yfm.primrec.push((CVar(qrec_var), qrec.clone(), recinfo));
  for &r in stat.src.iter() {
    node.queue.push_back(r);
  }
  for tup in qrec.rkey.tups.iter() {
    for &q in tup.pat.iter() {
      node.snk_req.insert(q);
    }
  }
  loop {
    let r = match node.queue.pop_front() {
      None => break,
      Some(r) => r
    };
    let v = match node.visit.get_mut(&r) {
      None => {
        node.visit.insert(r, 1);
        1
      }
      Some(v) => {
        *v += 1;
        *v
      }
    };
    if log_trace() {
      println!("DEBUG: cg2: _gen_rec: loop: r={} v={}", r, v);
    }
    match stat.bar.get(&r) {
      None => if v > 1 {
        panic!("bug: src loopy");
      }
      Some(&maxv) => if v > maxv {
        panic!("bug: loopy");
      } else if v < maxv {
        if log_trace() {
          println!("DEBUG: cg2: _gen_rec:   skip, maxv={}", maxv);
        }
        continue;
      }
    }
    // TODO
    let mut snk = false;
    match stat.fwd.get(&r) {
      None => {
        if log_trace() {
          println!("DEBUG: cg2: _gen_rec:   snk");
        }
        snk = true;
        stat.snk.insert(r);
      }
      Some(rels) => {
        if log_trace() {
          println!("DEBUG: cg2: _gen_rec:   fwd={}", rels.len());
        }
        for &r2 in rels.iter() {
          node.queue.push_back(r2);
        }
      }
    }
    let rel = qrec.lkey.rel[r as usize];
    let o = qrec.lkey.off[r as usize];
    let la = qrec.lkey.lary[r as usize];
    let ra = qrec.lkey.rary[r as usize];
    if ra > 0 {
      match yfm.shadow.get(&rel) {
        None => {
          let shd_rel = shm._fresh_var(TAttr::Gen);
          let shd_rec = shm._fresh_var(TAttr::Gen);
          if log_trace() {
            println!("DEBUG: cg2: _gen_rec:   shd fresh rel={} rec={}", shd_rel, shd_rec);
          }
          yfm.shadow.insert(rel.abs(), (CVar(shd_rec), shd_rel));
        }
        Some(_) => {}
      }
    }
    let tmp_rel = shm._fresh_var(TAttr::Gen);
    node.tmp.insert(r, tmp_rel);
    yfm.tmp_rel.insert(tmp_rel, rel.abs());
    let tmp_rec_var = CVar(shm._fresh_var(TAttr::Gen));
    if log_trace() {
      println!("DEBUG: cg2: _gen_rec:   tmp fresh rel={} rec={}", tmp_rel, tmp_rec_var.0);
    }
    let mut edge = Vec::new();
    match stat.bwd.get(&r) {
      None => {}
      Some(rels) => {
        for &r2 in rels.iter() {
          let rel2 = qrec.lkey.rel[r2 as usize];
          let o2 = qrec.lkey.off[r2 as usize];
          let la2 = qrec.lkey.lary[r2 as usize];
          let ra2 = qrec.lkey.rary[r2 as usize];
          let mut tup2 = Vec::with_capacity((la2 + ra2 + 1) as usize);
          for &p in qrec.lkey.pat[o2 as usize .. (o2 + la2 + ra2) as usize].iter() {
            if p < 0 {
              tup2.push(-p);
            } else {
              panic!("bug: sign");
            }
          }
          match (yfm.shadow.get(&rel2), node.tmp.get(&r2)) {
            (None, None) => {
              panic!("bug");
            }
            (Some(&(_, shd_rel2)), None) => {
              tup2.push(shd_rel2);
            }
            (None, Some(&tmp_rel2)) => {
              tup2.push(tmp_rel2);
            }
            //(Some(&shd_rel2), Some(_)) => {
            (Some(_), Some(&tmp_rel2)) => {
              //panic!("bug");
              //tup2.push(shd_rel2);
              tup2.push(tmp_rel2);
            }
          }
          edge.push(tup2);
        }
      }
    }
    let mut this_tup = Vec::with_capacity((la + ra + 1) as usize);
    for &p in qrec.lkey.pat[o as usize .. (o + la + ra) as usize].iter() {
      if p < 0 {
        this_tup.push(-p);
      } else {
        panic!("bug: sign (check params?)");
      }
    }
    this_tup.push(rel);
    edge.push(this_tup);
    // TODO
    edge.sort();
    let mut alp = BTreeMap::new();
    let mut ltmp_rel = Vec::with_capacity(edge.len());
    let mut ltmp_off = Vec::with_capacity(edge.len());
    let mut ltmp_lary = Vec::with_capacity(edge.len());
    let mut ltmp_rary = Vec::with_capacity(edge.len());
    let mut ltmp_pat = Vec::new();
    let mut ltmp_o = 0;
    for tup in edge.iter() {
      let rel = tup[tup.len() - 1];
      let a = (tup.len() - 1) as u32;
      ltmp_rel.push(rel);
      ltmp_off.push(ltmp_o);
      ltmp_lary.push(a);
      ltmp_rary.push(0);
      for i in 0 .. tup.len() - 1 {
        match alp.get(&(-tup[i])) {
          None => {
            let p = -(alp.len() as SNum + 1);
            alp.insert(-tup[i], p);
            ltmp_pat.push(p);
          }
          Some(&p) => {
            ltmp_pat.push(p);
          }
        }
      }
      ltmp_o += a;
    }
    let tmp_lkey = YKey{
      rel:    ltmp_rel,
      off:    ltmp_off,
      lary:   ltmp_lary,
      rary:   ltmp_rary,
      pat:    ltmp_pat,
    };
    let rtmp_rel = tmp_rel;
    let mut rtmp_tup = Vec::with_capacity((la + ra + 1) as usize);
    let mut rtmp_pat = Vec::with_capacity((la + ra) as usize);
    for &q in &qrec.lkey.pat[o as usize .. (o + la + ra) as usize] {
      rtmp_tup.push(-q);
      match alp.get(&q) {
        None => panic!("bug: alp"),
        Some(&p) => {
          rtmp_pat.push(p);
        }
      }
    }
    rtmp_tup.push(rtmp_rel);
    if !snk {
      // FIXME
      for &q in rtmp_tup[ .. rtmp_tup.len() - 1].iter() {
        if node.snk_req.contains(&(-q)) {
          snk = true;
          break;
          /*match node.snk_map.get(&q) {
            None => {
              snk = true;
              break;
            }
            Some(_) => {}
          }*/
        }
      }
    }
    if snk {
      /*for &q in rtmp_tup[ .. rtmp_tup.len() - 1].iter() {
        match node.snk_map.get_mut(&q) {
          None => {
            let mut tups = BTreeSet::new();
            tups.insert(rtmp_tup.clone());
            node.snk_map.insert(q, tups);
          }
          Some(tups) => {
            tups.insert(rtmp_tup.clone());
          }
        }
      }*/
      node.snk_set.insert(rtmp_tup);
      //node.snk_edge.push(rtmp_tup);
    }
    let rtmp_tup = YTup{
      rel:    rtmp_rel,
      pat:    rtmp_pat,
    };
    match yfm.tmp_rec.get_mut(&tmp_lkey) {
      None => {
        let mut usub = Vec::new();
        for &p in tmp_lkey.pat.iter() {
          let k = -(p + 1) as usize;
          if usub.len() <= k {
            for k_ in usub.len() .. k + 1 {
              usub.push(-(k_ as SNum + 1));
            }
          }
        }
        let mut tups = BTreeSet::new();
        tups.insert(rtmp_tup);
        let rec = YRec{
          usub,
          dsub:   Vec::new(),
          lkey:   tmp_lkey.clone(),
          rkey:   YRKey{tups},
        };
        let mut tmp_stat = YStatInfo::default();
        let mut tmp_node = YNodeInfo::default();
        _recinfo(&rec, &mut tmp_stat, &mut tmp_node);
        let recinfo = YKeyInfo::from(&tmp_stat, &tmp_node);
        yfm.tmp_rec.insert(tmp_lkey, (tmp_rec_var, rec, recinfo));
      }
      Some(&mut (_, ref mut tmp_rec, _)) => {
        tmp_rec.rkey.tups.insert(rtmp_tup);
      }
    }
  }
  if node.snk_set.is_empty() {
    panic!("bug: snk loopy");
  }
  /*for tup in node.snk_set.iter() {
    node.snk_edge.push(tup.clone());
  }
  assert_eq!(node.snk_set.len(), node.snk_edge.len());
  //node.snk_edge.sort();
  // TODO
  //let snk_rec_var = CVar(shm._fresh_var(TAttr::Gen));
  let mut alp = BTreeMap::new();
  let mut lsnk_rel = Vec::with_capacity(node.snk_edge.len());
  let mut lsnk_off = Vec::with_capacity(node.snk_edge.len());
  let mut lsnk_lary = Vec::with_capacity(node.snk_edge.len());
  let mut lsnk_rary = Vec::with_capacity(node.snk_edge.len());
  let mut lsnk_pat = Vec::new();
  let mut lsnk_o = 0;
  if log_trace() {
    println!("DEBUG: cg2: _gen_rec: snk edge={:?}", node.snk_edge);
  }
  for tup in node.snk_edge.iter() {
    let rel = tup[tup.len() - 1];
    let a = (tup.len() - 1) as u32;
    lsnk_rel.push(rel);
    lsnk_off.push(lsnk_o);
    lsnk_lary.push(a);
    lsnk_rary.push(0);
    for i in 0 .. tup.len() - 1 {
      match alp.get(&(-tup[i])) {
        None => {
          let p = -(alp.len() as SNum + 1);
          alp.insert(-tup[i], p);
          lsnk_pat.push(p);
        }
        Some(&p) => {
          lsnk_pat.push(p);
        }
      }
    }
    lsnk_o += a;
  }
  if log_trace() {
    println!("DEBUG: cg2: _gen_rec:   alp={:?}", alp);
  }
  let snk_lkey = YKey{
    rel:    lsnk_rel,
    off:    lsnk_off,
    lary:   lsnk_lary,
    rary:   lsnk_rary,
    pat:    lsnk_pat,
  };
  match yfm.snk_rec.get_mut(&snk_lkey) {
    None => {
      // TODO
      let mut usub = Vec::new();
      let mut dsub = Vec::with_capacity(qrec.dsub.len());
      for &p in snk_lkey.pat.iter() {
        if p <= 0 {
          let k = -(p + 1) as usize;
          if usub.len() <= k {
            for k_ in usub.len() .. k + 1 {
              usub.push(-(k_ as SNum + 1));
            }
          }
        }
      }
      let mut tups = BTreeSet::new();
      for tup in qrec.rkey.tups.iter() {
        let rel = tup.rel;
        let mut pat = Vec::with_capacity(tup.pat.len());
        for i in 0 .. tup.pat.len() {
          let op = tup.pat[i];
          let mut d = false;
          for &od in qrec.dsub.iter() {
            if od == op {
              d = true;
              let p = -(alp.len() as SNum + 1);
              alp.insert(op, p);
              dsub.push(p);
              pat.push(p);
              break;
            }
          }
          if d {
            continue;
          }
          match alp.get(&op) {
            None => panic!("bug: alp: {} q dsub={:?}, dsub={:?}", op, qrec.dsub, dsub),
            Some(&p) => {
              pat.push(p);
            }
          }
        }
        tups.insert(YTup{rel, pat});
      }
      assert_eq!(qrec.dsub.len(), dsub.len());
      let rec = YRec{
        usub,
        dsub,
        lkey:   snk_lkey.clone(),
        rkey:   YRKey{tups},
      };
      yfm.snk_rec.insert(snk_lkey, (CVar(qrec_var), rec));
    }
    Some(&mut (_, ref mut snk_rec)) => {
      for tup in qrec.rkey.tups.iter() {
        snk_rec.rkey.tups.insert(tup.clone());
      }
    }
  }*/
}

fn _lookup_i2v(var: IVar, i2v: &BTreeMap<IVar, SNum>, theory: &ITheoryEnv, dbgstack: &[ILoc]) -> SNum {
  match i2v.get(&var) {
    None => {
      println!("DEBUG: missing var: {:?}", var);
      for &loc in dbgstack.iter() {
        println!("DEBUG:   debuginfo? {:?}", theory.find_debuginfo_nonmut(loc));
      }
      panic!("BUG");
    }
    Some(&v) => v
  }
}

fn _pregen_rec(qrec: &IRecForm, theory: &ITheoryEnv, evar: SNum, i2v: &mut BTreeMap<IVar, SNum>, shm: &mut STFrame) -> YRec {
  // TODO
  match qrec {
    &IRecForm::P(..) => {
      panic!("bug: unimplemented: IRecForm::P");
    }
    &IRecForm::RPC(rec_loc, ref ctx, _, ref ante, ref cons) => {
      assert!(ctx.uvars.len() + ctx.dvars.len() + ctx.xvars.len() <= 127);
      let mut emit_usub = Vec::with_capacity(ctx.uvars.len());
      let mut emit_dsub = Vec::with_capacity(ctx.dvars.len());
      let mut param = BTreeMap::new();
      let mut p: SNum = -1;
      for &v in ctx.uvars.iter() {
        param.insert(v, p);
        emit_usub.push(p);
        p -= 1;
      }
      for &v in ctx.dvars.iter() {
        param.insert(v, p);
        emit_dsub.push(p);
        p -= 1;
      }
      for &v in ctx.xvars.iter() {
        /*param.insert(v, p);
        p -= 1;*/
        panic!("bug: unimplemented: xvars");
      }
      assert!(ante.len() + cons.len() <= 127);
      let mut is_cons = false;
      let mut lkey_rel = Vec::with_capacity(ante.len());
      let mut lkey_off = Vec::with_capacity(ante.len());
      let mut lkey_lary = Vec::with_capacity(ante.len());
      let mut lkey_rary = Vec::with_capacity(ante.len());
      let mut lkey_pat = Vec::new();
      let mut rkey_tups = BTreeSet::new();
      let mut r: u32 = 0;
      let mut o: u32 = 0;
      for f in ante.iter().chain(cons.iter()) {
        if r >= ante.len() as _ {
          is_cons = true;
        }
        match f {
          &IClausalForm::Lit(cla_loc, neg, ref atom) => match atom {
            &IAtomicForm::RPre(atom_loc, pre, ref args) => {
              let dbgstack = &[atom_loc, cla_loc, rec_loc];
              let rel = _lookup_i2v(pre, i2v, theory, dbgstack);
              let ar = args.len() as u32;
              // TODO
              if is_cons {
                let mut pat = Vec::with_capacity(args.len());
                for &arg in args.iter() {
                  let p = match param.get(&arg) {
                    None => _lookup_i2v(arg, i2v, theory, dbgstack),
                    Some(&p) => p
                  };
                  pat.push(p);
                }
                let rel = if neg {
                  -rel
                } else {
                  rel
                };
                let tup = YTup{rel, pat};
                rkey_tups.insert(tup);
              } else {
                if neg {
                  lkey_rel.push(-rel);
                } else {
                  lkey_rel.push(rel);
                }
                lkey_off.push(o);
                lkey_lary.push(ar);
                lkey_rary.push(0);
                for &arg in args.iter() {
                  let p = match param.get(&arg) {
                    None => _lookup_i2v(arg, i2v, theory, dbgstack),
                    Some(&p) => p
                  };
                  lkey_pat.push(p);
                }
                o += ar;
              }
            }
            &IAtomicForm::RApp(atom_loc, pre, ref largs, ref rargs) => {
              let dbgstack = &[atom_loc, cla_loc, rec_loc];
              let rel = _lookup_i2v(pre, i2v, theory, &[atom_loc, cla_loc, rec_loc]);
              let lar = largs.len() as u32;
              let rar = rargs.len() as u32;
              // TODO
              if is_cons {
                let mut pat = Vec::with_capacity(largs.len() + rargs.len());
                for &arg in largs.iter().chain(rargs.iter()) {
                  let p = match param.get(&arg) {
                    None => _lookup_i2v(arg, i2v, theory, dbgstack),
                    Some(&p) => p
                  };
                  pat.push(p);
                }
                let tup = YTup{rel, pat};
                rkey_tups.insert(tup);
              } else {
                lkey_rel.push(rel);
                lkey_off.push(o);
                lkey_lary.push(lar);
                lkey_rary.push(rar);
                for &arg in largs.iter().chain(rargs.iter()) {
                  let p = match param.get(&arg) {
                    None => _lookup_i2v(arg, i2v, theory, dbgstack),
                    Some(&p) => p
                  };
                  lkey_pat.push(p);
                }
                o += lar + rar;
              }
            }
            _ => panic!("bug: unimplemented: IAtomicForm::???")
          }
          &IClausalForm::Eq_(cla_loc, ref lexp, ref rexp) => {
            let dbgstack = &[cla_loc, rec_loc];
            let rel = evar;
            let ar = 2;
            let larg = match lexp {
              &IExp::RVar(_, v) => v,
              _ => panic!("bug: Eq_: IExp::???")
            };
            let rarg = match rexp {
              &IExp::RVar(_, v) => v,
              _ => panic!("bug: Eq_: IExp::???")
            };
            // TODO
            if is_cons {
              let mut pat = Vec::with_capacity(2);
              for &arg in [larg, rarg].iter() {
                let p = match param.get(&arg) {
                  None => _lookup_i2v(arg, i2v, theory, dbgstack),
                  Some(&p) => p
                };
                pat.push(p);
              }
              let tup = YTup{rel, pat};
              rkey_tups.insert(tup);
            } else {
              lkey_rel.push(rel);
              lkey_off.push(o);
              lkey_lary.push(ar);
              lkey_rary.push(0);
              for &arg in [larg, rarg].iter() {
                let p = match param.get(&arg) {
                  None => _lookup_i2v(arg, i2v, theory, dbgstack),
                  Some(&p) => p
                };
                lkey_pat.push(p);
              }
              o += 2;
            }
          }
          &IClausalForm::Neq(cla_loc, ref lexp, ref rexp) => {
            let dbgstack = &[cla_loc, rec_loc];
            let rel = evar;
            let ar = 2;
            let larg = match lexp {
              &IExp::RVar(_, v) => v,
              _ => panic!("bug: Neq: IExp::???")
            };
            let rarg = match rexp {
              &IExp::RVar(_, v) => v,
              _ => panic!("bug: Neq: IExp::???")
            };
            // TODO
            if is_cons {
              let mut pat = Vec::with_capacity(2);
              for &arg in [larg, rarg].iter() {
                let p = match param.get(&arg) {
                  None => _lookup_i2v(arg, i2v, theory, dbgstack),
                  Some(&p) => p
                };
                pat.push(p);
              }
              let tup = YTup{rel: -rel, pat};
              rkey_tups.insert(tup);
            } else {
              lkey_rel.push(-rel);
              lkey_off.push(o);
              lkey_lary.push(ar);
              lkey_rary.push(0);
              for &arg in [larg, rarg].iter() {
                let p = match param.get(&arg) {
                  None => _lookup_i2v(arg, i2v, theory, dbgstack),
                  Some(&p) => p
                };
                lkey_pat.push(p);
              }
              o += 2;
            }
          }
          _ => panic!("bug: unimplemented: IClausalForm::???")
        }
        r += 1;
      }
      let lkey = YKey{
        rel:    lkey_rel,
        off:    lkey_off,
        lary:   lkey_lary,
        rary:   lkey_rary,
        pat:    lkey_pat,
      };
      let rkey = YRKey{
        tups:   rkey_tups,
      };
      let emit = YRec{
        usub:   emit_usub,
        dsub:   emit_dsub,
        lkey,
        rkey,
      };
      emit
    }
    _ => {
      panic!("bug: unimplemented: IRecForm::???");
    }
  }
}

pub fn gen_frame_(theory: &mut ITheoryEnv) -> TFrame {
  let mut i2v = BTreeMap::new();
  let mut shm = STFrame::default();
  let mut yfm = YFrame::default();
  let evar = shm.evar;
  match theory.eqv {
    None => panic!("bug"),
    Some(var) => {
      i2v.insert(var, evar.0);
      theory._bind_var(var, evar);
    }
  }
  for (&name, &(_, var)) in theory.top.bind.iter() {
    // TODO
    match theory.eqv {
      None => panic!("bug"),
      Some(var2) => if var == var2 {
        if log_debug() {
          println!("DEBUG: cg2: gen_frame: top level var (equiv): {:?} {:?} {:?} '{}'",
              evar, var, name, theory.rev_lookup_name(name));
        }
        continue;
      }
    }
    let v = shm.cc.fresh(TAttr::Top, &mut shm.univ, &mut shm.clk);
    i2v.insert(var, v.0);
    theory._bind_var(var, v);
    if log_debug() {
      println!("DEBUG: cg2: gen_frame: top level var: {:?} {:?} {:?} '{}'",
          v, var, name, theory.rev_lookup_name(name));
    }
  }
  let mut equiv = false;
  let mut rels = IHTreapMap::default();
  for (_, rel) in theory.rels.iter() {
    // TODO
    let mut equiv_ = false;
    let rel_: ERelRef = match (rel.arity, rel.funarity) {
      (1, None) => match rel.schema {
        None => Rc::new(Rel1::default()),
        _ => unimplemented!()
      }
      (2, Some((1, 1))) => match rel.schema {
        None => Rc::new(Fun1::default()),
        _ => unimplemented!()
      }
      (2, None) => match rel.schema {
        None => Rc::new(Rel2::default()),
        Some(Symmetric) => Rc::new(SymmRel2::default()),
        Some(Equivalence) => {
          assert!(!equiv);
          equiv = true;
          equiv_ = true;
          Rc::new(EquivRel::default())
        }
        _ => unimplemented!()
      }
      (3, Some((2, 1))) => match rel.schema {
        None => Rc::new(Fun2::default()),
        Some(Symmetric) => Rc::new(SymmFun2::default()),
        _ => unimplemented!()
      }
      (3, None) => match rel.schema {
        None => Rc::new(Rel3::default()),
        Some(Symmetric) => Rc::new(SymmRel3::default()),
        _ => unimplemented!()
      }
      (4, Some((3, 1))) => match rel.schema {
        None => Rc::new(Fun3::default()),
        Some(Symmetric) => Rc::new(SymmFun3::default()),
        _ => unimplemented!()
      }
      (4, None) => match rel.schema {
        None => Rc::new(Rel4::default()),
        _ => unimplemented!()
      }
      (5, Some((4, 1))) => match rel.schema {
        None => Rc::new(Fun4::default()),
        Some(Cyclic) => Rc::new(CyclFun4::default()),
        _ => unimplemented!()
      }
      (6, None) => match rel.schema {
        None => Rc::new(Rel6::default()),
        _ => unimplemented!()
      }
      _ => {
        panic!("bug: cg2: gen_frame: unimplemented: {:?} {:?} {:?}", rel.arity, rel.funarity, rel.schema);
      }
    };
    let rel_var = if equiv_ {
      if log_debug() {
        println!("DEBUG: cg2: gen_frame: new equiv rel: {:?} {:?} {:?} '{}'",
            evar, rel.var, rel.name, theory.rev_lookup_name(rel.name));
      }
      evar
    } else {
      match i2v.get(&rel.var) {
        None => panic!("bug"),
        Some(&v) => {
          if log_debug() {
            println!("DEBUG: cg2: gen_frame: new rel: {:?} {:?} {:?} '{}'",
                CVar(v), rel.var, rel.name, theory.rev_lookup_name(rel.name));
          }
          CVar(v)
        }
      }
    };
    rels.insert(rel_var, rel_);
  }
  let mut node = YNodeInfo::default();
  let mut stat = YStatInfo::default();
  let mut rec_vars = Vec::with_capacity(theory.recs.len());
  for (_, rec) in theory.recs.iter() {
    let rec_var = shm.cc.fresh(TAttr::Top, &mut shm.univ, &mut shm.clk);
    rec_vars.push(rec_var);
  }
  for (&rel_var, rel) in rels.iter() {
    _postgen_rel(rel_var, rel, &mut yfm, &mut shm);
  }
  for ((_, rec), &rec_var) in theory.recs.iter().zip(rec_vars.iter()) {
    // TODO
    let rec = _pregen_rec(rec, &theory, evar.0, &mut i2v, &mut shm);
    _gen_rec(rec_var.0, &rec, &mut stat, &mut node, &mut yfm, &mut shm);
  }
  /*for (_, prop) in theory.prop.iter() {
    // TODO
    //_gen_prop(prop, &theory, evar.0, &mut i2v, &mut shm);
  }*/
  let mut prop_ = None;
  let mut p: u32 = 0;
  for (_, prop) in theory.prop.iter() {
    if log_debug() {
      println!("DEBUG: cg2: gen_frame: new prop");
    }
    if prop_.is_none() {
      prop_ = Some(TFre1::default());
    }
    let prop_ = prop_.as_mut().unwrap();
    match prop {
      &IForm::Fre(prop_loc, ref f) => {
        // FIXME
        match f {
          &IClausalForm::Lit(lit_loc, neg, ref atom) => match atom {
            &IAtomicForm::RPre(atom_loc, pre, ref args) => {
              let pre_ = match i2v.get(&pre) {
                None => {
                  println!("DEBUG: cg2: gen_frame: missing var: {:?}", pre);
                  println!("DEBUG: cg2: gen_frame:   debug info? {:?}", theory.find_debuginfo(atom_loc));
                  println!("DEBUG: cg2: gen_frame:   debug info? {:?}", theory.find_debuginfo(lit_loc));
                  println!("DEBUG: cg2: gen_frame:   debug info? {:?}", theory.find_debuginfo(prop_loc));
                  panic!("BUG");
                }
                Some(&v) => v
              };
              if neg {
                prop_.data.push(-1);
              } else {
                prop_.data.push(1);
              }
              assert!(p <= 127);
              prop_.freevar.push(pre_);
              prop_.data.push(p as i8);
              p += 1;
              for &arg in args.iter() {
                let arg_var = match i2v.get(&arg) {
                  None => {
                    println!("DEBUG: cg2: gen_frame: missing var: {:?}", arg);
                    println!("DEBUG: cg2: gen_frame:   debug info? {:?}", theory.find_debuginfo(atom_loc));
                    println!("DEBUG: cg2: gen_frame:   debug info? {:?}", theory.find_debuginfo(lit_loc));
                    println!("DEBUG: cg2: gen_frame:   debug info? {:?}", theory.find_debuginfo(prop_loc));
                    panic!("BUG");
                  }
                  Some(&v) => CVar(v)
                };
                assert!(p <= 127);
                prop_.freevar.push(arg_var.0);
                prop_.data.push(p as i8);
                p += 1;
              }
              prop_.rel_len += 1;
            }
            _ => unimplemented!()
          }
          &IClausalForm::Eq_(lit_loc, ref lexp, ref rexp) => {
            //panic!("bug: cg2: gen_frame: unimplemented prop form: Eq_");
            prop_.data.push(1);
            assert!(p <= 127);
            prop_.freevar.push(evar.0);
            prop_.data.push(p as i8);
            p += 1;
            let larg = match lexp {
              &IExp::RVar(_, v) => v,
              _ => panic!("bug")
            };
            let arg_var = match i2v.get(&larg) {
              None => {
                println!("DEBUG: cg2: gen_frame: missing var: {:?}", larg);
                println!("DEBUG: cg2: gen_frame:   debug info? {:?}", theory.find_debuginfo(lit_loc));
                println!("DEBUG: cg2: gen_frame:   debug info? {:?}", theory.find_debuginfo(prop_loc));
                panic!("BUG");
              }
              Some(&v) => CVar(v)
            };
            assert!(p <= 127);
            prop_.freevar.push(arg_var.0);
            prop_.data.push(p as i8);
            p += 1;
            let rarg = match rexp {
              &IExp::RVar(_, v) => v,
              _ => panic!("bug")
            };
            let arg_var = match i2v.get(&rarg) {
              None => {
                println!("DEBUG: cg2: gen_frame: missing var: {:?}", rarg);
                println!("DEBUG: cg2: gen_frame:   debug info? {:?}", theory.find_debuginfo(lit_loc));
                println!("DEBUG: cg2: gen_frame:   debug info? {:?}", theory.find_debuginfo(prop_loc));
                panic!("BUG");
              }
              Some(&v) => CVar(v)
            };
            assert!(p <= 127);
            prop_.freevar.push(arg_var.0);
            prop_.data.push(p as i8);
            p += 1;
            prop_.rel_len += 1;
          }
          _ => unimplemented!()
        }
      }
      _ => {
        panic!("bug: cg2: gen_frame: nonfree prop form");
      }
    }
  }
  yfm._emit_rels(&mut rels);
  let mut urec = HTreapMap::default();
  let mut drec = HTreapMap::default();
  yfm._emit_recs_1(&rels, &mut urec, &mut drec, &mut shm);
  TFrame{
    shm,
    //inc:    GCUFrame::default(),
    //swf:    WFrame::default(),
    rels,
    //r2r:    Rel2RecIndex::default(),
    //r2d:    Rel2RecIndex::default(),
    urec,
    drec,
    xrec:   HTreapMap::default(),
    prop:   prop_,
  }
}
