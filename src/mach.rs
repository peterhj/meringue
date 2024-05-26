use crate::algo::*;
use crate::config::{RuntimeConfig};
use crate::framework::*;
use crate::framework2::*;
use crate::ir::*;
use crate::log::*;
use crate::rng::*;
use crate::smp::{ExponentialBackoff};
use crate::smp::chan::*;
use crate::smp::group::{ThreadGroup, ThreadPeer};
use crate::timer::{WallclockStopwatch};

use std::cell::{Cell, RefCell};
use std::cmp::{Ordering, max};
use std::sync::{Arc as Rc};

const DEFAULT_MAXDEPTH: u32 = 1;

thread_local! {
  static TL_SEED: Cell<Option<u64>> = Cell::new(None);
  static TL_RNG: RefCell<XoshiroRng> = RefCell::new(
      match TL_SEED.with(|val| val.get()) {
        None => {
          println!("DEBUG: rng: init from entropy source (no seed)");
          match XoshiroRng::from_rng(EntropyRng::default()) {
            Err(_) => panic!("bug: TL_RNG: init failure"),
            Ok(rng) => rng
          }
        }
        Some(seed) => {
          println!("DEBUG: rng: init from seed={}", seed);
          XoshiroRng::from_u64_seed(seed)
        }
      }
  );
}

pub fn init_tl_rng_seed(seed: u64) {
  TL_SEED.with(|val| val.set(Some(seed)));
}

pub type XEvalCfg = XMachCfg;

#[derive(Clone, Copy, Debug)]
pub struct XMachCfg {
  pub maxdepth: u32,
}

impl Default for XMachCfg {
  fn default() -> XMachCfg {
    XMachCfg{
      maxdepth: DEFAULT_MAXDEPTH,
    }
  }
}

#[derive(Clone, Copy, Debug)]
pub enum MDebugStep {
  Ret,
  Sat,
  Par,
  //Unw,
  //Spl,
  Fix,
  Nul,
  Def(SNum),
  Mat(SNum),
  Cas(u32),
  //Unmat,
  Sol(TNum),
}

#[derive(Clone, Copy, Debug)]
pub enum MStepKind {
  Ret,
  Sat,
  Par,
  //Unw,
  //Spl,
  Fix,
  Nul,
  Def,
  Mat,
  Cas,
  //Unmat,
  Sol,
}

#[derive(Clone)]
pub enum MStep {
  Ret,
  Sat,
  Par,
  //Unw,
  //Spl,
  //Anz,
  Fix,
  Nul,
  Def(SNum),
  Mat(Vec<SNum>),
  Cas(u32, SNum),
  //Unmat,
  Sol(TNum, TFrameRef),
}

impl MStep {
  pub fn kind(&self) -> MStepKind {
    match self {
      &MStep::Ret => MStepKind::Ret,
      &MStep::Sat => MStepKind::Sat,
      &MStep::Par => MStepKind::Par,
      //&MStep::Unw => MStepKind::Unw,
      //&MStep::Spl => MStepKind::Spl,
      &MStep::Fix => MStepKind::Fix,
      &MStep::Nul => MStepKind::Nul,
      &MStep::Def(_) => MStepKind::Def,
      &MStep::Mat(_) => MStepKind::Mat,
      &MStep::Cas(..) => MStepKind::Cas,
      //&MStep::Unmat => MStepKind::Unmat,
      &MStep::Sol(..) => MStepKind::Sol,
    }
  }

  pub fn debugstep(&self) -> MDebugStep {
    match self {
      &MStep::Ret => MDebugStep::Ret,
      &MStep::Sat => MDebugStep::Sat,
      &MStep::Par => MDebugStep::Par,
      //&MStep::Unw => MDebugStep::Unw,
      //&MStep::Spl => MDebugStep::Spl,
      &MStep::Fix => MDebugStep::Fix,
      &MStep::Nul => MDebugStep::Nul,
      &MStep::Def(x) => MDebugStep::Def(x),
      &MStep::Mat(ref xs) => {
        assert!(xs.len() > 0);
        MDebugStep::Mat(xs[0])
      }
      &MStep::Cas(k, _) => MDebugStep::Cas(k),
      //&MStep::Unmat => MDebugStep::Unmat,
      &MStep::Sol(tlb, _) => MDebugStep::Sol(tlb),
    }
  }
}

/*pub struct MTrace {
  buf:  Vec<MStep>,
}*/

pub type XKontRef = Rc<XKont_>;

#[derive(Clone)]
pub enum XKont_ {
  // TODO
  Halt,
  //Push(TNum, TFrameRef, XKontRef),
  Max1(XMax1State, TNum, TFrameRef, XKontRef),
  //Mat_(Vec<SNum>, u32, XCase, Vec<(XCase, TNum, TFrameRef)>, TFrameRef, XKontRef),
  Mat_(XMatState, TNum, TFrameRef, XKontRef),
  Sol1(TNum, TFrameRef, XKontRef/*, XReg*/),
  // TODO
  Max(TFrameRef, XKontRef),
  Mat(TFrameRef, Vec<SNum>, Vec<(XCase, TFrameRef)>, XKontRef),
}

impl Default for XKont_ {
  fn default() -> XKont_ {
    XKont_::Halt
  }
}

impl XKont_ {
  pub fn halt(&self) -> bool {
    match self {
      &XKont_::Halt => true,
      _ => false
    }
  }
}

pub type XMax1SharedRef = Rc<RefCell<XMax1Shared>>;

#[derive(Default)]
pub struct XMax1Shared {
  //step: Option<MStep>,
  //opt:  Option<(XVal, TNum, TFrameRef)>,
  //opt:  Option<XTuple>,
  step: Option<(MStep, TNum, TFrameRef)>,
  opt:  Option<(XVal, (MStep, TNum, TFrameRef))>,
}

#[derive(Clone, Default)]
struct TupMem {
  //rht:  Vec<u32>,
  nod:  Vec<Vec<usize>>,
  idx:  Vec<u32>,
  sub:  Vec<SNum>,
  off:  Vec<u32>,
  ary:  Vec<u32>,
  rel:  Vec<SNum>,
  pat:  Vec<SNum>,
  tup:  Vec<SNum>,
  spat: Vec<SNum>,
  stup: Vec<SNum>,
  swap: Vec<SNum>,
  swp2: Vec<SNum>,
  //swtu: Vec<SNum>,
}

#[derive(Clone)]
pub struct XMax1State {
  ref_tlb:  TNum,
  ref_env:  TFrameRef,
  maxdepth: u32,
  toplevel: bool,
  nul_buf:  Vec<SNum>,
  def_buf:  Vec<SNum>,
  cat_buf:  Vec<SNum>,
  //nulchk:   Option<TSnapshot>,
  chk:      TSnapshot,
  nulfix:   bool,
  //nulenv:   Option<TFrameRef>,
  ptr:      Option<usize>,
  //opt:      Option<XTuple>,
  //pullback: Vec<SNum>,
  pullback: BTreeMap<SNum, u32>,
  pulled_b: Option<SNum>,
  //pullback: XPullback,
  tmp:      TupMem,
  shared:   XMax1SharedRef,
}

/*impl XMax1State {
  pub fn default(ref_tlb: TNum, ref_env: TFrameRef, maxdepth: u32, toplevel: bool, shared: XMax1SharedRef) -> XMax1State {
    XMax1State{
      ref_tlb,
      ref_env,
      maxdepth,
      toplevel,
      nul_buf:  Vec::new(),
      def_buf:  Vec::new(),
      nulfix:   false,
      ptr:      None,
      //opt:      None,
      tmp:      TupMem::default(),
      shared,
    }
  }
}*/

/*#[derive(Clone)]
pub struct XMatState {
  pub tup:  Vec<SNum>,
  pub case: u32,
  pub work: BTreeMap<u32, (TNum, TFrameRef)>,
  pub done: BTreeMap<u32, (TNum, TFrameRef)>,
  pub ins:  BTreeMap<u32, (TNum, TFrameRef)>,
}*/

#[derive(Clone)]
pub struct XMatState {
  ref_tlb:  TNum,
  ref_env:  TFrameRef,
  //toplevel: bool,
  maxdepth: Option<u32>,
  tup:      Vec<SNum>,
  case_buf: Vec<SNum>,
  chk:      TSnapshot,
  ptr:      usize,
  // TODO
}

#[derive(Clone, Copy)]
pub enum XCase {
  S,
  N,
  I,
}

#[derive(Clone)]
pub enum XReg {
  Emp,
  Res,
  Ret(()),
  //Trp(XTrap),
  Val(XVal),
  //Val(XVal, TNum, TFrameRef),
  //Stp(XTuple),
  Max(TNum, TFrameRef, /*XPullback,*/ u32, bool),
  //Poly(XPolicy),
  Trc(MStep, TNum, TFrameRef),
  Sol(TNum, TFrameRef),
  Sol0(TNum, TFrameRef),
  Sol1(TNum, TFrameRef),
  Sub1(TNum, TFrameRef, usize),
  Sat,
  Par,
  Fix,
}

impl Default for XReg {
  fn default() -> XReg {
    XReg::Emp
  }
}

pub type XTuple = (MStep, XVal, TNum, TFrameRef);

/*#[derive(Clone)]
pub enum XPolicy {
  Max(TNum, TFrameRef, u32),
}*/

/*#[derive(Clone, Default)]
pub struct XPullback {
  //heap: Vec<(u32, SNum)>,
  heap: IHTreapMap<SNum, u32>,
}*/

pub enum XPMsg {
  Hlt,
  Blk,
  Sub(TNum, TFrameRef, TMemoryRef, TTup, EvalEvent),
  RetSubBlk,
}

pub enum XPRet {
  Sub(BTreeMap<TTup, (EvalEvent, u32, TStatus)>),
}

pub struct XPeerMach {
  tlb:  TNum,
  env:  TFrameRef,
  mem:  TMemoryRef,
}

pub fn _peer_step_sub(mach: XPeerMach, sub_tu: TTup, sub_ev: EvalEvent, sub_set: &mut BTreeMap<TTup, (EvalEvent, u32, TStatus)>, /*peer_rx: &ChanRx<XPMsg>, peer_tx: &ChanTx<XPRet>, peer: &ThreadPeer*/) {
  //println!("TRACE: _peer_step_sub");
  let mut nul_buf = Vec::with_capacity(mach.env.nul_count());
  nul_buf.resize(mach.env.nul_count(), 0);
  mach.env.fill_nul(&mut nul_buf);
  let mut next_env = mach.env;
  let next_mut = Rc::make_mut(&mut next_env);
  let next_tlb = next_mut.snapshot().next_glb();
  //let mut watch = WallclockStopwatch::default();
  let mut tmp = TupMem::default();
  let mut swap = SwapBuf::default();
  let mut swp2 = SwapBuf::default();
  //let mut swap = SwapBuf_::default();
  //let mut swp2 = SwapBuf_::default();
  //let mut swap = SwapTrace::default();
  //let mut swp2 = SwapTrace::default();
  let mut cap = WCapture::default();
  //let mut rx = WChannel::default();
  //let mut swapcache = BTreeSet::new();
  // TODO
  let mut checkpt = next_mut.snapshot();
  let mut tlb = checkpt.next_glb();
  let tu = sub_tu;
  //watch.lap();
  let rel_var = CVar(tu.rel.abs());
  match next_mut.fun_arity(rel_var) {
    None => panic!("bug: _peer_step_sub: arity violation"),
    Some((larity, rarity)) => {
      // FIXME(HACK)
      let mut tup = Vec::with_capacity(larity + rarity);
      tup.extend_from_slice(&tu.tup[ .. larity]);
      tup.resize(larity + rarity, 0);
      let mut ubtup = Vec::with_capacity(larity + rarity);
      ubtup.extend_from_slice(&tu.tup[ .. larity]);
      ubtup.resize(larity + rarity, s_ub());
      let mut scan = if tu.rel < 0 {
        next_mut.scan_neg(rel_var, &tup, &ubtup)
      } else if tu.rel > 0 {
        next_mut.scan_pos(rel_var, &tup, &ubtup)
      } else {
        unreachable!();
      };
      match scan.next_tup(&mut tup) {
        Hit(_) => if &tu.tup[ .. larity] == &tup[ .. larity] {
          return;
        } /*else {
          // TODO
          tup[ .. larity].copy_from_slice(&tu.tup[ .. larity]);
          for ra in 0 .. rarity {
            tup[larity + ra] = next_mut.shm._fresh_var(TAttr::Gen);
          }
        }
        End | Skip => {
          // TODO
          tup[ .. larity].copy_from_slice(&tu.tup[ .. larity]);
          for ra in 0 .. rarity {
            tup[larity + ra] = next_mut.shm._fresh_var(TAttr::Gen);
          }
        }*/
        _ => {}
      }
      let mut ub = 0;
      for i in larity .. larity + rarity {
        ub = max(ub, tu.tup[i]);
      }
      assert!(ub > 0);
      //println!("TRACE: _peer_step_sub: stage: rel={} tup={:?}", tu.rel, tup);
      swap.reset_swapbuf();
      swap.stage_fresh(tlb, ub);
      //swap.stage_tup(tlb, SwapEvent::Nul, tu.rel, &tup);
      swap.stage_tup(tlb, SwapEvent::Nul, tu.rel, &tu.tup);
    }
  }
  //swp2.reset_swapbuf();
  cap.reset();
  /*next_mut.swapfix_(tlb, &mut swap.buf, &mut swp2.buf, cap._ubptr(), &mut cap, false);*/
  //println!("TRACE: _peer_step_sub: init swap");
  //next_mut.patch_swap(tlb, &mut swap);
  next_mut.fix_swap(tlb, &mut swap, &mut swp2, cap._ubptr(), &mut cap, false);
  //println!("TRACE: _peer_step_sub:   done");
  let checkpt2 = next_mut.snapshot();
  if checkpt == checkpt2 {
    return;
  }
  loop {
    let xlb = cap._ubptr();
    swap.reset_swapbuf();
    FixEvalStats::tl_reset(tlb);
    for &nul_rec in nul_buf.iter() {
      next_mut.nul_eval_1(
          tlb,
          CVar(nul_rec),
          &mut tmp.nod,
          &mut tmp.idx,
          &mut tmp.sub,
          &mut tmp.off,
          &mut tmp.ary,
          &mut tmp.rel,
          &mut tmp.pat,
          &mut tmp.tup,
          &mut tmp.spat,
          &mut swap,
          &mut cap,
      );
    }
    /*let top_k = FixEvalStats::tl_dump(tlb, Some(2));
    if top_k[top_k.len() - 1].0 >= 30_000 {
      println!("WARNING: _peer_step_sub: icount: tlb={} top_k={:?}", tlb, top_k);
    }*/
    //swp2.reset_swapbuf();
    /*next_mut.swapfix_(tlb, &mut swap.buf, &mut swp2.buf, xlb, &mut cap, true);*/
    //println!("TRACE: _peer_step_sub: next swap");
    //next_mut.patch_swap(tlb, &mut swap);
    next_mut.fix_swap(tlb, &mut swap, &mut swp2, xlb, &mut cap, true);
    //println!("TRACE: _peer_step_sub:   done");
    let checkpt2 = next_mut.snapshot();
    if checkpt == checkpt2 {
      break;
    }
    tlb = checkpt.next_glb();
    checkpt = checkpt2;
  }
  let val = mach.mem.eval(&cap);
  let par_ct = next_mut.count_par();
  if par_ct > 0 {
    /*println!("TRACE: _peer_step_sub: par: ct={} rel={} tup={:?} val={}", par_ct, tu_.rel, tu_.tup, val);
    next_mut.trace_dump_par();*/
    sub_set.insert(tu, (sub_ev, val, TStatus::Par));
    return;
  }
  //let mut ts = Vec::new();
  //let status = match next_mut.terminal_(mach.tlb, &mut ts) {
  let status = match next_mut.terminal(mach.tlb) {
    None |
    Some(TStatus::Unsat) => {
      TStatus::Unsat
    }
    Some(TStatus::Sat) => {
      TStatus::Sat
    }
    Some(TStatus::Par) => {
      TStatus::Par
    }
  };
  sub_set.insert(tu, (sub_ev, val, status));
}

pub fn peer_step(peer_rx: ChanRx<XPMsg>, peer_tx: ChanTx<XPRet>, peer: ThreadPeer) {
  // TODO
  let back = ExponentialBackoff::default();
  let mut sub_set = BTreeMap::new();
  loop {
    match peer_rx.try_take() {
      Err(_) | Ok(None) => {
        back.snooze();
      }
      Ok(Some(msg)) => match &*msg {
        &XPMsg::Hlt => {
          return;
        }
        &XPMsg::Blk => {
          peer.block();
          back.reset();
        }
        &XPMsg::Sub(tlb, ref env, ref mem, ref tup, ref ev) => {
          let pmach = XPeerMach{tlb, env: env.clone(), mem: mem.clone()};
          _peer_step_sub(pmach, tup.clone(), ev.clone(), &mut sub_set);
          back.reset();
        }
        &XPMsg::RetSubBlk => {
          peer_tx.push(Box::new(XPRet::Sub(sub_set)));
          peer.unblock_host();
          peer.block();
          sub_set = BTreeMap::new();
          back.reset();
        }
      }
    }
  }
}

pub struct XPBulkMach {
  tg:   ThreadGroup,
  ch:   ChanTx<XPMsg>,
  rxs:  Vec<ChanBlockingRx<XPRet>>,
}

impl XPBulkMach {
  pub fn new() -> XPBulkMach {
    let cfg = RuntimeConfig::cached();
    let mut tg = if cfg.parallel <= 0 {
      ThreadGroup::new(1)
    } else {
      ThreadGroup::new_full_rank()
    };
    let (ch, peer_rx) = chan(8000);
    let mut rxs = Vec::with_capacity(tg.num_peers());
    for _ in 0 .. tg.num_peers() {
      ch.push(Box::new(XPMsg::Blk));
    }
    for _ in 0 .. tg.num_peers() {
      let peer_rx = peer_rx.clone();
      let (peer_tx, rx) = chan_blocking_rx(1000);
      tg.split(move |peer| {
        let peer_rx = peer_rx;
        let peer_tx = peer_tx;
        peer_step(peer_rx, peer_tx, peer);
      });
      rxs.push(rx);
    }
    XPBulkMach{
      tg,
      ch,
      rxs,
    }
  }
}

pub enum XPCtrl {
  Emp,
  Sol(TFrameRef),
  Sub(/*TFrameRef,*/ u32),
  Trc,
  Nar,
  Ter(/*TFrameRef,*/ TStatus),
}

/*pub type XPHistRef = Rc<XPHist>;

pub struct XPHist {
  sol:  TFrameRef,
  step: Vec<(TTup, TNum, TFrameRef)>,
}*/

pub type XPKontRef = Option<Rc<XPKont>>;

#[derive(Clone)]
pub enum XPKont {
  //Hlt,
  //Sol(TFrameRef, XPKontRef),
  //Sol(TFrameRef, Vec<TTup>, Option<TStatus>, XPKontRef),
  Sol(TFrameRef, Vec<(EvalEvent, TTup)>, Option<TStatus>, XPKontRef),
  //Trc(TFrameRef, Vec<(EvalEvent, TTup)>, Vec<TFrameRef>, XPKontRef),
  Trc(TFrameRef, Vec<(EvalEvent, TTup)>, Option<TStatus>, Vec<TraceEvent>, XPKontRef),
}

impl XPKont {
  pub fn into_ref(self) -> XPKontRef {
    Some(Rc::new(self))
  }
}

pub struct XPMach {
  //reg:  XReg,
  ctl:  XPCtrl,
  pub tlb:  TNum,
  pub env:  TFrameRef,
  mem:  TMemoryRef,
  //hst:  XPHist,
  knt:  XPKontRef,
  halt: bool,
  bulk: XPBulkMach,
}

impl Drop for XPMach {
  fn drop(&mut self) {
    //self.halt = true;
    for _ in 0 .. self.bulk.tg.num_peers() {
      self.bulk.ch.push(Box::new(XPMsg::Hlt));
    }
    self.bulk.tg.unblock_peers();
  }
}

impl XPMach {
  pub fn new() -> XPMach {
    XPMach{
      //reg:  XReg::default(),
      ctl:  XPCtrl::Emp,
      tlb:  0,
      env:  TFrameRef::default(),
      mem:  TMemoryRef::default(),
      knt:  None,
      halt: false,
      bulk: XPBulkMach::new(),
    }
  }

  pub fn halt(&self) -> bool {
    self.halt
  }

  pub fn terminal(&self) -> Option<TStatus> {
    match &self.ctl {
      &XPCtrl::Ter(status) => {
        Some(status)
      }
      _ => None
    }
  }

  pub fn solve(mut self, sol_env: TFrameRef) -> XPMach {
    self.ctl = XPCtrl::Sol(sol_env);
    self
  }

  pub fn trace(mut self) -> XPMach {
    self.ctl = XPCtrl::Trc;
    self
  }

  pub fn step(mut self, theory: &ITheoryEnv) -> XPMach {
    //match &self.reg {
    match &self.ctl {
      /*&XReg::Sat | &XReg::Par | &XReg::Fix => {
        // TODO
        if log_trace_vvv() {
          println!("TRACE: step2: Sat/Par/Fix");
        }
        if log_debug() {
          println!("DEBUG: step2: Sat/Par/Fix: halting...");
        }
        self.halt = true;
        for _ in 0 .. self.bulk.tg.num_peers() {
          self.bulk.ch.push(Box::new(XPMsg::Hlt));
        }
        self.bulk.tg.unblock_peers();
        self
      }*/
      &XPCtrl::Emp => {
        panic!("bug: XPMach::step: Emp");
      }
      //&XReg::Sol0(ref_tlb, ref ref_env) => {
      &XPCtrl::Sol(ref ref_env) => {
        // TODO
        if log_trace_vvv() {
          println!("TRACE: XPMach::step: Sol");
        }
        self.tlb = 1;
        self.env = ref_env.clone();
        let mut nul_buf = Vec::with_capacity(self.env.nul_count());
        nul_buf.resize(self.env.nul_count(), 0);
        self.env.fill_nul(&mut nul_buf);
        let mut next_env = self.env.clone();
        let next_mut = Rc::make_mut(&mut next_env);
        if log_debug() {
          println!("DEBUG: XPMach::step: Sol: tlb={}", self.tlb);
        }
        let mut tmp = TupMem::default();
        //let mut swap = SwapBuf::default();
        //let mut swp2 = SwapBuf::default();
        let mut swap = SwapBuf_::default();
        let mut swp2 = SwapBuf_::default();
        //let mut swap = SwapTrace::default();
        //let mut swp2 = SwapTrace::default();
        let mut cap = WCapture::default();
        let mut checkpt = next_mut.snapshot();
        let mut tlb = 1;
        loop {
          if log_trace() {
            println!("TRACE: XPMach::step: Sol: begin nul eval...");
          }
          /*cap.reset();*/
          /*if checkpt.lub() != tlb {
            panic!("bug: Sol1: checkpt lub={} tlb={}", checkpt.lub(), tlb);
          }*/
          let xlb = cap._ubptr();
          swap.reset_swapbuf();
          for &nul_rec in nul_buf.iter() {
            next_mut.nul_eval_1(
                tlb,
                CVar(nul_rec),
                &mut tmp.nod,
                &mut tmp.idx,
                &mut tmp.sub,
                &mut tmp.off,
                &mut tmp.ary,
                &mut tmp.rel,
                &mut tmp.pat,
                &mut tmp.tup,
                &mut tmp.spat,
                &mut swap,
                &mut cap,
            );
          }
          if log_trace() {
            println!("TRACE: XPMach::step: Sol:   done");
          }
          if log_trace() {
            println!("TRACE: XPMach::step: Sol: begin swapfix...");
          }
          //swp2.reset_swapbuf();
          /*next_mut.swapfix_(tlb, &mut swap.buf, &mut swp2.buf, xlb, &mut cap, true);*/
          //next_mut.patch_swap(tlb, &mut swap);
          next_mut.fix_swap(tlb, &mut swap, &mut swp2, xlb, &mut cap, true);
          let mem_mut = Rc::make_mut(&mut self.mem);
          mem_mut.backup(&cap);
          drop(mem_mut);
          if log_trace() {
            println!("TRACE: XPMach::step: Sol:   done");
          }
          let checkpt2 = next_mut.snapshot();
          if checkpt == checkpt2 {
            if log_trace_vvv() {
              println!("TRACE: XPMach::step: Sol: nul fix");
            }
            // TODO
            break;
          }
          tlb = checkpt.next_glb();
          checkpt = checkpt2;
        }
        let par_ct = next_mut.count_par();
        if par_ct > 0 {
          println!("TRACE: XPMach::step: Sol: par: ct={}", par_ct);
          next_mut.trace_dump_par();
          //self.reg = XReg::Par;
          self.ctl = XPCtrl::Ter(/*next_env.clone(),*/ TStatus::Par);
          self.tlb = 1;
          self.env = next_env;
          return self;
        }
        match next_mut.terminal(self.tlb) {
          None |
          Some(TStatus::Unsat) => {
            if log_debug() {
              println!("DEBUG: XPMach::step: Sol: unsat");
            }
          }
          Some(TStatus::Sat) => {
            // TODO
            if log_debug() {
              println!("DEBUG: XPMach::step: Sol: sat");
            }
            //self.reg = XReg::Sat;
            let ref_env = ref_env.clone();
            self.ctl = XPCtrl::Ter(/*next_env.clone(),*/ TStatus::Sat);
            self.tlb = 1;
            self.env = next_env;
            self.knt = XPKont::Sol(ref_env, Vec::new(), None, self.knt.take()).into_ref();
            return self;
          }
          Some(TStatus::Par) => {
            // TODO
            if log_debug() {
              println!("DEBUG: XPMach::step: Sol: par");
            }
            //self.reg = XReg::Par;
            let ref_env = ref_env.clone();
            self.ctl = XPCtrl::Ter(/*next_env.clone(),*/ TStatus::Par);
            self.tlb = 1;
            self.env = next_env;
            self.knt = XPKont::Sol(ref_env, Vec::new(), None, self.knt.take()).into_ref();
            return self;
          }
        }
        drop(next_mut);
        // TODO
        //self.reg = XReg::Sub1(ref_tlb, ref_env.clone(), 1);
        let ref_env = ref_env.clone();
        self.ctl = XPCtrl::Sub(/*ref_env.clone(),*/ 1);
        self.tlb = 1;
        self.env = next_env;
        self.knt = XPKont::Sol(ref_env, Vec::new(), None, self.knt.take()).into_ref();
        self
      }
      //&XReg::Sub1(ref_tlb, ref ref_env, sub_depth) => {
      &XPCtrl::Sub(/*ref ref_env,*/ sub_depth) => {
        // TODO
        if log_trace_vvv() {
          println!("TRACE: XPMach::step: Sub");
        }
        let mut nul_buf = Vec::with_capacity(self.env.nul_count());
        let mut def_buf = Vec::with_capacity(self.env.def_count());
        nul_buf.resize(self.env.nul_count(), 0);
        def_buf.resize(self.env.def_count(), 0);
        self.env.fill_nul(&mut nul_buf);
        self.env.fill_def(&mut def_buf);
        let mut next_env = self.env.clone();
        let next_mut = Rc::make_mut(&mut next_env);
        let next_tlb = next_mut.snapshot().next_glb();
        if log_debug() {
          println!("DEBUG: XPMach::step: Sub: tlb={} next tlb={}", self.tlb, next_tlb);
        }
        let mut watch = WallclockStopwatch::default();
        let mut tmp = TupMem::default();
        //let mut swap = SwapBuf::default();
        //let mut swp2 = SwapBuf::default();
        let mut swap = SwapBuf_::default();
        let mut swp2 = SwapBuf_::default();
        //let mut swap = SwapTrace::default();
        //let mut swp2 = SwapTrace::default();
        let mut cap = WCapture::default();
        swap.reset_swapbuf();
        for &def_rec in def_buf.iter() {
          next_mut.def_eval_1(
              1,
              CVar(def_rec),
              &mut tmp.nod,
              &mut tmp.idx,
              &mut tmp.sub,
              &mut tmp.off,
              &mut tmp.ary,
              &mut tmp.rel,
              &mut tmp.pat,
              &mut tmp.tup,
              &mut tmp.spat,
              &mut swap,
              &mut cap,
          );
        }
        drop(next_mut);
        /*if log_debug() {
          println!("DEBUG: step2: Sub1: def swap: buf len={}", swap.buf.len());
        }*/
        /*let mut tups = BTreeMap::new();
        let mut o = 0;
        while o < swap.buf.len() {
          let rec_var = CVar(swap.buf[o]);
          let rel = swap.buf[o + 1];
          let rel_var = CVar(rel.abs());
          let a = self.env.rel_arity(rel_var);
          o += 2;
          let tu = TTup::from(rel, &swap.buf[o .. o + a]);
          match tups.get_mut(&tu) {
            None => {
              let mut recs = IHTreapSet::default();
              recs.insert(rec_var);
              tups.insert(tu, recs);
            }
            Some(recs) => {
              recs.insert(rec_var);
            }
          }
          o += a;
        }*/
        let tups = swap._etups_(&*self.env);
        if log_debug() {
          println!("DEBUG: step2: Sub1: def swap: uniq len={}", tups.len());
        }
        let def_delay = watch.lap();
        /*if log_debug() {
          println!("DEBUG: step2: Sub1: def swap: delay={:.06}", def_delay.as_scalar());
        }*/
        let mut cap = WCapture::default();
        let mut rx = WChannel::default();
        let mut swapcache = BTreeMap::new();
        // TODO
        //for (tu, _) in tups.iter() {
        for (tu, ev) in tups.iter() {
          //watch.lap();
          let mut next_env = self.env.clone();
          let next_mut = Rc::make_mut(&mut next_env);
          /*swap.reset_swapbuf();
          swap.buf.push(0);
          swap.buf.push(tu.rel);*/
          let rel_var = CVar(tu.rel.abs());
          match next_mut.fun_arity(rel_var) {
            None => panic!("bug: step2: Sub1: arity violation"),
            Some((larity, rarity)) => {
              // FIXME(HACK)
              let mut tup = Vec::with_capacity(larity + rarity);
              tup.extend_from_slice(&tu.tup[ .. larity]);
              tup.resize(larity + rarity, 0);
              let mut ubtup = Vec::with_capacity(larity + rarity);
              ubtup.extend_from_slice(&tu.tup[ .. larity]);
              ubtup.resize(larity + rarity, s_ub());
              let mut scan = if tu.rel < 0 {
                next_mut.scan_neg(rel_var, &tup, &ubtup)
              } else if tu.rel > 0 {
                next_mut.scan_pos(rel_var, &tup, &ubtup)
              } else {
                unreachable!();
              };
              match scan.next_tup(&mut tup) {
                Hit(_) => if &tu.tup[ .. larity] == &tup[ .. larity] {
                  continue;
                } /*else {
                  // TODO
                  //swap.buf.extend_from_slice(&tu.tup[ .. larity]);
                  tup[ .. larity].copy_from_slice(&tu.tup[ .. larity]);
                  for ra in 0 .. rarity {
                    //let x = next_mut.shm.cc.fresh(TAttr::Gen, &mut next_mut.shm.univ, &mut next_mut.shm.clk);
                    //swap.buf.push(x.0);
                    tup[larity + ra] = next_mut.shm._fresh_var(TAttr::Gen);
                  }
                }
                End | Skip => {
                  // TODO
                  //swap.buf.extend_from_slice(&tu.tup[ .. larity]);
                  tup[ .. larity].copy_from_slice(&tu.tup[ .. larity]);
                  for ra in 0 .. rarity {
                    //let x = next_mut.shm.cc.fresh(TAttr::Gen, &mut next_mut.shm.univ, &mut next_mut.shm.clk);
                    //swap.buf.push(x.0);
                    tup[larity + ra] = next_mut.shm._fresh_var(TAttr::Gen);
                  }
                }*/
                _ => {}
              }
              let mut ub = 0;
              for i in larity .. larity + rarity {
                ub = max(ub, tu.tup[i]);
              }
              assert!(ub > 0);
              //let qtu = TTup{rel: tu.rel, tup};
              let qtu = TTup{rel: tu.rel, tup: tu.tup.clone()};
              if swapcache.contains_key(&qtu) {
                continue;
              }
              let checkpt = next_mut.snapshot();
              let tlb = checkpt.next_glb();
              swap.reset_swapbuf();
              swap.stage_fresh(tlb, ub);
              swap.stage_tup(tlb, SwapEvent::Eva(ev.rec, &ev.sub, &[], /*&ev.off, &ev.ary, &ev.rel, &ev.tup*/), qtu.rel, &qtu.tup);
              swapcache.insert(qtu, ev.clone());
            }
          }
        }
        let cache_delay = watch.lap();
        //for swaptup in swapcache.iter() {
        for (qtu, ev) in swapcache.iter() {
          //let qtu = TTup{rel: swaptup[0], tup: swaptup[1 .. ].to_owned()};
          self.bulk.ch.push(Box::new(XPMsg::Sub(self.tlb, self.env.clone(), self.mem.clone(), qtu.clone(), ev.clone())));
        }
        self.bulk.tg.unblock_peers();
        for _ in 0 .. self.bulk.tg.num_peers() {
          self.bulk.ch.push(Box::new(XPMsg::RetSubBlk));
        }
        let mut sub_set = BTreeMap::new();
        for rank in 0 .. self.bulk.tg.num_peers() {
          match &*self.bulk.rxs[rank].take() {
            &XPRet::Sub(ref sub_set2) => {
              for (k, v) in sub_set2.iter() {
                sub_set.insert(k.clone(), v.clone());
              }
            }
          }
        }
        let work_delay = watch.lap();
        for (qtu, &(ref ev, val, status)) in sub_set.iter() {
          match status {
            TStatus::Unsat => {}
            TStatus::Sat => {
              // FIXME
              /*if log_trace_vvv() {
                println!("TRACE: step2: Sub1: sat");
              } else */
              if log_debug() {
                //println!("DEBUG: step2: Sub1: sat: rel={} tup={:?} val={} ts={:?}", qtu.rel, qtu.tup, val, ts);
                println!("DEBUG: XPMach::step: Sub: sat: rel={} tup={:?} val={}", qtu.rel, qtu.tup, val);
                println!("DEBUG: XPMach::step: Sub: sat: pretty={:?}", theory.pretty_print_def(qtu.rel, &qtu.tup));
                println!("DEBUG: XPMach::step: Sub: timings:  def={:.06} cache={:.06} work={:.06}",
                    def_delay.as_scalar(),
                    cache_delay.as_scalar(),
                    work_delay.as_scalar(),
                );
              }
              // TODO
              //self.reg = XReg::Trc(MStep::Sat, self.tlb, self.env.clone());
              //self.reg = XReg::Trc(MStep::Sat, ref_tlb, ref_env.clone());
              //self.reg = XReg::Sat;
              self.ctl = XPCtrl::Ter(/*next_env.clone(),*/ TStatus::Sat);
              self.tlb = next_tlb;
              self.env = next_env;
              //self.reg = XReg::Trc(MStep::Sat, tlb, next_env);
              match self.knt.as_mut().map(|k| Rc::make_mut(k)) {
                Some(&mut XPKont::Sol(_, ref mut tups, ref mut status, _)) => {
                  tups.push((ev.clone(), qtu.clone()));
                  *status = Some(TStatus::Sat);
                }
                _ => panic!("bug: XPMach::step: Sub: expected Sol knt")
              }
              return self;
            }
            TStatus::Par => {
              // FIXME
              if log_debug() {
                println!("DEBUG: XPMach::step: Sub: par: rel={} tup={:?} val={}", qtu.rel, qtu.tup, val);
                println!("DEBUG: XPMach::step: Sub: timings:  def={:.06} cache={:.06} work={:.06}",
                    def_delay.as_scalar(),
                    cache_delay.as_scalar(),
                    work_delay.as_scalar(),
                );
              }
              // TODO
              //self.reg = XReg::Trc(MStep::Par, self.tlb, self.env.clone());
              //self.reg = XReg::Par;
              self.ctl = XPCtrl::Ter(/*next_env.clone(),*/ TStatus::Par);
              self.tlb = next_tlb;
              self.env = next_env;
              //self.reg = XReg::Trc(MStep::Par, tlb, next_env);
              match self.knt.as_mut().map(|k| Rc::make_mut(k)) {
                Some(&mut XPKont::Sol(_, ref mut tups, ref mut status, _)) => {
                  tups.push((ev.clone(), qtu.clone()));
                  *status = Some(TStatus::Par);
                }
                _ => panic!("bug: XPMach::step: Sub: expected Sol knt")
              }
              return self;
            }
          }
          rx.cache(qtu.clone(), ev, val);
        }
        if log_debug() {
          println!("DEBUG: XPMach::step: Sub: retrieve: cache len={}", swapcache.len());
          println!("DEBUG: XPMach::step: Sub: retrieve: rx len={}", rx.len());
        }
        if rx.is_empty() {
          // TODO
          if log_debug() {
            println!("DEBUG: XPMach::step: Sub: fix");
          }
          //self.reg = XReg::Fix;
          self.ctl = XPCtrl::Ter(/*self.env.clone(),*/ TStatus::Unsat);
          //self.reg = XReg::Trc(MStep::Fix, self.tlb, self.env.clone());
          match self.knt.as_mut().map(|k| Rc::make_mut(k)) {
            Some(&mut XPKont::Sol(_, ref mut tups, ref mut status, _)) => {
              *status = Some(TStatus::Unsat);
            }
            _ => panic!("bug: XPMach::step: Sub: expected Sol knt")
          }
          return self;
        }
        let (rxtu, rxev) = {
          let (rxtu, rxev, rx_v, rx_idx, rx_len) = TL_RNG.with(|rng| {
            let mut rng = rng.borrow_mut();
            rx.retrieve(&mut *rng)
            //rx.retrieve2(&mut *rng)
          });
          if log_debug() {
            println!("DEBUG: XPMach::step: Sub: retrieve: rel={} tup={:?} val={} idx={} len={}",
                rxtu.rel, rxtu.tup, rx_v, rx_idx, rx_len);
            /*
            println!("DEBUG: XPMach::step: Sub: retrieve: rel={} ({:?}) tup={:?} val={} idx={} len={}",
                rxtu.rel, theory.rev_lookup_top_level_num(rxtu.rel).unwrap(),
                rxtu.tup, rx_v, rx_idx, rx_len);
            */
            println!("DEBUG: XPMach::step: Sub: retrieve: pretty={:?}",
                theory.pretty_print_def(rxtu.rel, &rxtu.tup));
          }
          (rxtu, rxev)
        };
        let rx_delay = watch.lap();
        let mut next_env = self.env.clone();
        let next_mut = Rc::make_mut(&mut next_env);
        let mut checkpt = next_mut.snapshot();
        let mut tlb = checkpt.next_glb();
        let rel_var = if rxtu.rel < 0 {
          CVar(-rxtu.rel)
        } else {
          CVar(rxtu.rel)
        };
        match next_mut.fun_arity(rel_var) {
          None => panic!("bug: XPMach::step: Sub: arity violation"),
          Some((larity, rarity)) => {
            // FIXME(HACK)
            let mut tup = Vec::with_capacity(larity + rarity);
            tup.extend_from_slice(&rxtu.tup[ .. larity]);
            tup.resize(larity + rarity, 0);
            let mut ubtup = Vec::with_capacity(larity + rarity);
            ubtup.extend_from_slice(&rxtu.tup[ .. larity]);
            ubtup.resize(larity + rarity, s_ub());
            let mut scan = if rxtu.rel < 0 {
              next_mut.scan_neg(rel_var, &tup, &ubtup)
            } else if rxtu.rel > 0 {
              next_mut.scan_pos(rel_var, &tup, &ubtup)
            } else {
              unreachable!();
            };
            match scan.next_tup(&mut tup) {
              Hit(_) => if &rxtu.tup[ .. larity] == &tup[ .. larity] {
                panic!("bug: XPMach::step: Sub: stale def");
              } /*else {
                // TODO
                //swap.buf.extend_from_slice(&rxtu.tup[ .. larity]);
                tup[ .. larity].copy_from_slice(&rxtu.tup[ .. larity]);
                for ra in 0 .. rarity {
                  //let x = next_mut.shm.cc.fresh(TAttr::Gen, &mut next_mut.shm.univ, &mut next_mut.shm.clk);
                  //swap.buf.push(x.0);
                  tup[larity + ra] = next_mut.shm._fresh_var(TAttr::Gen);
                }
              }
              End | Skip => {
                // TODO
                //swap.buf.extend_from_slice(&rxtu.tup[ .. larity]);
                tup[ .. larity].copy_from_slice(&rxtu.tup[ .. larity]);
                for ra in 0 .. rarity {
                  //let x = next_mut.shm.cc.fresh(TAttr::Gen, &mut next_mut.shm.univ, &mut next_mut.shm.clk);
                  //swap.buf.push(x.0);
                  tup[larity + ra] = next_mut.shm._fresh_var(TAttr::Gen);
                }
              }*/
              _ => {}
            }
            let mut ub = 0;
            for i in larity .. larity + rarity {
              ub = max(ub, rxtu.tup[i]);
            }
            assert!(ub > 0);
            swap.reset_swapbuf();
            swap.stage_fresh(tlb, ub);
            //swap.stage_tup(tlb, SwapEvent::Nul, rxtu.rel, &tup);
            //swap.stage_tup(tlb, SwapEvent::Eva(rxev.rec, &rxev.sub, &[], /*&rxev.off, &rxev.ary, &rxev.rel, &rxev.tup*/), rxtu.rel, &tup);
            swap.stage_tup(tlb, SwapEvent::Eva(rxev.rec, &rxev.sub, &[], /*&rxev.off, &rxev.ary, &rxev.rel, &rxev.tup*/), rxtu.rel, &rxtu.tup);
            if log_debug() {
              println!("DEBUG: XPMach::step: Sub: staged:   rel={} tup={:?}",
                  rxtu.rel, tup);
            }
          }
        }
        /*if log_debug() {
          println!("DEBUG: XPMach::step: Sub: actual:   rel={} tup={:?}",
              swap.buf[1], &swap.buf[2 .. ]);
        }*/
        //swp2.reset_swapbuf();
        cap.reset();
        /*next_mut.swapfix_(tlb, &mut swap.buf, &mut swp2.buf, cap._ubptr(), &mut cap, false);*/
        //next_mut.patch_swap(tlb, &mut swap);
        next_mut.fix_swap(tlb, &mut swap, &mut swp2, cap._ubptr(), &mut cap, false);
        let checkpt2 = next_mut.snapshot();
        if checkpt == checkpt2 {
          panic!("bug: XPMach::step: Sub: unexpected fix");
        }
        loop {
          let xlb = cap._ubptr();
          swap.reset_swapbuf();
          for &nul_rec in nul_buf.iter() {
            next_mut.nul_eval_1(
                tlb,
                CVar(nul_rec),
                &mut tmp.nod,
                &mut tmp.idx,
                &mut tmp.sub,
                &mut tmp.off,
                &mut tmp.ary,
                &mut tmp.rel,
                &mut tmp.pat,
                &mut tmp.tup,
                &mut tmp.spat,
                &mut swap,
                &mut cap,
            );
          }
          //swp2.reset_swapbuf();
          /*next_mut.swapfix_(tlb, &mut swap.buf, &mut swp2.buf, xlb, &mut cap, true);*/
          //next_mut.patch_swap(tlb, &mut swap);
          next_mut.fix_swap(tlb, &mut swap, &mut swp2, xlb, &mut cap, true);
          let checkpt2 = next_mut.snapshot();
          if checkpt == checkpt2 {
            break;
          }
          tlb = checkpt.next_glb();
          checkpt = checkpt2;
        }
        let mem_mut = Rc::make_mut(&mut self.mem);
        mem_mut.backup(&cap);
        drop(mem_mut);
        drop(next_mut);
        let step_delay = watch.lap();
        if log_debug() {
          println!("DEBUG: XPMach::step: Sub: timings:  def={:.06} cache={:.06} work={:.06} rx={:.06} step={:.06}",
              def_delay.as_scalar(),
              cache_delay.as_scalar(),
              work_delay.as_scalar(),
              rx_delay.as_scalar(),
              step_delay.as_scalar(),
          );
        }
        //self.reg = XReg::Sub1(ref_tlb, ref_env.clone(), sub_depth + 1);
        self.ctl = XPCtrl::Sub(/*ref_env.clone(),*/ sub_depth + 1);
        self.tlb = next_tlb;
        self.env = next_env;
        match self.knt.as_mut().map(|k| Rc::make_mut(k)) {
          Some(&mut XPKont::Sol(_, ref mut tups, ref status, _)) => {
            tups.push((rxev.clone(), rxtu.clone()));
            match status {
              &None => {}
              &Some(status) => {
                println!("bug: XPMach::step: Sub: overcomplete status={:?}", status);
              }
            }
          }
          _ => panic!("bug: XPMach::step: Sub: expected Sol knt")
        }
        self
      }
      &XPCtrl::Trc => {
        match self.knt.as_mut().map(|k| Rc::make_mut(k)) {
          Some(&mut XPKont::Sol(ref mut init_env, ref steps, status, ..)) => {
            // TODO
            /*if step_envs.len() > steps.len() {
            } else if step_envs.len() == steps.len() {
              self.ctl = XPCtrl::TrcBwd;
            }*/
            self.tlb = 1;
            self.env = init_env.clone();
            let mut nul_buf = Vec::with_capacity(self.env.nul_count());
            let mut def_buf = Vec::with_capacity(self.env.def_count());
            nul_buf.resize(self.env.nul_count(), 0);
            def_buf.resize(self.env.def_count(), 0);
            self.env.fill_nul(&mut nul_buf);
            self.env.fill_def(&mut def_buf);
            let mut env = self.env.clone();
            let env_mut = Rc::make_mut(&mut env);
            let mut tlb = 1;
            let mut tmp = TupMem::default();
            let mut cap = DummyCapture::default();
            let mut checkpt = env_mut.snapshot();
            let mut swap = SwapTrace::default();
            let mut swp2 = SwapTrace::default();
            loop {
              let xlb = cap._ubptr();
              swap.reset_swapbuf();
              for &nul_rec in nul_buf.iter() {
                env_mut.nul_eval_1(
                    tlb,
                    CVar(nul_rec),
                    &mut tmp.nod,
                    &mut tmp.idx,
                    &mut tmp.sub,
                    &mut tmp.off,
                    &mut tmp.ary,
                    &mut tmp.rel,
                    &mut tmp.pat,
                    &mut tmp.tup,
                    &mut tmp.spat,
                    &mut swap,
                    &mut cap,
                );
              }
              env_mut.fix_swap(tlb, &mut swap, &mut swp2, xlb, &mut cap, true);
              let checkpt2 = env_mut.snapshot();
              if checkpt == checkpt2 {
                break;
              }
              tlb = checkpt.next_glb();
              checkpt = checkpt2;
            }
            for (i, &(ref qev, ref qtu)) in steps.iter().enumerate() {
              let (larity, rarity) = env_mut.rel_arity2(CVar(qtu.rel.abs()));
              let (rec_larity, rec_rarity) = env_mut.rec_arity(qev.rec);
              print!("DEBUG: XPMach::step: Trc: step: idx={} rec={} lrec={} rrec={} pretty:",
                  i,
                  qev.rec.lower(), rec_larity, rec_rarity,
              );
              for r in 0 .. rec_larity {
                let rel = qev.rel[r];
                let o = qev.off[r] as usize;
                let o2 = qev.off[r+1] as usize;
                print!(" {}", theory.pretty_print_tup(rel, &qev.tup[o .. o2]));
                if r+1 < rec_larity {
                  print!(",");
                }
              }
              print!(" -:");
              for r in rec_larity .. rec_larity + rec_rarity {
                let rel = qev.rel[r];
                let o = qev.off[r] as usize;
                let o2 = qev.off[r+1] as usize;
                print!(" {}", theory.pretty_print_tup(rel, &qev.tup[o .. o2]));
                if r+1 < rec_larity + rec_rarity {
                  print!(",");
                }
              }
              println!();
              println!("DEBUG: XPMach::step: Trc: step:     rel={} ltup={:?} rtup={:?} pretty={:?}",
                  qtu.rel, &qtu.tup[ .. larity], &qtu.tup[larity .. ],
                  theory.pretty_print_def2(qtu.rel, &qtu.tup[ .. larity], &qtu.tup[larity .. ]));
              /*for ra in 0 .. rarity {
                assert_eq!(qtu.tup[larity + ra], env_mut.shm._fresh_var(TAttr::Gen));
              }*/
              let mut ub = 0;
              for i in larity .. larity + rarity {
                ub = max(ub, qtu.tup[i]);
              }
              assert!(ub > 0);
              swap.reset_swapbuf();
              swap.stage_fresh(tlb, ub);
              swap.stage_tup(tlb, SwapEvent::Eva(qev.rec, &qev.sub, &[], /*&qev.off, &qev.ary, &qev.rel, &qev.tup*/), qtu.rel, &qtu.tup);
              cap.reset();
              env_mut.fix_swap(tlb, &mut swap, &mut swp2, cap._ubptr(), &mut cap, false);
              let checkpt2 = env_mut.snapshot();
              if checkpt == checkpt2 {
                panic!("bug: XPMach::step: Trc: unexpected fix");
              }
              loop {
                let xlb = cap._ubptr();
                swap.reset_swapbuf();
                for &nul_rec in nul_buf.iter() {
                  env_mut.nul_eval_1(
                      tlb,
                      CVar(nul_rec),
                      &mut tmp.nod,
                      &mut tmp.idx,
                      &mut tmp.sub,
                      &mut tmp.off,
                      &mut tmp.ary,
                      &mut tmp.rel,
                      &mut tmp.pat,
                      &mut tmp.tup,
                      &mut tmp.spat,
                      &mut swap,
                      &mut cap,
                  );
                }
                env_mut.fix_swap(tlb, &mut swap, &mut swp2, xlb, &mut cap, true);
                let checkpt2 = env_mut.snapshot();
                if checkpt == checkpt2 {
                  break;
                }
                tlb = checkpt.next_glb();
                checkpt = checkpt2;
              }
            }
            let mut prop_ts = Vec::new();
            let mut prop_rel = Vec::new();
            let mut prop_pat = Vec::new();
            let mut prop_tup = Vec::new();
            match env_mut.prop_eval_1(0, &mut prop_ts, &mut prop_rel, &mut prop_pat, &mut prop_tup) {
              Some(TStatus::Sat) => {}
              status => {
                panic!("bug: XPMach::step: Trc: unexpected status={:?}", status);
              }
            }
            let mut prop_tg = Vec::with_capacity(prop_rel.len());
            let mut uprop_tg = Vec::with_capacity(prop_rel.len());
            let mut o = 0;
            for r in 0 .. prop_rel.len() {
              let a = env_mut.rel_arity(CVar(prop_rel[r].abs()));
              let tu = TTup{rel: prop_rel[r], tup: prop_tup[o .. o + a].to_owned()};
              let mut u_tu = tu.clone();
              for i in 0 .. tu.tup.len() {
                let (_, x) = env_mut.shm.cc.find(CVar(tu.tup[i]));
                u_tu.tup[i] = x.0;
              }
              prop_tg.push((prop_ts[r], tu));
              uprop_tg.push((prop_ts[r], u_tu));
              o += a;
            }
            println!("DEBUG: XPMach::step: Trc: tg={:?}", prop_tg);
            println!("DEBUG: XPMach::step: Trc: u_tg={:?}", uprop_tg);
            for &(t, ref tu) in prop_tg.iter() {
              println!("DEBUG: XPMach::step: Trc: pretty tg[{:?}]={:?}",
                  t, theory.pretty_print_tup(tu.rel, &tu.tup));
            }
            for &(t, ref tu) in uprop_tg.iter() {
              println!("DEBUG: XPMach::step: Trc: pretty u_tg[{:?}]={:?}",
                  t, theory.pretty_print_tup(tu.rel, &tu.tup));
            }
            // TODO
            let mut trace_buf = Vec::new();
            // FIXME: traceback needs rewrite.
            /*swap._gen_trace(&prop_tg, &mut trace_buf);
            println!("DEBUG: XPMach::step: Trc: dump trace buf...");
            for (i, item) in trace_buf.iter().rev().enumerate() {
              println!("DEBUG: XPMach::step: Trc:   idx={} {:?}", i, item);
            }*/
            // TODO
            self.ctl = XPCtrl::Ter(TStatus::Sat);
            self.knt = XPKont::Trc(init_env.clone(), steps.clone(), status, trace_buf, self.knt.take()).into_ref();
            self
          }
          _ => panic!("bug: XPMach::step: Trc: expected Sol knt")
        }
      }
      &XPCtrl::Nar => {
        //match self.knt.as_mut().map(|k| Rc::make_mut(k)) {
        match self.knt.as_ref().map(|k| &**k) {
          Some(&XPKont::Trc(ref init_env, ref steps, status, ref trace_buf, ..)) => {
            // TODO
            //unimplemented!();
            match status {
              None | Some(TStatus::Unsat) => {
                self.ctl = XPCtrl::Ter(TStatus::Unsat);
              }
              Some(TStatus::Sat) => {
                self.ctl = XPCtrl::Ter(TStatus::Sat);
              }
              Some(TStatus::Par) => {
                self.ctl = XPCtrl::Ter(TStatus::Par);
              }
            }
            self
          }
          _ => panic!("bug: XPMach::step: Nar: expected Trc knt")
        }
      }
      &XPCtrl::Ter(/*ref _env,*/ status) => {
        if log_debug() {
          println!("TRACE: XPMach::step: Ter: {:?}", status);
        }
        /*if log_debug() {
          println!("DEBUG: XPMach::step: Ter: halting... status={:?}", status);
        }
        self.halt = true;
        for _ in 0 .. self.bulk.tg.num_peers() {
          self.bulk.ch.push(Box::new(XPMsg::Hlt));
        }
        self.bulk.tg.unblock_peers();*/
        self
      }
      _ => panic!("bug: XPMach::step: unimpl ctrl")
    }
  }
}

#[derive(Clone)]
pub struct XMach_ {
  //tape: Vec<MStep>,
  //maxd: u32,
  pub cfg:  XMachCfg,
  pub tlb:  TNum,
  pub tlb2: TNum,
  pub env:  TFrameRef,
  kont: XKont_,
  reg:  XReg,
}

impl Default for XMach_ {
  fn default() -> XMach_ {
    XMach_{
      //maxd: DEFAULT_MAXDEPTH,
      cfg:  XMachCfg::default(),
      tlb:  0,
      tlb2: 0,
      env:  TFrameRef::default(),
      kont: XKont_::default(),
      reg:  XReg::default(),
    }
  }
}

impl XMach_ {
  pub fn new_with_maxdepth(maxdepth: u32) -> XMach_ {
    XMach_{
      //maxd: maxdepth,
      cfg:  XMachCfg{maxdepth},
      tlb:  0,
      tlb2: 0,
      env:  TFrameRef::default(),
      kont: XKont_::default(),
      reg:  XReg::default(),
    }
  }

  pub fn new_with_config(cfg: XMachCfg) -> XMach_ {
    XMach_{
      cfg,
      tlb:  0,
      tlb2: 0,
      env:  TFrameRef::default(),
      kont: XKont_::default(),
      reg:  XReg::default(),
    }
  }

  pub fn halt(&self) -> bool {
    self.kont.halt()
  }
}

pub trait MTrace {
  fn append(&mut self, step: &MStep, tlb: TNum, env: &TFrameRef);
}

#[derive(Clone, Copy, Default)]
pub struct MVoidTape {}

impl MTrace for MVoidTape {
  fn append(&mut self, _step: &MStep, _tlb: TNum, _env: &TFrameRef) {
  }
}

/*#[derive(Clone, Default)]
pub struct MBufferTape {
  buf:  Vec<(MStep, TNum, TFrameRef)>,
}*/

#[derive(Clone, Default)]
pub struct MDigestTape {
  buf:  Vec<MStep>,
}

impl MTrace for MDigestTape {
  fn append(&mut self, step: &MStep, _tlb: TNum, _env: &TFrameRef) {
    self.buf.push(step.clone());
  }
}

impl MDigestTape {
  pub fn len(&self) -> usize {
    self.buf.len()
  }

  pub fn debuglaststep(&self) -> MDebugStep {
    if self.buf.is_empty() {
      panic!("bug");
    }
    self.buf[self.buf.len() - 1].debugstep()
  }

  pub fn debugtrace(&self) -> Vec<MDebugStep> {
    self.buf.iter().map(|s| s.debugstep()).collect()
  }
}

#[derive(Clone, Default)]
pub struct MDebugDigestTape {
  buf:  Vec<(MStep, TNum, (u64, u64))>,
}

impl MTrace for MDebugDigestTape {
  fn append(&mut self, step: &MStep, tlb: TNum, env: &TFrameRef) {
    self.buf.push((step.clone(), tlb, env.tup_size()));
  }
}

impl MDebugDigestTape {
  pub fn debugtrace(&self) -> Vec<(MDebugStep, TNum, (u64, u64))> {
    self.buf.iter().map(|&(ref s, tlb, sz)| (s.debugstep(), tlb, sz)).collect()
  }
}

pub fn solve2_(mut mach: XMach_, tlb: TNum, env: TFrameRef) -> XMach_ {
  mach.reg = XReg::Sol0(tlb, env);
  mach
}

pub fn solve2(mut mach: XMach_, tlb: TNum, env: TFrameRef) -> XMach_ {
  mach.reg = XReg::Sol(tlb, env);
  mach
}

pub fn step2<T: MTrace>(mut mach: XMach_, tape: &mut T) -> XMach_ {
  match &mach.reg {
    &XReg::Emp => {
      panic!("bug: step2: Emp");
    }
    &XReg::Res => {
      match &mut mach.kont {
        &mut XKont_::Halt => {
          //panic!("TRACE: step2: halt");
          mach
        }
        &mut XKont_::Max1(ref mut state, prev_tlb, ref prev_env, ref prev_kont) => {
          if log_trace_vvv() {
            println!("TRACE: step2: Res/Max1: maxdepth={:?} toplevel?{:?}",
                state.maxdepth, state.toplevel);
          }
          match state.ptr {
            None => {
              if log_trace_vvv() {
                println!("TRACE: step2: Res/Max1:   try nul");
              }
              // FIXME(HACK): debugging.
              state.ptr = Some(state.def_buf.len());
              //state.ptr = Some(0);
              assert_eq!(state.chk, mach.env.snapshot());
              let mut null_env = mach.env.clone();
              let null_mut = Rc::make_mut(&mut null_env);
              //null_mut.patch_least_ub();
              let null_checkpt = null_mut.snapshot();
              state.tmp.swap.clear();
              for &nul_rec in state.nul_buf.iter() {
                null_mut.nul_eval_1(
                    //None,
                    //Some(1_000_000),
                    //Some(10_000_000),
                    mach.tlb,
                    CVar(nul_rec),
                    //&mut state.tmp.rht,
                    &mut state.tmp.nod,
                    &mut state.tmp.idx,
                    &mut state.tmp.sub,
                    &mut state.tmp.off,
                    &mut state.tmp.ary,
                    &mut state.tmp.rel,
                    &mut state.tmp.pat,
                    &mut state.tmp.tup,
                    &mut state.tmp.spat,
                    &mut state.tmp.swap,
                    &mut WCapture::default(),
                );
              }
              state.tmp.swp2.clear();
              null_mut.swapfix(&mut state.tmp.swap, &mut state.tmp.swp2);
              let null_checkpt2 = null_mut.snapshot();
              drop(null_mut);
              if state.toplevel {
                if log_trace_vvv() {
                  println!("TRACE: step2: nul: update step: new tlb={}", state.chk.next_glb());
                }
                let mut shared = state.shared.borrow_mut();
                shared.step = Some((MStep::Nul, state.chk.next_glb(), null_env.clone()));
              }
              let old_nulfix = state.nulfix;
              let new_nulfix = null_checkpt == null_checkpt2;
              state.nulfix |= new_nulfix;
              if !old_nulfix && new_nulfix {
                if log_trace_vvv() {
                  println!("TRACE: step2: nul: fix val");
                }
                //state.nulenv = Some(null_env);
                let null_tlb = state.chk.next_glb();
                let null_mut = Rc::make_mut(&mut null_env);
                let val = evaldiff(null_tlb, null_mut, state.ref_tlb, &state.ref_env);
                mach.reg = XReg::Val(val);
                return mach;
              }
              if log_trace_vvv() {
                println!("TRACE: step2: nul: pass");
              }
              assert!(state.maxdepth >= 1);
              //let ref_env = state.ref_env.clone();
              let maxdepth = state.maxdepth - 1;
              let toplevel = false;
              //mach.tlb = state.chk.t;
              //mach.env = null_env;
              //mach.reg = XReg::Max(state.ref_tlb, ref_env, maxdepth, toplevel);
              mach.reg = XReg::Max(state.chk.next_glb(), null_env, maxdepth, toplevel);
              mach
            }
            Some(ptr) => {
              if log_trace_vvv() {
                println!("TRACE: step2: Res/Max1:   try def: ptr={}", ptr);
              }
              if ptr > state.def_buf.len() {
                panic!("bug: step2: Res/Max1: ptr overflow: {}", ptr);
              } else if ptr == state.def_buf.len() {
                if log_trace_vvv() {
                  println!("TRACE: step2: Res/Max1:     ret");
                }
                if !state.pullback.is_empty() && state.pulled_b.is_none() {
                  println!("TRACE: step2: Res/Max1:     nonempty pullback");
                  state.ptr = Some(0);
                  //state.pullback.sort();
                  //state.pullback.dedup();
                  //state.pulled_b = true;
                  let mut pullbk_q = Vec::with_capacity(state.pullback.len());
                  for (&rel, &max_ht) in state.pullback.iter() {
                    pullbk_q.push((max_ht, rel));
                  }
                  pullbk_q.sort();
                  println!("TRACE: step2: Res/Max1:       {:?}", &pullbk_q);
                  state.pulled_b = Some(pullbk_q[pullbk_q.len() - 1].1);
                  println!("TRACE: step2: Res/Max1:       {:?}", state.pulled_b);
                  return mach;
                }
                if state.toplevel {
                  let shared = state.shared.borrow();
                  match shared.opt.as_ref() {
                    //None => panic!("bug: empty opt"),
                    None => {
                      mach.reg = XReg::Trc(MStep::Fix, mach.tlb, mach.env.clone());
                    }
                    Some(&(ref val, (ref step, next_tlb, ref next_env))) => {
                      if log_debug() {
                        println!("DEBUG: step2: Res/Max1: trace next: val={:?} step={:?}", val, step.debugstep());
                      }
                      mach.reg = XReg::Trc(step.clone(), next_tlb, next_env.clone());
                    }
                  }
                }
                mach.tlb = prev_tlb;
                mach.env = prev_env.clone();
                mach.kont = (&**prev_kont).clone();
                return mach;
              }
              let def_rec = state.def_buf[ptr];
              state.ptr = Some(ptr + 1);
              if log_trace_vvv() {
                println!("TRACE: step2: def: try def={}", def_rec);
              }
              assert_eq!(state.chk, mach.env.snapshot());
              let mut next_env = mach.env.clone();
              let next_mut = Rc::make_mut(&mut next_env);
              //swapbuf.clear();
              //next_mut.def_eval_1(CVar(def_rec), &mut idx, &mut sub, &mut rel, &mut pat, &mut tup, &mut savetup, &mut swapbuf);
              state.tmp.swap.clear();
              next_mut.def_eval_1(
                  mach.tlb,
                  CVar(def_rec),
                  //&mut state.tmp.rht,
                  &mut state.tmp.nod,
                  &mut state.tmp.idx,
                  &mut state.tmp.sub,
                  &mut state.tmp.off,
                  &mut state.tmp.ary,
                  &mut state.tmp.rel,
                  &mut state.tmp.pat,
                  &mut state.tmp.tup,
                  &mut state.tmp.spat,
                  //&mut state.tmp.stup,
                  &mut state.tmp.swap,
                  &mut WCapture::default(),
              );
              if state.tmp.swap.is_empty() {
                if log_trace_vvv() {
                  println!("TRACE: step2: def: bail 2 early def={}", def_rec);
                }
                return mach;
              }
              let def_checkpt = next_mut.snapshot();
              //next_mut.swap(&swapbuf);
              state.tmp.swp2.clear();
              next_mut.swapfix(&mut state.tmp.swap, &mut state.tmp.swp2);
              let def_checkpt2 = next_mut.snapshot();
              if def_checkpt == def_checkpt2 {
                // TODO
                if log_trace_vvv() {
                  println!("TRACE: step2: def: bail 2 late def={}", def_rec);
                }
                return mach;
              }
              if log_trace_vvv() {
                println!("TRACE: step2: def: pass 2 def={}", def_rec);
              }
              state.tmp.swap.clear();
              for &nul_rec in state.nul_buf.iter() {
                //next_mut.nul_eval_1(start, CVar(nul_rec), &mut idx, &mut sub, &mut rel, &mut pat, &mut tup, &mut swapbuf);
                next_mut.nul_eval_1(
                    //None,
                    //Some(1_000_000),
                    //Some(10_000_000),
                    mach.tlb,
                    CVar(nul_rec),
                    //&mut state.tmp.rht,
                    &mut state.tmp.nod,
                    &mut state.tmp.idx,
                    &mut state.tmp.sub,
                    &mut state.tmp.off,
                    &mut state.tmp.ary,
                    &mut state.tmp.rel,
                    &mut state.tmp.pat,
                    &mut state.tmp.tup,
                    &mut state.tmp.spat,
                    &mut state.tmp.swap,
                    &mut WCapture::default(),
                );
              }
              state.tmp.swp2.clear();
              next_mut.swapfix(&mut state.tmp.swap, &mut state.tmp.swp2);
              drop(next_mut);
              if log_trace_vvv() {
                println!("TRACE: step2: def: pass def={}", def_rec);
              }
              // TODO
              if state.toplevel {
                let mut shared = state.shared.borrow_mut();
                shared.step = Some((MStep::Def(def_rec), state.chk.next_glb(), next_env.clone()));
              }
              assert!(state.maxdepth >= 1);
              //let ref_env = state.ref_env.clone();
              let maxdepth = state.maxdepth - 1;
              let toplevel = false;
              //mach.reg = XReg::Max(state.ref_tlb, ref_env, maxdepth, toplevel);
              //mach.tlb = state.chk.t;
              //mach.env = next_env;
              mach.reg = XReg::Max(state.chk.next_glb(), next_env, maxdepth, toplevel);
              mach
            }
          }
        }
        &mut XKont_::Mat_(ref mut state, prev_tlb, ref prev_env, ref prev_kont) => {
          if log_trace_vvv() {
            println!("TRACE: step2: Res/Mat_: maxdepth={:?}", state.maxdepth);
          }
          let ptr = state.ptr;
          if log_trace_vvv() {
            println!("TRACE: step2: Res/Mat_:   next: {}", ptr);
          }
          if ptr > state.case_buf.len() {
            panic!("bug: step2: Res/Mat_: ptr overflow: {}", ptr);
          } else if ptr == state.case_buf.len() {
            if log_trace_vvv() {
              println!("TRACE: step2: Res/Mat_:     ret");
            }
            mach.tlb = prev_tlb;
            mach.env = prev_env.clone();
            mach.kont = (&**prev_kont).clone();
            return mach;
          }
          state.ptr = ptr + 1;
          let cat_var = CVar(state.tup[0]);
          let case_var = CVar(state.case_buf[ptr]);
          let case_idx = (ptr as u32) + 1;
          let mut next_env = mach.env.clone();
          match state.maxdepth {
            None => {
              // FIXME
              unimplemented!();
            }
            Some(maxdepth) => {
              assert!(maxdepth >= 1);
              tape.append(&MStep::Cas(case_idx, case_var.0), state.chk.next_glb(), &next_env);
              //let ref_env = state.ref_env.clone();
              let toplevel = false;
              mach.reg = XReg::Max(state.chk.next_glb(), next_env, maxdepth, toplevel);
              mach
            }
          }
        }
        &mut XKont_::Sol1(prev_tlb, ref prev_env, ref prev_kont) => {
          // TODO
          panic!("bug: step2: Res/Sol1: unimpl");
        }
        _ => panic!("bug: step2: Res: missing kont")
      }
    }
    &XReg::Val(ref val) => {
    //&XReg::Val(val, next_tlb, ref next_env) => {
      match &mut mach.kont {
        &mut XKont_::Max1(ref mut state, _, _, _) => {
          if log_trace_vvv() {
            println!("TRACE: step2: Val/Max1: val={:?} zero? {:?}", val, val.zero());
          }
          if !val.zero() {
            let mut shared = state.shared.borrow_mut();
            //let tuple = (val, mach.tlb, mach.env.clone());
            //let tuple = (shared.step.clone().unwrap(), val, mach.tlb, mach.env.clone());
            let tuple = (val.clone(), shared.step.clone().unwrap());
            match shared.opt.as_ref() {
              None => {
                if log_trace() || log_debug() && (val.sat > 0 || val.par > 0) {
                  println!("DEBUG: step2: Val/Max1: update opt: val={:?}", val);
                }
                shared.opt = Some(tuple);
              }
              Some(&(ref old_val, _)) => if old_val < val {
                if log_trace() || log_debug() && (val.sat > 0 || val.par > 0) {
                  println!("DEBUG: step2: Val/Max1: update opt: oldval={:?} val={:?}", old_val, val);
                }
                shared.opt = Some(tuple);
              } else {
                if log_trace_vvv() {
                  println!("TRACE: step2: Val/Max1: non update opt: oldval={:?} val={:?}", old_val, val);
                }
              }
            }
          }
          mach.reg = XReg::Res;
          mach
        }
        _ => panic!("bug: step2: Val: missing kont")
      }
    }
    //&XReg::Max(ref_tlb, ref ref_env, maxdepth, toplevel) => {
    &XReg::Max(next_tlb, ref next_env, maxdepth, toplevel) => {
      if log_trace_vvv() {
        if toplevel {
          println!("TRACE: step2: Max: maxdepth={} toplevel", maxdepth);
        } else {
          println!("TRACE: step2: Max: maxdepth={} sublevel", maxdepth);
        }
      }
      if maxdepth == 0 {
        match &mach.kont {
          &XKont_::Max1(ref state, ..) => {
            if log_trace_vvv() {
              println!("TRACE: step2: Max:   eval maxdepth=0");
            }
            let mut next_env = next_env.clone();
            let next_mut = Rc::make_mut(&mut next_env);
            let val = evaldiff(next_tlb, next_mut, state.ref_tlb, &state.ref_env);
            mach.reg = XReg::Val(val);
            return mach;
          }
          _ => panic!("bug: sublevel not in Max1 kont (maxdepth=0)")
        }
      }
      let mut nul_buf = Vec::with_capacity(next_env.nul_count());
      let mut def_buf = Vec::with_capacity(next_env.def_count());
      let mut cat_buf = Vec::new();
      nul_buf.resize(next_env.nul_count(), 0);
      def_buf.resize(next_env.def_count(), 0);
      next_env.fill_nul(&mut nul_buf);
      next_env.fill_def(&mut def_buf);
      let chk = next_env.snapshot();
      // FIXME: inherit previous Max1 nulstate?
      let nulfix = false;
      //let nulenv = None;
      let ptr = None;
      // FIXME: inherit pullback state.
      let tmp = TupMem::default();
      //let shared = XMax1SharedRef::default();
      let (ref_tlb, ref_env, pullback, pulled_b, shared) = if !toplevel {
        match &mach.kont {
          &XKont_::Max1(ref state, ..) => {
            (state.ref_tlb,
             state.ref_env.clone(),
             state.pullback.clone(),
             state.pulled_b,
             state.shared.clone())
          }
          _ => panic!("bug: step2: Max: sublevel not in Max1 kont")
        }
      } else {
        (next_tlb,
         next_env.clone(),
         //Vec::new(),
         //false,
         BTreeMap::new(),
         None,
         XMax1SharedRef::default())
      };
      let initstate = XMax1State{
        ref_tlb,
        ref_env,
        maxdepth,
        toplevel,
        nul_buf,
        def_buf,
        cat_buf,
        chk,
        nulfix,
        //nulenv,
        ptr,
        pullback,
        pulled_b,
        tmp,
        shared,
      };
      mach.kont = XKont_::Max1(initstate, mach.tlb, mach.env, mach.kont.into());
      mach.tlb = next_tlb;
      mach.env = next_env.clone();
      mach.reg = XReg::Res;
      mach
    }
    &XReg::Trc(ref step, next_tlb, ref next_env) => {
      match &mach.kont {
        &XKont_::Mat_(ref _state, prev_tlb, ref prev_env, ref prev_kont) => {
          // FIXME
          println!("TRACE: step2: Trc/Mat_");
          unimplemented!();
        }
        &XKont_::Sol1(prev_tlb, ref prev_env, ref prev_kont/*, ref prev_reg*/) => {
          if log_trace_vvv() {
            println!("TRACE: step2: Trc/Sol1");
            match step {
              &MStep::Fix => {
                println!("TRACE: step2: Trc/Sol1: step: Fix");
              }
              &MStep::Nul => {
                println!("TRACE: step2: Trc/Sol1: step: Nul");
              }
              &MStep::Def(x) => {
                println!("TRACE: step2: Trc/Sol1: step: Def({})", x);
              }
              _ => {
                println!("TRACE: step2: Trc/Sol1: step: {:?}", step.kind());
              }
            }
          }
          tape.append(step, next_tlb, next_env);
          let mut next_env = next_env.clone();
          let next_mut = Rc::make_mut(&mut next_env);
          match next_mut.terminal(next_tlb) {
            None |
            Some(TStatus::Unsat) => {
              match step {
                &MStep::Fix => {
                  if log_trace_vvv() {
                    println!("TRACE: step2: Trc/Sol1: Fix");
                  }
                  mach.tlb = prev_tlb;
                  mach.env = prev_env.clone();
                  mach.kont = (&**prev_kont).clone();
                  mach.reg = XReg::Res;
                  //mach.reg = XReg::Ret(...);
                  return mach;
                }
                _ => {}
              }
              mach.tlb = next_tlb;
              mach.env = next_env.clone();
              mach.reg = XReg::Max(next_tlb, next_env.clone(), mach.cfg.maxdepth, true);
              mach
            }
            Some(TStatus::Sat) => {
              if log_trace_vvv() {
                println!("TRACE: step2: Trc/Sol1: Sat");
              }
              tape.append(&MStep::Sat, next_tlb, &next_env);
              mach.tlb = prev_tlb;
              mach.env = prev_env.clone();
              mach.kont = (&**prev_kont).clone();
              mach.reg = XReg::Res;
              //mach.reg = XReg::Ret(...);
              mach
            }
            Some(TStatus::Par) => {
              if log_trace_vvv() {
                println!("TRACE: step2: Trc/Sol1: Par");
              }
              tape.append(&MStep::Par, next_tlb, &next_env);
              mach.tlb = prev_tlb;
              mach.env = prev_env.clone();
              mach.kont = (&**prev_kont).clone();
              mach.reg = XReg::Res;
              //mach.reg = XReg::Ret(...);
              mach
            }
          }
        }
        _ => panic!("bug: step2: Trc: missing kont")
      }
    }
    &XReg::Sol(ref_tlb, ref ref_env) => {
      if log_trace_vvv() {
        println!("TRACE: step2: Sol");
      }
      tape.append(&MStep::Sol(ref_tlb, ref_env.clone()), ref_tlb, ref_env);
      mach.kont = XKont_::Sol1(mach.tlb, mach.env, mach.kont.into());
      mach.tlb = ref_tlb;
      mach.env = ref_env.clone();
      mach.reg = XReg::Max(ref_tlb, ref_env.clone(), mach.cfg.maxdepth, true);
      mach
    }
    _ => panic!("bug: step2: unimpl reg")
  }
}

#[derive(Clone)]
pub struct XMach {
  cfg:  XMachCfg,
  //tape: Vec<MStep>,
  tlb:  TNum,
  env:  TFrameRef,
  kont: XKontRef,
  reg:  XReg,
}

impl XMach {
  pub fn empty(cfg: XMachCfg) -> XMach {
    let tlb = 0;
    let env = TFrameRef::default();
    let kont = XKont_::Halt.into();
    let reg = XReg::Emp;
    XMach{
      cfg,
      tlb,
      env,
      kont,
      reg,
    }
  }

  pub fn solve(cfg: XMachCfg, tlb: TNum, env: TFrameRef) -> XMach {
    let kont = XKont_::Halt.into();
    let reg = XReg::Sol(tlb, env);
    //let reg = XReg::Stp(MStep::Sol(tlb, env));
    XMach{
      cfg,
      tlb:  0,
      env:  TFrameRef::default(),
      kont,
      reg,
    }
  }

  pub fn halt(&self) -> bool {
    self.kont.halt()
  }
}

pub fn evaldiff_(tlb: TNum, env: &mut TFrame, root_tlb: TNum, root_env: &TFrameRef, pull: Option<SNum>) -> XVal {
  if tlb == root_tlb {
    return XVal::default();
  }
  let (par, sat) = match env.terminal(tlb) {
    None |
    Some(TStatus::Unsat) => (0, 0),
    Some(TStatus::Sat) => (0, 1),
    Some(TStatus::Par) => (1, 0),
  };
  //let mut pul = Vec::with_capacity(pullback.len());
  let mut pul = None;
  //for &rel in pullback.iter() {
  if let Some(srel) = pull {
    let rel = if srel < 0 {
      CVar(-srel)
    } else {
      CVar(srel)
    };
    env.patch_rel(rel);
    let (new_pos, new_neg) = env.patchdiff_rel(rel, root_env);
    //pul.push((rel, new as i32));
    if srel < 0 {
      pul = Some(new_neg as i32);
    } else {
      pul = Some(new_pos as i32);
    }
  }
  let (old, new) = env.shm.cc.patchdiff(&root_env.shm.cc);
  let (old, new) = (old as i32, new as i32);
  let diff = env.shm.clk.diff(&root_env.shm.clk);
  let dx_val = diff.offset() as i32;
  //let val = XVal{par, sat, pul: Some(pul), old, new, dt: dx_val};
  let val = XVal{par, sat, bon: 0, pul, old, new, dt: dx_val};
  val
}

//pub fn evaldiff(env: &TFrameRef, root_env: &TFrameRef) -> (MStep, XVal, TNum, TFrameRef) {
//pub fn evaldiff(env: &TFrameRef, root_env: &TFrameRef) -> XTuple {
pub fn evaldiff(tlb: TNum, env: &mut TFrame, root_tlb: TNum, root_env: &TFrameRef) -> XVal {
  if tlb < root_tlb {
    panic!("bug: evaldiff: time travel");
  } else if tlb == root_tlb {
    if log_trace_vvv() {
      println!("TRACE: evaldiff: tlb={} root tlb={} bail", tlb, root_tlb);
    }
    return XVal::default();
  }
  let (par, sat) = match env.terminal(tlb) {
    None |
    Some(TStatus::Unsat) => (0, 0),
    Some(TStatus::Sat) => (0, 1),
    Some(TStatus::Par) => (1, 0),
  };
  /*let udiff = env.shm.cc.udiff(&root_env.shm.cc);
  let u_val = udiff.size() as i32;*/
  let bon = 0;
  //let bon = max(0, env.neg_tup_size(CVar(31)) as i32 - root_env.neg_tup_size(CVar(31)) as i32);
  //let bon = max(0, env.pos_tup_size(CVar(42)) as i32 - root_env.pos_tup_size(CVar(42)) as i32);
  let (old, new) = env.shm.cc.patchdiff(&root_env.shm.cc);
  let (old, new) = (old as i32, new as i32);
  let diff = env.shm.clk.diff(&root_env.shm.clk);
  let dx_val = diff.offset() as i32;
  //let val = XVal{inct: 0, exct: u_val, unct: dx_val};
  //let val = XVal{par, sat, exct: u_val, unct: dx_val};
  let val = XVal{par, sat, bon, pul: None, old, new, dt: dx_val};
  val
}

pub fn step(cfg: XMachCfg, mach: &mut XMach, trace: &mut Vec<MStep>) -> bool {
  match &*mach.kont {
    &XKont_::Halt => {
      return true;
    }
    &XKont_::Max(ref root_env, ref prev_kont) => {
      let mut tmp = EvalMaxTmp::default();
      _eval_max(cfg.maxdepth, mach.tlb, &mach.env, root_env, prev_kont, &mut tmp);
      match tmp.opt {
        None => {
          mach.kont = prev_kont.clone();
          trace.push(MStep::Ret);
          return false;
        }
        Some((step, _, next_tlb, next_env, next_kont)) => {
          mach.tlb = next_tlb;
          mach.env = next_env;
          mach.kont = next_kont;
          trace.push(step);
          return false;
        }
      }
    }
    &XKont_::Mat(ref root_env, _, ref cases, ref prev_kont) => {
      let opt = _eval_mat(cfg.maxdepth, mach.tlb, cases, /*mach.env.clone(),*/ root_env, mach.kont.clone());
      match opt {
        None => {
          mach.kont = prev_kont.clone();
          trace.push(MStep::Ret);
          return false;
        }
        Some((_, step, _, next_tlb, next_env, next_kont)) => {
          mach.tlb = next_tlb;
          mach.env = next_env;
          mach.kont = next_kont;
          trace.push(step);
          return false;
        }
      }
    }
    _ => unimplemented!()
  }
}

#[derive(Default)]
struct EvalMaxTmp {
  opt:  Option<(MStep, XVal, TNum, TFrameRef, XKontRef)>,
}

impl EvalMaxTmp {
  fn _lt(&self, other: &EvalMaxTmp) -> bool {
    match (self.opt.as_ref(), other.opt.as_ref()) {
      (Some(&(_, ref lval, ..)), Some(&(_, ref rval, ..))) => {
        lval < rval
      }
      (None, Some(_)) => true,
      (_, None) => false
    }
  }
}

fn _eval_max(maxdepth: u32, tlb: TNum, env: &TFrameRef, root_env: &TFrameRef, prev_kont: &XKontRef, /*tmp_trace: &mut Vec<MStep>,*/ tmp: &mut EvalMaxTmp) {
  if maxdepth == 0 {
    // TODO
  }
  /*let env = Rc::make_mut(env);
  let next_kont = Kont_::Max(env, prev_kont).into();
  unimplemented!();*/
  //let curr = env.snapshot();
  let mut nul_buf = Vec::new();
  let mut def_buf = Vec::new();
  nul_buf.resize(env.nul_count(), 0);
  def_buf.resize(env.def_count(), 0);
  env.fill_nul(&mut nul_buf);
  env.fill_def(&mut def_buf);
  //let mut mask = BTreeSet::new();
  //let mut rht = Vec::new();
  let mut nod = Vec::new();
  let mut idx = Vec::new();
  let mut sub = Vec::new();
  let mut off = Vec::new();
  let mut ary = Vec::new();
  let mut rel = Vec::new();
  let mut pat = Vec::new();
  let mut tup = Vec::new();
  let mut savepat = Vec::new();
  //let mut savetup = Vec::new();
  let mut swapbuf = Vec::new();
  let mut null = env.clone();
  let null_mut = Rc::make_mut(&mut null);
  let null_checkpt = null_mut.snapshot();
  for &rec in nul_buf.iter() {
    null_mut.nul_eval_1(/*None,*/ tlb, CVar(rec), /*&mut rht,*/ &mut nod, &mut idx, &mut sub, &mut off, &mut ary, &mut rel, &mut pat, &mut tup, &mut savepat, &mut swapbuf, &mut WCapture::default());
  }
  null_mut.swap(&swapbuf, &mut Vec::new());
  let null_checkpt2 = null_mut.snapshot();
  drop(null_mut);
  let new_nulfix = null_checkpt == null_checkpt2;
  //if maxdepth == 0 && !(nulfix || new_nulfix) {
  //if maxdepth == 0 || (!nulfix && new_nulfix) {
  if maxdepth == 0 || new_nulfix {
    let udiff = null.shm.cc.udiff(&root_env.shm.cc);
    let u_val = udiff.size() as i32;
    let diff = null.shm.clk.diff(&root_env.shm.clk);
    let dx_val = diff.offset() as i32;
    if u_val != 0 || dx_val != 0 {
      // FIXME
      /*let kont = kont0.unwrap_or(XKont::Nul);
      let val = XVal{inct: 0, exct: u_val, unct: dx_val};
      match self.kmax.as_ref() {
        None => {
          self.kmax = Some((kont, val, null.clone()));
        }
        Some(&(_, old_val, _)) => if old_val < val {
          self.kmax = Some((kont, val, null.clone()));
        }
      }*/
    }
  }
  //nulfix = nulfix || new_nulfix;
  //if maxdepth > 0 && !nulfix {
  if maxdepth > 0 && !new_nulfix {
    // FIXME
    /*let mut next_mach = XMach{
      tlb:  curr.t,
      env:  null,
      kont: Kont_::Max(root_env.clone(), mach.kont.clone()).into(),
    }
    step(maxdepth - 1, &mut next_mach, tmp_trace, tmp);*/
  }
  for &_def_rec in def_buf.iter() {
    // TODO
  }
}

fn _eval_mat(maxdepth: u32, tlb: TNum, cases: &[(XCase, TFrameRef)], root_env: &TFrameRef, kont: XKontRef) -> Option<(u32, MStep, XVal, TNum, TFrameRef, XKontRef)> {
  let mut optcase = 0;
  let mut tmp = EvalMaxTmp::default();
  for (case_idx, &(_case, ref env)) in cases.iter().enumerate() {
    let mut casetmp = EvalMaxTmp::default();
    _eval_max(maxdepth - 1, tlb, env, root_env, &kont, &mut casetmp);
    if tmp._lt(&casetmp) {
      // TODO
      optcase = (case_idx + 1) as u32;
      tmp = casetmp;
    }
  }
  match tmp.opt {
    None => None,
    Some((a, b, c, d, e)) => {
      assert!(optcase > 0);
      Some((optcase, a, b, c, d, e))
    }
  }
}

#[derive(Clone, Copy, Debug)]
//#[derive(Clone, Debug)]
pub enum XKont {
  Nul,
  Def(SNum),
  //Mat(SNum, Cell<u32>),
  //Sup(SNum, u32),
  Mat(SNum),
  //Mat(SNum, Vec<SNum>),
  Sup(u32),
  Pop,
  Erg(SNum),
  Bot,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct XVal {
  //pub inct: i32,
  pub par:  i32,
  pub sat:  i32,
  pub bon:  i32,
  //pub pul:  i32,
  //pub pul:  Option<Vec<(SNum, i32)>>,
  pub pul:  Option<i32>,
  //pub exct: i32,
  pub old:  i32,
  pub new:  i32,
  //pub unct: i32,
  pub dt:   i32,
}

impl PartialOrd for XVal {
  fn partial_cmp(&self, other: &XVal) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for XVal {
  fn cmp(&self, other: &XVal) -> Ordering {
    //match self.inct.cmp(&other.inct) {
    match self.par.cmp(&other.par) {
      Ordering::Equal => {}
      Ordering::Less => {
        return Ordering::Less;
      }
      Ordering::Greater => {
        return Ordering::Greater;
      }
    }
    match self.sat.cmp(&other.sat) {
      Ordering::Equal => {}
      Ordering::Less => {
        return Ordering::Less;
      }
      Ordering::Greater => {
        return Ordering::Greater;
      }
    }
    match self.bon.cmp(&other.bon) {
      Ordering::Equal => {}
      Ordering::Less => {
        return Ordering::Less;
      }
      Ordering::Greater => {
        return Ordering::Greater;
      }
    }
    match self.old.cmp(&other.old) {
      Ordering::Equal => {}
      Ordering::Less => {
        return Ordering::Less;
      }
      Ordering::Greater => {
        return Ordering::Greater;
      }
    }
    //match (self.pul.as_ref(), other.pul.as_ref()) {
    match (self.pul, other.pul) {
      (None, None) => {}
      (None, Some(h)) => {
        if h > 0 {
          return Ordering::Less;
        }
      }
      (Some(h), None) => {
        if h > 0 {
          return Ordering::Greater;
        }
      }
      (Some(this_pul), Some(other_pul)) => {
        match this_pul.cmp(&other_pul) {
          Ordering::Equal => {}
          Ordering::Less => {
            return Ordering::Less;
          }
          Ordering::Greater => {
            return Ordering::Greater;
          }
        }
      }
    }
    match self.new.cmp(&other.new) {
      Ordering::Equal => {}
      Ordering::Less => {
        return Ordering::Less;
      }
      Ordering::Greater => {
        return Ordering::Greater;
      }
    }
    //self.unct.cmp(&other.unct)
    self.dt.cmp(&other.dt)
  }
}

impl Default for XVal {
  fn default() -> XVal {
    //XVal{inct: 0, exct: 0, unct: 0}
    //XVal{par: 0, sat: 0, exct: 0, unct: 0}
    XVal{par: 0, sat: 0, bon: 0, pul: None, old: 0, new: 0, dt: 0}
  }
}

impl XVal {
  pub fn zero(&self) -> bool {
    //self.inct == 0 && self.exct == 0 && self.unct == 0
    //self.par == 0 && self.sat == 0 && self.exct == 0 && self.unct == 0
    self.par == 0 && self.sat == 0 && self.bon == 0 && self.old == 0 && self.new == 0 && self.dt == 0
        && {
      match self.pul {
        None => true,
        Some(pul) => {
          pul == 0
        }
      }
    }
  }
}
