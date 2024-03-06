use crate::algo::*;
use crate::framework::{SNum, CVar};
use crate::lang::*;
use crate::log::*;

use std::cell::{RefCell};
use std::collections::{VecDeque};
use std::rc::{Rc};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct IVar(i32);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct IName(i32);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ILoc(i32);

#[derive(Clone, Copy, Debug)]
pub enum IRelSchema {
  Equivalence,
  Symmetric,
  Cyclic,
}

#[derive(Clone)]
pub struct IRel {
  // TODO
  //pub name:     String,
  pub name:     IName,
  pub var:      IVar,
  pub arity:    usize,
  pub funarity: Option<(usize, usize)>,
  pub schema:   Option<IRelSchema>,
}

#[derive(Clone, Copy, Debug)]
pub enum ITerm {
  //Place,
  //Name(String),
  Name(IName),
  //TVar(IName, IVar),
  FVar(IName, IVar),
  RVar(IName, IVar),
  Var(IVar),
}

impl From<IName> for ITerm {
  fn from(name: IName) -> ITerm {
    ITerm::Name(name)
  }
}

impl From<IVar> for ITerm {
  fn from(v: IVar) -> ITerm {
    ITerm::Var(v)
  }
}

pub type IExpRef<V> = Rc<IExp<V>>;

#[derive(Clone)]
//pub enum IExp<V=Option<IDebugInfo>> {
pub enum IExp<V=ILoc> {
  Term(V, ITerm),
  Desc(V, ITerm, IAtomicForm<V>),
  Bind(V, ITerm, IAtomicForm<V>, IExpRef<V>),
  App(V, IExpRef<V>, Vec<IExp<V>>),
  RVar(V, IVar),
}

impl IExp<Option<IDebugInfo>> {
  fn _set_debug_info(&mut self, dbginfo: IDebugInfo) {
    *match self {
      &mut IExp::Term(ref mut dbginfo, ..) => dbginfo,
      &mut IExp::Desc(ref mut dbginfo, ..) => dbginfo,
      &mut IExp::Bind(ref mut dbginfo, ..) => dbginfo,
      &mut IExp::App(ref mut dbginfo, ..) => dbginfo,
      &mut IExp::RVar(ref mut dbginfo, ..) => dbginfo,
    } = Some(dbginfo);
  }
}

#[derive(Clone)]
//pub enum IAtomicForm<V=Option<IDebugInfo>> {
pub enum IAtomicForm<V=ILoc> {
  //Pre(V, String, Vec<IExp<V>>),
  //VPre(V, IVar, Vec<IExp<V>>),
  //App(V, String, Vec<IExp<V>>, Vec<IExp<V>>),
  //Dom(V, String, Vec<IExp<V>>),
  //Img(V, String, Vec<IExp<V>>),
  Pre(V, ITerm, Vec<IExp<V>>),
  App(V, ITerm, Vec<IExp<V>>, Vec<IExp<V>>),
  Dom(V, ITerm, Vec<IExp<V>>),
  Img(V, ITerm, Vec<IExp<V>>),
  RPre(V, IVar, Vec<IVar>),
  RApp(V, IVar, Vec<IVar>, Vec<IVar>),
  RDom(V, IVar, Vec<IVar>),
  RImg(V, IVar, Vec<IVar>),
}

#[derive(Clone)]
//pub enum IClausalForm<V=Option<IDebugInfo>> {
pub enum IClausalForm<V=ILoc> {
  // TODO
  Lit(V, bool, IAtomicForm<V>),
  //Cat(V, Vec<(bool, IAtomicForm<V>)>),
  //Dis(V, Vec<(bool, IAtomicForm<V>)>),
  Eq_(V, IExp<V>, IExp<V>),
  Neq(V, IExp<V>, IExp<V>),
  Lt_(V, IExp<V>, IExp<V>),
  Lte(V, IExp<V>, IExp<V>),
  //Nlt(V, IExp<V>, IExp<V>),
}

impl<V: Clone> IClausalForm<V> {
  pub fn negative(&self) -> IClausalForm<V> {
    match self {
      &IClausalForm::Lit(ref v, neg, ref atom) => {
        IClausalForm::Lit(v.clone(), !neg, atom.clone())
      }
      &IClausalForm::Eq_(ref v, ref lexp, ref rexp) => {
        IClausalForm::Neq(v.clone(), lexp.clone(), rexp.clone())
      }
      &IClausalForm::Neq(ref v, ref lexp, ref rexp) => {
        IClausalForm::Eq_(v.clone(), lexp.clone(), rexp.clone())
      }
      _ => unimplemented!()
    }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IBinder {
  Top,
  Universal,
  Definitive,
  Existential,
  //Nonexistential,
}

#[derive(Clone)]
pub struct IRPCtx {
  //pub tvars:    Vec<IVar>,
  pub uvars:    Vec<IVar>,
  pub dvars:    Vec<IVar>,
  pub xvars:    Vec<IVar>,
  //pub innerctx: ICtx,
}

//pub type IRecFormRef<V=Option<IDebugInfo>> = Rc<IRecForm<V>>;
pub type IRecFormRef<V=ILoc> = Rc<IRecForm<V>>;

#[derive(Clone)]
pub struct IPrefixRecForm<V=ILoc> {
  //pub tvars:    Vec<ITerm>,
  pub uparams:  Vec<ITerm>,
  pub dparams:  Vec<ITerm>,
  pub xparams:  Vec<ITerm>,
  pub bicond:   bool,
  pub ante:     Vec<IForm<V>>,
  pub cons:     Vec<IForm<V>>,
}

#[derive(Clone)]
//pub enum IRecForm<V=Option<IDebugInfo>> {
pub enum IRecForm<V=ILoc> {
  C(V, bool, Vec<IForm<V>>, Vec<IForm<V>>),
  Q(V, IBinder, ITerm, IRecFormRef<V>),
  P(V, IPrefixRecForm<V>),
  RQs(V, VecDeque<(IBinder, IVar)>, IRecFormRef<V>),
  RPC(V, IRPCtx, bool, Vec<IClausalForm<V>>, Vec<IClausalForm<V>>),
}

//pub type IFormRef<V=Option<IDebugInfo>> = Rc<IForm<V>>;
pub type IFormRef<V=ILoc> = Rc<IForm<V>>;

#[derive(Clone)]
//pub enum IForm<V=Option<IDebugInfo>> {
pub enum IForm<V=ILoc> {
  Cla(V, IClausalForm<V>),
  Con(V, Vec<IForm<V>>),
  //Cat(V, Vec<IForm<V>>),
  //Dis(V, Vec<IForm<V>>),
  Fre(V, IClausalForm<V>),
  Rec(V, IRecForm<V>),
}

#[derive(Clone)]
pub struct INameTable {
  nctr: i32,
  nmap: HTreapMap<String, IName>,
  nrev: HTreapMap<IName, String>,
}

impl Default for INameTable {
  fn default() -> INameTable {
    INameTable{
      nctr: 0,
      nmap: HTreapMap::default(),
      nrev: HTreapMap::default(),
    }
  }
}

impl INameTable {
  pub fn lookup_str(&mut self, name: &str) -> IName {
    match self.nmap.get(name) {
      None => {
        let new_n = self.nctr + 1;
        assert!(new_n > 0);
        self.nctr = new_n;
        self.nmap.insert(name.to_string(), IName(new_n));
        self.nrev.insert(IName(new_n), name.to_string());
        IName(new_n)
      }
      Some(&n) => n
    }
  }

  pub fn rev_lookup(&self, name: IName) -> &str {
    match self.nrev.get(&name) {
      None => {
        panic!("bug: INameTable::rev_lookup: missing key: {:?}", name);
      }
      Some(ref s) => s
    }
  }
}

#[derive(Clone)]
pub struct ILocTable {
  lctr: i32,
  lset: IHTreapSet<ILoc>,
  lmap: IHTreapMap<ILoc, ILoc>,
  dbgi: IHTreapMap<ILoc, IDebugInfo>,
  ctx:  IHTreapMap<ILoc, ICtx>,
}

impl Default for ILocTable {
  fn default() -> ILocTable {
    ILocTable{
      lctr: 0,
      lset: IHTreapSet::default(),
      lmap: IHTreapMap::default(),
      dbgi: IHTreapMap::default(),
      ctx:  IHTreapMap::default(),
    }
  }
}

impl ILocTable {
  pub fn fresh_loc(&mut self) -> ILoc {
    let new_l = self.lctr + 1;
    assert!(new_l > 0);
    self.lctr = new_l;
    self.lset.insert(ILoc(new_l));
    self.lmap.insert(ILoc(new_l), ILoc(new_l));
    ILoc(new_l)
  }

  pub fn find_debugloc_nonmut(&self, k: ILoc) -> ILoc {
    let mut nx = match self.lmap.get(&k) {
      None => panic!("bug: ILocTable::find_debugloc_nonmut: missing key: {:?}", k),
      Some(&v) => v
    };
    if k == nx {
      return nx;
    }
    loop {
      let nx2 = match self.lmap.get(&nx) {
        None => panic!("bug: ILocTable::find_debugloc_nonmut: missing cursor: {:?}", nx),
        Some(&v) => v
      };
      if nx == nx2 {
        return nx;
      }
      nx = nx2;
    }
  }

  pub fn find_debugloc(&mut self, k: ILoc) -> ILoc {
    let mut nx = match self.lmap.get(&k) {
      None => panic!("bug: ILocTable::find_debugloc: missing key: {:?}", k),
      Some(&v) => v
    };
    if k == nx {
      return nx;
    }
    let mut x = nx;
    loop {
      let nx2 = match self.lmap.get(&nx) {
        None => panic!("bug: ILocTable::find_debugloc: missing cursor: {:?}", nx),
        Some(&v) => v
      };
      if nx == nx2 {
        return nx;
      }
      self.lmap.insert(x, nx2);
      x = nx;
      nx = nx2;
    }
  }

  fn _lunify_debuglocs(&mut self, lr: ILoc, rr: ILoc) {
    self.lset.remove(&rr);
    self.lmap.insert(rr, lr);
    self.lmap.insert(lr, lr);
    // FIXME: unify debuginfo.
    // FIXME: unify ctx.
  }

  pub fn unify_debuglocs(&mut self, lk: ILoc, rk: ILoc) {
    // FIXME
    let lr = self.find_debugloc(lk);
    if lk == rk {
      //return lr;
      return;
    }
    let rr = self.find_debugloc(rk);
    if lr == rr {
      //return rr;
      return;
    }
    if lr == rr {
      panic!("bug: ILocTable::unify_debuglocs: unreachable");
    } else if lr < rr {
      self._lunify_debuglocs(lr, rr)
    } else {
      self._lunify_debuglocs(rr, lr)
    }
  }

  pub fn find_debuginfo_nonmut(&self, k: ILoc) -> Option<IDebugInfo> {
    let r = self.find_debugloc_nonmut(k);
    match self.dbgi.get(&r) {
      None => None,
      Some(dbginfo) => Some(dbginfo.clone())
    }
  }

  pub fn find_debuginfo(&mut self, k: ILoc) -> Option<IDebugInfo> {
    let r = self.find_debugloc(k);
    match self.dbgi.get(&r) {
      None => None,
      Some(dbginfo) => Some(dbginfo.clone())
    }
  }

  pub fn set_debuginfo(&mut self, k: ILoc, dbginfo: IDebugInfo) {
    // TODO
    self.dbgi.insert(k, dbginfo);
  }

  pub fn ctx(&self, k: ILoc) -> ICtx {
    match self.ctx.get(&k) {
      None => panic!("bug: ILocTable::ctx: missing key: {:?}", k),
      Some(ctx) => ctx.clone()
    }
  }

  pub fn set_ctx(&mut self, k: ILoc, ctx: ICtx) {
    // TODO
    self.ctx.insert(k, ctx);
  }
}

#[derive(Clone, Debug)]
pub struct IDebugInfo {
  // FIXME
  hquote:   HQuote,
  spaninfo: HSpanInfo,
}

impl From<HExp> for IDebugInfo {
  fn from(hexp: HExp) -> IDebugInfo {
    let spaninfo = hexp.spaninfo();
    IDebugInfo{
      hquote:   HQuote::Exp(hexp),
      spaninfo,
    }
  }
}

impl From<HForm> for IDebugInfo {
  fn from(hform: HForm) -> IDebugInfo {
    let spaninfo = hform.spaninfo();
    IDebugInfo{
      hquote:   HQuote::Form(hform),
      spaninfo,
    }
  }
}

impl From<HRecForm> for IDebugInfo {
  fn from(hform: HRecForm) -> IDebugInfo {
    let spaninfo = hform.spaninfo();
    IDebugInfo{
      hquote:   HQuote::Form(HForm::Rec(hform, spaninfo)),
      spaninfo,
    }
  }
}

impl From<HClausalForm> for IDebugInfo {
  fn from(hform: HClausalForm) -> IDebugInfo {
    let spaninfo = hform.spaninfo();
    IDebugInfo{
      hquote:   HQuote::Form(HForm::Cla(hform, spaninfo)),
      spaninfo,
    }
  }
}

impl From<HAtomicForm> for IDebugInfo {
  fn from(hform: HAtomicForm) -> IDebugInfo {
    let spaninfo = hform.spaninfo();
    IDebugInfo{
      hquote:   HQuote::Atom(hform),
      spaninfo,
    }
  }
}

#[derive(Clone)]
pub struct ICtx {
  pub bind: IHTreapMap<IName, (IBinder, IVar)>,
  rbind:    IHTreapMap<IVar, (IBinder, IName)>,
  abind:    IHTreapMap<IVar, IBinder>,
  //dbginfo:  Option<IDebugInfo>,
}

impl Default for ICtx {
  fn default() -> ICtx {
    ICtx::empty()
  }
}

impl ICtx {
  fn empty() -> ICtx {
    ICtx{
      bind:     IHTreapMap::default(),
      rbind:    IHTreapMap::default(),
      abind:    IHTreapMap::default(),
      //dbginfo:  None,
    }
  }

  fn bind(mut self, binder: IBinder, name: IName, var: IVar) -> ICtx {
    self.bind_mut(binder, name, var);
    self
  }

  fn bind_mut(&mut self, binder: IBinder, name: IName, var: IVar) {
    self.bind.insert(name, (binder, var));
    self.rbind.insert(var, (binder, name));
  }

  fn anon_bind(mut self, binder: IBinder, var: IVar) -> ICtx {
    self.anon_bind_mut(binder, var);
    self
  }

  fn anon_bind_mut(&mut self, binder: IBinder, var: IVar) {
    self.abind.insert(var, binder);
  }

  fn lookup(&self, name: IName) -> Option<(IBinder, IVar)> {
    match self.bind.get(&name) {
      None => None,
      Some(&(binder, var)) => Some((binder, var))
    }
  }

  fn rev_lookup(&self, var: IVar) -> Option<(IBinder, IName)> {
    // FIXME
    match self.rbind.get(&var) {
      None => None,
      Some(&(binder, name)) => Some((binder, name))
    }
  }

  fn lookup2(&self, binder: IBinder, name: IName) -> Option<IVar> {
    match self.bind.get(&name) {
      None => None,
      Some(&(binder2, v)) => if binder != binder2 {
        None
      } else {
        Some(v)
      }
    }
  }

  fn lookup2v(&self, binder: IBinder, var: IVar) -> Option<IVar> {
    match self.abind.get(&var) {
      Some(&binder2) => if binder == binder2 {
        return Some(var);
      }
      None => {}
    }
    match self.rbind.get(&var) {
      Some(&(binder2, _)) => if binder == binder2 {
        return Some(var);
      }
      None => {}
    }
    None
  }
}

#[derive(Clone)]
//pub struct ITheoryEnv<V=Option<IDebugInfo>> {
pub struct ITheoryEnv<V=ILoc> {
  pub ntbl: INameTable,
  pub ltbl: ILocTable,
  pub vctr: i32,
  v2i:  Rc<RefCell<BTreeMap<CVar, IVar>>>,
  //pub eqn:  Option<String>,
  pub eqn:  Option<IName>,
  pub eqv:  Option<IVar>,
  //pub top:  HTreapMap<String, IVar>,
  pub top:  ICtx,
  pub rels: HTreapMap<usize, IRel>,
  //pub rels: HTreapMap<IVar, IRel>,
  //pub cats: HTreapMap<usize, ICat>,
  //pub diss: HTreapMap<usize, IDis>,
  pub recs: HTreapMap<usize, IRecForm<V>>,
  pub prop: HTreapMap<usize, IForm<V>>,
}

impl<V> Default for ITheoryEnv<V> {
  fn default() -> ITheoryEnv<V> {
    ITheoryEnv{
      ntbl: INameTable::default(),
      ltbl: ILocTable::default(),
      vctr: 0,
      v2i:  Rc::new(RefCell::new(BTreeMap::new())),
      eqn:  None,
      eqv:  None,
      top:  ICtx::empty(),
      rels: HTreapMap::default(),
      //cats: HTreapMap::default(),
      recs: HTreapMap::default(),
      prop: HTreapMap::default(),
    }
  }
}

impl ITheoryEnv {
  pub fn fresh_loc(&mut self) -> ILoc {
    self.ltbl.fresh_loc()
  }

  pub fn unify_debuglocs(&mut self, lk: ILoc, rk: ILoc) {
    self.ltbl.unify_debuglocs(lk, rk)
  }

  pub fn find_debuginfo_nonmut(&self, k: ILoc) -> Option<IDebugInfo> {
    self.ltbl.find_debuginfo_nonmut(k)
  }

  pub fn find_debuginfo(&mut self, k: ILoc) -> Option<IDebugInfo> {
    self.ltbl.find_debuginfo(k)
  }

  pub fn set_debuginfo(&mut self, loc: ILoc, dbginfo: IDebugInfo) {
    self.ltbl.set_debuginfo(loc, dbginfo);
  }

  pub fn ctx(&self, k: ILoc) -> ICtx {
    self.ltbl.ctx(k)
  }

  pub fn set_ctx(&mut self, loc: ILoc, ctx: ICtx) {
    self.ltbl.set_ctx(loc, ctx);
  }

  pub fn copy_ctx(&mut self, lk: ILoc, rk: ILoc) {
    let ctx = self.ctx(lk);
    self.set_ctx(rk, ctx);
  }
}

impl<V> ITheoryEnv<V> {
  pub fn lookup_str(&mut self, name: &str) -> IName {
    self.ntbl.lookup_str(name)
  }

  pub fn rev_lookup_name(&self, name: IName) -> &str {
    self.ntbl.rev_lookup(name)
  }

  pub fn rev_lookup_top_level_var(&self, var: CVar) -> Option<&str> {
    let ivar = match self.v2i.borrow().get(&var) {
      None => return None,
      Some(&iv) => iv
    };
    match self.top.rbind.get(&ivar) {
      None => return None,
      Some(&(_, name)) => {
        Some(self.rev_lookup_name(name))
      }
    }
  }

  pub fn rev_lookup_top_level_num(&self, num: SNum) -> Option<&str> {
    self.rev_lookup_top_level_var(CVar(num))
  }

  pub fn pretty_print_num(&self, num: SNum) -> String {
    match self.rev_lookup_top_level_num(num) {
      None => {
        format!("#{}", num)
      }
      Some(s) => {
        s.to_string()
      }
    }
  }

  pub fn pretty_print_tup(&self, rel: SNum, tup: &[SNum]) -> String {
    let mut s = String::new();
    if rel == 1 || rel == -1 {
      assert_eq!(tup.len(), 2);
      s.push_str(&self.pretty_print_num(tup[0]));
      if rel == 1 {
        s.push_str(" = ");
      } else {
        s.push_str(" /= ");
      }
      s.push_str(&self.pretty_print_num(tup[1]));
      return s;
    }
    s.push_str(&self.pretty_print_num(rel));
    s.push_str("(");
    for (i, &t) in tup.iter().enumerate() {
      s.push_str(&self.pretty_print_num(t));
      if i + 1 < tup.len() {
        s.push_str(", ");
      }
    }
    s.push_str(")");
    s
  }

  pub fn pretty_print_def(&self, rel: SNum, tup: &[SNum]) -> String {
    let mut s = String::new();
    if rel == 1 || rel == -1 {
      assert_eq!(tup.len(), 2);
      s.push_str(&self.pretty_print_num(tup[0]));
      if rel == 1 {
        s.push_str(" = ");
      } else {
        s.push_str(" /= ");
      }
      s.push_str(&self.pretty_print_num(tup[1]));
      return s;
    }
    s.push_str(&self.pretty_print_num(rel));
    s.push_str("(");
    for (i, &t) in tup.iter().enumerate() {
      s.push_str(&self.pretty_print_num(t));
      if i + 2 == tup.len() {
        s.push_str(" -> ");
      } else if i + 1 < tup.len() {
        s.push_str(", ");
      }
    }
    s.push_str(")");
    s
  }

  pub fn pretty_print_def2(&self, rel: SNum, ltup: &[SNum], rtup: &[SNum]) -> String {
    assert_eq!(rtup.len(), 1);
    let mut s = String::new();
    if rel == 1 || rel == -1 {
      assert_eq!(ltup.len(), 1);
      s.push_str(&self.pretty_print_num(ltup[0]));
      if rel == 1 {
        s.push_str(" = ");
      } else {
        s.push_str(" /= ");
      }
      s.push_str(&self.pretty_print_num(rtup[0]));
      return s;
    }
    s.push_str(&self.pretty_print_num(rel));
    s.push_str("(");
    for (i, &t) in ltup.iter().enumerate() {
      s.push_str(&self.pretty_print_num(t));
      if i + 1 < ltup.len() {
        s.push_str(", ");
      }
    }
    s.push_str(" -> ");
    s.push_str(&self.pretty_print_num(rtup[0]));
    s.push_str(")");
    s
  }

  pub fn _bind_var(&self, ivar: IVar, var: CVar) {
    self.v2i.borrow_mut().insert(var, ivar);
  }

  pub fn fresh_var(&mut self) -> IVar {
    let new_v = self.vctr + 1;
    assert!(new_v > 0);
    self.vctr = new_v;
    IVar(new_v)
  }

  pub fn top_level_name(&mut self, name: IName) -> IVar {
    match self.top.lookup(name) {
      None => {
        let new_v = self.vctr + 1;
        assert!(new_v > 0);
        self.vctr = new_v;
        //self.top.insert(name.to_string(), IVar(new_v));
        self.top.bind_mut(IBinder::Top, name, IVar(new_v));
        IVar(new_v)
      }
      Some((IBinder::Top, v)) => v,
      Some((binder, _)) => {
        panic!("bug: ITheoryEnv::top_level_name: bad toplevel name: {:?} binder: {:?}", name, binder);
      }
    }
  }

  pub fn top_level_name_def(&mut self, name: IName) -> IVar {
    // FIXME
    //unimplemented!();
    self.top_level_name(name)
  }

  pub fn top_level_name_use(&mut self, name: IName) -> IVar {
    // FIXME
    //unimplemented!();
    self.top_level_name(name)
  }

  pub fn resolve_name(&mut self, name: IName, ctx: &ICtx) -> IVar {
  //pub fn resolve_name(&mut self, name: &str, ctx: &ICtx) -> (IBinder, IVar) {
    /*match ctx.bind.get(name) {
      None => {}
      Some(&(_, v)) => return v
    }
    match self.top.get(name) {
      None => panic!("bug: resolve_name: unbound name: {}", name),
      Some(&v) => v
    }*/
    match ctx.lookup(name) {
      Some((_, v)) => return v,
      None => {}
    }
    match self.top.lookup(name) {
      Some((IBinder::Top, v)) => v,
      //Some(_) => panic!("bug: ITheoryEnv::resolve_name: bad toplevel name: '{}'", name),
      Some((binder, _)) => panic!("bug: ITheoryEnv::resolve_name: bad toplevel name: {:?} binder: {:?}", name, binder),
      None => panic!("bug: ITheoryEnv::resolve_name: unbound name: {:?}", name),
    }
  }

  pub fn resolve_name_(&mut self, name: IName, ctx: &ICtx) -> (IBinder, IVar) {
    match ctx.lookup(name) {
      Some((binder, v)) => return (binder, v),
      None => {}
    }
    match self.top.lookup(name) {
      Some((IBinder::Top, v)) => (IBinder::Top, v),
      Some((binder, _)) => panic!("bug: ITheoryEnv::resolve_name_: bad toplevel name: {:?} binder: {:?}", name, binder),
      None => panic!("bug: ITheoryEnv::resolve_name_: unbound name: {:?}", name),
    }
  }
}

fn _lower_rel(rel: HRel, theory: &mut ITheoryEnv) -> IRel {
  let name = theory.lookup_str(&rel.name);
  let var = theory.top_level_name_def(name);
  assert!(!rel.quals.func);
  let mut schema = None;
  if !rel.quals.equiv && !rel.quals.symm && !rel.quals.cycl {
  } else if rel.quals.equiv {
    schema = Some(IRelSchema::Equivalence);
    match theory.eqn {
      None => {
        theory.eqn = Some(name);
      }
      Some(old_name) => {
        panic!("bug: _lower_rel: double equiv names: {:?} {:?}", old_name, name);
      }
    }
    match theory.eqv {
      None => {
        theory.eqv = Some(var);
      }
      Some(old_var) => {
        panic!("bug: _lower_rel: double equiv vars: {:?} {:?}", old_var, var);
      }
    }
  } else if rel.quals.symm && !rel.quals.cycl {
    schema = Some(IRelSchema::Symmetric);
  } else if !rel.quals.symm && rel.quals.cycl {
    schema = Some(IRelSchema::Cyclic);
  } else {
    panic!("bug: _lower_rel: invalid relation schema combo: {:?}", rel.quals);
  }
  IRel{
    name,
    var,
    arity:      rel.arity,
    funarity:   None,
    schema,
  }
}

fn _lower_fun(rel: HFun, theory: &mut ITheoryEnv) -> IRel {
  let name = theory.lookup_str(&rel.name);
  let var = theory.top_level_name_def(name);
  assert!(rel.quals.func);
  let mut schema = None;
  if !rel.quals.equiv && !rel.quals.symm && !rel.quals.cycl {
  } else if rel.quals.equiv {
    panic!("bug: _lower_fun: functions cannot be equivalence relations");
  } else if rel.quals.symm && !rel.quals.cycl {
    schema = Some(IRelSchema::Symmetric);
  } else if !rel.quals.symm && rel.quals.cycl {
    schema = Some(IRelSchema::Cyclic);
  } else {
    panic!("bug: _lower_fun: invalid relation schema combo: {:?}", rel.quals);
  }
  IRel{
    name,
    var,
    arity:      rel.l_arity + rel.r_arity,
    funarity:   Some((rel.l_arity, rel.r_arity)),
    schema,
  }
}

fn _lower_exp(e: HExp, theory: &mut ITheoryEnv) -> IExp {
  let this = theory.fresh_loc();
  let dbginfo = e.clone().into();
  theory.set_debuginfo(this, dbginfo);
  match e {
    HExp::Group(inner, _spaninfo) => {
      let inner = Rc::try_unwrap(inner.0).unwrap_or_else(|e| (&*e).clone());
      // FIXME: preserve group loc/dbginfo?
      _lower_exp(inner, theory)
    }
    HExp::Term(term, _spaninfo) => {
      let term = match term {
        //HTerm::Place => ITerm::Place,
        HTerm::Name(name) => ITerm::Name(theory.lookup_str(&name)),
      };
      IExp::Term(this, term)
    }
    HExp::App(fun, args, _spaninfo) => {
      let fun = Rc::try_unwrap(fun.0).unwrap_or_else(|e| (&*e).clone());
      let fun = _lower_exp(fun, theory);
      let mut args_ = Vec::with_capacity(args.len());
      for arg in args.into_iter() {
        //let arg = Rc::try_unwrap(arg.0).unwrap_or_else(|e| (&*e).clone());
        args_.push(_lower_exp(arg, theory));
      }
      IExp::App(this, fun.into(), args_)
    }
    _ => unimplemented!()
  }
}

fn _lower_atomic_form(f: HAtomicForm, theory: &mut ITheoryEnv) -> IAtomicForm {
  let this = theory.fresh_loc();
  let dbginfo = f.clone().into();
  theory.set_debuginfo(this, dbginfo);
  match f {
    HAtomicForm::Pre(f) => {
      let mut exps = Vec::with_capacity(f.exps.len());
      for exp in f.exps.into_iter() {
        exps.push(_lower_exp(exp, theory));
      }
      IAtomicForm::Pre(this, theory.lookup_str(&f.rel_name).into(), exps)
    }
    HAtomicForm::App(f) => {
      let mut lexps = Vec::with_capacity(f.lexps.len());
      let mut rexps = Vec::with_capacity(f.rexps.len());
      for exp in f.lexps.into_iter() {
        lexps.push(_lower_exp(exp, theory));
      }
      for exp in f.rexps.into_iter() {
        rexps.push(_lower_exp(exp, theory));
      }
      IAtomicForm::App(this, theory.lookup_str(&f.rel_name).into(), lexps, rexps)
    }
    HAtomicForm::Dom(f) => {
      let mut lexps = Vec::with_capacity(f.lexps.len());
      for exp in f.lexps.into_iter() {
        lexps.push(_lower_exp(exp, theory));
      }
      IAtomicForm::Dom(this, theory.lookup_str(&f.rel_name).into(), lexps)
    }
    HAtomicForm::Img(f) => {
      let mut rexps = Vec::with_capacity(f.rexps.len());
      for exp in f.rexps.into_iter() {
        rexps.push(_lower_exp(exp, theory));
      }
      IAtomicForm::Img(this, theory.lookup_str(&f.rel_name).into(), rexps)
    }
  }
}

enum OrderClass {
  Equal,
  Less,
  Greater,
}

fn _lower_clausal_form(f: HClausalForm, theory: &mut ITheoryEnv) -> Vec<IClausalForm> {
  let this = theory.fresh_loc();
  let dbginfo = f.clone().into();
  theory.set_debuginfo(this, dbginfo);
  match f {
    HClausalForm::Lit(neg, atom, _spaninfo) => {
      let atom = _lower_atomic_form(atom, theory);
      vec![IClausalForm::Lit(this, neg, atom)]
    }
    HClausalForm::Xeq(lexp, rexps, _spaninfo) => {
      let mut equal = false;
      let mut not_equal = 0;
      let mut less = false;
      let mut greater = false;
      for &(o, _) in rexps.iter() {
        match o {
          HOrder::Equal => {
            equal = true;
          }
          HOrder::NotEqual => {
            equal = true;
            not_equal += 1;
          }
          HOrder::Less |
          HOrder::LessEqual => {
            less = true;
          }
          HOrder::Greater |
          HOrder::GreaterEqual => {
            greater = true;
          }
          HOrder::NotLess |
          HOrder::NotLessEqual |
          HOrder::NotGreater |
          HOrder::NotGreaterEqual => {
            panic!("bug: unimplemented: negations of orderings");
          }
        }
      }
      let klass = if equal && not_equal <= 1 && !less && !greater {
        OrderClass::Equal
      } else if not_equal == 0 && less && !greater {
        OrderClass::Less
      } else if not_equal == 0 && !less && greater {
        OrderClass::Greater
      } else {
        panic!("bug: ambiguous order classification");
      };
      match klass {
        OrderClass::Equal => {
          let mut forms = Vec::with_capacity(rexps.len());
          let mut lexp = _lower_exp(lexp, theory);
          for (ro, rexp) in rexps.into_iter() {
            // FIXME
            //let dbginfo = Some(rexp.clone().into());
            let this = theory.fresh_loc();
            let rexp = _lower_exp(rexp, theory);
            match ro {
              HOrder::Equal => {
                forms.push(IClausalForm::Eq_(this, lexp, rexp.clone()));
              }
              HOrder::NotEqual => {
                forms.push(IClausalForm::Neq(this, lexp, rexp.clone()));
              }
              _ => unreachable!()
            };
            lexp = rexp;
          }
          forms
        }
        OrderClass::Less => {
          let mut forms = Vec::with_capacity(rexps.len());
          let mut lexp = _lower_exp(lexp, theory);
          for (ro, rexp) in rexps.into_iter() {
            // FIXME
            //let dbginfo = Some(rexp.clone().into());
            let this = theory.fresh_loc();
            let rexp = _lower_exp(rexp, theory);
            match ro {
              HOrder::Equal => {
                forms.push(IClausalForm::Eq_(this, lexp, rexp.clone()));
              }
              HOrder::Less => {
                forms.push(IClausalForm::Lt_(this, lexp, rexp.clone()));
              }
              HOrder::LessEqual => {
                forms.push(IClausalForm::Lte(this, lexp, rexp.clone()));
              }
              _ => unreachable!()
            };
            lexp = rexp;
          }
          forms
        }
        OrderClass::Greater => {
          // NB: Reversal is OK here.
          let mut forms = Vec::with_capacity(rexps.len());
          let llexp = _lower_exp(lexp, theory);
          let mut ro = None;
          let mut rexp = None;
          for (o, lexp) in rexps.into_iter().rev() {
            // FIXME
            //let dbginfo = Some(lexp.clone().into());
            let this = theory.fresh_loc();
            let lexp = _lower_exp(lexp, theory);
            let rexp_ = match rexp.take() {
              None => {
                ro = Some(o);
                rexp = Some(lexp);
                continue;
              }
              Some(rexp_) => rexp_
            };
            match ro {
              Some(HOrder::Equal) => {
                forms.push(IClausalForm::Eq_(this, rexp_, lexp.clone()));
              }
              Some(HOrder::Greater) => {
                forms.push(IClausalForm::Lt_(this, rexp_, lexp.clone()));
              }
              Some(HOrder::GreaterEqual) => {
                forms.push(IClausalForm::Lte(this, rexp_, lexp.clone()));
              }
              _ => unreachable!()
            };
            ro = Some(o);
            rexp = Some(lexp);
          }
          let this = theory.fresh_loc();
          match (ro, rexp) {
            (Some(HOrder::Equal), Some(rexp_)) => {
              forms.push(IClausalForm::Eq_(this, rexp_, llexp));
            }
            (Some(HOrder::Greater), Some(rexp_)) => {
              forms.push(IClausalForm::Lt_(this, rexp_, llexp));
            }
            (Some(HOrder::GreaterEqual), Some(rexp_)) => {
              forms.push(IClausalForm::Lte(this, rexp_, llexp));
            }
            _ => unreachable!()
          }
          forms
        }
      }
    }
  }
}

fn _lower_rec_form(f: HRecForm, theory: &mut ITheoryEnv) -> IRecForm {
  let this = theory.fresh_loc();
  let dbginfo = f.clone().into();
  theory.set_debuginfo(this, dbginfo);
  match f {
    HRecForm::Con(f) => {
      let mut ante = Vec::with_capacity(f.ante.len());
      let mut cons = Vec::with_capacity(f.cons.len());
      for g in f.ante.into_iter() {
        ante.extend(_lower_form(g, theory));
      }
      for g in f.cons.into_iter() {
        cons.extend(_lower_form(g, theory));
      }
      IRecForm::C(this, f.bicond, ante, cons)
    }
    HRecForm::Qua(f) => {
      let quant = match f.quant {
        HQuant::Universal => IBinder::Universal,
        HQuant::Definitive => IBinder::Definitive,
        HQuant::Existential => IBinder::Existential,
        HQuant::Nonexistential => unimplemented!(),
      };
      let term = match f.q_term {
        //HTerm::Place => ITerm::Place,
        HTerm::Name(name) => ITerm::Name(theory.lookup_str(&name)),
      };
      let nested = Rc::try_unwrap(f.nested).unwrap_or_else(|g| (&*g).clone());
      IRecForm::Q(this, quant, term, _lower_rec_form(nested, theory).into())
    }
  }
}

fn _lower_form(f: HForm, theory: &mut ITheoryEnv) -> Vec<IForm> /*IForm*/ {
  let this = theory.fresh_loc();
  let dbginfo = f.clone().into();
  theory.set_debuginfo(this, dbginfo);
  match f {
    HForm::Cla(f, _spaninfo) => {
      let forms = _lower_clausal_form(f, theory);
      let mut forms_ = Vec::with_capacity(forms.len());
      for f in forms.into_iter() {
        //let dbginfo = Some(f.clone().into());
        forms_.push(IForm::Cla(theory.fresh_loc(), f));
      }
      forms_
    }
    HForm::Con(_, _spaninfo) => {
      // FIXME
      unimplemented!();
    }
    HForm::Rec(f, _spaninfo) => {
      vec![IForm::Rec(this, _lower_rec_form(f, theory))]
    }
  }
}

fn _lower_new_theory(decls: Vec<HTheoryDecl>, progs: Vec<HProgram>, theory: &mut ITheoryEnv) {
  for decl in decls.into_iter() {
    match decl {
      //HTheoryDecl::Top => unreachable!(),
      HTheoryDecl::Rel(rel) => {
        let rel = _lower_rel(rel, theory);
        theory.rels.insert(theory.rels.len(), rel);
      }
      HTheoryDecl::Fun(fun) => {
        let rel = _lower_fun(fun, theory);
        theory.rels.insert(theory.rels.len(), rel);
      }
      HTheoryDecl::Rec(_name, f) => {
        let rec = _lower_rec_form(f, theory);
        theory.recs.insert(theory.recs.len(), rec);
      }
    }
  }
  for prog in progs.into_iter() {
    match prog {
      HProgram::Let(names) => {
        for name in names.into_iter() {
          let name = theory.lookup_str(&name);
          let _ = theory.top_level_name_def(name);
        }
      }
      HProgram::Where(cons) => {
        let mut cons_ = Vec::with_capacity(cons.len());
        for f in cons.into_iter() {
          cons_.extend(_lower_form(f, theory));
        }
        let rec = IRecForm::C(theory.fresh_loc(), false, Vec::new(), cons_);
        theory.recs.insert(theory.recs.len(), rec);
      }
      HProgram::Propose(cons) => {
        for f in cons.into_iter() {
          for f in _lower_form(f, theory).into_iter() {
            match f {
              IForm::Cla(loc, clausal_f) => {
                if log_trace() {
                  println!("TRACE: _lower_new_theory: prop form");
                }
                let free_loc = theory.fresh_loc();
                theory.unify_debuglocs(loc, free_loc);
                let free_f = IForm::Fre(free_loc, clausal_f);
                theory.prop.insert(theory.prop.len(), free_f);
              }
              IForm::Fre(..) => {
                panic!("bug: _lower_new_theory: early free prop form");
              }
              _ => {
                panic!("bug: _lower_new_theory: non-clausal prop form");
              }
            }
          }
        }
      }
    }
  }
}

pub fn lower_new_theory(htree: HTree, mut theory: ITheoryEnv) -> ITheoryEnv {
  match htree {
    HTree::Theory{decl, prog} => {
      _lower_new_theory(decl, prog, &mut theory);
      theory
    }
    //_ => unimplemented!()
  }
}

fn _flatten_rec_form(f: IRecForm, theory: &mut ITheoryEnv) -> IRecForm {
  match f {
    IRecForm::C(this, bicond, ante, cons) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let mut ante_ = Vec::new();
      let mut cons_ = Vec::new();
      for f in ante.into_iter() {
        _flatten_con_form(f, &mut ante_, theory);
      }
      for f in cons.into_iter() {
        _flatten_con_form(f, &mut cons_, theory);
      }
      IRecForm::C(that, bicond, ante_, cons_)
    }
    IRecForm::Q(this, binder, term, nested) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let nested = Rc::try_unwrap(nested).unwrap_or_else(|g| (&*g).clone());
      let nested = _flatten_rec_form(nested, theory);
      IRecForm::Q(that, binder, term, nested.into())
    }
    _ => unimplemented!()
  }
}

fn _flatten_con_form(f: IForm, con: &mut Vec<IForm>, theory: &mut ITheoryEnv) {
  match f {
    IForm::Con(_, fs) => {
      for f in fs.into_iter() {
        _flatten_con_form(f, con, theory);
      }
    }
    IForm::Cla(..) |
    IForm::Fre(..) |
    IForm::Rec(..) => {
      con.push(_flatten_form(f, theory));
    }
  }
}

fn _flatten_form(f: IForm, theory: &mut ITheoryEnv) -> IForm {
  match f {
    IForm::Cla(..) |
    IForm::Fre(..) => {
      f
    }
    IForm::Con(this, fs) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let mut con = Vec::new();
      for f in fs.into_iter() {
        _flatten_con_form(f, &mut con, theory);
      }
      IForm::Con(that, con)
    }
    IForm::Rec(this, f) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let f = _flatten_rec_form(f, theory);
      IForm::Rec(that, f)
    }
  }
}

pub fn flatten_new_theory(mut theory: ITheoryEnv) -> ITheoryEnv {
  let mut recs = HTreapMap::default();
  let mut prop = HTreapMap::default();
  for (&idx, f) in theory.recs.clone().iter() {
    let f = _flatten_rec_form(f.clone(), &mut theory);
    recs.insert(idx, f);
  }
  for (&idx, f) in theory.prop.clone().iter() {
    let f = _flatten_form(f.clone(), &mut theory);
    prop.insert(idx, f);
  }
  theory.recs = recs;
  theory.prop = prop;
  theory
}

fn _index0_exp(e: IExp, ctx: ICtx, theory: &mut ITheoryEnv) -> IExp {
  match e {
    IExp::Term(this, term) => {
      theory.set_ctx(this, ctx);
      IExp::Term(this, term)
    }
    IExp::App(this, fun, args) => {
      // TODO
      theory.set_ctx(this, ctx);
      unimplemented!();
    }
    _ => unimplemented!()
  }
}

fn _index0_atomic_form(f: IAtomicForm, ctx: ICtx, theory: &mut ITheoryEnv) -> IAtomicForm {
  match f {
    IAtomicForm::Pre(this, rel, exps) => {
      let mut exps_ = Vec::with_capacity(exps.len());
      for e in exps.into_iter() {
        exps_.push(_index0_exp(e, ctx.clone(), theory));
      }
      theory.set_ctx(this, ctx);
      IAtomicForm::Pre(this, rel, exps_)
    }
    IAtomicForm::App(this, rel, lexps, rexps) => {
      let mut lexps_ = Vec::with_capacity(lexps.len());
      let mut rexps_ = Vec::with_capacity(rexps.len());
      for e in lexps.into_iter() {
        lexps_.push(_index0_exp(e, ctx.clone(), theory));
      }
      for e in rexps.into_iter() {
        rexps_.push(_index0_exp(e, ctx.clone(), theory));
      }
      theory.set_ctx(this, ctx);
      IAtomicForm::App(this, rel, lexps_, rexps_)
    }
    IAtomicForm::Img(this, rel, rexps) => {
      let mut rexps_ = Vec::with_capacity(rexps.len());
      for e in rexps.into_iter() {
        rexps_.push(_index0_exp(e, ctx.clone(), theory));
      }
      theory.set_ctx(this, ctx);
      IAtomicForm::Img(this, rel, rexps_)
    }
    _ => unimplemented!()
  }
}

fn _index0_clausal_form(f: IClausalForm, ctx: ICtx, theory: &mut ITheoryEnv) -> IClausalForm {
  match f {
    IClausalForm::Lit(this, neg, atom) => {
      let atom = _index0_atomic_form(atom, ctx.clone(), theory);
      theory.set_ctx(this, ctx);
      IClausalForm::Lit(this, neg, atom)
    }
    IClausalForm::Eq_(this, lexp, rexp) => {
      let lexp = _index0_exp(lexp, ctx.clone(), theory);
      let rexp = _index0_exp(rexp, ctx.clone(), theory);
      theory.set_ctx(this, ctx);
      IClausalForm::Eq_(this, lexp, rexp)
    }
    IClausalForm::Neq(this, lexp, rexp) => {
      let lexp = _index0_exp(lexp, ctx.clone(), theory);
      let rexp = _index0_exp(rexp, ctx.clone(), theory);
      theory.set_ctx(this, ctx);
      IClausalForm::Neq(this, lexp, rexp)
    }
    IClausalForm::Lt_(this, lexp, rexp) => {
      let lexp = _index0_exp(lexp, ctx.clone(), theory);
      let rexp = _index0_exp(rexp, ctx.clone(), theory);
      theory.set_ctx(this, ctx);
      IClausalForm::Lt_(this, lexp, rexp)
    }
    IClausalForm::Lte(this, lexp, rexp) => {
      let lexp = _index0_exp(lexp, ctx.clone(), theory);
      let rexp = _index0_exp(rexp, ctx.clone(), theory);
      theory.set_ctx(this, ctx);
      IClausalForm::Lte(this, lexp, rexp)
    }
    //_ => unimplemented!()
  }
}

fn _index0_rec_form(f: IRecForm, ctx: ICtx, theory: &mut ITheoryEnv) -> IRecForm {
  // TODO
  match f {
    IRecForm::C(this, bicond, ante, cons) => {
      let mut ante_ = Vec::with_capacity(ante.len());
      let mut cons_ = Vec::with_capacity(cons.len());
      for g in ante.into_iter() {
        ante_.push(_index0_form(g, ctx.clone(), theory));
      }
      for g in cons.into_iter() {
        cons_.push(_index0_form(g, ctx.clone(), theory));
      }
      theory.set_ctx(this, ctx);
      IRecForm::C(this, bicond, ante_, cons_)
    }
    IRecForm::Q(this, binder, term, nested) => {
      let nested_ctx = match &term {
        &ITerm::Name(name) => {
          ctx.clone().bind(binder, name, theory.fresh_var())
        }
        &ITerm::FVar(..) => unimplemented!(),
        &ITerm::RVar(name, v) => {
          ctx.clone().bind(binder, name, v)
        }
        &ITerm::Var(v) => {
          // FIXME: check for preexisting binding.
          ctx.clone().anon_bind(binder, v)
        }
      };
      let nested = Rc::try_unwrap(nested).unwrap_or_else(|g| (&*g).clone());
      theory.set_ctx(this, ctx);
      IRecForm::Q(this, binder, term, _index0_rec_form(nested, nested_ctx, theory).into())
    }
    IRecForm::P(this, prefix) => {
      // FIXME
      let mut inside_ctx = ctx.clone();
      for term in prefix.uparams.iter() {
        let binder = IBinder::Universal;
        match term {
          &ITerm::Name(name) => {
            inside_ctx.bind_mut(binder, name.clone(), theory.fresh_var());
          }
          &ITerm::FVar(..) => unimplemented!(),
          &ITerm::RVar(name, v) => {
            inside_ctx.bind_mut(binder, name, v);
          }
          &ITerm::Var(v) => {
            inside_ctx.anon_bind_mut(binder, v);
          }
        }
      }
      for term in prefix.dparams.iter() {
        let binder = IBinder::Definitive;
        match term {
          &ITerm::Name(name) => {
            inside_ctx.bind_mut(binder, name.clone(), theory.fresh_var());
          }
          &ITerm::FVar(..) => unimplemented!(),
          &ITerm::RVar(name, v) => {
            inside_ctx.bind_mut(binder, name, v);
          }
          &ITerm::Var(v) => {
            inside_ctx.anon_bind_mut(binder, v);
          }
        }
      }
      for term in prefix.xparams.iter() {
        let binder = IBinder::Existential;
        match term {
          &ITerm::Name(name) => {
            inside_ctx.bind_mut(binder, name.clone(), theory.fresh_var());
          }
          &ITerm::FVar(..) => unimplemented!(),
          &ITerm::RVar(name, v) => {
            inside_ctx.bind_mut(binder, name, v);
          }
          &ITerm::Var(v) => {
            inside_ctx.anon_bind_mut(binder, v);
          }
        }
      }
      let mut ante_ = Vec::with_capacity(prefix.ante.len());
      let mut cons_ = Vec::with_capacity(prefix.cons.len());
      for f in prefix.ante.into_iter() {
        ante_.push(_index0_form(f, inside_ctx.clone(), theory));
      }
      for f in prefix.cons.into_iter() {
        cons_.push(_index0_form(f, inside_ctx.clone(), theory));
      }
      let prefix = IPrefixRecForm{
        //tvars:      _,
        uparams:    prefix.uparams,
        dparams:    prefix.dparams,
        xparams:    prefix.xparams,
        bicond:     prefix.bicond,
        ante:       ante_,
        cons:       cons_,
      };
      theory.set_ctx(this, ctx);
      IRecForm::P(this, prefix)
    }
    _ => unimplemented!()
  }
}

fn _index0_form(f: IForm, ctx: ICtx, theory: &mut ITheoryEnv) -> IForm {
  match f {
    IForm::Cla(this, f) => {
      let f = _index0_clausal_form(f, ctx.clone(), theory);
      theory.set_ctx(this, ctx);
      IForm::Cla(this, f)
    }
    IForm::Con(..) => {
      unimplemented!();
    }
    IForm::Fre(this, f) => {
      let f = _index0_clausal_form(f, ctx.clone(), theory);
      theory.set_ctx(this, ctx);
      IForm::Fre(this, f)
    }
    IForm::Rec(this, f) => {
      let f = _index0_rec_form(f, ctx.clone(), theory);
      theory.set_ctx(this, ctx);
      IForm::Rec(this, f)
    }
  }
}

//pub fn index0_new_theory<V: Clone>(mut theory: ITheoryEnv<V>) -> ITheoryEnv<ICtx> {
pub fn index0_new_theory(mut theory: ITheoryEnv) -> ITheoryEnv {
  let mut recs = HTreapMap::default();
  let mut prop = HTreapMap::default();
  for (&idx, f) in theory.recs.clone().iter() {
    let ctx = ICtx::empty();
    let f = _index0_rec_form(f.clone(), ctx, &mut theory);
    recs.insert(idx, f);
  }
  for (&idx, f) in theory.prop.clone().iter() {
    let ctx = ICtx::empty();
    let f = _index0_form(f.clone(), ctx, &mut theory);
    prop.insert(idx, f);
  }
  /*theory.recs = recs;
  theory.prop = prop;
  theory*/
  ITheoryEnv{
    ntbl:   theory.ntbl,
    ltbl:   theory.ltbl,
    vctr:   theory.vctr,
    v2i:    theory.v2i.clone(),
    eqn:    theory.eqn,
    eqv:    theory.eqv,
    top:    theory.top,
    rels:   theory.rels,
    //cats:   theory.cats,
    recs,
    prop,
  }
}

fn _resolve_exp(e: IExp, theory: &mut ITheoryEnv) -> IExp {
  match e {
    IExp::Term(this, term) => {
      let ctx = theory.ctx(this);
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      match term {
        //ITerm::Place => unimplemented!(),
        ITerm::Name(name) => {
          match ctx.lookup(name) {
            Some((_, var)) => {
              IExp::RVar(that, var)
            }
            None => {
              let var = theory.top_level_name_use(name);
              IExp::RVar(that, var)
            }
          }
        }
        ITerm::FVar(..) => unimplemented!(),
        ITerm::RVar(name, var) => {
          IExp::RVar(that, var)
        }
        ITerm::Var(var) => {
          // FIXME
          //panic!("bug: _resolve_exp: var termexp");
          IExp::RVar(that, var)
        }
      }
    }
    IExp::App(this, fun, args) => {
      // TODO
      unimplemented!();
    }
    _ => unimplemented!()
  }
}

fn _resolve_atomic_form(f: IAtomicForm, theory: &mut ITheoryEnv) -> IAtomicForm {
  match f {
    IAtomicForm::Pre(this, rel, exps) => {
      // FIXME
      let ctx = theory.ctx(this);
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let rel_var = match &rel {
        &ITerm::Name(name) => theory.resolve_name(name, &ctx),
        &ITerm::FVar(..) => unimplemented!(),
        //&ITerm::RVar(_, v) => v,
        &ITerm::RVar(name, _) => theory.resolve_name(name, &ctx),
        &ITerm::Var(v) => v,
      };
      let mut exps_ = Vec::with_capacity(exps.len());
      let mut args = Vec::with_capacity(exps.len());
      for e in exps.into_iter() {
        let e = _resolve_exp(e, theory);
        match e {
          IExp::RVar(_, v) => args.push(v),
          _ => {}
        }
        exps_.push(e);
      }
      if exps_.len() == args.len() {
        IAtomicForm::RPre(that, rel_var, args)
      } else {
        IAtomicForm::Pre(that, rel, exps_)
      }
    }
    IAtomicForm::App(this, rel, lexps, rexps) => {
      // FIXME
      let ctx = theory.ctx(this);
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let rel_var = match &rel {
        &ITerm::Name(name) => theory.resolve_name(name, &ctx),
        &ITerm::FVar(..) => unimplemented!(),
        //&ITerm::RVar(_, v) => v,
        &ITerm::RVar(name, _) => theory.resolve_name(name, &ctx),
        &ITerm::Var(v) => v,
      };
      let mut lexps_ = Vec::with_capacity(lexps.len());
      let mut rexps_ = Vec::with_capacity(rexps.len());
      let mut largs = Vec::with_capacity(lexps.len());
      let mut rargs = Vec::with_capacity(rexps.len());
      for e in lexps.into_iter() {
        let e = _resolve_exp(e, theory);
        match e {
          IExp::RVar(_, v) => largs.push(v),
          _ => {}
        }
        lexps_.push(e);
      }
      for e in rexps.into_iter() {
        let e = _resolve_exp(e, theory);
        match e {
          IExp::RVar(_, v) => rargs.push(v),
          _ => {}
        }
        rexps_.push(e);
      }
      if lexps_.len() == largs.len() && rexps_.len() == rargs.len() {
        IAtomicForm::RApp(that, rel_var, largs, rargs)
      } else {
        IAtomicForm::App(that, rel, lexps_, rexps_)
      }
    }
    _ => unimplemented!()
  }
}

fn _resolve_clausal_form(f: IClausalForm, theory: &mut ITheoryEnv) -> IClausalForm {
  match f {
    IClausalForm::Lit(this, neg, atom) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let atom = _resolve_atomic_form(atom, theory);
      IClausalForm::Lit(that, neg, atom)
    }
    IClausalForm::Eq_(this, lexp, rexp) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let lexp = _resolve_exp(lexp, theory);
      let rexp = _resolve_exp(rexp, theory);
      IClausalForm::Eq_(that, lexp, rexp)
    }
    IClausalForm::Neq(this, lexp, rexp) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let lexp = _resolve_exp(lexp, theory);
      let rexp = _resolve_exp(rexp, theory);
      IClausalForm::Neq(that, lexp, rexp)
    }
    IClausalForm::Lt_(this, lexp, rexp) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let lexp = _resolve_exp(lexp, theory);
      let rexp = _resolve_exp(rexp, theory);
      IClausalForm::Lt_(that, lexp, rexp)
    }
    IClausalForm::Lte(this, lexp, rexp) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let lexp = _resolve_exp(lexp, theory);
      let rexp = _resolve_exp(rexp, theory);
      IClausalForm::Lte(that, lexp, rexp)
    }
    //_ => unimplemented!()
  }
}

fn _resolve_rec_form(f: IRecForm, theory: &mut ITheoryEnv) -> IRecForm {
  match f {
    IRecForm::C(this, bicond, ante, cons) => {
      // TODO
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let mut ante_ = Vec::with_capacity(ante.len());
      let mut cons_ = Vec::with_capacity(cons.len());
      for g in ante.into_iter() {
        ante_.push(_resolve_form(g, theory));
      }
      for g in cons.into_iter() {
        cons_.push(_resolve_form(g, theory));
      }
      theory.copy_ctx(this, that);
      IRecForm::C(that, bicond, ante_, cons_)
    }
    IRecForm::Q(this, binder, term, nested) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let nested = Rc::try_unwrap(nested).unwrap_or_else(|g| (&*g).clone());
      match _resolve_rec_form(nested, theory) {
        IRecForm::C(this2, bicond, ante, cons) => {
          let ctx2 = theory.ctx(this2);
          let that2 = theory.fresh_loc();
          theory.unify_debuglocs(this2, that2);
          let maybe_var = match term {
            //ITerm::Place => None,
            ITerm::Name(name) => ctx2.lookup(name).map(|(_, v)| v),
            ITerm::FVar(..) => unimplemented!(),
            ITerm::RVar(_, v) => Some(v),
            // FIXME
            ITerm::Var(v) => panic!("bug"),
          };
          let var = match maybe_var {
            None => panic!("bug"),
            Some(v) => v
          };
          theory.copy_ctx(this2, that2);
          theory.copy_ctx(this, that);
          IRecForm::RQs(that, vec![(binder, var)].into(), IRecForm::C(that2, bicond, ante, cons).into())
        }
        IRecForm::Q(..) => {
          unimplemented!();
        }
        IRecForm::P(..) => {
          unimplemented!();
        }
        IRecForm::RQs(this2, mut bvars, nested2) => {
          let ctx2 = theory.ctx(this2);
          let maybe_var = match term {
            //ITerm::Place => None,
            ITerm::Name(name) => ctx2.lookup(name).map(|(_, v)| v),
            ITerm::FVar(..) => unimplemented!(),
            ITerm::RVar(_, v) => Some(v),
            // FIXME
            ITerm::Var(v) => panic!("bug"),
          };
          let var = match maybe_var {
            None => panic!("bug"),
            Some(v) => v
          };
          bvars.push_front((binder, var));
          theory.copy_ctx(this, that);
          IRecForm::RQs(that, bvars, nested2)
        }
        IRecForm::RPC(..) => {
          unimplemented!();
        }
      }
    }
    IRecForm::P(this, prefix) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let mut ante = Vec::with_capacity(prefix.ante.len());
      let mut cons = Vec::with_capacity(prefix.cons.len());
      for g in prefix.ante.into_iter() {
        ante.push(_resolve_form(g, theory));
      }
      for g in prefix.cons.into_iter() {
        cons.push(_resolve_form(g, theory));
      }
      let prefix = IPrefixRecForm{
        uparams:    prefix.uparams,
        dparams:    prefix.dparams,
        xparams:    prefix.xparams,
        bicond:     prefix.bicond,
        ante,
        cons,
      };
      IRecForm::P(that, prefix)
    }
    IRecForm::RQs(this, bvars, nested) => {
      // TODO
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let nested = Rc::try_unwrap(nested).unwrap_or_else(|g| (&*g).clone());
      match nested {
        IRecForm::C(..) => {
          theory.copy_ctx(this, that);
          IRecForm::RQs(that, bvars, _resolve_rec_form(nested, theory).into())
        }
        IRecForm::Q(..) => {
          unimplemented!();
        }
        IRecForm::P(..) => {
          unimplemented!();
        }
        IRecForm::RQs(..) => {
          unimplemented!();
        }
        IRecForm::RPC(..) => {
          unimplemented!();
        }
      }
    }
    IRecForm::RPC(..) => {
      unimplemented!();
    }
  }
}

fn _resolve_form(f: IForm, theory: &mut ITheoryEnv) -> IForm {
  match f {
    IForm::Cla(this, f) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let f = _resolve_clausal_form(f, theory);
      IForm::Cla(that, f)
    }
    IForm::Con(..) => {
      unimplemented!();
    }
    IForm::Fre(this, f) => {
      // FIXME: check bound.
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let f = _resolve_clausal_form(f, theory);
      IForm::Fre(that, f)
    }
    IForm::Rec(this, f) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let f = _resolve_rec_form(f, theory);
      IForm::Rec(that, f)
    }
  }
}

pub fn resolve_new_theory(mut theory: ITheoryEnv) -> ITheoryEnv {
  let mut recs = HTreapMap::default();
  let mut prop = HTreapMap::default();
  for (&idx, f) in theory.recs.clone().iter() {
    let f = _resolve_rec_form(f.clone(), &mut theory);
    recs.insert(idx, f);
  }
  for (&idx, f) in theory.prop.clone().iter() {
    let f = _resolve_form(f.clone(), &mut theory);
    prop.insert(idx, f);
  }
  theory.recs = recs;
  theory.prop = prop;
  theory
}

fn _resolve2_exp(ctx: ICtx, e: IExp, theory: &mut ITheoryEnv) -> IExp {
  match e {
    IExp::Term(this, term) => {
      match term {
        ITerm::FVar(name, v) => {
          panic!("bug: _resolve2_exp: FVar in exp position: {:?} {:?}", name, v);
        }
        ITerm::Name(name) |
        ITerm::RVar(name, _) => {
          let that = theory.fresh_loc();
          theory.unify_debuglocs(this, that);
          let v = theory.resolve_name(name, &ctx);
          theory.set_ctx(that, ctx);
          IExp::Term(that, ITerm::RVar(name, v))
        }
        ITerm::Var(_) => {
          let that = theory.fresh_loc();
          theory.unify_debuglocs(this, that);
          theory.set_ctx(that, ctx);
          IExp::Term(that, term)
        }
      }
    }
    IExp::Desc(..) => {
      panic!("bug: _resolve2_exp: unnormalized Desc exp");
    }
    IExp::Bind(..) => {
      panic!("bug: _resolve2_exp: unnormalized Bind exp");
    }
    _ => unimplemented!()
  }
}

fn _resolve2_atomic_form(ctx: ICtx, f: IAtomicForm, theory: &mut ITheoryEnv) -> IAtomicForm {
  match f {
    IAtomicForm::Pre(this, rel, args) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let rel = match rel {
        ITerm::FVar(name, v) => {
          panic!("bug: _resolve2_atomic_form: FVar in form position: {:?} {:?}", name, v);
        }
        ITerm::Name(name) |
        ITerm::RVar(name, _) => {
          let v = theory.resolve_name(name, &ctx);
          ITerm::RVar(name, v)
        }
        ITerm::Var(_) => {
          rel
        }
      };
      let mut args_ = Vec::with_capacity(args.len());
      for e in args.into_iter() {
        args_.push(_resolve2_exp(ctx.clone(), e, theory));
      }
      theory.set_ctx(that, ctx);
      IAtomicForm::Pre(that, rel, args_)
    }
    IAtomicForm::App(this, fun, largs, rargs) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let fun = match fun {
        ITerm::FVar(name, v) => {
          panic!("bug: _resolve2_atomic_form: FVar in form position: {:?} {:?}", name, v);
        }
        ITerm::Name(name) |
        ITerm::RVar(name, _) => {
          let v = theory.resolve_name(name, &ctx);
          ITerm::RVar(name, v)
        }
        ITerm::Var(_) => {
          fun
        }
      };
      let mut largs_ = Vec::with_capacity(largs.len());
      let mut rargs_ = Vec::with_capacity(rargs.len());
      for e in largs.into_iter() {
        largs_.push(_resolve2_exp(ctx.clone(), e, theory));
      }
      for e in rargs.into_iter() {
        rargs_.push(_resolve2_exp(ctx.clone(), e, theory));
      }
      theory.set_ctx(that, ctx);
      IAtomicForm::App(that, fun, largs_, rargs_)
    }
    _ => unimplemented!()
  }
}

fn _resolve2_clausal_form(ctx: ICtx, f: IClausalForm, theory: &mut ITheoryEnv) -> IClausalForm {
  match f {
    IClausalForm::Lit(this, neg, atom) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let atom = _resolve2_atomic_form(ctx.clone(), atom, theory);
      theory.set_ctx(that, ctx);
      IClausalForm::Lit(that, neg, atom)
    }
    IClausalForm::Eq_(this, lhs, rhs) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let lhs = _resolve2_exp(ctx.clone(), lhs, theory);
      let rhs = _resolve2_exp(ctx.clone(), rhs, theory);
      theory.set_ctx(that, ctx);
      IClausalForm::Eq_(that, lhs, rhs)
    }
    IClausalForm::Neq(this, lhs, rhs) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let lhs = _resolve2_exp(ctx.clone(), lhs, theory);
      let rhs = _resolve2_exp(ctx.clone(), rhs, theory);
      theory.set_ctx(that, ctx);
      IClausalForm::Neq(that, lhs, rhs)
    }
    _ => unimplemented!()
  }
}

fn _resolve2_rec_form(ctx: ICtx, f: IRecForm, theory: &mut ITheoryEnv) -> IRecForm {
  match f {
    IRecForm::C(this, bicond, ante, cons) => {
      panic!("bug: _resolve2_rec_form: unexpected C");
    }
    IRecForm::P(this, prefix) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let mut uparams = Vec::with_capacity(prefix.uparams.len());
      let mut dparams = Vec::with_capacity(prefix.dparams.len());
      let mut xparams = Vec::with_capacity(prefix.xparams.len());
      let mut inside_ctx = ctx.clone();
      for term in prefix.uparams.iter() {
        let binder = IBinder::Universal;
        let term = match term {
          &ITerm::RVar(name, v) => {
            panic!("bug: _resolve2_rec_form: bound RVar term (u): {:?} {:?}", name, v);
          }
          &ITerm::Name(name) => {
            let v = theory.fresh_var();
            inside_ctx.bind_mut(binder, name, v);
            ITerm::FVar(name, v)
          }
          &ITerm::FVar(name, v) => {
            inside_ctx.bind_mut(binder, name, v);
            ITerm::FVar(name, v)
          }
          &ITerm::Var(v) => {
            inside_ctx.anon_bind_mut(binder, v);
            ITerm::Var(v)
          }
        };
        uparams.push(term);
      }
      for term in prefix.dparams.iter() {
        let binder = IBinder::Definitive;
        let term = match term {
          &ITerm::RVar(name, v) => {
            panic!("bug: _resolve2_rec_form: bound RVar term (d): {:?} {:?}", name, v);
          }
          &ITerm::Name(name) => {
            let v = theory.fresh_var();
            inside_ctx.bind_mut(binder, name.clone(), v);
            ITerm::FVar(name, v)
          }
          &ITerm::FVar(name, v) => {
            ITerm::FVar(name, v)
          }
          &ITerm::Var(v) => {
            inside_ctx.anon_bind_mut(binder, v);
            ITerm::Var(v)
          }
        };
        dparams.push(term);
      }
      for term in prefix.xparams.iter() {
        let binder = IBinder::Existential;
        let term = match term {
          &ITerm::RVar(name, v) => {
            panic!("bug: _resolve2_rec_form: bound RVar term (x): {:?} {:?}", name, v);
          }
          &ITerm::Name(name) => {
            let v = theory.fresh_var();
            inside_ctx.bind_mut(binder, name.clone(), v);
            ITerm::FVar(name, v)
          }
          &ITerm::FVar(name, v) => {
            ITerm::FVar(name, v)
          }
          &ITerm::Var(v) => {
            inside_ctx.anon_bind_mut(binder, v);
            ITerm::Var(v)
          }
        };
        xparams.push(term);
      }
      let bicond = prefix.bicond;
      let mut ante = Vec::with_capacity(prefix.ante.len());
      let mut cons = Vec::with_capacity(prefix.cons.len());
      for g in prefix.ante.into_iter() {
        ante.push(_resolve2_form(inside_ctx.clone(), g, theory));
      }
      for g in prefix.cons.into_iter() {
        cons.push(_resolve2_form(inside_ctx.clone(), g, theory));
      }
      let prefix = IPrefixRecForm{
        uparams,
        dparams,
        xparams,
        bicond,
        ante,
        cons,
      };
      theory.set_ctx(that, ctx);
      IRecForm::P(that, prefix)
    }
    _ => unimplemented!()
  }
}

fn _resolve2_form(ctx: ICtx, f: IForm, theory: &mut ITheoryEnv) -> IForm {
  match f {
    IForm::Cla(this, f) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let f = _resolve2_clausal_form(ctx.clone(), f, theory);
      theory.set_ctx(that, ctx);
      IForm::Cla(that, f)
    }
    IForm::Fre(this, f) => {
      // FIXME: check bound.
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let f = _resolve2_clausal_form(ctx.clone(), f, theory);
      theory.set_ctx(that, ctx);
      IForm::Fre(that, f)
    }
    IForm::Rec(this, f) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let f = _resolve2_rec_form(ctx.clone(), f, theory);
      theory.set_ctx(that, ctx);
      IForm::Rec(that, f)
    }
    _ => unimplemented!()
  }
}

pub fn resolve2_new_theory(mut theory: ITheoryEnv) -> ITheoryEnv {
  let mut recs = HTreapMap::default();
  let mut prop = HTreapMap::default();
  for (&idx, f) in theory.recs.clone().iter() {
    let f = _resolve2_rec_form(ICtx::empty(), f.clone(), &mut theory);
    recs.insert(idx, f);
  }
  for (&idx, f) in theory.prop.clone().iter() {
    let f = _resolve2_form(ICtx::empty(), f.clone(), &mut theory);
    prop.insert(idx, f);
  }
  theory.recs = recs;
  theory.prop = prop;
  theory
}

fn _formalize_exp(e: IExp, theory: &mut ITheoryEnv) -> IExp {
  match e {
    IExp::Term(this, term) => {
      IExp::Term(this, term)
    }
    IExp::Desc(this, term, atom) => {
      IExp::Desc(this, term, atom)
    }
    IExp::Bind(this, term, atom, rest) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let rest = _formalize_exp((&*rest).clone(), theory).into();
      IExp::Bind(that, term, atom, rest)
    }
    IExp::App(_this, fun, args) => {
      // TODO
      /*let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);*/
      let mut args_ = Vec::with_capacity(args.len());
      for e in args.into_iter() {
        args_.push(_formalize_exp(e, theory));
      }
      match _formalize_exp((&*fun).clone(), theory) {
        IExp::Term(fun_loc, fun_term) => {
          let tmp_v = theory.fresh_var();
          //let desc_ctx = ctx.clone().anon_bind(IBinder::Definitive, tmp_v);
          IExp::Desc(theory.fresh_loc(), ITerm::Var(tmp_v), IAtomicForm::App(theory.fresh_loc(), fun_term, args_, vec![IExp::Term(theory.fresh_loc(), ITerm::Var(tmp_v))]))
        }
        IExp::Desc(fun_loc, fun_term, fun_atom) => {
          let fun_loc_ = theory.fresh_loc();
          theory.unify_debuglocs(fun_loc, fun_loc_);
          let tmp_v = theory.fresh_var();
          //let desc_ctx = fun_ctx.clone().anon_bind(IBinder::Definitive, tmp_v);
          IExp::Bind(fun_loc_, fun_term.clone(), fun_atom,
              IExp::Desc(theory.fresh_loc(), ITerm::Var(tmp_v), IAtomicForm::App(theory.fresh_loc(), fun_term, args_, vec![IExp::Term(theory.fresh_loc(), ITerm::Var(tmp_v))])).into()
          )
        }
        IExp::Bind(bound_loc, bound_term, bound_atom, fun_exp) => {
          let bound_loc_ = theory.fresh_loc();
          theory.unify_debuglocs(bound_loc, bound_loc_);
          match &bound_term {
            &ITerm::Name(name) => {
              panic!("bug: _formalize_exp: potentially unsafe bound term: {:?}", name);
            }
            &ITerm::FVar(name, v) => {
              panic!("bug: _formalize_exp: FVar in exp position: {:?} {:?}", name, v);
            }
            &ITerm::RVar(..) => {}
            &ITerm::Var(_) => {}
          }
          let fun_exp = _formalize_exp((&*fun_exp).clone(), theory).into();
          IExp::Bind(bound_loc_, bound_term, bound_atom, fun_exp)
        }
        IExp::App(..) => {
          panic!("bug: _formalize_exp: funexp failure");
        }
        //_ => panic!("bug: _formalize_exp: desc or bind expected")
        _ => panic!("bug: _formalize_exp: funexp unsupported")
      }
    }
    IExp::RVar(this, var) => {
      IExp::RVar(this, var)
    }
  }
}

fn _formalize_atomic_form(f: IAtomicForm, theory: &mut ITheoryEnv) -> IAtomicForm {
  // TODO
  match f {
    IAtomicForm::Pre(this, rel, args) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let mut args_ = Vec::with_capacity(args.len());
      for arg in args.into_iter() {
        args_.push(_formalize_exp(arg, theory));
      }
      IAtomicForm::Pre(that, rel, args_)
    }
    IAtomicForm::App(this, rel, largs, rargs) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let mut largs_ = Vec::with_capacity(largs.len());
      let mut rargs_ = Vec::with_capacity(rargs.len());
      for e in largs.into_iter() {
        largs_.push(_formalize_exp(e, theory));
      }
      for e in rargs.into_iter() {
        rargs_.push(_formalize_exp(e, theory));
      }
      IAtomicForm::App(that, rel, largs_, rargs_)
    }
    _ => unimplemented!()
  }
}

fn _formalize_clausal_form(f: IClausalForm, theory: &mut ITheoryEnv) -> IClausalForm {
  // TODO
  match f {
    IClausalForm::Lit(this, neg, atom) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let atom = _formalize_atomic_form(atom, theory);
      IClausalForm::Lit(that, neg, atom)
    }
    IClausalForm::Eq_(this, lexp, rexp) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let lexp = _formalize_exp(lexp, theory);
      let rexp = _formalize_exp(rexp, theory);
      IClausalForm::Eq_(that, lexp, rexp)
    }
    IClausalForm::Neq(this, lexp, rexp) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let lexp = _formalize_exp(lexp, theory);
      let rexp = _formalize_exp(rexp, theory);
      IClausalForm::Neq(that, lexp, rexp)
    }
    _ => unimplemented!()
  }
}

fn _formalize_rec_form(f: IRecForm, theory: &mut ITheoryEnv) -> IRecForm {
  // TODO
  match f {
    IRecForm::C(this, bicond, ante, cons) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let mut ante_ = Vec::with_capacity(ante.len());
      let mut cons_ = Vec::with_capacity(cons.len());
      for f in ante.into_iter() {
        ante_.push(_formalize_form(f, theory));
      }
      for f in cons.into_iter() {
        cons_.push(_formalize_form(f, theory));
      }
      IRecForm::C(that, bicond, ante_, cons_)
    }
    IRecForm::Q(this, binder, term, nested) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let nested = _formalize_rec_form((&*nested).clone(), theory);
      IRecForm::Q(that, binder, term, nested.into())
    }
    IRecForm::P(..) => {
      unimplemented!();
    }
    IRecForm::RQs(..) => {
      unimplemented!();
    }
    IRecForm::RPC(..) => {
      unimplemented!();
    }
  }
}

fn _formalize_form(f: IForm, theory: &mut ITheoryEnv) -> IForm {
  match f {
    IForm::Cla(this, f) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let f = _formalize_clausal_form(f, theory);
      IForm::Cla(that, f)
    }
    IForm::Con(..) => {
      unimplemented!();
    }
    IForm::Fre(this, f) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let f = _formalize_clausal_form(f, theory);
      IForm::Fre(that, f)
    }
    IForm::Rec(this, f) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let f = _formalize_rec_form(f, theory);
      IForm::Rec(that, f)
    }
  }
}

pub fn formalize_new_theory(mut theory: ITheoryEnv) -> ITheoryEnv {
  let mut recs = HTreapMap::default();
  let mut prop = HTreapMap::default();
  for (&idx, f) in theory.recs.clone().iter() {
    let f = _formalize_rec_form(f.clone(), &mut theory);
    recs.insert(idx, f);
  }
  for (&idx, f) in theory.prop.clone().iter() {
    let f = _formalize_form(f.clone(), &mut theory);
    prop.insert(idx, f);
  }
  theory.recs = recs;
  theory.prop = prop;
  theory
}

#[derive(Default)]
struct Iterate {
  changed:  bool,
}

impl Iterate {
  pub fn repeat(&self) -> bool {
    self.changed
  }

  pub fn reset(&mut self) {
    self.changed = false;
  }

  fn update(&mut self) {
    self.changed = true;
  }
}

fn _normalize_exp(e: IExp, theory: &mut ITheoryEnv) -> IExp {
  match e {
    IExp::Term(..) => {
      unreachable!();
    }
    IExp::Desc(..) => {
      unreachable!();
    }
    IExp::Bind(..) => {
      unreachable!();
    }
    IExp::App(this, fun, args) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let fun = Rc::try_unwrap(fun).unwrap_or_else(|g| (&*g).clone());
      let fun = _normalize_exp(fun, theory);
      let mut args_ = Vec::with_capacity(args.len());
      for arg in args.into_iter() {
        args_.push(_normalize_exp(arg, theory));
      }
      //theory.copy_ctx(this, that);
      IExp::App(that, fun.into(), args_)
    }
    IExp::RVar(this, var) => {
      IExp::RVar(this, var)
    }
    _ => unimplemented!()
  }
}

//fn _normalize_cons_atomic_form(f: IAtomicForm, used: ICtx, new_def_clauses: &mut Vec<(IVar, IClausalForm)>, theory: &mut ITheoryEnv, iter: &mut Iterate) -> IAtomicForm {
fn _normalize_atomic_form(f: IAtomicForm, theory: &mut ITheoryEnv, /*iter: &mut Iterate*/) -> IAtomicForm {
  match f {
    IAtomicForm::Pre(this, rel_name, exps) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let mut exps_ = Vec::with_capacity(exps.len());
      for e in exps.into_iter() {
        exps_.push(_normalize_exp(e, theory));
      }
      //theory.copy_ctx(this, that);
      IAtomicForm::Pre(that, rel_name, exps_)
    }
    IAtomicForm::App(this, rel_name, lexps, rexps) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let mut lexps_ = Vec::with_capacity(lexps.len());
      let mut rexps_ = Vec::with_capacity(rexps.len());
      for e in lexps.into_iter() {
        lexps_.push(_normalize_exp(e, theory));
      }
      for e in rexps.into_iter() {
        rexps_.push(_normalize_exp(e, theory));
      }
      //theory.copy_ctx(this, that);
      IAtomicForm::App(that, rel_name, lexps_, rexps_)
    }
    IAtomicForm::RPre(this, rel_var, args) => {
      IAtomicForm::RPre(this, rel_var, args)
    }
    IAtomicForm::RApp(this, rel_var, largs, rargs) => {
      IAtomicForm::RApp(this, rel_var, largs, rargs)
    }
    _ => unimplemented!()
  }
}

//fn _normalize_cons_clausal_form(f: IClausalForm, used: ICtx, new_def_clauses: &mut Vec<(IVar, IClausalForm)>, theory: &mut ITheoryEnv, iter: &mut Iterate) -> IClausalForm {
fn _normalize_clausal_form(f: IClausalForm, theory: &mut ITheoryEnv, /*iter: &mut Iterate*/) -> IClausalForm {
  match f {
    IClausalForm::Lit(this, neg, atom) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let atom = _normalize_atomic_form(atom, theory);
      //theory.copy_ctx(this, that);
      IClausalForm::Lit(that, neg, atom)
    }
    IClausalForm::Eq_(this, lexp, rexp) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let lexp = _normalize_exp(lexp, theory);
      let rexp = _normalize_exp(rexp, theory);
      //theory.copy_ctx(this, that);
      IClausalForm::Eq_(that, lexp, rexp)
    }
    IClausalForm::Neq(this, lexp, rexp) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let lexp = _normalize_exp(lexp, theory);
      let rexp = _normalize_exp(rexp, theory);
      //theory.copy_ctx(this, that);
      IClausalForm::Neq(that, lexp, rexp)
    }
    IClausalForm::Lt_(this, lexp, rexp) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let lexp = _normalize_exp(lexp, theory);
      let rexp = _normalize_exp(rexp, theory);
      //theory.copy_ctx(this, that);
      IClausalForm::Lt_(that, lexp, rexp)
    }
    IClausalForm::Lte(this, lexp, rexp) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let lexp = _normalize_exp(lexp, theory);
      let rexp = _normalize_exp(rexp, theory);
      //theory.copy_ctx(this, that);
      IClausalForm::Lte(that, lexp, rexp)
    }
    //_ => unimplemented!()
  }
}

fn _normalize_rec_form(f: IRecForm, theory: &mut ITheoryEnv, /*iter: &mut Iterate*/) -> IRecForm {
  match f {
    IRecForm::C(this, bicond, ante, cons) => {
      // TODO
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let mut ante_ = Vec::with_capacity(ante.len());
      let mut cons_ = Vec::with_capacity(cons.len());
      for g in ante.into_iter() {
        match _normalize_form(g, theory) {
          IForm::Cla(_, h) => {
            ante_.push(h);
          }
          IForm::Con(..) => {
            unimplemented!();
          }
          IForm::Fre(..) => unimplemented!(),
          IForm::Rec(..) => unimplemented!()
        }
      }
      for g in cons.into_iter() {
        match _normalize_form(g, theory) {
          IForm::Cla(_, h) => {
            cons_.push(h);
          }
          IForm::Con(..) => {
            unimplemented!();
          }
          IForm::Fre(..) => unimplemented!(),
          IForm::Rec(..) => unimplemented!()
        }
      }
      //let ctx = theory.ctx(this);
      let pctx = IRPCtx{
        uvars:      Vec::new(),
        dvars:      Vec::new(),
        xvars:      Vec::new(),
        //innerctx:   ctx.clone(),
      };
      //theory.copy_ctx(this, that);
      IRecForm::RPC(that, pctx, bicond, ante_, cons_)
    }
    IRecForm::Q(..) => {
      unimplemented!();
    }
    IRecForm::P(..) => {
      unimplemented!();
    }
    IRecForm::RQs(this, bvars, nested) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let nested = Rc::try_unwrap(nested).unwrap_or_else(|g| (&*g).clone());
      match nested {
        IRecForm::C(this2, bicond, ante, cons) => {
          let mut uvars = Vec::new();
          let mut dvars = Vec::new();
          let mut xvars = Vec::new();
          for &(binder, var) in bvars.iter() {
            match binder {
              IBinder::Top => {
                panic!("bug: _normalize_rec_form: toplevel binder");
              }
              IBinder::Universal => {
                if !dvars.is_empty() || !xvars.is_empty() {
                  println!("TRACE: normalize: dump bvars:");
                  let ctx2 = theory.ctx(this2);
                  for &(_, var) in bvars.iter() {
                    println!("TRACE: normalize:   {:?} {:?}", var, ctx2.rev_lookup(var));
                  }
                  panic!("bug: _normalize_rec_form: unhandled non-normal (u): {:?}", bvars);
                }
                uvars.push(var);
              }
              IBinder::Definitive => {
                if !xvars.is_empty() {
                  println!("TRACE: normalize: dump bvars:");
                  let ctx2 = theory.ctx(this2);
                  for &(_, var) in bvars.iter() {
                    println!("TRACE: normalize:   {:?} {:?}", var, ctx2.rev_lookup(var));
                  }
                  panic!("bug: _normalize_rec_form: unhandled non-normal (d): {:?}", bvars);
                }
                dvars.push(var);
              }
              IBinder::Existential => {
                xvars.push(var);
              }
            }
          }
          let mut ante_ = Vec::with_capacity(ante.len());
          let mut cons_ = Vec::with_capacity(cons.len());
          for g in ante.into_iter() {
            match _normalize_form(g, theory) {
              IForm::Cla(_, h) => {
                ante_.push(h);
              }
              IForm::Con(..) => {
                unimplemented!();
              }
              IForm::Fre(..) => unimplemented!(),
              IForm::Rec(..) => unimplemented!()
            }
          }
          for g in cons.into_iter() {
            match _normalize_form(g, theory) {
              IForm::Cla(_, h) => {
                cons_.push(h);
              }
              IForm::Con(..) => {
                unimplemented!();
              }
              IForm::Fre(..) => unimplemented!(),
              IForm::Rec(..) => unimplemented!()
            }
          }
          let pctx = IRPCtx{uvars, dvars, xvars, /*innerctx: ctx2*/};
          //theory.copy_ctx(this, that);
          IRecForm::RPC(that, pctx, bicond, ante_, cons_)
        }
        _ => unimplemented!()
      }
    }
    IRecForm::RPC(..) => f,
  }
}

fn _normalize_form(f: IForm, theory: &mut ITheoryEnv, /*iter: &mut Iterate*/) -> IForm {
  match f {
    IForm::Cla(this, f) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let f = _normalize_clausal_form(f, theory);
      //theory.copy_ctx(this, that);
      IForm::Cla(that, f)
    }
    IForm::Con(..) => {
      unimplemented!();
    }
    IForm::Fre(this, f) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let f = _normalize_clausal_form(f, theory);
      //theory.copy_ctx(this, that);
      IForm::Fre(that, f)
    }
    IForm::Rec(this, f) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let f = _normalize_rec_form(f, theory);
      //theory.copy_ctx(this, that);
      IForm::Rec(that, f)
    }
  }
}

pub fn normalize_new_theory(mut theory: ITheoryEnv) -> ITheoryEnv {
  let mut recs = HTreapMap::default();
  let mut prop = HTreapMap::default();
  for (&idx, f) in theory.recs.clone().iter() {
    let f = _normalize_rec_form(f.clone(), &mut theory);
    recs.insert(idx, f);
  }
  for (&idx, f) in theory.prop.clone().iter() {
    let f = _normalize_form(f.clone(), &mut theory);
    prop.insert(idx, f);
  }
  theory.recs = recs;
  theory.prop = prop;
  theory
}

pub struct IPreNormalRecForm<V=ILoc> {
  params:   Vec<(IBinder, ITerm)>,
  //innerctx: V,
  bicond:   bool,
  ante_bnd: Vec<(ITerm, IAtomicForm<V>)>,
  ante:     Vec<IForm<V>>,
  cons_bnd: Vec<(ITerm, IAtomicForm<V>)>,
  cons:     Vec<IForm<V>>,
}

pub enum INormalRecForm<V=ILoc> {
  Just(IRecForm<V>),
  PreNormal(V, IPreNormalRecForm<V>),
}

pub enum INormalForm<V=ILoc> {
  Just(IForm<V>),
  Bind(Vec<(ITerm, IAtomicForm<V>)>, IForm<V>),
}

fn _normalize2_exp_rec(e: IExp, bound: &mut Vec<(ITerm, IAtomicForm)>, theory: &mut ITheoryEnv, it: &mut Iterate) -> IExp {
  // TODO
  match e {
    IExp::Term(this, term) => {
      IExp::Term(this, term)
    }
    IExp::Desc(this, term, atom) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let atom = _normalize2_atomic_form_rec(atom, bound, theory, it);
      bound.push((term.clone(), atom));
      IExp::Term(that, term)
    }
    IExp::Bind(_this, term, atom, rest) => {
      // FIXME
      //let atom = _normalize2_atomic_form_rec(atom, bound, theory, it);
      bound.push((term, atom));
      _normalize2_exp_rec((&*rest).clone(), bound, theory, it)
    }
    IExp::App(..) => {
      unreachable!();
    }
    IExp::RVar(_this, _var) => {
      panic!("bug: _normalize2_exp_rec: should normalize2 before resolve");
    }
  }
}

/*fn _normalize2_exp(e: IExp<ICtx>, theory: &mut ITheoryEnv<ICtx>, it: &mut Iterate) -> INormalExp<ICtx> {
  // TODO
  let mut bound = Vec::new();
  let e = _normalize2_exp_rec(e, &mut bound, theory, it);
  if bound.is_empty() {
    INormalExp::Just(e)
  } else {
    INormalExp::Bind(bound, e)
  }
}*/

fn _normalize2_atomic_form_rec(f: IAtomicForm, bound: &mut Vec<(ITerm, IAtomicForm)>, theory: &mut ITheoryEnv, it: &mut Iterate) -> IAtomicForm {
  // TODO
  match f {
    IAtomicForm::Pre(this, rel, args) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let mut args_ = Vec::with_capacity(args.len());
      for e in args.into_iter() {
        match _normalize2_exp_rec(e, bound, theory, it) {
          IExp::Term(e_loc, e_term) => {
            args_.push(IExp::Term(e_loc, e_term));
          }
          _ => unimplemented!()
        }
      }
      IAtomicForm::Pre(that, rel, args_)
    }
    IAtomicForm::App(this, rel, largs, rargs) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let mut largs_ = Vec::with_capacity(largs.len());
      let mut rargs_ = Vec::with_capacity(rargs.len());
      for e in largs.into_iter() {
        match _normalize2_exp_rec(e, bound, theory, it) {
          IExp::Term(e_loc, e_term) => {
            largs_.push(IExp::Term(e_loc, e_term));
          }
          _ => unimplemented!()
        }
      }
      for e in rargs.into_iter() {
        match _normalize2_exp_rec(e, bound, theory, it) {
          IExp::Term(e_loc, e_term) => {
            rargs_.push(IExp::Term(e_loc, e_term));
          }
          _ => unimplemented!()
        }
      }
      IAtomicForm::App(that, rel, largs_, rargs_)
    }
    _ => unimplemented!()
  }
}

fn _normalize2_clausal_form_rec(f: IClausalForm, bound: &mut Vec<(ITerm, IAtomicForm)>, theory: &mut ITheoryEnv, it: &mut Iterate) -> IClausalForm {
  match f {
    IClausalForm::Lit(this, neg, atom) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let atom = _normalize2_atomic_form_rec(atom, bound, theory, it);
      IClausalForm::Lit(that, neg, atom)
    }
    IClausalForm::Eq_(this, larg, rarg) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let larg = _normalize2_exp_rec(larg, bound, theory, it);
      let rarg = _normalize2_exp_rec(rarg, bound, theory, it);
      IClausalForm::Eq_(that, larg, rarg)
      /*let neg = false;
      let eq_v = match theory.eqv {
        None => panic!("bug: _normalize2_clausal_form_rec: missing eq var"),
        Some(v) => v
      };
      let atom = IAtomicForm::Pre(ctx.clone(), ITerm::Var(eq_v), vec![larg, rarg]);
      IClausalForm::Lit(ctx, neg, atom)*/
    }
    IClausalForm::Neq(this, larg, rarg) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let larg = _normalize2_exp_rec(larg, bound, theory, it);
      let rarg = _normalize2_exp_rec(rarg, bound, theory, it);
      IClausalForm::Neq(that, larg, rarg)
      /*let neg = true;
      let eq_v = match theory.eqv {
        None => panic!("bug: _normalize2_clausal_form_rec: missing eq var"),
        Some(v) => v
      };
      let atom = IAtomicForm::Pre(ctx.clone(), ITerm::Var(eq_v), vec![larg, rarg]);
      IClausalForm::Lit(ctx, neg, atom)*/
    }
    _ => unimplemented!()
  }
}

fn _normalize2_rec_form_rec(f: IRecForm, params: &mut Vec<(IBinder, ITerm)>, theory: &mut ITheoryEnv, it: &mut Iterate) -> (Vec<(ITerm, IAtomicForm)>, Vec<(ITerm, IAtomicForm)>, IRecForm) {
  match f {
    IRecForm::C(this, bicond, ante, cons) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let mut ante_bnd = Vec::new();
      let mut cons_bnd = Vec::new();
      let mut ante_ = Vec::with_capacity(ante.len());
      let mut cons_ = Vec::with_capacity(cons.len());
      for f in ante.into_iter() {
        match _normalize2_form_nonrec(f, theory, it) {
          INormalForm::Just(f) => {
            ante_.push(f);
          }
          INormalForm::Bind(f_bound, f) => {
            ante_bnd.extend(f_bound);
            ante_.push(f);
          }
        }
      }
      for f in cons.into_iter() {
        match _normalize2_form_nonrec(f, theory, it) {
          INormalForm::Just(f) => {
            cons_.push(f);
          }
          INormalForm::Bind(f_bound, f) => {
            cons_bnd.extend(f_bound);
            cons_.push(f);
          }
        }
      }
      (ante_bnd, cons_bnd, IRecForm::C(that, bicond, ante_, cons_))
    }
    IRecForm::Q(_this, binder, term, nested) => {
      params.push((binder, term));
      _normalize2_rec_form_rec((&*nested).clone(), params, theory, it)
    }
    _ => unimplemented!()
  }
}

fn _normalize2_rec_form(f: IRecForm, theory: &mut ITheoryEnv, it: &mut Iterate) -> INormalRecForm {
  let (params, ante_bnd, cons_bnd, f) = match &f {
    &IRecForm::C(..) => {
      let mut params = Vec::new();
      let (ante_bnd, cons_bnd, f) = _normalize2_rec_form_rec(f, &mut params, theory, it);
      assert!(params.is_empty());
      (params, ante_bnd, cons_bnd, f)
    }
    &IRecForm::Q(..) => {
      let mut params = Vec::new();
      let (ante_bnd, cons_bnd, f) = _normalize2_rec_form_rec(f, &mut params, theory, it);
      (params, ante_bnd, cons_bnd, f)
    }
    _ => unimplemented!()
  };
  if params.is_empty() && ante_bnd.is_empty() && cons_bnd.is_empty() {
    INormalRecForm::Just(f)
  } else {
    match f {
      IRecForm::C(this, bicond, ante, cons) => {
        let that = theory.fresh_loc();
        theory.unify_debuglocs(this, that);
        let g = IPreNormalRecForm{
          params,
          //innerctx: ctx,
          bicond,
          ante_bnd,
          ante,
          cons_bnd,
          cons,
        };
        INormalRecForm::PreNormal(that, g)
      }
      _ => unimplemented!()
    }
  }
}

fn _normalize2_prefix_rec_form(g: IPreNormalRecForm, theory: &mut ITheoryEnv, it: &mut Iterate) -> IPrefixRecForm {
  // FIXME
  //let mut tvars = Vec::new();
  let mut uparams = Vec::new();
  let mut dparams = Vec::new();
  let mut xparams = Vec::new();
  for &(binder, ref term) in g.params.iter() {
    match binder {
      IBinder::Top => {
        panic!("bug: _normalize2_prefix_rec_form: toplevel binder");
      }
      IBinder::Universal => {
        if !dparams.is_empty() || !xparams.is_empty() {
          /*println!("TRACE: normalize: dump bvars:");
          for &(_, var) in g.params.iter() {
            println!("TRACE: normalize:   {:?} {:?}", var, ctx2.rev_lookup(var));
          }*/
          panic!("bug: _normalize2_prefix_rec_form: unhandled non-normal (u): {:?}", g.params);
        }
        uparams.push(term.clone());
      }
      IBinder::Definitive => {
        if !xparams.is_empty() {
          /*println!("TRACE: normalize: dump bvars:");
          for &(_, var) in g.params.iter() {
            println!("TRACE: normalize:   {:?} {:?}", var, ctx2.rev_lookup(var));
          }*/
          panic!("bug: _normalize2_prefix_rec_form: unhandled non-normal (d): {:?}", g.params);
        }
        dparams.push(term.clone());
      }
      IBinder::Existential => {
        xparams.push(term.clone());
      }
    }
  }
  let mut ante_ = Vec::with_capacity(g.ante_bnd.len() + g.cons_bnd.len() + g.ante.len());
  for (term, atom) in g.ante_bnd.into_iter() {
    uparams.push(term);
    // FIXME
    ante_.push(IForm::Cla(theory.fresh_loc(), IClausalForm::Lit(theory.fresh_loc(), false, atom)));
  }
  for (term, atom) in g.cons_bnd.into_iter() {
    uparams.push(term);
    // FIXME
    ante_.push(IForm::Cla(theory.fresh_loc(), IClausalForm::Lit(theory.fresh_loc(), false, atom)));
  }
  ante_.extend(g.ante);
  IPrefixRecForm{
    //tvars,
    uparams,
    dparams,
    xparams,
    bicond: g.bicond,
    ante:   ante_,
    cons:   g.cons,
  }
}

fn _normalize2_form_nonrec(f: IForm, theory: &mut ITheoryEnv, it: &mut Iterate) -> INormalForm {
  let mut bound = Vec::new();
  let f = match f {
    IForm::Cla(this, f) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let f = _normalize2_clausal_form_rec(f, &mut bound, theory, it);
      IForm::Cla(that, f)
    }
    IForm::Con(this, fs) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let mut fs_ = Vec::with_capacity(fs.len());
      for f in fs.into_iter() {
        match _normalize2_form_nonrec(f, theory, it) {
          INormalForm::Just(f) => {
            fs_.push(f);
          }
          INormalForm::Bind(f_bound, f) => {
            bound.extend(f_bound);
            fs_.push(f);
          }
        }
      }
      IForm::Con(that, fs_)
    }
    IForm::Fre(this, f) => {
      let that = theory.fresh_loc();
      theory.unify_debuglocs(this, that);
      let f = _normalize2_clausal_form_rec(f, &mut bound, theory, it);
      IForm::Fre(that, f)
    }
    IForm::Rec(..) => panic!("bug: _normalize2_form_nonrec: rec form")
  };
  if bound.is_empty() {
    INormalForm::Just(f)
  } else {
    INormalForm::Bind(bound, f)
  }
}

pub fn normalize2_new_theory(mut theory: ITheoryEnv) -> ITheoryEnv {
  // TODO
  let mut it = Iterate::default();
  let mut recs = HTreapMap::default();
  let mut prop = HTreapMap::default();
  for (&idx, f) in theory.recs.clone().iter() {
    let f = match _normalize2_rec_form(f.clone(), &mut theory, &mut it) {
      INormalRecForm::Just(f) => f,
      INormalRecForm::PreNormal(this, g) => {
        let that = theory.fresh_loc();
        theory.unify_debuglocs(this, that);
        let prefix = _normalize2_prefix_rec_form(g, &mut theory, &mut it);
        IRecForm::P(that, prefix)
      }
    };
    recs.insert(idx, f);
  }
  for (&idx, f) in theory.prop.clone().iter() {
    let f = match _normalize2_form_nonrec(f.clone(), &mut theory, &mut it) {
      INormalForm::Just(f) => f,
      INormalForm::Bind(..) => {
        panic!("bug: normalize2_new_theory: normal prop form with bound terms");
      }
    };
    prop.insert(idx, f);
  }
  theory.recs = recs;
  theory.prop = prop;
  theory
}
