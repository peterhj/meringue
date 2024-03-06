use crate::re::{ReTrie};

use std::borrow::{Borrow};
use std::cmp::{max, min};
use std::fmt::{Debug as FmtDebug, Error as FmtError, Formatter};
use std::fs::{File};
use std::io::{Read};
use std::ops::{Deref};
use std::path::{Path};
use std::rc::{Rc};

#[derive(Clone, Debug)]
pub enum HToken {
  Newline,
  Whitespace,
  EolComment,
  DocComment,
  LBlockComment,
  RBlockComment,
  Abstract,
  All,
  And,
  Any,
  Assert,
  Assume,
  Assuming,
  Axiom,
  Axm,
  By,
  Case,
  Cases,
  Choose,
  Con,
  Const,
  Contra,
  Cycl,
  Deduce,
  Def,
  Do,
  Done,
  Elided,
  Else,
  End,
  Equiv,
  Exist,
  Export,
  Extend_,
  Extends,
  Find,
  For,
  Fresh,
  From_,
  Fun,
  Func,
  Function,
  Hyp,
  Id,
  If,
  Iff,
  Image,
  In,
  Include,
  Invert,
  Is,
  Known,
  Lem,
  Lemma,
  Let,
  Lsymm,
  Map,
  Match,
  Maybe,
  Mod,
  Module,
  Monc,
  No,
  NoProof,
  Not,
  Only,
  Open,
  Or,
  Order,
  Preimage,
  Proof,
  Propose,
  Prove,
  Rcyc,
  Rec,
  Ref,
  Rel,
  Rels,
  Relation,
  Require,
  Requires,
  Rflx,
  Rsymm,
  Rule,
  Rules,
  Sketch,
  Some_,
  Strictly,
  Suppose,
  Symm,
  The,
  Then,
  Theorem,
  Theory,
  Thm,
  To,
  Trace,
  Undef,
  Unk,
  Var,
  Vars,
  Where,
  With,
  UnicLambda,
  UnicNegation,
  UnicNotEquals,
  UnicGte,
  UnicLte,
  Comma,
  Dot,
  DotDot,
  Ellipsis,
  Semi,
  SemiSemi,
  Colon,
  ColonColon,
  ColonDash,
  ColonEquals,
  Quote,
  Backquote,
  Tilde,
  Hash,
  Caret,
  Dash,
  DashColon,
  DashQuery,
  DashSlash,
  RArrow,
  RSlashArrow,
  Equals,
  RDArrow,
  Plus,
  PlusPlus,
  PlusSlashDash,
  Gt,
  Gte,
  Lt,
  Lte,
  LArrow,
  Star,
  StarStar,
  Slash,
  SlashBackslash,
  SlashEquals,
  SlashGt,
  SlashGte,
  SlashLt,
  SlashLte,
  SlashZero,
  Query,
  QueryDash,
  Bang,
  BangDash,
  Backslash,
  BackslashSlash,
  Bar,
  BarBar,
  LBarArrow,
  RBarArrow,
  LBarSlashArrow,
  RBarSlashArrow,
  LColonArrow,
  RColonArrow,
  //LDotParen,
  //RDotParen,
  LCurly,
  RCurly,
  LParen,
  RParen,
  LBrack,
  RBrack,
  LEscCurly,
  REscCurly,
  Place,
  Integer(String),
  Ident(String),
  ArityIdent(String),
  FuncArityIdent(String),
  DQuoteIdent(String),
  _Err,
  _Eof,
}

pub type HTokenResult = Result<HTokenSpan, HErrorSpan>;

#[derive(Clone, Debug)]
pub struct HTokenSpan {
  pub token:    HToken,
  pub spaninfo: HSpanInfo,
}

#[derive(Clone, Debug)]
pub struct HErrorSpan {
  pub error:    HError,
  pub spaninfo: HSpanInfo,
}

impl From<(HError, HSpanInfo)> for HErrorSpan {
  fn from(tup: (HError, HSpanInfo)) -> HErrorSpan {
    HErrorSpan{
      error:    tup.0,
      spaninfo: tup.1,
    }
  }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct HSpanInfo {
  //pub line_nr:  usize,
  //pub line_pos: usize,
  pub lnpos_s:  (usize, usize),
  pub lnpos_e:  (usize, usize),
  pub span:     (usize, usize),
}

impl HSpanInfo {
  pub fn union(self, other: HSpanInfo) -> HSpanInfo {
    HSpanInfo{
      lnpos_s:  min(self.lnpos_s, other.lnpos_s),
      lnpos_e:  max(self.lnpos_e, other.lnpos_e),
      span:     (min(self.span.0, other.span.0), max(self.span.1, other.span.1)),
    }
  }
}

thread_local! {
  static HLEXER_TRIE: ReTrie<HToken> = default_lexer_trie();
}

pub fn default_lexer_trie() -> ReTrie<HToken> {
  let mut tr = ReTrie::default();
  tr.push(r"\r\n",      |_| HToken::Newline);
  tr.push(r"\r",        |_| HToken::Newline);
  tr.push(r"\n",        |_| HToken::Newline);
  tr.push(r"[ \t]+",    |_| HToken::Whitespace);
  tr.push(r"\(\*",      |_| HToken::LBlockComment);
  tr.push(r"\*\)",      |_| HToken::RBlockComment);
  tr.push(r"\-\-[\-]*[ \t]*\|[^\n]*", |_| HToken::DocComment);
  tr.push(r"\-\-[^\n]*", |_| HToken::EolComment);
  tr.push(r"all",       |_| HToken::All);
  tr.push(r"and",       |_| HToken::And);
  tr.push(r"any",       |_| HToken::Any);
  tr.push(r"assert",    |_| HToken::Assert);
  tr.push(r"assume",    |_| HToken::Assume);
  tr.push(r"assuming",  |_| HToken::Assuming);
  tr.push(r"axm",       |_| HToken::Axm);
  tr.push(r"by",        |_| HToken::By);
  tr.push(r"cases",     |_| HToken::Cases);
  tr.push(r"case",      |_| HToken::Case);
  tr.push(r"choose",    |_| HToken::Choose);
  tr.push(r"contra",    |_| HToken::Contra);
  tr.push(r"con",       |_| HToken::Con);
  tr.push(r"cycl",      |_| HToken::Cycl);
  tr.push(r"deduce",    |_| HToken::Deduce);
  tr.push(r"def",       |_| HToken::Def);
  tr.push(r"done",      |_| HToken::Done);
  tr.push(r"elided",    |_| HToken::Elided);
  tr.push(r"end",       |_| HToken::End);
  tr.push(r"equiv",     |_| HToken::Equiv);
  tr.push(r"exist",     |_| HToken::Exist);
  tr.push(r"find",      |_| HToken::Find);
  tr.push(r"for",       |_| HToken::For);
  tr.push(r"fresh",     |_| HToken::Fresh);
  tr.push(r"from",      |_| HToken::From_);
  tr.push(r"func",      |_| HToken::Func);
  tr.push(r"fun",       |_| HToken::Fun);
  tr.push(r"iff",       |_| HToken::Iff);
  tr.push(r"if",        |_| HToken::If);
  tr.push(r"in",        |_| HToken::In);
  tr.push(r"lem",       |_| HToken::Lem);
  tr.push(r"let",       |_| HToken::Let);
  tr.push(r"lsymm",     |_| HToken::Lsymm);
  tr.push(r"map",       |_| HToken::Map);
  tr.push(r"match",     |_| HToken::Match);
  tr.push(r"maybe",     |_| HToken::Maybe);
  //tr.push(r"module",    |_| HToken::Module);
  tr.push(r"mod",       |_| HToken::Mod);
  tr.push(r"monc",      |_| HToken::Monc);
  tr.push(r"not",       |_| HToken::Not);
  tr.push(r"noproof",   |_| HToken::NoProof);
  tr.push(r"no",        |_| HToken::No);
  tr.push(r"open",      |_| HToken::Open);
  tr.push(r"proof",     |_| HToken::Proof);
  tr.push(r"propose",   |_| HToken::Propose);
  tr.push(r"rcyc",      |_| HToken::Rcyc);
  tr.push(r"rec",       |_| HToken::Rec);
  tr.push(r"ref",       |_| HToken::Ref);
  tr.push(r"rel",       |_| HToken::Rel);
  tr.push(r"rflx",      |_| HToken::Rflx);
  tr.push(r"rsymm",     |_| HToken::Rsymm);
  tr.push(r"some",      |_| HToken::Some_);
  tr.push(r"symm",      |_| HToken::Symm);
  tr.push(r"then",      |_| HToken::Then);
  tr.push(r"theory",    |_| HToken::Theory);
  tr.push(r"the",       |_| HToken::The);
  tr.push(r"thm",       |_| HToken::Thm);
  tr.push(r"undef",     |_| HToken::Undef);
  tr.push(r"unk",       |_| HToken::Unk);
  tr.push(r"where",     |_| HToken::Where);
  tr.push(r"with",      |_| HToken::With);
  tr.push(r"'",         |_| HToken::Quote);
  tr.push(r"`",         |_| HToken::Backquote);
  tr.push(r"\~",        |_| HToken::Tilde);
  tr.push(r"\#",        |_| HToken::Hash);
  tr.push(r"\^",        |_| HToken::Caret);
  tr.push(r"!\-",       |_| HToken::BangDash);
  tr.push(r"!",         |_| HToken::Bang);
  tr.push(r"\?\-",      |_| HToken::QueryDash);
  tr.push(r"\?",        |_| HToken::Query);
  tr.push(r",",         |_| HToken::Comma);
  tr.push(r"\.\.\.",    |_| HToken::Ellipsis);
  tr.push(r"\.\.",      |_| HToken::DotDot);
  tr.push(r"\.",        |_| HToken::Dot);
  tr.push(r";;",        |_| HToken::SemiSemi);
  tr.push(r";",         |_| HToken::Semi);
  tr.push(r"::",        |_| HToken::ColonColon);
  tr.push(r":\-",       |_| HToken::ColonDash);
  tr.push(r":=",        |_| HToken::ColonEquals);
  tr.push(r":>",        |_| HToken::RColonArrow);
  tr.push(r":",         |_| HToken::Colon);
  tr.push(r"\->",       |_| HToken::RArrow);
  tr.push(r"\-/>",      |_| HToken::RSlashArrow);
  tr.push(r"\-:",       |_| HToken::DashColon);
  tr.push(r"\-\?",      |_| HToken::DashQuery);
  tr.push(r"\-/",       |_| HToken::DashSlash);
  tr.push(r"\-",        |_| HToken::Dash);
  tr.push(r"=",         |_| HToken::Equals);
  tr.push(r"<=",        |_| HToken::Lte);
  tr.push(r"<",         |_| HToken::Lt);
  tr.push(r">=",        |_| HToken::Gte);
  tr.push(r">",         |_| HToken::Gt);
  tr.push(r"\+",        |_| HToken::Plus);
  tr.push(r"\*",        |_| HToken::Star);
  tr.push(r"/=",        |_| HToken::SlashEquals);
  tr.push(r"/",         |_| HToken::Slash);
  tr.push(r"\\",        |_| HToken::Backslash);
  tr.push(r"\|>",       |_| HToken::RBarArrow);
  tr.push(r"\|\|",      |_| HToken::BarBar);
  tr.push(r"\|",        |_| HToken::Bar);
  tr.push(r"\{",        |_| HToken::LCurly);
  tr.push(r"\}",        |_| HToken::RCurly);
  tr.push(r"\(",        |_| HToken::LParen);
  tr.push(r"\)",        |_| HToken::RParen);
  tr.push(r"\[",        |_| HToken::LBrack);
  tr.push(r"\]",        |_| HToken::RBrack);
  tr.push(r"\\\{",      |_| HToken::LEscCurly);
  tr.push(r"\\\}",      |_| HToken::REscCurly);
  tr.push(r"[a-zA-Z][a-zA-Z0-9_']*/[0-9]+\+[0-9]+", |t| HToken::FuncArityIdent(t.to_owned()));
  tr.push(r"[a-zA-Z][a-zA-Z0-9_']*/[0-9]+", |t| HToken::ArityIdent(t.to_owned()));
  tr.push(r"[a-zA-Z][a-zA-Z0-9_']*", |t| HToken::Ident(t.to_owned()));
  tr.push(r"\-[0-9]+",  |t| HToken::Integer(t.to_owned()));
  tr.push(r"[0-9]+",    |t| HToken::Integer(t.to_owned()));
  tr
}

#[derive(Clone)]
pub struct HLexer<'src> {
  source:   &'src str,
  offset:   usize,
  line_nr:  usize,
  line_pos: usize,
  next_pos: usize,
  eof:      bool,
}

impl<'src> HLexer<'src> {
  pub fn new(source: &'src str) -> HLexer<'src> {
    HLexer{
      source,
      offset:   0,
      line_nr:  1,
      line_pos: 0,
      next_pos: 1,
      eof:      false,
    }
  }
}

impl<'src> Iterator for HLexer<'src> {
  type Item = HTokenResult;

  fn next(&mut self) -> Option<HTokenResult> {
    HLEXER_TRIE.with(|trie| {
      loop {
        if self.eof {
          let tok_info = HSpanInfo{
            lnpos_s:    (self.line_nr, self.line_pos),
            lnpos_e:    (self.line_nr, self.line_pos),
            span:       (self.offset, self.offset),
          };
          return Some(Ok(HTokenSpan{token: HToken::_Eof, spaninfo: tok_info}));
        }
        let (tok, tok_span, tok_text) = match trie.match_at(&self.source, self.offset) {
          None => {
            self.line_pos = self.next_pos;
            self.eof = true;
            (HToken::_Eof, (self.offset, self.offset), None)
          }
          Some((tok, tok_end)) => {
            //println!("TRACE: lexer: token: {:?} start: {} end: {}", tok, self.offset, tok_end);
            let tok_start = self.offset;
            assert!(tok_start < tok_end);
            let tok_len = tok_end - tok_start;
            let tok_span = (tok_start, tok_end);
            let tok_text = &self.source[tok_start .. tok_end];
            self.offset += tok_len;
            self.line_pos = self.next_pos;
            self.next_pos += tok_len;
            (tok, tok_span, Some(tok_text))
          }
        };
        match (tok, tok_span, tok_text) {
          (HToken::Newline, _, _) => {
            self.line_nr += 1;
            self.line_pos = 0;
            self.next_pos = 1;
            continue;
          }
          // FIXME: documentation comments should annotate a token.
          (HToken::Whitespace, _, _) |
          //(HToken::EolComment, _, _) => {
          (HToken::EolComment, _, _) |
          (HToken::DocComment, _, _) => {
            continue;
          }
          (HToken::LBlockComment, _, _) |
          (HToken::RBlockComment, _, _) => {
            unimplemented!();
          }
          // FIXME
          (HToken::_Eof, _, _) => {
            let tok_info = HSpanInfo{
              lnpos_s:  (self.line_nr, self.line_pos),
              lnpos_e:  (self.line_nr, self.line_pos),
              span:     (self.offset, self.offset),
            };
            return Some(Ok(HTokenSpan{token: HToken::_Eof, spaninfo: tok_info}));
          }
          (tok, tok_span, _) => {
            let tok_info = HSpanInfo{
              lnpos_s:  (self.line_nr, self.line_pos),
              lnpos_e:  (self.line_nr, self.next_pos - 1),
              span:     tok_span,
            };
            return Some(Ok(HTokenSpan{token: tok, spaninfo: tok_info}));
          }
        }
      }
    })
  }
}

#[derive(Clone, Debug)]
pub enum HError {
  Eof,
  Input,
  Encoding,
  Unknown,
  MissingLBlockComment,
  Reserved(String),
  Unexpected(HToken),
  Expected(Vec<HToken>, HToken),
  InvalidArity,
  InvalidFuncArity,
  InvalidFuncInArity,
  InvalidFuncOutArity,
  UnsupportedFuncArity(usize, usize),
  DoubleNegationSyntax,
  EmptyForm,
  ExpectedClausalForm,
  ExpectedRecursion,
  InvalidAtom,
  InvalidBiconditional,
  InvalidClausalForm,
  InvalidConditional,
  InvalidForm,
  InvalidNegation,
  InvalidNegativeClausalForm,
  InvalidRule,
  MissingNullDenotation(HToken),
  //MissingLeftDenotation(HExpr, HToken),
  Other,
}

#[derive(Clone, Copy, Debug)]
pub enum HOrder {
  Equal,
  Less,
  LessEqual,
  Greater,
  GreaterEqual,
  NotEqual,
  NotLess,
  NotLessEqual,
  NotGreater,
  NotGreaterEqual,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct HRelQuals {
  pub cat:      bool,
  pub const_:   bool,
  pub cycl:     bool,
  pub equiv:    bool,
  pub func:     bool,
  pub monc:     bool,
  pub order:    bool,
  pub rflx:     bool,
  pub symm:     bool,
}

#[derive(Clone, Debug)]
pub struct HRel {
  pub quals:    HRelQuals,
  pub name:     String,
  pub arity:    usize,
}

#[derive(Clone, Debug)]
pub struct HFun {
  pub quals:    HRelQuals,
  pub name:     String,
  pub l_arity:  usize,
  pub r_arity:  usize,
}

#[derive(Clone, Copy, Debug)]
pub enum HQuant {
  Universal,
  Definitive,
  Existential,
  Nonexistential,
}

#[derive(Clone, Debug)]
pub enum HTerm {
  //Place,
  Name(String),
}

#[derive(Clone)]
pub struct HExpRef(pub Rc<HExp>);

impl From<HExp> for HExpRef {
  fn from(hexp: HExp) -> HExpRef {
    HExpRef(Rc::new(hexp))
  }
}

impl Deref for HExpRef {
  type Target = HExp;

  fn deref(&self) -> &HExp {
    &*self.0
  }
}

impl FmtDebug for HExpRef {
  fn fmt(&self, f: &mut Formatter) -> Result<(), FmtError> {
    FmtDebug::fmt(&*self.0, f)
  }
}

#[derive(Clone, Debug)]
pub enum HExp<E=HExpRef> {
  Group(E, HSpanInfo),
  Term(HTerm, HSpanInfo),
  App(E, Vec<HExp<E>>, HSpanInfo),
  Integer(i64),
  //Sum(E, Vec<E>),
  Sum(E, E),
  //Prod(E, Vec<E>),
  Prod(E, E),
  Diff(E, E),
  Frac(E, E),
  Neg(E),
  Power(E, E),
}

impl<E> HExp<E> {
  pub fn spaninfo(&self) -> HSpanInfo {
    match self {
      &HExp::Group(_, spaninfo) => spaninfo,
      &HExp::Term(_, spaninfo) => spaninfo,
      &HExp::App(_, _, spaninfo) => spaninfo,
      _ => panic!("bug: HExp: missing spaninfo")
    }
  }
}

#[derive(Clone, Debug)]
pub struct HPreForm {
  pub rel_name: String,
  pub exps:     Vec<HExp>,
  pub spaninfo: HSpanInfo,
}

#[derive(Clone, Debug)]
pub struct HAppForm {
  pub rel_name: String,
  pub lexps:    Vec<HExp>,
  pub rexps:    Vec<HExp>,
  pub spaninfo: HSpanInfo,
}

#[derive(Clone, Debug)]
pub struct HDomForm {
  pub rel_name: String,
  pub lexps:    Vec<HExp>,
  pub spaninfo: HSpanInfo,
}

#[derive(Clone, Debug)]
pub struct HImgForm {
  pub rel_name: String,
  pub rexps:    Vec<HExp>,
  pub spaninfo: HSpanInfo,
}

#[derive(Clone, Debug)]
pub enum HAtomicForm {
  Pre(HPreForm),
  App(HAppForm),
  Dom(HDomForm),
  Img(HImgForm),
}

impl HAtomicForm {
  pub fn spaninfo(&self) -> HSpanInfo {
    match self {
      &HAtomicForm::Pre(ref f) => f.spaninfo,
      &HAtomicForm::App(ref f) => f.spaninfo,
      &HAtomicForm::Dom(ref f) => f.spaninfo,
      &HAtomicForm::Img(ref f) => f.spaninfo,
    }
  }
}

#[derive(Clone, Debug)]
pub enum HClausalForm {
  Lit(bool, HAtomicForm, HSpanInfo),
  Xeq(HExp, Vec<(HOrder, HExp)>, HSpanInfo),
}

impl HClausalForm {
  pub fn spaninfo(&self) -> HSpanInfo {
    //panic!("bug: HClausalForm: missing spaninfo");
    match self {
      &HClausalForm::Lit(_, _, spaninfo) => spaninfo,
      &HClausalForm::Xeq(_, _, spaninfo) => spaninfo,
    }
  }
}

#[derive(Clone, Debug)]
pub struct HQuantForm {
  pub quant:    HQuant,
  pub q_term:   HTerm,
  pub nested:   HRecFormRef,
  pub spaninfo: HSpanInfo,
}

#[derive(Clone, Debug)]
pub struct HCondForm {
  pub bicond:   bool,
  pub ante:     Vec<HForm>,
  pub cons:     Vec<HForm>,
  pub spaninfo: HSpanInfo,
}

pub type HRecFormRef = Rc<HRecForm>;

#[derive(Clone, Debug)]
pub enum HRecForm {
  Con(HCondForm),
  Qua(HQuantForm),
}

impl HRecForm {
  pub fn spaninfo(&self) -> HSpanInfo {
    //panic!("bug: HRecForm: missing spaninfo");
    match self {
      &HRecForm::Con(ref f) => f.spaninfo,
      &HRecForm::Qua(ref f) => f.spaninfo,
    }
  }
}

#[derive(Clone, Debug)]
pub enum HForm {
  Cla(HClausalForm, HSpanInfo),
  Con(Vec<HForm>, HSpanInfo),
  Rec(HRecForm, HSpanInfo),
}

impl HForm {
  pub fn spaninfo(&self) -> HSpanInfo {
    //panic!("bug: HForm: missing spaninfo");
    match self {
      &HForm::Cla(_, spaninfo) => spaninfo,
      &HForm::Con(_, spaninfo) => spaninfo,
      &HForm::Rec(_, spaninfo) => spaninfo,
    }
  }
}

#[derive(Clone, Debug)]
pub enum HTheoryDecl {
  //Top,
  Rel(HRel),
  Fun(HFun),
  Rec(Option<String>, HRecForm),
}

pub type HProgramRef = Rc<HProgram>;

#[derive(Clone, Debug)]
pub enum HProgram {
//pub enum HProgram<P=HProgramRef> {
  Let(Vec<String>),
  Where(Vec<HForm>),
  Propose(Vec<HForm>),
}

#[derive(Clone, Debug)]
pub enum HTree {
  //Theory(Vec<HTheoryDecl>),
  Theory{decl: Vec<HTheoryDecl>, prog: Vec<HProgram>},
}

#[derive(Clone, Debug)]
pub struct HTheory {
  pub decl: Vec<HTheoryDecl>,
  pub prog: Vec<HProgram>,
}

#[derive(Clone, Debug)]
pub enum HQuote {
  // FIXME
  Exp(HExp),
  Form(HForm),
  Atom(HAtomicForm),
}

impl HQuote {
  pub fn spaninfo(&self) -> HSpanInfo {
    match self {
      &HQuote::Exp(ref e) => e.spaninfo(),
      &HQuote::Form(ref f) => f.spaninfo(),
      &HQuote::Atom(ref a) => a.spaninfo(),
    }
  }
}

#[derive(Clone)]
pub struct HQuoteRef(pub Rc<HQuote>);

impl From<HQuote> for HQuoteRef {
  fn from(hquote: HQuote) -> HQuoteRef {
    HQuoteRef(Rc::new(hquote))
  }
}

impl Deref for HQuoteRef {
  type Target = HQuote;

  fn deref(&self) -> &HQuote {
    &*self.0
  }
}

impl FmtDebug for HQuoteRef {
  fn fmt(&self, f: &mut Formatter) -> Result<(), FmtError> {
    FmtDebug::fmt(&*self.0, f)
  }
}

#[derive(Clone, Debug)]
pub struct HQuoteSpan {
  pub quote:    HQuote,
  pub spaninfo: HSpanInfo,
}

fn parse_arity_ident<S: Borrow<str>>(text: S) -> Result<(String, usize), HError> {
  let toks: Vec<_> = text.borrow().split("/").collect();
  if toks.len() != 2 {
    println!("TRACE: parse_arity_ident: 0 '{}'", text.borrow());
    return Err(HError::InvalidArity);
  }
  let arity_nr = match toks[1].parse() {
    Err(_) => {
      println!("TRACE: parse_arity_ident: 1 '{}'", text.borrow());
      return Err(HError::InvalidArity);
    }
    Ok(0) => {
      println!("TRACE: parse_arity_ident: 2 '{}'", text.borrow());
      return Err(HError::InvalidArity);
    }
    Ok(n) => n
  };
  Ok((toks[0].to_owned(), arity_nr))
}

fn parse_func_arity_ident<S: Borrow<str>>(text: S) -> Result<(String, usize, usize), HError> {
  let toks: Vec<_> = text.borrow().split("/").collect();
  if toks.len() != 2 {
    return Err(HError::InvalidFuncArity);
  }
  let ar_toks: Vec<_> = toks[1].split("+").collect();
  if ar_toks.len() != 2 {
    return Err(HError::InvalidFuncArity);
  }
  let func_arity_in = match ar_toks[0].parse() {
    Err(_) |
    Ok(0) => return Err(HError::InvalidFuncInArity),
    Ok(n) => n
  };
  let func_arity_out = match ar_toks[1].parse() {
    Err(_) |
    Ok(0) => return Err(HError::InvalidFuncOutArity),
    Ok(n) => n
  };
  Ok((toks[0].to_owned(), func_arity_in, func_arity_out))
}

#[derive(Clone, Copy)]
enum AtomParse {
  Top,
  Arr,
  Dom,
  Img,
}

#[derive(Clone, Copy)]
enum FormParse {
  Top,
  LCond,
  RCond,
  BCond,
}

pub struct HParser<Toks> {
  toks: Toks,
  span: HSpanInfo,
  curr: Option<HTokenResult>,
  prev: Option<HTokenResult>,
  bt:   bool,
}

//impl<Toks: Iterator<Item=(Result<HToken, HError>, HSpanInfo)> + Clone> HParser<Toks> {
impl<Toks: Iterator<Item=HTokenResult> + Clone> HParser<Toks> {
  pub fn new(toks: Toks) -> HParser<Toks> {
    HParser{
      toks: toks,
      span: HSpanInfo::default(),
      curr: None,
      prev: None,
      bt:   false,
    }
  }

  fn backtrack(&mut self) {
    assert!(!self.bt);
    self.bt = true;
  }

  fn advance(&mut self) {
    if self.bt {
      self.bt = false;
    } else {
      self.prev = self.curr.take();
      self.curr = self.toks.next();
      //println!("TRACE: parser: advance: {:?}", self.curr);
    }
  }

  //fn current_token(&self) -> Result<HToken, HError> {
  fn current_token(&self) -> HTokenResult {
    if self.bt {
      match self.prev.as_ref() {
        //Some((ref tok, _)) => tok.clone(),
        Some(tok) => tok.clone(),
        None => panic!("bug: current_token: backtrack failed")
      }
    } else {
      match self.curr.as_ref() {
        //Some((ref tok, _)) => tok.clone(),
        Some(tok) => tok.clone(),
        //None => Err(HError::Eof),
        None => panic!("bug: current_token: expected eof")
      }
    }
  }

  fn exp_lbp(&self, tok: &HTokenSpan) -> i32 {
    // TODO
    match &tok.token {
      &HToken::_Eof => 0,
      &HToken::Assume |
      &HToken::Axm |
      &HToken::Cycl |
      &HToken::End |
      &HToken::Equiv |
      &HToken::For |
      &HToken::Fun |
      &HToken::Lem |
      &HToken::Let |
      &HToken::Map |
      &HToken::Proof |
      &HToken::Propose |
      &HToken::Rcyc |
      &HToken::Rflx |
      &HToken::Rel |
      &HToken::Symm |
      &HToken::Thm => 0,
      &HToken::Bar |
      &HToken::ColonColon |
      &HToken::ColonDash |
      &HToken::Comma |
      &HToken::Equals |
      &HToken::UnicNotEquals |
      &HToken::SlashEquals => 0,
      &HToken::RArrow => 0,
      &HToken::RSlashArrow => 0,
      &HToken::RBarArrow => 0,
      &HToken::RBarSlashArrow => 0,
      &HToken::LParen => 0,
      &HToken::RParen => 0,
      &HToken::LCurly => 0,
      &HToken::RCurly => 0,
      // FIXME
      &HToken::LBrack => 700,
      &HToken::RBrack => 0,
      &HToken::Plus => 300,
      &HToken::Star => 320,
      //&HToken::Dash => _,
      //&HToken::Slash => _,
      t => panic!("bug: missing exp lbp: {:?}", t)
    }
  }

  fn exp_rbp(&self, tok: &HTokenSpan) -> i32 {
    let lbp = self.exp_lbp(tok);
    match &tok.token {
      &HToken::Plus |
      &HToken::Star => {
        lbp - 1
      }
      _ => lbp
    }
  }

  fn exp_nud(&mut self, tok: HTokenSpan) -> Result<HExp, HErrorSpan> {
    // TODO
    match tok.token {
      HToken::_Eof => {
        Err((HError::Eof, tok.spaninfo).into())
      }
      HToken::LParen => {
        let mut spaninfo = tok.spaninfo;
        let e = self.exp(0)?;
        let tok = self.current_token()?;
        spaninfo = spaninfo.union(tok.spaninfo);
        match tok.token {
          HToken::RParen => {
            self.advance();
          }
          t => return Err((HError::Expected(vec![HToken::RParen], t), spaninfo).into())
        }
        Ok(HExp::Group(e.into(), spaninfo))
      }
      HToken::Integer(text) => {
        let n: i64 = match text.parse() {
          Err(_) => panic!("bug: failed to parse integer: {}", text),
          Ok(n) => n
        };
        Ok(HExp::Integer(n))
      }
      HToken::Ident(name) => {
        Ok(HExp::Term(HTerm::Name(name), tok.spaninfo))
      }
      HToken::Dash => {
        // FIXME
        unimplemented!();
      }
      //t => Err(HError::MissingNullDenotation(t))
      t => panic!("bug: missing exp nud: {:?}", t)
    }
  }

  fn exp_led(&mut self, left: HExp, tok: HTokenSpan) -> Result<HExp, HErrorSpan> {
    // TODO
    match tok.token {
      HToken::_Eof => {
        Err((HError::Eof, tok.spaninfo).into())
      }
      HToken::Plus => {
        let right = self.exp(self.exp_rbp(&tok))?;
        Ok(HExp::Sum(left.into(), right.into()))
      }
      HToken::Dash => {
        let right = self.exp(self.exp_rbp(&tok))?;
        Ok(HExp::Diff(left.into(), right.into()))
      }
      HToken::Star => {
        let right = self.exp(self.exp_rbp(&tok))?;
        Ok(HExp::Prod(left.into(), right.into()))
      }
      HToken::Slash => {
        let right = self.exp(self.exp_rbp(&tok))?;
        Ok(HExp::Frac(left.into(), right.into()))
      }
      HToken::Caret => {
        let right = self.exp(self.exp_rbp(&tok))?;
        Ok(HExp::Power(left.into(), right.into()))
      }
      HToken::LBrack => {
        let mut spaninfo = tok.spaninfo;
        let mut args = Vec::new();
        loop {
          let right = self.exp(0)?;
          args.push(right);
          let tok = self.current_token()?;
          match tok.token {
            HToken::Comma => {
              self.advance();
            }
            HToken::RBrack => {
              self.advance();
              spaninfo = spaninfo.union(tok.spaninfo);
              break;
            }
            t => {
              spaninfo = spaninfo.union(tok.spaninfo);
              return Err((HError::Expected(vec![HToken::Comma, HToken::RBrack], t), spaninfo).into());
            }
          }
        }
        Ok(HExp::App(left.into(), args, spaninfo))
      }
      t => panic!("bug: missing exp led: {:?} {:?}", left, t)
    }
  }

  fn exp(&mut self, rbp: i32) -> Result<HExp, HErrorSpan> {
    let mut t = self.current_token()?;
    self.advance();
    let mut left = self.exp_nud(t)?;
    t = self.current_token()?;
    while rbp < self.exp_lbp(&t) {
      self.advance();
      left = self.exp_led(left, t)?;
      t = self.current_token()?;
    }
    Ok(left)
  }

  fn form_cla_nud(&mut self, neg: bool, tok: HTokenSpan) -> Result<HClausalForm, HErrorSpan> {
    // TODO
    match tok.token {
      HToken::_Eof => {
        Err((HError::Eof, tok.spaninfo).into())
      }
      HToken::UnicNegation |
      HToken::DashSlash => {
        // FIXME: multiple negation.
        if neg {
          return Err((HError::DoubleNegationSyntax, tok.spaninfo).into());
        }
        let mut spaninfo = tok.spaninfo;
        let tok = self.current_token()?;
        self.advance();
        match self.form_cla_nud(true, tok)? {
          HClausalForm::Lit(neg, atom, f_spaninfo) => {
            spaninfo = spaninfo.union(f_spaninfo);
            Ok(HClausalForm::Lit(!neg, atom, spaninfo))
          }
          f => {
            spaninfo = spaninfo.union(f.spaninfo());
            Err((HError::InvalidNegativeClausalForm, spaninfo).into())
          }
        }
      }
      _ => {
        // FIXME: negation?
        self.backtrack();
        let exp = self.exp(0)?;
        match exp {
          /*HExp::Term(HTerm::Place, _) => {
            let spaninfo = tok.spaninfo.union(exp.spaninfo());
            Err((HError::InvalidClausalForm, spaninfo).into())
          }*/
          HExp::Term(HTerm::Name(rel_name), term_spaninfo) => {
            let mut spaninfo = tok.spaninfo;
            let tok = self.current_token()?;
            match tok.token {
              HToken::LParen => {
                self.advance();
                let mut aparse = AtomParse::Top;
                //let mut neg = false;
                let mut lexps = Vec::new();
                let mut rexps = Vec::new();
                let tok = self.current_token()?;
                match tok.token {
                  HToken::RBarArrow => {
                    self.advance();
                    aparse = AtomParse::Img;
                  }
                  _ => {}
                }
                loop {
                  let e = self.exp(0)?;
                  match aparse {
                    AtomParse::Top => {
                      lexps.push(e);
                    }
                    _ => {
                      rexps.push(e);
                    }
                  }
                  let tok = self.current_token()?;
                  match tok.token {
                    HToken::Comma => {
                      self.advance();
                    }
                    HToken::RArrow => {
                      if neg {
                        spaninfo = spaninfo.union(tok.spaninfo);
                        return Err((HError::InvalidNegation, spaninfo).into());
                      }
                      self.advance();
                      match aparse {
                        AtomParse::Top => {
                          aparse = AtomParse::Arr;
                        }
                        _ => {
                          spaninfo = spaninfo.union(tok.spaninfo);
                          return Err((HError::InvalidAtom, spaninfo).into());
                        }
                      }
                    }
                    /*HToken::RSlashArrow => {
                      self.advance();
                      match aparse {
                        AtomParse::Top => {
                          aparse = AtomParse::Arr;
                        }
                        _ => {
                          spaninfo = spaninfo.union(tok.spaninfo);
                          return Err((HError::InvalidAtom, spaninfo).into());
                        }
                      }
                      neg = true;
                    }*/
                    HToken::RBarArrow => {
                      self.advance();
                      match aparse {
                        AtomParse::Top => {
                          aparse = AtomParse::Dom;
                        }
                        _ => {
                          spaninfo = spaninfo.union(tok.spaninfo);
                          return Err((HError::InvalidAtom, spaninfo).into());
                        }
                      }
                    }
                    /*HToken::RBarSlashArrow => {
                      self.advance();
                      match aparse {
                        AtomParse::Top => {
                          aparse = AtomParse::Dom;
                        }
                        _ => {
                          spaninfo = spaninfo.union(tok.spaninfo);
                          return Err((HError::InvalidAtom, spaninfo).into());
                        }
                      }
                      neg = true;
                    }*/
                    HToken::RParen => {
                      self.advance();
                      match aparse {
                        AtomParse::Top => {
                          if lexps.is_empty() || !rexps.is_empty() {
                            spaninfo = spaninfo.union(tok.spaninfo);
                            return Err((HError::InvalidAtom, spaninfo).into());
                          }
                          spaninfo = spaninfo.union(tok.spaninfo);
                          let pre = HPreForm{
                            rel_name,
                            exps: lexps,
                            spaninfo,
                          };
                          return Ok(HClausalForm::Lit(neg, HAtomicForm::Pre(pre), spaninfo));
                        }
                        AtomParse::Arr => {
                          if lexps.is_empty() || rexps.is_empty() {
                            spaninfo = spaninfo.union(tok.spaninfo);
                            return Err((HError::InvalidClausalForm, spaninfo).into());
                          }
                          spaninfo = spaninfo.union(tok.spaninfo);
                          let app = HAppForm{
                            rel_name,
                            lexps,
                            rexps,
                            spaninfo,
                          };
                          return Ok(HClausalForm::Lit(neg, HAtomicForm::App(app), spaninfo));
                        }
                        AtomParse::Dom => {
                          if lexps.is_empty() || !rexps.is_empty() {
                            spaninfo = spaninfo.union(tok.spaninfo);
                            return Err((HError::InvalidClausalForm, spaninfo).into());
                          }
                          spaninfo = spaninfo.union(tok.spaninfo);
                          let dom = HDomForm{
                            rel_name,
                            lexps,
                            spaninfo,
                          };
                          return Ok(HClausalForm::Lit(neg, HAtomicForm::Dom(dom), spaninfo));
                        }
                        AtomParse::Img => {
                          if !lexps.is_empty() || rexps.is_empty() {
                            spaninfo = spaninfo.union(tok.spaninfo);
                            return Err((HError::InvalidClausalForm, spaninfo).into());
                          }
                          spaninfo = spaninfo.union(tok.spaninfo);
                          let img = HImgForm{
                            rel_name,
                            rexps,
                            spaninfo,
                          };
                          return Ok(HClausalForm::Lit(neg, HAtomicForm::Img(img), spaninfo));
                        }
                      }
                    }
                    t => {
                      return Err((HError::Expected(vec![
                          HToken::Comma,
                          HToken::RArrow,
                          //HToken::RSlashArrow,
                          HToken::RBarArrow,
                          //HToken::RBarSlashArrow,
                          HToken::RParen,
                      ], t), tok.spaninfo).into());
                    }
                  }
                }
              }
              HToken::UnicNotEquals |
              HToken::UnicGte |
              HToken::UnicLte |
              HToken::Equals |
              HToken::SlashEquals |
              HToken::Gt |
              HToken::Gte |
              HToken::Lt |
              HToken::Lte |
              HToken::SlashGt |
              HToken::SlashGte |
              HToken::SlashLt |
              HToken::SlashLte => {
                if neg {
                  panic!("bug: unimplemented: negation of xeq");
                }
                // TODO
                //panic!("bug: unimplemented: xeq clausal forms");
                let left = HExp::Term(HTerm::Name(rel_name), term_spaninfo);
                // FIXME
                self.advance();
                let ord = match tok.token {
                  HToken::UnicNotEquals => HOrder::NotEqual,
                  HToken::UnicGte => HOrder::GreaterEqual,
                  HToken::UnicLte => HOrder::LessEqual,
                  HToken::Equals => HOrder::Equal,
                  HToken::SlashEquals => HOrder::NotEqual,
                  HToken::Gt => HOrder::Greater,
                  HToken::Gte => HOrder::GreaterEqual,
                  HToken::Lt => HOrder::Less,
                  HToken::Lte => HOrder::LessEqual,
                  HToken::SlashGt => HOrder::NotGreater,
                  HToken::SlashGte => HOrder::NotGreaterEqual,
                  HToken::SlashLt => HOrder::NotLess,
                  HToken::SlashLte => HOrder::NotLessEqual,
                  //_ => unreachable!()
                  _t => panic!("bug: unimplemented: order tok")
                };
                let right = self.exp(0)?;
                spaninfo = spaninfo.union(right.spaninfo());
                Ok(HClausalForm::Xeq(left, vec![(ord, right)], spaninfo))
              }
              t => {
                //spaninfo = spaninfo.union(tok.spaninfo);
                return Err((HError::Expected(vec![
                    HToken::LParen,
                    HToken::UnicNotEquals,
                    HToken::UnicGte,
                    HToken::UnicLte,
                    HToken::Equals,
                    HToken::SlashEquals,
                    HToken::Gt,
                    HToken::Gte,
                    HToken::Lt,
                    HToken::Lte,
                    HToken::SlashGt,
                    HToken::SlashGte,
                    HToken::SlashLt,
                    HToken::SlashLte,
                ], t), tok.spaninfo).into());
              }
            }
          }
          left => {
            if neg {
              panic!("bug: unimplemented: negation of xeq");
            }
            let mut spaninfo = tok.spaninfo;
            let tok = self.current_token()?;
            match tok.token {
              HToken::UnicNotEquals |
              HToken::UnicGte |
              HToken::UnicLte |
              HToken::Equals |
              HToken::SlashEquals |
              HToken::Gt |
              HToken::Gte |
              HToken::Lt |
              HToken::Lte |
              HToken::SlashGt |
              HToken::SlashGte |
              HToken::SlashLt |
              HToken::SlashLte => {
                // FIXME
                self.advance();
                let ord = match tok.token {
                  HToken::UnicNotEquals => HOrder::NotEqual,
                  HToken::UnicGte => HOrder::GreaterEqual,
                  HToken::UnicLte => HOrder::LessEqual,
                  HToken::Equals => HOrder::Equal,
                  HToken::SlashEquals => HOrder::NotEqual,
                  HToken::Gt => HOrder::Greater,
                  HToken::Gte => HOrder::GreaterEqual,
                  HToken::Lt => HOrder::Less,
                  HToken::Lte => HOrder::LessEqual,
                  HToken::SlashGt => HOrder::NotGreater,
                  HToken::SlashGte => HOrder::NotGreaterEqual,
                  HToken::SlashLt => HOrder::NotLess,
                  HToken::SlashLte => HOrder::NotLessEqual,
                  //_ => unreachable!()
                  _t => panic!("bug: unimplemented: order tok")
                };
                let right = self.exp(0)?;
                spaninfo = spaninfo.union(right.spaninfo());
                Ok(HClausalForm::Xeq(left, vec![(ord, right)], spaninfo))
              }
              t => {
                //spaninfo = spaninfo.union(tok.spaninfo);
                return Err((HError::Expected(vec![
                    HToken::UnicNotEquals,
                    HToken::UnicGte,
                    HToken::UnicLte,
                    HToken::Equals,
                    HToken::SlashEquals,
                    HToken::Gt,
                    HToken::Gte,
                    HToken::Lt,
                    HToken::Lte,
                    HToken::SlashGt,
                    HToken::SlashGte,
                    HToken::SlashLt,
                    HToken::SlashLte,
                ], t), tok.spaninfo).into());
              }
            }
          }
        }
      }
    }
  }

  fn form_rec_nud(&mut self, tok: HTokenSpan) -> Result<HRecForm, HErrorSpan> {
    // TODO
    match tok.token {
      HToken::_Eof => {
        Err((HError::Eof, tok.spaninfo).into())
      }
      HToken::For => {
        let mut spaninfo = tok.spaninfo;
        let mut quant = HQuant::Universal;
        let tok = self.current_token()?;
        match tok.token {
          HToken::All => {
            self.advance();
            quant = HQuant::Universal;
          }
          HToken::The => {
            self.advance();
            quant = HQuant::Definitive;
          }
          HToken::Some_ => {
            self.advance();
            quant = HQuant::Existential;
          }
          HToken::No => {
            self.advance();
            quant = HQuant::Nonexistential;
          }
          _ => {}
        }
        let tok = self.current_token()?;
        let mut kont: Box<dyn FnOnce(HRecForm) -> HRecForm> = match tok.token {
          HToken::Ident(name) => {
            self.advance();
            Box::new(move |f: HRecForm| {
              let spaninfo = spaninfo.union(f.spaninfo());
              HRecForm::Qua(HQuantForm{
                quant,
                q_term: HTerm::Name(name),
                nested: f.into(),
                spaninfo,
              })
            })
          }
          t => {
            return Err((HError::Expected(vec![HToken::Ident("<quant>".to_string())], t), tok.spaninfo).into());
          }
        };
        loop {
          let tok = self.current_token()?;
          match tok.token {
            HToken::Comma => {
              self.advance();
            }
            HToken::All => {
              self.advance();
              quant = HQuant::Universal;
            }
            HToken::The => {
              self.advance();
              quant = HQuant::Definitive;
            }
            HToken::Some_ => {
              self.advance();
              quant = HQuant::Existential;
            }
            HToken::No => {
              self.advance();
              quant = HQuant::Nonexistential;
            }
            HToken::For => {
              self.advance();
              return Ok(kont(self.form_rec_nud(tok)?));
            }
            HToken::LCurly |
            //HToken::For |
            HToken::If |
            HToken::Iff |
            HToken::Then => {
              self.advance();
              return Ok(kont(match self.form_nud(tok)? {
                HForm::Cla(f, spaninfo) => HRecForm::Con(HCondForm{
                  bicond:   false,
                  ante:     Vec::new(),
                  cons:     vec![HForm::Cla(f, spaninfo)],
                  spaninfo,
                }),
                HForm::Con(cons, spaninfo) => HRecForm::Con(HCondForm{
                  bicond:   false,
                  ante:     Vec::new(),
                  cons,
                  spaninfo,
                }),
                HForm::Rec(f, _) => f
              }));
            }
            /*HToken::For |
            HToken::If |
            HToken::Iff |
            HToken::Then => {
              /*return self.form_rec(kont);*/
              return Ok(kont(self.form_rec_nud(tok)?));
            }*/
            t => {
              //spaninfo = spaninfo.union(tok.spaninfo);
              return Err((HError::Expected(vec![
                  HToken::Comma,
                  HToken::All, HToken::The, HToken::Some_, HToken::No,
                  HToken::For,
                  HToken::LCurly,
                  HToken::If, HToken::Iff, HToken::Then,
              ], t), tok.spaninfo).into());
            }
          }
          let tok = self.current_token()?;
          match tok.token {
            HToken::Ident(name) => {
              self.advance();
              kont = Box::new(move |f: HRecForm| {
                let spaninfo = spaninfo.union(f.spaninfo());
                kont(HRecForm::Qua(HQuantForm{
                  quant,
                  q_term:   HTerm::Name(name),
                  nested:   f.into(),
                  spaninfo,
                }))
              });
            }
            t => {
              //spaninfo = spaninfo.union(tok.spaninfo);
              return Err((HError::Expected(vec![HToken::Ident("<quant>".to_string())], t), tok.spaninfo).into());
            }
          }
        }
      }
      HToken::If => {
        let mut spaninfo = tok.spaninfo;
        let bicond = false;
        let mut ante = Vec::new();
        let mut cons = Vec::new();
        loop {
          let f = self.form()?;
          ante.push(f);
          let tok = self.current_token()?;
          match tok.token {
            HToken::Comma => {
              self.advance();
            }
            HToken::Then => {
              self.advance();
              break;
            }
            t => {
              //spaninfo = spaninfo.union(tok.spaninfo);
              return Err((HError::Expected(vec![HToken::Comma, HToken::Then], t), tok.spaninfo).into());
            }
          }
        }
        loop {
          let f = self.form()?;
          cons.push(f);
          let tok = self.current_token()?;
          match tok.token {
            HToken::Comma => {
              self.advance();
            }
            _ => {
              spaninfo = spaninfo.union(tok.spaninfo);
              return Ok(HRecForm::Con(HCondForm{
                bicond,
                ante,
                cons,
                spaninfo,
              }));
            }
          }
        }
      }
      HToken::Iff => {
        let mut spaninfo = tok.spaninfo;
        let bicond = true;
        let mut ante = Vec::new();
        let mut cons = Vec::new();
        loop {
          let f = self.form()?;
          ante.push(f);
          let tok = self.current_token()?;
          match tok.token {
            HToken::Comma => {
              self.advance();
            }
            HToken::Then => {
              self.advance();
              break;
            }
            t => {
              //spaninfo = spaninfo.union(tok.spaninfo);
              return Err((HError::Expected(vec![HToken::Comma, HToken::Then], t), tok.spaninfo).into());
            }
          }
        }
        loop {
          let f = self.form()?;
          cons.push(f);
          let tok = self.current_token()?;
          match tok.token {
            HToken::Comma => {
              self.advance();
            }
            _ => {
              spaninfo = spaninfo.union(tok.spaninfo);
              return Ok(HRecForm::Con(HCondForm{
                bicond,
                ante,
                cons,
                spaninfo,
              }));
            }
          }
        }
      }
      HToken::Then => {
        let mut spaninfo = tok.spaninfo;
        let mut bicond = false;
        let mut ante = Vec::new();
        let mut cons = Vec::new();
        loop {
          let f = self.form()?;
          cons.push(f);
          let tok = self.current_token()?;
          match tok.token {
            HToken::Comma => {
              self.advance();
            }
            HToken::ColonColon => {
              self.advance();
              bicond = true;
              break;
            }
            HToken::ColonDash => {
              self.advance();
              break;
            }
            _ => {
              spaninfo = spaninfo.union(tok.spaninfo);
              return Ok(HRecForm::Con(HCondForm{
                bicond,
                ante,
                cons,
                spaninfo,
              }));
            }
          }
        }
        loop {
          let f = self.form()?;
          ante.push(f);
          let tok = self.current_token()?;
          match tok.token {
            HToken::Comma => {
              self.advance();
            }
            _ => {
              spaninfo = spaninfo.union(tok.spaninfo);
              return Ok(HRecForm::Con(HCondForm{
                bicond,
                ante,
                cons,
                spaninfo,
              }));
            }
          }
        }
      }
      //t => Err(HError::MissingNullDenotation(t))
      _ => Err((HError::ExpectedRecursion, tok.spaninfo).into())
    }
  }

  fn form_nud(&mut self, tok: HTokenSpan) -> Result<HForm, HErrorSpan> {
    // TODO
    match tok.token {
      HToken::_Eof => {
        Err((HError::Eof, tok.spaninfo).into())
      }
      HToken::LCurly => {
        let mut spaninfo = tok.spaninfo;
        let mut fparse = FormParse::Top;
        let mut tmp_spaninfo = tok.spaninfo;
        let mut tmp_fs = Vec::new();
        let mut alt_fs = Vec::new();
        let mut alt = false;
        let tok = self.current_token()?;
        match tok.token {
          HToken::RCurly => {
            spaninfo = spaninfo.union(tok.spaninfo);
            return Err((HError::EmptyForm, spaninfo).into());
          }
          HToken::Comma => {
            spaninfo = spaninfo.union(tok.spaninfo);
            return Err((HError::InvalidForm, spaninfo).into());
          }
          HToken::ColonDash => {
            spaninfo = spaninfo.union(tok.spaninfo);
            return Err((HError::InvalidConditional, spaninfo).into());
          }
          HToken::DashColon => {
            self.advance();
            fparse = FormParse::RCond;
            alt = true;
          }
          HToken::ColonColon => {
            spaninfo = spaninfo.union(tok.spaninfo);
            return Err((HError::InvalidBiconditional, spaninfo).into());
          }
          _ => {}
        }
        loop {
          let tok = self.current_token()?;
          self.advance();
          let f = self.form_nud(tok)?;
          if alt {
            alt_fs.push(f);
          } else {
            if tmp_fs.is_empty() {
              tmp_spaninfo = f.spaninfo();
            } else {
              tmp_spaninfo = tmp_spaninfo.union(f.spaninfo());
            }
            tmp_fs.push(f);
          }
          let tok = self.current_token()?;
          match tok.token {
            HToken::RCurly => {
              self.advance();
              match fparse {
                FormParse::Top => {
                  match tmp_fs.len() {
                    0 => {
                      spaninfo = spaninfo.union(tok.spaninfo);
                      return Err((HError::EmptyForm, spaninfo).into());
                    }
                    1 => {
                      return Ok(tmp_fs.pop().unwrap());
                    }
                    _ => {
                      spaninfo = spaninfo.union(tok.spaninfo);
                      return Ok(HForm::Con(tmp_fs, spaninfo));
                    }
                  }
                }
                FormParse::LCond => {
                  spaninfo = spaninfo.union(tok.spaninfo);
                  return Ok(HForm::Rec(HRecForm::Con(HCondForm{
                    bicond: false,
                    ante:   alt_fs,
                    cons:   tmp_fs,
                    spaninfo,
                  }), spaninfo));
                }
                FormParse::RCond => {
                  spaninfo = spaninfo.union(tok.spaninfo);
                  return Ok(HForm::Rec(HRecForm::Con(HCondForm{
                    bicond: false,
                    ante:   tmp_fs,
                    cons:   alt_fs,
                    spaninfo,
                  }), spaninfo));
                }
                FormParse::BCond => {
                  // FIXME
                  panic!("bug: missing BCond");
                  /*return Ok(HForm::Rec(HRecForm::Con(HCondForm{
                    bicond: true,
                    ante:   tmp_fs,
                    cons:   alt_fs,
                  })));*/
                }
              }
            }
            HToken::Comma => {
              self.advance();
            }
            HToken::ColonDash => {
              self.advance();
              match fparse {
                FormParse::Top => {
                  fparse = FormParse::LCond;
                  if alt {
                    panic!("bug");
                  }
                  alt = true;
                }
                FormParse::LCond => {
                  assert!(alt);
                }
                FormParse::RCond => {
                  spaninfo = spaninfo.union(tok.spaninfo);
                  return Err((HError::InvalidConditional, spaninfo).into());
                }
                FormParse::BCond => {
                  spaninfo = spaninfo.union(tok.spaninfo);
                  return Err((HError::InvalidBiconditional, spaninfo).into());
                }
              }
            }
            HToken::DashColon => {
              self.advance();
              match fparse {
                FormParse::Top => {
                  fparse = FormParse::RCond;
                  if alt {
                    panic!("bug");
                  }
                  alt = true;
                }
                FormParse::RCond => {
                  assert!(alt);
                }
                FormParse::LCond => {
                  spaninfo = spaninfo.union(tok.spaninfo);
                  return Err((HError::InvalidConditional, spaninfo).into());
                }
                FormParse::BCond => {
                  spaninfo = spaninfo.union(tok.spaninfo);
                  return Err((HError::InvalidBiconditional, spaninfo).into());
                }
              }
            }
            HToken::ColonColon => {
              self.advance();
              match fparse {
                FormParse::Top => {
                  fparse = FormParse::BCond;
                  if alt {
                    panic!("bug");
                  }
                  alt = true;
                }
                FormParse::BCond => {
                  assert!(alt);
                }
                FormParse::LCond | FormParse::RCond => {
                  spaninfo = spaninfo.union(tok.spaninfo);
                  return Err((HError::InvalidConditional, spaninfo).into());
                }
              }
            }
            t => {
              spaninfo = spaninfo.union(tok.spaninfo);
              return Err((HError::Expected(vec![
                  HToken::RCurly,
                  HToken::Comma,
                  HToken::Bar,
                  HToken::Semi,
                  HToken::ColonDash,
                  HToken::DashColon,
                  HToken::ColonColon], t), spaninfo).into());
            }
          }
        }
      }
      HToken::For |
      HToken::If |
      HToken::Iff |
      HToken::Then => {
        let f = self.form_rec_nud(tok)?;
        let f_spaninfo = f.spaninfo();
        Ok(HForm::Rec(f, f_spaninfo))
      }
      HToken::UnicNegation |
      HToken::DashSlash => {
        self.advance();
        let tok = self.current_token()?;
        let f = self.form_cla_nud(true, tok)?;
        let f_spaninfo = f.spaninfo();
        Ok(HForm::Cla(f, f_spaninfo))
      }
      _ => {
        // TODO
        /*match self.form(0)? {
          HForm::Cla(HClausalForm::Lit(neg, atom)) => {
            Ok(HForm::Cla(HClausalForm::Lit(!neg, atom)))
          }
          _ => Err(HError::InvalidNegation)
        }*/
        let f = self.form_cla_nud(false, tok)?;
        let f_spaninfo = f.spaninfo();
        Ok(HForm::Cla(f, f_spaninfo))
      }
      //t => Err(HError::MissingNullDenotation(t))
    }
  }

  fn form(&mut self) -> Result<HForm, HErrorSpan> {
    let t = self.current_token()?;
    self.advance();
    let left = self.form_nud(t)?;
    Ok(left)
  }

  fn tree_parse_rel(&mut self, mut spaninfo: HSpanInfo) -> Result<HTheoryDecl, HErrorSpan> {
    let mut rel_quals = HRelQuals::default();
    loop {
      let tok = self.current_token()?;
      match tok.token {
        HToken::Const => {
          self.advance();
          rel_quals.const_ = true;
        }
        HToken::Cycl => {
          self.advance();
          rel_quals.cycl = true;
        }
        HToken::Equiv => {
          self.advance();
          rel_quals.equiv = true;
        }
        HToken::Func => {
          self.advance();
          rel_quals.func = true;
        }
        HToken::Monc => {
          self.advance();
          rel_quals.monc = true;
        }
        HToken::Order => {
          self.advance();
          rel_quals.order = true;
        }
        HToken::Rcyc => {
          self.advance();
          rel_quals.cycl = true;
          rel_quals.rflx = true;
        }
        HToken::Rflx => {
          self.advance();
          rel_quals.rflx = true;
        }
        HToken::Symm => {
          self.advance();
          rel_quals.symm = true;
        }
        HToken::Fun |
        HToken::Map => {
          self.advance();
          rel_quals.func = true;
          break;
        }
        HToken::Rel => {
          self.advance();
          break;
        }
        t => {
          return Err((HError::Expected(vec![
              HToken::Const,
              HToken::Cycl,
              HToken::Equiv,
              HToken::Fun,
              HToken::Func,
              HToken::Map,
              HToken::Order,
              HToken::Rcyc,
              HToken::Rflx,
              HToken::Rel,
              HToken::Symm], t), tok.spaninfo).into());
        }
      }
    }
    let tok = self.current_token()?;
    let t_spaninfo = tok.spaninfo;
    match (rel_quals.func, tok.token) {
      (false, HToken::ArityIdent(text)) => {
        self.advance();
        let (name, arity) = parse_arity_ident(text).map_err(move |e| HErrorSpan::from((e, t_spaninfo)))?;
        let rel = HRel{
          quals:    rel_quals,
          name,
          arity,
        };
        Ok(HTheoryDecl::Rel(rel))
      }
      (true, HToken::FuncArityIdent(text)) => {
        self.advance();
        let (name, l_arity, r_arity) = parse_func_arity_ident(text).map_err(move |e| HErrorSpan::from((e, t_spaninfo)))?;
        if r_arity > 1 {
          return Err((HError::UnsupportedFuncArity(l_arity, r_arity), t_spaninfo).into());
        }
        let fun = HFun{
          quals:    rel_quals,
          name,
          l_arity,
          r_arity,
        };
        Ok(HTheoryDecl::Fun(fun))
      }
      (false, t) => {
        return Err((HError::Expected(vec![HToken::ArityIdent("<rel>/<arity>".to_owned())], t), t_spaninfo).into());
      }
      (true, t) => {
        return Err((HError::Expected(vec![HToken::FuncArityIdent("<fun>/<in-arity>+<out-arity>".to_owned())], t), t_spaninfo).into());
      }
      (_, t) => {
        return Err((HError::Unexpected(t), t_spaninfo).into());
      }
    }
  }

  fn tree_parse_lem(&mut self, mut spaninfo: HSpanInfo) -> Result<HTheoryDecl, HErrorSpan> {
    let tok = self.current_token()?;
    match tok.token {
      HToken::Axm => {
        self.advance();
        let tok = self.current_token()?;
        let axm_name = match tok.token {
          HToken::Ident(name) => {
            self.advance();
            let tok = self.current_token()?;
            match tok.token {
              HToken::Colon => {
                self.advance();
              }
              t => return Err((HError::Expected(vec![HToken::Colon], t), tok.spaninfo).into())
            }
            Some(name)
          }
          _ => None
        };
        let form = self.form()?;
        let f_spaninfo = form.spaninfo();
        let form = match form {
          HForm::Cla(_, _) |
          HForm::Con(_, _) => {
            return Err((HError::ExpectedRecursion, f_spaninfo).into());
          }
          // FIXME
          HForm::Rec(f, _spaninfo) => f
        };
        // TODO
        Ok(HTheoryDecl::Rec(axm_name, form))
      }
      HToken::Thm => {
        self.advance();
        let tok = self.current_token()?;
        let thm_name = match tok.token {
          HToken::Ident(name) => {
            self.advance();
            let tok = self.current_token()?;
            match tok.token {
              HToken::Colon => {
                self.advance();
              }
              t => return Err((HError::Expected(vec![HToken::Colon], t), spaninfo).into())
            }
            Some(name)
          }
          _ => None
        };
        let form = self.form()?;
        let f_spaninfo = form.spaninfo();
        let form = match form {
          HForm::Cla(_, _) |
          HForm::Con(_, _) => {
            return Err((HError::ExpectedRecursion, f_spaninfo).into());
          }
          // FIXME
          HForm::Rec(f, _spaninfo) => f
        };
        let tok = self.current_token()?;
        match tok.token {
          HToken::Proof => {
            self.advance();
          }
          t => return Err((HError::Expected(vec![HToken::Proof], t), tok.spaninfo).into())
        }
        // FIXME
        let tok = self.current_token()?;
        match tok.token {
          HToken::Elided => {
            self.advance();
          }
          t => return Err((HError::Expected(vec![HToken::Elided], t), tok.spaninfo).into())
        }
        // TODO
        Ok(HTheoryDecl::Rec(thm_name, form))
      }
      HToken::Lem => {
        self.advance();
        let tok = self.current_token()?;
        let lem_name = match tok.token {
          HToken::Ident(name) => {
            self.advance();
            let tok = self.current_token()?;
            match tok.token {
              HToken::Colon => {
                self.advance();
              }
              t => return Err((HError::Expected(vec![HToken::Colon], t), tok.spaninfo).into())
            }
            Some(name)
          }
          _ => None
        };
        let form = self.form()?;
        let f_spaninfo = form.spaninfo();
        let form = match form {
          HForm::Cla(_, _) |
          HForm::Con(_, _) => {
            return Err((HError::ExpectedRecursion, f_spaninfo).into());
          }
          // FIXME
          HForm::Rec(f, _spaninfo) => f
        };
        let tok = self.current_token()?;
        match tok.token {
          HToken::Proof => {
            self.advance();
          }
          t => return Err((HError::Expected(vec![HToken::Proof], t), tok.spaninfo).into())
        }
        // FIXME
        let tok = self.current_token()?;
        match tok.token {
          HToken::Elided => {
            self.advance();
          }
          t => return Err((HError::Expected(vec![HToken::Elided], t), tok.spaninfo).into())
        }
        // TODO
        Ok(HTheoryDecl::Rec(lem_name, form))
      }
      HToken::Assume => {
        self.advance();
        let tok = self.current_token()?;
        match tok.token {
          HToken::Lem => {
            self.advance();
          }
          t => return Err((HError::Expected(vec![HToken::Lem], t), tok.spaninfo).into())
        }
        let tok = self.current_token()?;
        let lem_name = match tok.token {
          HToken::Ident(name) => {
            self.advance();
            let tok = self.current_token()?;
            match tok.token {
              HToken::Colon => {
                self.advance();
              }
              t => return Err((HError::Expected(vec![HToken::Colon], t), tok.spaninfo).into())
            }
            Some(name)
          }
          _ => None
        };
        let form = self.form()?;
        let f_spaninfo = form.spaninfo();
        let form = match form {
          HForm::Cla(_, _) |
          HForm::Con(_, _) => {
            return Err((HError::ExpectedRecursion, f_spaninfo).into());
          }
          // FIXME
          HForm::Rec(f, _spaninfo) => f
        };
        // TODO
        Ok(HTheoryDecl::Rec(lem_name, form))
      }
      HToken::Propose => {
        self.advance();
        let tok = self.current_token()?;
        match tok.token {
          HToken::Lem => {
            self.advance();
          }
          t => return Err((HError::Expected(vec![HToken::Lem], t), tok.spaninfo).into())
        }
        let tok = self.current_token()?;
        let lem_name = match tok.token {
          HToken::Ident(name) => {
            self.advance();
            let tok = self.current_token()?;
            match tok.token {
              HToken::Colon => {
                self.advance();
              }
              t => return Err((HError::Expected(vec![HToken::Colon], t), tok.spaninfo).into())
            }
            Some(name)
          }
          _ => None
        };
        let form = self.form()?;
        let f_spaninfo = form.spaninfo();
        let form = match form {
          HForm::Cla(_, _) |
          HForm::Con(_, _) => {
            return Err((HError::ExpectedRecursion, f_spaninfo).into());
          }
          HForm::Rec(f, _spaninfo) => f
        };
        // TODO
        Ok(HTheoryDecl::Rec(lem_name, form))
      }
      //_ => unreachable!()
      t => {
        return Err((HError::Expected(vec![HToken::Axm, HToken::Thm, HToken::Lem, HToken::Assume, HToken::Propose], t), tok.spaninfo).into());
      }
    }
  }

  fn tree_parse_prog(&mut self, mut spaninfo: HSpanInfo) -> Result<HProgram, HErrorSpan> {
    let tok = self.current_token()?;
    match tok.token {
      HToken::Let => {
        self.advance();
        let mut names = Vec::new();
        loop {
          let tok = self.current_token()?;
          match tok.token {
            HToken::Ident(name) => {
              self.advance();
              names.push(name);
            }
            t => {
              return Err((HError::Expected(vec![HToken::Ident("<ident>".to_string())], t), tok.spaninfo).into());
            }
          }
          let tok = self.current_token()?;
          match tok.token {
            HToken::Comma => {
              self.advance();
            }
            _ => return Ok(HProgram::Let(names)),
          }
        }
      }
      HToken::Where => {
        self.advance();
        let mut cons = Vec::new();
        loop {
          let f = self.form()?;
          cons.push(f);
          let tok = self.current_token()?;
          match tok.token {
            HToken::Comma => {
              self.advance();
            }
            _ => return Ok(HProgram::Where(cons)),
          }
        }
      }
      HToken::Propose => {
        self.advance();
        let mut cons = Vec::new();
        loop {
          let f = self.form()?;
          cons.push(f);
          let tok = self.current_token()?;
          match tok.token {
            HToken::Comma => {
              self.advance();
            }
            _ => return Ok(HProgram::Propose(cons)),
          }
        }
      }
      //_ => unreachable!()
      t => return Err((HError::Expected(vec![HToken::Let, HToken::Where, HToken::Propose], t), tok.spaninfo).into())
    }
  }

  fn tree_nud(&mut self, tok: HTokenSpan) -> Result<HTree, HErrorSpan> {
    // TODO
    match tok.token {
      HToken::_Eof => {
        Err((HError::Eof, tok.spaninfo).into())
      }
      HToken::Theory => {
        //let mut spaninfo = tok.spaninfo;
        let mut decl = Vec::new();
        let mut prog = Vec::new();
        loop {
          let tok = self.current_token()?;
          match tok.token {
            HToken::End => {
              self.advance();
              return Ok(HTree::Theory{decl, prog});
            }
            HToken::Const |
            HToken::Cycl |
            HToken::Equiv |
            HToken::Func |
            HToken::Rcyc |
            HToken::Rflx |
            HToken::Symm |
            HToken::Rel |
            HToken::Fun |
            HToken::Map => {
              decl.push(self.tree_parse_rel(tok.spaninfo)?);
            }
            // FIXME
            /*HToken::Fun |
            HToken::Map => {
              decl.push(self.tree_parse_fun()?);
            }*/
            HToken::Axm |
            HToken::Lem |
            HToken::Thm => {
            //HToken::Assume |
            //HToken::Propose => {
              decl.push(self.tree_parse_lem(tok.spaninfo)?);
            }
            HToken::Let |
            HToken::Propose |
            HToken::Where => {
              prog.push(self.tree_parse_prog(tok.spaninfo)?);
            }
            t => {
              //spaninfo = spaninfo.union(tok.spaninfo);
              return Err((HError::Expected(vec![
                  HToken::End,
                  HToken::Const,
                  HToken::Cycl,
                  HToken::Equiv,
                  HToken::Func,
                  HToken::Rcyc,
                  HToken::Rflx,
                  HToken::Symm,
                  HToken::Rel,
                  HToken::Fun,
                  HToken::Map,
                  HToken::Axm,
                  HToken::Thm,
                  HToken::Lem,
                  HToken::Assume,
                  HToken::Propose], t), tok.spaninfo).into());
            }
          }
        }
      }
      //t => Err(HError::MissingNullDenotation(t))
      t => return Err((HError::Expected(vec![HToken::Theory], t), tok.spaninfo).into())
    }
  }

  fn tree(&mut self) -> Result<HTree, HErrorSpan> {
    let t = self.current_token()?;
    self.advance();
    let left = self.tree_nud(t)?;
    Ok(left)
  }
}

//pub fn parse_new_htree_from_path<P: AsRef<Path>>(path: P) -> Result<HTree, (HError, Option<HSpanInfo>)> {
pub fn parse_new_htree_from_path<P: AsRef<Path>>(path: P) -> Result<HTree, HErrorSpan> {
  let mut source = String::new();
  {
    let mut file = match File::open(path.as_ref()) {
      Err(_) => return Err((HError::Input, HSpanInfo::default()).into()),
      Ok(f) => f
    };
    match file.read_to_string(&mut source) {
      Err(_) => return Err((HError::Encoding, HSpanInfo::default()).into()),
      Ok(_) => {}
    }
  }
  let lexer = HLexer::new(&source);
  let mut parser = HParser::new(lexer);
  parser.advance();
  parser.tree()
}
