use std::fs::File;
use std::io::{self, Read, Seek, SeekFrom};

pub trait BackScan {
  fn back_scan(&mut self, _: &[u8]) -> Option<usize>;
}

pub trait Mode: Default {
  type BackScanState: BackScan;
  fn bin(&self) -> bool;
  fn new_back_scan(&self) -> Self::BackScanState;
  fn keyword(&self, it: &mut impl Iterator<Item=u8>) -> Option<u8> { it.next() }
  fn unum(&self, it: &mut impl Iterator<Item=u8>) -> Option<u64>;
  fn num(&self, it: &mut impl Iterator<Item=u8>) -> Option<i64>;
  fn comment(&self, it: &mut impl Iterator<Item=u8>) -> String;

  fn uvec(&self, it: &mut impl Iterator<Item=u8>) -> Vec<u64> {
    let mut vec = Vec::new();
    loop { match self.unum(it).expect("bad step") {
      0 => return vec,
      i => vec.push(i)
    } }
  }

  fn ivec(&self, it: &mut impl Iterator<Item=u8>) -> Vec<i64> {
    let mut vec = Vec::new();
    loop { match self.num(it).expect("bad step") {
      0 => return vec,
      i => vec.push(i)
    } }
  }

  fn uvec2(&self, it: &mut impl Iterator<Item=u8>) -> Vec<(u64, u64)> {
    let mut vec = Vec::new();
    loop {
      match self.unum(it).expect("bad step") {
        0 => return vec,
        i => vec.push((i, match self.unum(it) {
          Some(j) if j != 0 => j,
          _ => panic!("odd relocation")
        }))
      }
    }
  }

  fn segment_mut(&self, ch: impl FnOnce() -> usize, it: &mut impl Iterator<Item=u8>) -> Segment {
    match self.keyword(it) {
      Some(b'c') => Segment::Comment(self.comment(it)),
      Some(b'a') => Segment::Add(self.unum(it).unwrap(), self.ivec(it)),
      Some(b'd') => Segment::Del(self.unum(it).unwrap(), self.ivec(it)),
      Some(b'f') => Segment::Final(self.unum(it).unwrap(), self.ivec(it)),
      Some(b'l') => Segment::LProof(self.ivec(it)),
      Some(b'o') => Segment::Orig(self.unum(it).unwrap(), self.ivec(it)),
      Some(b'r') => Segment::Reloc(self.uvec2(it)),
      Some(b't') => {
        let n = self.unum(it).unwrap();
        assert!(self.unum(it).unwrap() == 0, "parse error at todo, expected 1 number");
        Segment::Todo(n)
      }
      Some(k) => panic!("parse error at char {}: bad step {:?}", ch(), k as char),
      None => panic!("parse error at char {}: bad step None", ch()),
    }
  }

  fn check_empty(&self, mut it: impl Iterator<Item=u8>) -> bool {
    it.next().is_none()
  }

  fn segment(&self, ch: impl Fn() -> usize, mut it: impl Iterator<Item=u8>) -> Segment {
    let seg = self.segment_mut(&ch, &mut it);
    assert!(self.check_empty(it), "parse error at char {}: segment has trailing characters", ch());
    seg
  }

	fn drat_step(&mut self, it: &mut impl Iterator<Item=u8>) -> Option<DRATStep>;
}

#[derive(Debug)]
pub enum Segment {
  Comment(String),
  Orig(u64, Vec<i64>),
  Add(u64, Vec<i64>),
  LProof(Vec<i64>),
  Reloc(Vec<(u64, u64)>),
  Del(u64, Vec<i64>),
  Final(u64, Vec<i64>),
  Todo(u64),
}

#[derive(Default)] pub struct Bin;
#[derive(Default)] pub struct Ascii;

impl BackScan for Bin {
  fn back_scan(&mut self, buf: &[u8]) -> Option<usize> {
    for (i, &v) in buf.iter().enumerate().rev() {
      if v == 0 { return Some(i + 1) }
    }
    None
  }
}

impl Mode for Bin {
  type BackScanState = Bin;
  #[inline] fn bin(&self) -> bool {true}
  fn new_back_scan(&self) -> Self::BackScanState { Bin }

  fn unum(&self, it: &mut impl Iterator<Item=u8>) -> Option<u64> {
    let mut res: u64 = 0;
    let mut mul: u8 = 0;
    for c in it {
      res |= ((c & 0x7F) as u64) << mul;
      mul += 7;
      if c & 0x80 == 0 {
        return Some(res)
      }
    }
    if res != 0 { panic!("iterator ran out with incomplete number") }
    None
  }

  fn num(&self, it: &mut impl Iterator<Item=u8>) -> Option<i64> {
    self.unum(it).map(|ulit|
      if ulit & 1 != 0 { -((ulit >> 1) as i64) }
      else { (ulit >> 1) as i64 })
  }

  fn comment(&self, it: &mut impl Iterator<Item=u8>) -> String {
    String::from_utf8(it.take_while(|i| *i != 0).collect()).expect("non-utf8")
  }

	fn drat_step(&mut self, it: &mut impl Iterator<Item=u8>) -> Option<DRATStep> {
    match self.keyword(it)? {
      b'c' => Some(DRATStep::Comment(self.comment(it))),
      b'd' => Some(DRATStep::Del(self.ivec(it))),
      b'a' => Some(DRATStep::Add(AddStep(self.ivec(it)))),
      k => panic!("bad keyword {}", k as char)
    }
  }
}

impl Ascii {
  fn spaces(it: &mut impl Iterator<Item=u8>) -> Option<u8> {
    loop { match it.next() {
      Some(c) if c == b' ' || c == b'\n' || c == b'\r' => {},
      o => return o
    } }
  }
  fn initial_neg(it: &mut impl Iterator<Item=u8>) -> (bool, Option<u8>) {
    match Ascii::spaces(it) {
      Some(c) if c == b'-' => (true, it.next()),
      o => (false, o)
    }
  }

  fn parse_num(peek: Option<u8>, it: &mut impl Iterator<Item=u8>) -> Option<u64> {
    let mut val = (peek? as char).to_digit(10).unwrap() as u64;
		while let Some(parsed) = it.next().and_then(|c| (c as char).to_digit(10)) {
			val *= 10;
      val += parsed as u64;
    }
		Some(val)
  }
}

#[derive(Debug, Default)]
pub struct AsciiBackScan {
  in_comment: bool,
  comment_start: bool
}

impl AsciiBackScan {
  #[cold] fn back_scan_comment(&mut self, buf: &[u8]) -> Option<usize> {
    for (i, &v) in buf.iter().enumerate().rev() {
      if v == b'\n' && self.comment_start {
        self.in_comment = false;
        self.comment_start = false;
        return Some(i + 1)
      }
      self.comment_start = v == b'c';
    }
    None
  }
}

impl BackScan for AsciiBackScan {
  fn back_scan(&mut self, buf: &[u8]) -> Option<usize> {
    if self.in_comment {
      self.back_scan_comment(buf)
    } else {
      for (i, &v) in buf.iter().enumerate().rev() {
        if v > b'9' { return Some(i) }
        if v == b'.' {
          self.in_comment = true;
          return self.back_scan_comment(&buf[..i])
        }
      }
      None
    }
  }
}

impl Mode for Ascii {
  type BackScanState = AsciiBackScan;
  #[inline] fn bin(&self) -> bool {false}
  fn new_back_scan(&self) -> Self::BackScanState { AsciiBackScan::default() }
  fn keyword(&self, it: &mut impl Iterator<Item=u8>) -> Option<u8> { Ascii::spaces(it) }
  fn unum(&self, it: &mut impl Iterator<Item=u8>) -> Option<u64> {
    Ascii::parse_num(Ascii::spaces(it), it)
  }
  fn num(&self, it: &mut impl Iterator<Item=u8>) -> Option<i64> {
    let (neg, peek) = Ascii::initial_neg(it);
    let val = Ascii::parse_num(peek, it)?;
    Some(if neg { -(val as i64) } else { val as i64 })
  }
  fn comment(&self, it: &mut impl Iterator<Item=u8>) -> String {
    let mut vec = match it.next() {
      None | Some(b'\n') => return String::new(),
      Some(b' ') => vec![],
      Some(c) => vec![c],
    };
    loop {
      match it.next() {
        None | Some(b'\n') => break,
        Some(b'.') => match it.next() {
          None | Some(b'\n') => break,
          Some(c) => { vec.push(b'.'); vec.push(c) }
        },
        Some(c) => vec.push(c)
      }
    }
    String::from_utf8(vec).expect("non-utf8")
  }
  fn check_empty(&self, mut it: impl Iterator<Item=u8>) -> bool {
    it.all(|c| matches!(c, b' ' | b'\n'))
  }

	fn drat_step(&mut self, it: &mut impl Iterator<Item=u8>) -> Option<DRATStep> {
    match self.keyword(it)? {
      b'c' => Some(DRATStep::Comment(self.comment(it))),
      b'd' => Some(DRATStep::Del(self.ivec(it))),
      k => Some(DRATStep::Add(AddStep(
        self.ivec(&mut Some(k).iter().cloned().chain(it)))))
    }
  }
}

impl BackScan for Option<AsciiBackScan> {
  fn back_scan(&mut self, buf: &[u8]) -> Option<usize> {
    match self {
      Some(this) => this.back_scan(buf),
      None => Bin.back_scan(buf),
    }
  }
}

#[cfg(feature="ascii")]
pub use Ascii as DefaultMode;

#[cfg(not(feature="ascii"))]
pub use Bin as DefaultMode;

impl Mode for bool {
  type BackScanState = Option<AsciiBackScan>;
  fn bin(&self) -> bool {*self}
  fn new_back_scan(&self) -> Self::BackScanState { self.then(AsciiBackScan::default) }
  fn keyword(&self, it: &mut impl Iterator<Item=u8>) -> Option<u8> {
    if *self {Bin.keyword(it)} else {Ascii.keyword(it)}
  }
  fn unum(&self, it: &mut impl Iterator<Item=u8>) -> Option<u64> {
    if *self {Bin.unum(it)} else {Ascii.unum(it)}
  }
  fn num(&self, it: &mut impl Iterator<Item=u8>) -> Option<i64> {
    if *self {Bin.num(it)} else {Ascii.num(it)}
  }
  fn comment(&self, it: &mut impl Iterator<Item=u8>) -> String {
    if *self {Bin.comment(it)} else {Ascii.comment(it)}
  }
  fn uvec(&self, it: &mut impl Iterator<Item=u8>) -> Vec<u64> {
    if *self {Bin.uvec(it)} else {Ascii.uvec(it)}
  }
  fn ivec(&self, it: &mut impl Iterator<Item=u8>) -> Vec<i64> {
    if *self {Bin.ivec(it)} else {Ascii.ivec(it)}
  }
  fn uvec2(&self, it: &mut impl Iterator<Item=u8>) -> Vec<(u64, u64)> {
    if *self {Bin.uvec2(it)} else {Ascii.uvec2(it)}
  }
  fn segment_mut(&self, ch: impl FnOnce() -> usize, it: &mut impl Iterator<Item=u8>) -> Segment {
    if *self {Bin.segment_mut(ch, it)} else {Ascii.segment_mut(ch, it)}
  }
  fn check_empty(&self, it: impl Iterator<Item=u8>) -> bool {
    if *self {Bin.check_empty(it)} else {Ascii.check_empty(it)}
  }
  fn segment(&self, ch: impl Fn() -> usize, it: impl Iterator<Item=u8>) -> Segment {
    if *self {Bin.segment(ch, it)} else {Ascii.segment(ch, it)}
  }
  fn drat_step(&mut self, it: &mut impl Iterator<Item=u8>) -> Option<DRATStep> {
    if *self {Bin.drat_step(it)} else {Ascii.drat_step(it)}
  }
}

pub fn detect_binary(f: &mut File) -> io::Result<bool> {
  if f.seek(SeekFrom::End(-1)).is_err() { return Ok(false) }
  let mut c = [0u8; 1];
  f.read_exact(&mut c)?;
  Ok(c[0] == 0)
}

pub struct LRATParser<M, I> {mode: M, it: I}

impl<M, I> LRATParser<M, I> {
	pub fn from(mode: M, it: I) -> Self { LRATParser {mode, it} }
}

#[derive(Debug)]
pub enum LRATStep {
	Comment(String),
	Add(AddStep, Vec<i64>),
	Del(Vec<i64>)
}

impl<M: Mode, I: Iterator<Item=u8>> Iterator for LRATParser<M, I> {
	type Item = (u64, LRATStep);
	fn next(&mut self) -> Option<(u64, LRATStep)> {
		Some((self.mode.unum(&mut self.it)?,
      match self.mode.keyword(&mut self.it)? {
        b'c' => LRATStep::Comment(self.mode.comment(&mut self.it)),
        b'd' => LRATStep::Del(self.mode.ivec(&mut self.it)),
        k => LRATStep::Add(
          AddStep(self.mode.ivec(&mut Some(k).into_iter().chain(&mut self.it))),
          self.mode.ivec(&mut self.it))
      }
    ))
	}
}

pub struct DRATParser<M, I> {mode: M, it: I}

impl<M, I> DRATParser<M, I> {
	pub fn from(mode: M, it: I) -> Self { DRATParser {mode, it} }
}

#[derive(Debug)]
pub enum DRATStep {
	Comment(String),
	Add(AddStep),
	Del(Vec<i64>)
}

impl<M: Mode, I: Iterator<Item=u8>> Iterator for DRATParser<M, I> {
	type Item = DRATStep;
	fn next(&mut self) -> Option<DRATStep> { self.mode.drat_step(&mut self.it) }
}

#[derive(Debug)]
pub enum Proof {
  LRAT(Vec<i64>),
}

#[derive(Debug, Copy, Clone)]
pub enum ProofRef<'a> {
  LRAT(&'a [i64]),
}

impl Proof {
  pub fn as_ref(&self) -> ProofRef {
    match self {
      Proof::LRAT(v) => ProofRef::LRAT(v),
    }
  }
}

#[derive(Clone)]
pub struct AddStep(pub Vec<i64>);

#[derive(Debug, Copy, Clone)]
pub enum AddStepRef<'a> {
  One(&'a [i64]),
  #[allow(unused)] Two(&'a [i64], &'a [i64]),
}

#[derive(Debug, Copy, Clone)]
pub enum AddKind<'a> {
  RAT(&'a [i64]),
  PR(&'a [i64], &'a [i64]),
}
impl<'a> AddKind<'a> {
  pub fn lemma(&self) -> &'a [i64] {
    match *self {
      AddKind::RAT(lemma) | AddKind::PR(lemma, _) => lemma,
    }
  }

  pub fn witness(&self) -> Option<&'a [i64]> {
    match *self {
      AddKind::RAT(_) => None,
      AddKind::PR(_, witness) => Some(witness),
    }
  }

  #[allow(unused)] pub fn as_ref(self) -> AddStepRef<'a> {
    match self {
      AddKind::RAT(lemma) => AddStepRef::One(lemma),
      AddKind::PR(lemma, witness) => AddStepRef::Two(lemma, witness),
    }
  }
}

impl AddStep {
  pub fn as_ref(&self) -> AddStepRef<'_> { AddStepRef::One(&self.0) }

  pub fn parse(&self) -> AddKind<'_> {
    if let Some(i) = self.0.split_first()
        .and_then(|(&pivot, rest)| rest.iter().position(|&x| pivot == x)) {
      let (lemma, witness) = self.0.split_at(i+1);
      AddKind::PR(lemma, witness)
    } else {
      AddKind::RAT(&self.0)
    }
  }

  pub fn parse_into<R>(mut self, f: impl FnOnce(AddKind<'_>) -> R) -> (R, Vec<i64>) {
    let ak = self.parse();
    (f(ak), {
      if let AddKind::PR(lemma, _) = ak {
        let n = lemma.len();
        self.0.truncate(n)
      }
      self.0
    })
  }
}

impl std::fmt::Debug for AddStep {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.parse().fmt(f) }
}

#[derive(Debug)]
pub enum Step {
  Comment(String),
  Orig(u64, Vec<i64>),
  Add(u64, AddStep, Option<Proof>),
  Del(u64, Vec<i64>),
  Reloc(Vec<(u64, u64)>),
  Final(u64, Vec<i64>),
  Todo(u64),
}

#[derive(Debug, Copy, Clone)]
pub enum StepRef<'a> {
  Comment(&'a str),
  Orig(u64, &'a [i64]),
  Add(u64, AddStepRef<'a>, Option<ProofRef<'a>>),
  Del(u64, &'a [i64]),
  Reloc(&'a [(u64, u64)]),
  Final(u64, &'a [i64]),
  Todo(u64),
}

impl Step {
  pub fn as_ref(&self) -> StepRef<'_> {
    match *self {
      Step::Comment(ref s) => StepRef::Comment(s),
      Step::Orig(i, ref v) => StepRef::Orig(i, v),
      Step::Add(i, ref v, ref p) => StepRef::Add(i, v.as_ref(), p.as_ref().map(Proof::as_ref)),
      Step::Del(i, ref v) => StepRef::Del(i, v),
      Step::Reloc(ref v) => StepRef::Reloc(v),
      Step::Final(i, ref v) => StepRef::Final(i, v),
      Step::Todo(i) => StepRef::Todo(i)
    }
  }
}

impl<'a> StepRef<'a> {
  #[inline] pub fn add(idx: u64, step: &'a [i64], proof: Option<&'a [i64]>) -> Self {
    Self::Add(idx, AddStepRef::One(step), proof.map(ProofRef::LRAT))
  }
}

#[derive(Debug, Clone)]
pub enum ElabStep {
  Comment(String),
  Orig(u64, Vec<i64>),
  Add(u64, AddStep, Vec<i64>),
  Reloc(Vec<(u64, u64)>),
  Del(u64),
}

#[derive(Debug, Clone)]
pub enum ElabStepRef<'a> {
  Comment(&'a str),
  Orig(u64, &'a [i64]),
  Add(u64, AddStepRef<'a>, &'a [i64]),
  Reloc(&'a [(u64, u64)]),
  Del(u64),
}

impl ElabStep {
  pub fn as_ref(&self) -> ElabStepRef {
    match *self {
      ElabStep::Comment(ref s) => ElabStepRef::Comment(s),
      ElabStep::Orig(i, ref v) => ElabStepRef::Orig(i, v),
      ElabStep::Add(i, ref v, ref p) => ElabStepRef::Add(i, v.as_ref(), p),
      ElabStep::Reloc(ref v) => ElabStepRef::Reloc(v),
      ElabStep::Del(i) => ElabStepRef::Del(i),
    }
  }
}

pub(crate) const BUFFER_SIZE: usize = 0x4000;

struct FwdParserInner {
  file: File,
  buffer_start: usize,
  buffer: [u8; BUFFER_SIZE],
  pos: usize,
  end: usize,
}

impl FwdParserInner {
  fn refill(&mut self) -> io::Result<bool> {
    if self.end == BUFFER_SIZE {
      self.buffer_start += BUFFER_SIZE;
      self.pos = 0
    } else {
      self.pos = self.end
    }
    let n = self.file.read(&mut self.buffer[self.pos..])?;
    if n == 0 { return Ok(false) }
    self.end = self.pos + n;
    assert!(self.end <= BUFFER_SIZE);
    Ok(true)
  }
}

impl Iterator for FwdParserInner {
  type Item = u8;
  fn next(&mut self) -> Option<Self::Item> {
    if self.pos < self.end || self.refill().expect("could not read from proof file") {
      let c = unsafe { *self.buffer.get_unchecked(self.pos) };
      self.pos += 1;
      Some(c)
    } else {
      None
    }
  }
}

pub struct FwdParser<M: Mode> {
  mode: M,
  inner: FwdParserInner
}

impl<M: Mode> FwdParser<M> {
  pub fn new(mode: M, file: File) -> Self {
    let inner = FwdParserInner { file, buffer_start: 0, buffer: [0; BUFFER_SIZE], pos: 0, end: 0 };
    Self { mode, inner }
  }
}
impl<M: Mode> Iterator for FwdParser<M> {
  type Item = Segment;

  fn next(&mut self) -> Option<Segment> {
    let inner = &mut self.inner;
    self.mode.keyword(inner)?;
    inner.pos -= 1;
    let start = inner.buffer_start + inner.pos;
    Some(self.mode.segment_mut(|| start, inner))
  }
}
