use std::fs::File;
use std::io::{self, Read, Seek, SeekFrom};

pub trait Mode: Default {
  fn offset(&self) -> usize;
  fn bin(&self) -> bool;
  fn back_scan(&self, c: u8) -> bool;
  fn keyword(&self, it: &mut impl Iterator<Item=u8>) -> Option<u8> { it.next() }
  fn unum(&self, it: &mut impl Iterator<Item=u8>) -> Option<u64>;
  fn num(&self, it: &mut impl Iterator<Item=u8>) -> Option<i64>;

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

  fn segment(&self, it: &mut impl Iterator<Item=u8>) -> Segment {
    match self.keyword(it) {
      Some(b'a') => Segment::Add(self.unum(it).unwrap(), self.ivec(it)),
      Some(b'd') => Segment::Del(self.unum(it).unwrap(), self.ivec(it)),
      Some(b'f') => Segment::Final(self.unum(it).unwrap(), self.ivec(it)),
      Some(b'l') => Segment::LProof(self.ivec(it)),
      Some(b'o') => Segment::Orig(self.unum(it).unwrap(), self.ivec(it)),
      Some(b'r') => Segment::Reloc(self.uvec2(it)),
      Some(b't') => Segment::Todo(self.unum(it).unwrap()),
      Some(k) => panic!("bad step {:?}", k as char),
      None => panic!("bad step None"),
    }
  }
}

#[derive(Debug)]
pub enum Segment {
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

impl Mode for Bin {
  #[inline] fn offset(&self) -> usize {1}
  #[inline] fn bin(&self) -> bool {true}
  #[inline] fn back_scan(&self, c: u8) -> bool { c == 0 }

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

impl Mode for Ascii {
  #[inline] fn offset(&self) -> usize {0}
  #[inline] fn bin(&self) -> bool {false}
  #[inline] fn back_scan(&self, c: u8) -> bool { c > b'9' }
  fn keyword(&self, it: &mut impl Iterator<Item=u8>) -> Option<u8> { Ascii::spaces(it) }
  fn unum(&self, it: &mut impl Iterator<Item=u8>) -> Option<u64> {
    Ascii::parse_num(Ascii::spaces(it), it)
  }
  fn num(&self, it: &mut impl Iterator<Item=u8>) -> Option<i64> {
    let (neg, peek) = Ascii::initial_neg(it);
    let val = Ascii::parse_num(peek, it)?;
    Some(if neg { -(val as i64) } else { val as i64 })
  }
}

impl Mode for bool {
  fn offset(&self) -> usize {if *self {Bin.offset()} else {Ascii.offset()}}
  fn bin(&self) -> bool {*self}
  fn back_scan(&self, c: u8) -> bool {
    if *self {Bin.back_scan(c)} else {Ascii.back_scan(c)}
  }
  fn keyword(&self, it: &mut impl Iterator<Item=u8>) -> Option<u8> {
    if *self {Bin.keyword(it)} else {Ascii.keyword(it)}
  }
  fn unum(&self, it: &mut impl Iterator<Item=u8>) -> Option<u64> {
    if *self {Bin.unum(it)} else {Ascii.unum(it)}
  }
  fn num(&self, it: &mut impl Iterator<Item=u8>) -> Option<i64> {
    if *self {Bin.num(it)} else {Ascii.num(it)}
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
	Add(AddStep, Vec<i64>),
	Del(Vec<i64>)
}

impl<M: Mode, I: Iterator<Item=u8>> Iterator for LRATParser<M, I> {
	type Item = (u64, LRATStep);
	fn next(&mut self) -> Option<(u64, LRATStep)> {
		Some((self.mode.unum(&mut self.it)?,
      match self.mode.keyword(&mut self.it)? {
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
	Add(AddStep),
	Del(Vec<i64>)
}

impl<M: Mode, I: Iterator<Item=u8>> Iterator for DRATParser<M, I> {
	type Item = DRATStep;
	fn next(&mut self) -> Option<DRATStep> {
    if self.mode.bin() {
      match self.mode.keyword(&mut self.it)? {
        b'd' => Some(DRATStep::Del(self.mode.ivec(&mut self.it))),
        b'a' => Some(DRATStep::Add(AddStep(self.mode.ivec(&mut self.it)))),
        k => panic!("bad keyword {}", k as char)
      }
    } else {
      match self.mode.keyword(&mut self.it)? {
        b'd' => Some(DRATStep::Del(self.mode.ivec(&mut self.it))),
        k => Some(DRATStep::Add(AddStep(
          self.mode.ivec(&mut Some(k).iter().cloned().chain(&mut self.it)))))
      }
    }
	}
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

#[derive(Debug, Clone)]
pub struct AddStep(pub Vec<i64>);

#[derive(Debug, Copy, Clone)]
pub enum AddStepRef<'a> {
  One(&'a [i64]),
  #[allow(unused)] Two(&'a [i64], &'a [i64]),
}

#[derive(Debug, Copy, Clone)]
pub enum AddKind<'a> {
  DRAT(&'a [i64]),
  PR(&'a [i64], &'a [i64]),
}
impl<'a> AddKind<'a> {
  pub fn lemma(&self) -> &'a [i64] {
    match *self {
      AddKind::DRAT(lemma) | AddKind::PR(lemma, _) => lemma,
    }
  }

  pub fn witness(&self) -> Option<&'a [i64]> {
    match *self {
      AddKind::DRAT(_) => None,
      AddKind::PR(_, witness) => Some(witness),
    }
  }

  #[allow(unused)] pub fn as_ref(self) -> AddStepRef<'a> {
    match self {
      AddKind::DRAT(lemma) => AddStepRef::One(lemma),
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
      AddKind::DRAT(&self.0)
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

#[derive(Debug)]
pub enum Step {
  Orig(u64, Vec<i64>),
  Add(u64, AddStep, Option<Proof>),
  Del(u64, Vec<i64>),
  Reloc(Vec<(u64, u64)>),
  Final(u64, Vec<i64>),
  Todo(u64),
}

#[derive(Debug, Copy, Clone)]
pub enum StepRef<'a> {
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
  Orig(u64, Vec<i64>),
  Add(u64, AddStep, Vec<i64>),
  Reloc(Vec<(u64, u64)>),
  Del(u64),
}

#[derive(Debug, Clone)]
pub enum ElabStepRef<'a> {
  Orig(u64, &'a [i64]),
  Add(u64, AddStepRef<'a>, &'a [i64]),
  Reloc(&'a [(u64, u64)]),
  Del(u64),
}

impl ElabStep {
  pub fn as_ref(&self) -> ElabStepRef {
    match *self {
      ElabStep::Orig(i, ref v) => ElabStepRef::Orig(i, v),
      ElabStep::Add(i, ref v, ref p) => ElabStepRef::Add(i, v.as_ref(), p),
      ElabStep::Reloc(ref v) => ElabStepRef::Reloc(v),
      ElabStep::Del(i) => ElabStepRef::Del(i),
    }
  }
}

impl<'a> ElabStepRef<'a> {
  #[inline] pub fn add(idx: u64, step: &'a [i64], proof: &'a [i64]) -> Self {
    Self::Add(idx, AddStepRef::One(step), proof)
  }
}
