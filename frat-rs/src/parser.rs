use std::fs::File;
use std::io::{self, Read, Seek, SeekFrom};
use std::marker::PhantomData;

pub trait Mode: Default {
  const OFFSET: usize;
  fn back_scan(c: u8) -> bool;
  fn keyword<I: Iterator<Item=u8>>(it: &mut I) -> Option<u8> { it.next() }
  fn unum<I: Iterator<Item=u8>>(it: &mut I) -> Option<u64>;
  fn num<I: Iterator<Item=u8>>(it: &mut I) -> Option<i64>;

  fn uvec<I: Iterator<Item=u8>>(it: &mut I) -> Vec<u64> {
    let mut vec = Vec::new();
    loop { match Self::unum(it).expect("bad step") {
      0 => return vec,
      i => vec.push(i)
    } }
  }

  fn ivec<I: Iterator<Item=u8>>(it: &mut I) -> Vec<i64> {
    let mut vec = Vec::new();
    loop { match Self::num(it).expect("bad step") {
      0 => return vec,
      i => vec.push(i)
    } }
  }

  fn uvec2<I: Iterator<Item=u8>>(it: &mut I) -> Vec<(u64, u64)> {
    let mut vec = Vec::new();
    loop {
      match Self::unum(it).expect("bad step") {
        0 => return vec,
        i => vec.push((i, match Self::unum(it) {
          Some(j) if j != 0 => j,
          _ => panic!("odd relocation")
        }))
      }
    }
  }
}

#[derive(Default)] pub struct Bin;
#[derive(Default)] pub struct Ascii;

impl Mode for Bin {
  const OFFSET: usize = 1;
  fn back_scan(c: u8) -> bool { c == 0 }

  fn unum<I: Iterator<Item=u8>>(it: &mut I) -> Option<u64> {
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

  fn num<I: Iterator<Item=u8>>(it: &mut I) -> Option<i64> {
    Bin::unum(it).map(|ulit|
      if ulit & 1 != 0 { -((ulit >> 1) as i64) }
      else { (ulit >> 1) as i64 })
  }
}
impl Ascii {
  fn spaces<I: Iterator<Item=u8>>(it: &mut I) -> Option<u8> {
    loop { match it.next() {
      Some(c) if c == (' ' as u8) || c == ('\n' as u8) || c == ('\r' as u8) => {},
      o => return o
    } }
  }
  fn initial_neg<I: Iterator<Item=u8>>(it: &mut I) -> (bool, Option<u8>) {
    match Ascii::spaces(it) {
      Some(c) if c == ('-' as u8) => (true, it.next()),
      o => (false, o)
    }
  }

  fn parse_num<I: Iterator<Item=u8>>(peek: Option<u8>, it: &mut I) -> Option<u64> {
    let mut val = (peek? as char).to_digit(10).unwrap() as u64;
		while let Some(parsed) = it.next().and_then(|c| (c as char).to_digit(10)) {
			val *= 10;
      val += parsed as u64;
    }
		Some(val)
  }

}
impl Mode for Ascii {
  const OFFSET: usize = 0;
  fn back_scan(c: u8) -> bool { c > ('9' as u8) }
  fn keyword<I: Iterator<Item=u8>>(it: &mut I) -> Option<u8> { Ascii::spaces(it) }
  fn unum<I: Iterator<Item=u8>>(it: &mut I) -> Option<u64> {
    Ascii::parse_num(Ascii::spaces(it), it)
  }
  fn num<I: Iterator<Item=u8>>(it: &mut I) -> Option<i64> {
    let (neg, peek) = Ascii::initial_neg(it);
    let val = Ascii::parse_num(peek, it)?;
    Some(if neg { -(val as i64) } else { val as i64 })
  }
}

pub fn detect_binary(f: &mut File) -> io::Result<bool> {
  if let Err(_) = f.seek(SeekFrom::End(-1)) { return Ok(false) }
  let mut c = [0u8; 1];
  f.read_exact(&mut c)?;
  Ok(c[0] == 0)
}

pub struct LRATParser<M, I>(I, PhantomData<M>);

impl<M, I> LRATParser<M, I> {
	pub fn from(_: M, it: I) -> Self { LRATParser(it, PhantomData) }
}

pub enum LRATStep {
	Add(Vec<i64>, Vec<i64>),
	Del(Vec<i64>)
}

impl<M: Mode, I: Iterator<Item=u8>> Iterator for LRATParser<M, I> {
	type Item = (u64, LRATStep);
	fn next(&mut self) -> Option<(u64, LRATStep)> {
    const D: u8 = 'd' as u8;
		Some((M::unum(&mut self.0)?,
      match M::keyword(&mut self.0)? {
        D => LRATStep::Del(M::ivec(&mut self.0)),
        k => LRATStep::Add(
          M::ivec(&mut Some(k).iter().cloned().chain(&mut self.0)),
          M::ivec(&mut self.0))
      }
    ))
	}
}

pub struct DRATParser<M, I>(I, PhantomData<M>);

impl<M, I> DRATParser<M, I> {
	pub fn from(_: M, it: I) -> Self { DRATParser(it, PhantomData) }
}

pub enum DRATStep {
	Add(Vec<i64>),
	Del(Vec<i64>)
}

impl<M: Mode, I: Iterator<Item=u8>> Iterator for DRATParser<M, I> {
	type Item = DRATStep;
	fn next(&mut self) -> Option<DRATStep> {
    const D: u8 = 'd' as u8;
    match M::keyword(&mut self.0)? {
      D => Some(DRATStep::Del(M::ivec(&mut self.0))),
      k => Some(DRATStep::Add(M::ivec(&mut Some(k).iter().cloned().chain(&mut self.0))))
    }
	}
}

#[derive(Debug)]
pub enum Proof {
  LRAT(Vec<u64>),
  Sorry
}

#[derive(Debug)]
pub enum Step {
  Orig(u64, Vec<i64>),
  Add(u64, Vec<i64>, Option<Proof>),
  Del(u64, Vec<i64>),
  Reloc(Vec<(u64, u64)>),
  Final(u64, Vec<i64>),
  Todo(u64),
}

#[derive(Debug, Clone)]
pub enum ElabStep {
  Orig(u64, Vec<i64>),
  Add(u64, Vec<i64>, Vec<u64>),
  Reloc(Vec<(u64, u64)>),
  Del(u64),
}

#[derive(Debug, Copy, Clone)]
pub enum ProofRef<'a> {
  LRAT(&'a Vec<u64>),
  Sorry
}

#[derive(Debug, Copy, Clone)]
pub enum StepRef<'a> {
  Orig(u64, &'a Vec<i64>),
  Add(u64, &'a Vec<i64>, Option<ProofRef<'a>>),
  Del(u64, &'a Vec<i64>),
  Reloc(&'a Vec<(u64, u64)>),
  Final(u64, &'a Vec<i64>),
  Todo(u64),
}

impl Proof {
  pub fn as_ref(&self) -> ProofRef {
    match self {
      Proof::LRAT(ref v) => ProofRef::LRAT(v),
      Proof::Sorry => ProofRef::Sorry
    }
  }
}

impl Step {
  pub fn as_ref(&self) -> StepRef {
    match self {
      &Step::Orig(i, ref v) => StepRef::Orig(i, v),
      &Step::Add(i, ref v, ref p) => StepRef::Add(i, v, p.as_ref().map(Proof::as_ref)),
      &Step::Del(i, ref v) => StepRef::Del(i, v),
      &Step::Reloc(ref v) => StepRef::Reloc(v),
      &Step::Final(i, ref v) => StepRef::Final(i, v),
      &Step::Todo(i) => StepRef::Todo(i)
    }
  }
}