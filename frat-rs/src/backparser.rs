use std::fs::File;
use std::io::{self, Read, Seek, SeekFrom};
use std::marker::PhantomData;
use super::parser::*;

const BUFFER_SIZE: usize = 0x4000;

pub type Clause = Vec<i64>;

#[derive(Debug)]
enum Segment {
  Orig(u64, Clause),
  Add(u64, Clause),
  LProof(Vec<u64>),
  Reloc(u64, u64),
  Del(u64, Clause),
  Final(u64, Clause),
  Todo(u64),
}

#[derive(Debug)]
pub enum Proof {
  LRAT(Vec<u64>),
  Sorry
}

#[derive(Debug)]
pub enum Step {
  Orig(u64, Clause),
  Add(u64, Clause, Option<Proof>),
  Del(u64, Clause),
  Reloc(u64, u64),
  Final(u64, Clause),
  Todo(u64),
}

#[derive(Debug, Clone)]
pub enum ElabStep {
  Orig(u64, Vec<i64>),
  Add(u64, Vec<i64>, Vec<u64>),
  Reloc(u64, u64),
  Del(u64),
}

struct BackParser<M> {
  file: File,
  remaining: usize,
  pos: usize,
  last_read: usize,
  buffers: Vec<Box<[u8]>>,
  free: Vec<Box<[u8]>>,
  _marker: PhantomData<M>,
}

impl<M> BackParser<M> {
  pub fn new(mut file: File) -> io::Result<BackParser<M>> {
    let len = file.metadata()?.len() as usize;
    let pos = len % BUFFER_SIZE;
    file.seek(SeekFrom::End(-(pos as i64)))?;
    let mut buf = Box::new([0; BUFFER_SIZE]);
    file.read_exact(&mut buf[..pos])?;
    Ok(BackParser {
      file,
      remaining: len / BUFFER_SIZE,
      pos,
      last_read: pos,
      buffers: vec![buf],
      free: Vec::new(),
      _marker: PhantomData
    })
  }

  fn read_chunk(&mut self) -> io::Result<Option<Box<[u8]>>> {
    if self.remaining == 0 { return Ok(None) }
    let mut buf: Box<[u8]> = self.free.pop().unwrap_or_else(|| Box::new([0; BUFFER_SIZE]));
    self.file.seek(SeekFrom::Current(-((BUFFER_SIZE + self.last_read) as i64)))?;
    self.file.read_exact(&mut buf)?;
    self.last_read = BUFFER_SIZE;
    self.remaining -= 1;
    Ok(Some(buf))
  }
}

pub trait Mode {
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

  fn ivec<I: Iterator<Item=u8>>(it: &mut I) -> Clause {
    let mut vec = Vec::new();
    loop { match Self::num(it).expect("bad step") {
      0 => return vec,
      i => vec.push(i)
    } }
  }
}

pub struct Bin;
pub struct Ascii;

impl Mode for Bin {
  const OFFSET: usize = 1;
  fn back_scan(c: u8) -> bool { c == 0 }
  fn unum<I: Iterator<Item=u8>>(it: &mut I) -> Option<u64> { parse_unum(it) }
  fn num<I: Iterator<Item=u8>>(it: &mut I) -> Option<i64> { parse_num(it) }
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

impl<M: Mode> BackParser<M> {
  fn parse_segment<I: Iterator<Item=u8>>(mut it: I) -> Segment {
    const A: u8 = 'a' as u8;
    const D: u8 = 'd' as u8;
    const F: u8 = 'f' as u8;
    const O: u8 = 'o' as u8;
    const L: u8 = 'l' as u8;
    const R: u8 = 'r' as u8;
    const T: u8 = 't' as u8;
    match M::keyword(&mut it) {
      Some(A) => Segment::Add(M::unum(&mut it).unwrap(), M::ivec(&mut it)),
      Some(D) => Segment::Del(M::unum(&mut it).unwrap(), M::ivec(&mut it)),
      Some(F) => Segment::Final(M::unum(&mut it).unwrap(), M::ivec(&mut it)),
      Some(L) => Segment::LProof(M::uvec(&mut it)),
      Some(O) => Segment::Orig(M::unum(&mut it).unwrap(), M::ivec(&mut it)),
      Some(R) => Segment::Reloc(M::unum(&mut it).unwrap(), M::unum(&mut it).unwrap()),
      Some(T) => Segment::Todo(M::unum(&mut it).unwrap()),
      Some(k) => panic!("bad step {:?}", k as char),
      None => panic!("bad step None"),
    }
  }

  fn parse_segment_from(&mut self, b: usize, i: usize) -> Segment {
    if b == 0 {
      let res = BackParser::<M>::parse_segment(self.buffers[0][i..self.pos].iter().copied());
      self.pos = i;
      return res
    } else {
      let res = BackParser::<M>::parse_segment(
        self.buffers[b][i..].iter()
          .chain(self.buffers[1..b].iter().rev().flat_map(|buf| buf.iter()))
          .chain(self.buffers[0][..self.pos].iter()).copied());
      self.pos = i;
      self.free.extend(self.buffers.drain(0..b));
      return res
    }
  }
}

impl<M: Mode> Iterator for BackParser<M> {
  type Item = Segment;

  fn next(&mut self) -> Option<Segment> {
    for b in 0.. {
      let buf: &[u8] = match self.buffers.get(b) {
        None => match self.read_chunk().expect("could not read from proof file") {
          None => {
            if b == 1 && self.pos == 0 { break }
            return Some(self.parse_segment_from(b-1, 0))
          },
          Some(buf) => { self.buffers.push(buf); self.buffers.last().unwrap() }
        },
        Some(buf) => buf
      };
      if b == 0 {
        if self.pos != 0 {
          for i in (0..self.pos-1).rev() {
            if M::back_scan(buf[i]) { return Some(self.parse_segment_from(b, i + M::OFFSET)) }
          }
        }
      } else {
        for (i, &v) in buf.iter().enumerate().rev() {
          if M::back_scan(v) { return Some(self.parse_segment_from(b, i + M::OFFSET)) }
        }
      }
    }
    None
  }
}

pub struct StepParser<M>(BackParser<M>);

impl<M> StepParser<M> {
  pub fn new(file: File) -> io::Result<StepParser<M>> {
    Ok(StepParser(BackParser::new(file)?))
  }
}

impl<M: Mode> Iterator for StepParser<M> {
  type Item = Step;

  fn next(&mut self) -> Option<Step> {
    match self.0.next() {
      None => None,
      Some(Segment::Orig(idx, vec)) => Some(Step::Orig(idx, vec)),
      Some(Segment::Add(idx, vec)) => Some(Step::Add(idx, vec, None)),
      Some(Segment::Del(idx, vec)) => Some(Step::Del(idx, vec)),
      Some(Segment::Reloc(from, to)) => Some(Step::Reloc(from, to)),
      Some(Segment::Final(idx, vec)) => Some(Step::Final(idx, vec)),
      Some(Segment::LProof(steps)) => match self.0.next() {
        Some(Segment::Add(idx, vec)) =>
          Some(Step::Add(idx, vec, Some(Proof::LRAT(steps)))),
        _ => panic!("'l' step not preceded by 'a' step")
      },
      Some(Segment::Todo(idx)) => Some(Step::Todo(idx)),
    }
  }
}

pub struct ElabStepParser<M>(BackParser<M>);

impl<M> ElabStepParser<M> {
  pub fn new(file: File) -> io::Result<ElabStepParser<M>> {
    Ok(ElabStepParser(BackParser::new(file)?))
  }
}

impl<M: Mode> Iterator for ElabStepParser<M> {
  type Item = ElabStep;

  fn next(&mut self) -> Option<ElabStep> {
    match self.0.next() {
      None => None,
      Some(Segment::Orig(idx, vec)) => Some(ElabStep::Orig(idx, vec)),
      Some(Segment::Add(_, _)) => panic!("add step has no proof"),
      Some(Segment::Del(idx, vec)) =>
        {assert!(vec.is_empty()); Some(ElabStep::Del(idx))},
      Some(Segment::Reloc(from, to)) => Some(ElabStep::Reloc(from, to)),
      Some(Segment::LProof(steps)) => match self.0.next() {
        Some(Segment::Add(idx, vec)) =>
          Some(ElabStep::Add(idx, vec, steps)),
        _ => panic!("'l' step not preceded by 'a' step")
      },
      Some(_) => self.next(),
    }
  }
}

pub fn detect_binary(f: &mut File) -> io::Result<bool> {
  let mut buf = [0u8; 2];
  let i = f.read(&mut buf)?;
  Ok(i == 2 && !(buf[0] == (' ' as u8) || buf[1] == (' ' as u8)))
}
