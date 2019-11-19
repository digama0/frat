use std::fs::File;
use std::io::{self, Read, Seek, SeekFrom};
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

struct BackParser {
  file: File,
  remaining: usize,
  pos: usize,
  last_read: usize,
  buffers: Vec<Box<[u8]>>,
  free: Vec<Box<[u8]>>,
}

impl BackParser {
  pub fn new(mut file: File) -> io::Result<BackParser> {
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
      free: Vec::new()
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

  fn parse_segment<I: Iterator<Item=u8>>(mut it: I) -> Segment {
    const A: u8 = 'a' as u8;
    const D: u8 = 'd' as u8;
    const F: u8 = 'f' as u8;
    const O: u8 = 'o' as u8;
    const L: u8 = 'l' as u8;
    const R: u8 = 'r' as u8;
    const T: u8 = 't' as u8;
    fn mk_uvec<I: Iterator<Item=u8>>(it: &mut I) -> Vec<u64> {
      let mut vec = Vec::new();
      loop { match parse_unum(it).expect("bad step") {
        0 => return vec,
        i => vec.push(i) } } }
    fn mk_ivec<I: Iterator<Item=u8>>(it: &mut I) -> Clause {
      let mut vec = Vec::new();
      loop { match parse_num(it).expect("bad step") {
        0 => return vec,
        i => vec.push(i) } } }
    match it.next() {
      Some(A) => Segment::Add(parse_unum(&mut it).unwrap(), mk_ivec(&mut it)),
      Some(D) => Segment::Del(parse_unum(&mut it).unwrap(), mk_ivec(&mut it)),
      Some(F) => Segment::Final(parse_unum(&mut it).unwrap(), mk_ivec(&mut it)),
      Some(L) => Segment::LProof(mk_uvec(&mut it)),
      Some(O) => Segment::Orig(parse_unum(&mut it).unwrap(), mk_ivec(&mut it)),
      Some(R) => Segment::Reloc(parse_unum(&mut it).unwrap(), parse_unum(&mut it).unwrap()),
      Some(T) => Segment::Todo(parse_unum(&mut it).unwrap()),
      Some(k) => panic!("bad step {:?}", k as char),
      None => panic!("bad step None"),
    }
  }

  fn parse_segment_from(&mut self, b: usize, i: usize) -> Segment {
    if b == 0 {
      let res = BackParser::parse_segment(self.buffers[0][i..self.pos].iter().copied());
      self.pos = i;
      return res
    } else {
      let res = BackParser::parse_segment(
        self.buffers[b][i..].iter()
          .chain(self.buffers[1..b].iter().rev().flat_map(|buf| buf.iter()))
          .chain(self.buffers[0][..self.pos].iter()).copied());
      self.pos = i;
      self.free.extend(self.buffers.drain(0..b));
      return res
    }
  }
}

impl Iterator for BackParser {
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
            if buf[i] == 0 { return Some(self.parse_segment_from(b, i+1)) }
          }
        }
      } else {
        for (i, &v) in buf.iter().enumerate().rev() {
          if v == 0 { return Some(self.parse_segment_from(b, i+1)) }
        }
      }
    }
    None
  }
}

pub struct StepParser(BackParser);

impl StepParser {
  pub fn new(file: File) -> io::Result<StepParser> {
    Ok(StepParser(BackParser::new(file)?))
  }
}

impl Iterator for StepParser {
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

pub struct ElabStepParser(BackParser);

impl ElabStepParser {
  pub fn new(file: File) -> io::Result<ElabStepParser> {
    Ok(ElabStepParser(BackParser::new(file)?))
  }
}

impl Iterator for ElabStepParser {
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
