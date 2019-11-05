use std::fs::File;
use std::io::{self, Read, Seek, SeekFrom};
use super::parser::{parse_unum, parse_num};

const BUFFER_SIZE: usize = 0x4000;

#[derive(Debug)]
enum Segment {
  Orig(u64, Vec<i64>),
  Add(u64, Vec<i64>),
  LProof(Vec<u64>),
  Del(u64, Vec<i64>),
  Final(u64, Vec<i64>)
}

#[derive(Debug)]
enum Proof {
  LRAT(Vec<u64>)
}

#[derive(Debug)]
enum Step {
  Orig(u64, Vec<i64>),
  Add(u64, Vec<i64>, Option<Proof>),
  Del(u64, Vec<i64>),
  Final(u64, Vec<i64>),
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
  fn new(mut file: File) -> io::Result<BackParser> {
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
    fn mk_uvec<I: Iterator<Item=u8>>(mut it: I) -> Vec<u64> {
      let mut vec = Vec::new();
      loop { match parse_unum(&mut it).expect("bad step") {
        0 => return vec,
        i => vec.push(i) } } }
    fn mk_ivec<I: Iterator<Item=u8>>(mut it: I) -> Vec<i64> {
      let mut vec = Vec::new();
      loop { match parse_num(&mut it).expect("bad step") {
        0 => return vec,
        i => vec.push(i) } } }
    match it.next() {
      Some(A) => Segment::Add(parse_unum(&mut it).unwrap(), mk_ivec(&mut it)),
      Some(D) => Segment::Del(parse_unum(&mut it).unwrap(), mk_ivec(&mut it)),
      Some(F) => Segment::Final(parse_unum(&mut it).unwrap(), mk_ivec(&mut it)),
      Some(L) => Segment::LProof(mk_uvec(&mut it)),
      Some(O) => Segment::Orig(parse_unum(&mut it).unwrap(), mk_ivec(&mut it)),
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

  fn next_segment(&mut self) -> Option<Segment> {
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

impl Iterator for BackParser {
  type Item = Step;

  fn next(&mut self) -> Option<Step> {
    match self.next_segment() {
      None => None,
      Some(Segment::Orig(idx, vec)) => Some(Step::Orig(idx, vec)),
      Some(Segment::Add(idx, vec)) => Some(Step::Add(idx, vec, None)),
      Some(Segment::Del(idx, vec)) => Some(Step::Del(idx, vec)),
      Some(Segment::Final(idx, vec)) => Some(Step::Final(idx, vec)),
      Some(Segment::LProof(steps)) => match self.next_segment() {
        Some(Segment::Add(idx, vec)) =>
          Some(Step::Add(idx, vec, Some(Proof::LRAT(steps)))),
        _ => panic!("'l' step not preceded by 'a' step")
      },
    }
  }
}

pub fn check_proof(proof: File) -> io::Result<()> {
  let bp = BackParser::new(proof)?;
  let mut orig: i64 = 0;
  let mut added: i64 = 0;
  let mut deleted: i64 = 0;
  let mut fin: i64 = 0;
  for s in bp {
    match s {
      Step::Orig(_, _) => orig += 1,
      Step::Add(_, _, _) => added += 1,
      Step::Del(_, _) => deleted += 1,
      Step::Final(_, _) => fin += 1,
    }
  }
  println!("{} orig + {} added - {} deleted - {} finalized = {}\n",
    orig, added, deleted, fin, orig + added - deleted - fin);
  Ok(())
}
