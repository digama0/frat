use std::fs::File;
use std::io::{self, Read, Seek, SeekFrom};
use super::parser::parse_num;

const BUFFER_SIZE: usize = 0x4000;

#[derive(Debug)]
enum StepKind { Orig(i64), Add(i64), LProof, Del(i64), Final(i64) }

#[derive(Debug)]
enum Proof {
  LRAT(Vec<i64>)
}

#[derive(Debug)]
enum Step {
  Orig(i64, Vec<i64>),
  Add(i64, Vec<i64>, Option<Proof>),
  Del(i64, Vec<i64>),
  Final(i64, Vec<i64>),
}

struct BackParser {
  file: File,
  remaining: usize,
  pos: usize,
  buffers: Vec<Box<[u8]>>,
  free: Vec<Box<[u8]>>,
}

impl BackParser {
  fn new(mut file: File) -> io::Result<BackParser> {
    let len = file.metadata()?.len();
    let pos = (len % BUFFER_SIZE as u64) as usize;
    file.seek(SeekFrom::End(-(pos as i64)))?;
    let mut buf = Box::new([0; BUFFER_SIZE]);
    file.read_exact(&mut buf[..pos])?;
    Ok(BackParser {
      file,
      remaining: (len / BUFFER_SIZE as u64) as usize,
      pos,
      buffers: vec![buf],
      free: Vec::new()
    })
  }

  fn read_chunk(&mut self) -> io::Result<Option<Box<[u8]>>> {
    if self.remaining == 0 { return Ok(None) }
    let mut buf: Box<[u8]> = self.free.pop().unwrap_or_else(|| Box::new([0; BUFFER_SIZE]));
    self.file.read_exact(&mut buf)?;
    self.remaining -= 1;
    Ok(Some(buf))
  }

  fn parse_segment<I: Iterator<Item=u8>>(mut it: I) -> (StepKind, Vec<i64>) {
    const A: u8 = 'a' as u8;
    const D: u8 = 'd' as u8;
    const F: u8 = 'f' as u8;
    const O: u8 = 'o' as u8;
    const L: u8 = 'l' as u8;
    let k = match it.next() {
      Some(A) => StepKind::Add(parse_num(&mut it).unwrap()),
      Some(D) => StepKind::Del(parse_num(&mut it).unwrap()),
      Some(F) => StepKind::Final(parse_num(&mut it).unwrap()),
      Some(L) => StepKind::LProof,
      Some(O) => StepKind::Orig(parse_num(&mut it).unwrap()),
      Some(k) => panic!("bad step {:?}", k as char),
      None => panic!("bad step None"),
    };
    let mut vec = Vec::new();
    loop {
      match parse_num(&mut it).expect("bad step") {
        0 => return (k, vec),
        i => vec.push(i)
      }
    }
  }

  fn parse_segment_from(&mut self, b: usize, i: usize) -> (StepKind, Vec<i64>) {
    if b == 0 {
      let res = BackParser::parse_segment(self.buffers[0][i..self.pos].iter().copied());
      self.pos = i;
      return res
    } else {
      let res = BackParser::parse_segment(
        self.buffers[1..b+1].iter().rev()
          .flat_map(|buf| buf.iter())
          .chain(self.buffers[b][i..].iter()).copied());
      self.pos = i;
      self.free.extend(self.buffers.drain(0..b));
      return res
    }
  }

  fn next_segment(&mut self) -> Option<(StepKind, Vec<i64>)> {
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
      Some((StepKind::Orig(idx), vec)) => Some(Step::Orig(idx, vec)),
      Some((StepKind::Add(idx), vec)) => Some(Step::Add(idx, vec, None)),
      Some((StepKind::Del(idx), vec)) => Some(Step::Del(idx, vec)),
      Some((StepKind::Final(idx), vec)) => Some(Step::Final(idx, vec)),
      Some((StepKind::LProof, steps)) => match self.next_segment() {
        Some((StepKind::Add(idx), vec)) =>
          Some(Step::Add(idx, vec, Some(Proof::LRAT(steps)))),
        _ => panic!("l step not preceded by a step")
      },
    }
  }
}

pub fn check_proof(proof: File) -> io::Result<()> {
  let bp = BackParser::new(proof)?;
  for s in bp { eprintln!("{:?}", s) }
  Ok(())
}
