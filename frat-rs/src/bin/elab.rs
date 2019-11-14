#[path="../parser.rs"] mod parser;

// use std::process::exit;
// use std::collections::HashMap;
use std::io::{self, Read, Write, Seek, SeekFrom};
use std::fs::{File, read_to_string};
use std::env;
use std::convert::TryInto;
use parser::{parse_unum, parse_num, parse_dimacs};
use std::collections::HashMap;

const BUFFER_SIZE: usize = 0x4000;

type Clause = Vec<i64>;

#[derive(Debug)]
enum Segment {
  Orig(u64, Vec<i64>),
  Add(u64, Vec<i64>),
  LProof(Vec<u64>),
  Del(u64, Vec<i64>),
  Final(u64, Vec<i64>),
  Todo(u64),
}

#[derive(Debug)]
pub enum Proof {
  LRAT(Vec<u64>)
}

#[derive(Debug)]
pub enum Step {
  Orig(u64, Vec<i64>),
  Add(u64, Vec<i64>, Option<Proof>),
  Del(u64, Vec<i64>),
  Final(u64, Vec<i64>),
  Todo(u64),
}

#[derive(Debug)]
#[derive(Clone)]
pub enum ElabStep {
  Orig(u64, Vec<i64>),
  Add(u64, Vec<i64>, Vec<u64>),
  Del(u64),
}

// Type used to represent the status of a clause under a specific variable assigntment.
pub enum ClaSta {
  Unsat,
  Unit(i64),
  Plural
}

// #[derive(Clone)]
// #[derive(Debug)]
struct IdCla<'a> {
  id: u64,
  marked: bool,
  used: bool,
  cla: & 'a Clause
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
    const T: u8 = 't' as u8;
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
      Some(Segment::Todo(idx)) => Some(Step::Todo(idx))
    }
  }
}

fn clause_status(v: &Vec<i64>, c: &Clause) -> ClaSta {
  // 'uf' holds an unfalsified literal of the clause, if one has been found
  let mut uf: Option<i64> = None;

  for l in c {
    if !v.contains(&-l) {
      if uf == None {
        uf = Some(*l);
      } else {
        return ClaSta::Plural
      }
    }
  }

  match uf {
    None => ClaSta::Unsat,
    Some(l) => ClaSta::Unit(l)
  }
}

// Derive a new subunit clause and update all arguments accordingly.
// Return true if a contradiction was found, false if a unit clause
// was derived, and panic if neither
fn propagate_once(is: &mut Vec<u64>, v: &mut Vec<i64>, ics: &mut Vec<IdCla>) -> bool {
  for ic in ics {
    if !ic.used { // Only consider clauses that have not been used for UP yet
      match clause_status(v, ic.cla) {
        ClaSta::Unsat => {
          is.push(ic.id);
          ic.used = true;
          return true;
        }
        ClaSta::Unit(l) => {
          is.push(ic.id);
          v.push(l);
          ic.used = true;
          return false;
        }
        ClaSta:: Plural => ()
      }
    }
  }

  panic!("Unit progress stuck");
}

fn propagate_core(mut is: Vec<u64>, mut v: Vec<i64>, mut cs: Vec<(IdCla)>) -> Vec<u64> {
  if propagate_once(&mut is, &mut v, &mut cs) { is }
  else { propagate_core(is, v, cs) }
}

fn propagate(v: Vec<i64>, cs: Vec<IdCla>) -> Vec<u64> {
  let is: Vec<u64> = Vec::new();
  propagate_core(is, v, cs)
}

fn undelete(is: &Vec<u64>, cs: &mut HashMap<u64, (bool, Clause)>, temp: &mut File) {
  for i in is {
    if ! cs.get(i).unwrap().0 { // If the necessary clause is not active yet
      cs.get_mut(i).unwrap().0 = true; // Make it active
      temp.write(&Binary::encode(&ElabStep::Del(*i)))
        .expect("Failed to write delete step");
    }
  }
}

trait Binary {
  fn encode(x: &Self) -> Vec<u8>;
  // fn decode(v: Vec<u8>) -> Option<Vec<u8>>;
}

impl Binary for u64 {
  fn encode(x: &u64) -> Vec<u8> {

    let mut y = *x;
    let mut v = Vec::new();

    while 128 <= y {
      let u = (y % 128) as u8;
      v.push(u);
      y = y / 128;
    }
    v.push(y as u8);
    v
  }
}

impl Binary for i64 {
  fn encode(x: &i64) -> Vec<u8> {
    if *x < 0 {
      return Binary::encode(&(((2 * -x) + 1) as u64))
    } else {
      return Binary::encode(&((2 * x) as u64))
    }
  }
}

fn encode_vector<T: Binary>(ts: &Vec<T>) -> Vec<u8> {
  let mut v = Vec::new();
  for t in ts {v.append(&mut Binary::encode(t));}
  v
}

impl Binary for ElabStep {
  fn encode(x: &ElabStep) -> Vec<u8> {
    match x {
      ElabStep::Orig(i, ls) => {
        let mut v = vec!['o' as u8];
        v.append(&mut Binary::encode(i));
        v.append(&mut encode_vector(ls));
        v.push(0);
        v
      },
      ElabStep::Add(i, ls, is) => {
        let mut v = vec!['a' as u8];
        v.append(&mut Binary::encode(i));
        v.append(&mut encode_vector(ls));
        v.push(0);
        v.push('l' as u8);
        v.append(&mut encode_vector(is));
        v.push(0);
        v
      },
      ElabStep::Del(i) => {
        let mut v = vec!['d' as u8];
        v.append(&mut Binary::encode(i));
        v.push(0);
        v
      }
    }
  }
}

fn elab(frat: File, temp: &mut File) -> io::Result<()> {
  let mut bp = BackParser::new(frat)?.peekable();
  let mut cs: HashMap<u64, (bool, Clause)> = HashMap::new();

  while let Some(s) = bp.next() {

    match s {

      Step::Orig(i, ls) => {
        if cs.get(&i).unwrap().0 {  // If the original clause is active
         temp.write(&Binary::encode(&ElabStep::Orig(i, ls)))
           .expect("Failed to write orig step");
        }
        cs.remove(&i);
      }

      Step::Add(i, ls, p) => {
        if cs.get(&i).unwrap().0 {
          let is : Vec<u64> = match p {
            None => {
              // v is the valuation obtained by negating all literals in the clause to be added
              let v : Vec<i64> = ls.iter().map(|x| -x).collect();
              // scs is all the potentially vailable clauses (i.e., both active and passive)
              // against which v will be shown to be unsat

              let ics : Vec<IdCla> = cs.iter().map(|x| IdCla {id: *x.0, marked:(x.1).0, used: false, cla: &(x.1).1}).collect();
              // js is the IDs of clauses used in showing v unsat
              propagate(v, ics)
            }
            Some(Proof::LRAT(is)) => is
          };
          undelete(&is, &mut cs, temp);
          temp.write(&Binary::encode(&ElabStep::Add(i, ls, is)))
            .expect("Failed to write add step");
        }

        cs.remove(&i);
      },
      Step::Del(i, ls) => {
        assert_eq!(None, cs.insert(i, (false, ls)),
          "Encountered a delete step for preexisting clause");
      },
      Step::Final(i, ls) => {
        // Identical to the Del case, except that the clause should be marked if empty
        assert_eq!(None, cs.insert(i, (ls.is_empty(), ls)),
          "Encountered a delete step for preexisting clause");
      }
      Step::Todo(_i) => ()
    }
  }

  Ok(())
}

fn trim_bin(cnf: Vec<parser::Clause>, temp: File, lrat: &mut File) -> io::Result<()> {
  let mut k: u64 = cnf.len().try_into().unwrap(); // Counter for the last used ID
  let mut m: HashMap<u64, u64> = HashMap::new(); // Mapping between old and new IDs
  let mut bp = BackParser::new(temp)?.peekable();

  while let Some(s) = bp.next() {

    match s {

      Step::Orig(i, ls) => {
        assert!(!m.contains_key(&i), "Multiple orig steps with duplicate IDs");
        let j: u64 = cnf.iter().position(|x| is_perm(x, &ls)) // Find position of clause in original problem
           .expect("Orig steps refers to nonexistent clause").try_into().unwrap();
        m.insert(i, j + 1);
      },
      Step::Add(i, ls, Some(Proof::LRAT(is))) => {
        k += 1; // Get the next fresh ID
        m.insert(i, k); // The ID of added clause is mapped to a fresh ID
        let b = ls.is_empty();
        let js: Vec<u64> = is.iter().map(|x| m.get(x).unwrap().clone()).collect();
        // lrat.write(&Binary::encode(&ElabStep::Add(j, ls, js)))
        //   .expect("Cannot write trim_binmed add step");
        lrat.write(k.to_string().as_bytes())?;
        lrat.write(ls.into_iter().map(|x| format!(" {}", x.to_string())).collect::<String>().as_bytes())?;
        lrat.write(" 0".as_bytes())?;
        lrat.write(js.into_iter().map(|x| format!(" {}", x.to_string())).collect::<String>().as_bytes())?;
        lrat.write(" 0\n".as_bytes())?;

        if b {return Ok(())}
      }
      Step::Del(i, ls) => {
        assert!(ls.is_empty(), "Elaboration did not eliminate deletion literals");
        let j = m.get(&i).unwrap().clone();

        lrat.write(k.to_string().as_bytes())?;
        lrat.write(" d ".as_bytes())?;
        lrat.write(j.to_string().as_bytes())?;
        lrat.write(" 0\n".as_bytes())?;

        m.remove(&i); // Remove ID mapping to free space
        // lrat.write(&Binary::encode(&ElabStep::Del(j)))
        //   .expect("Cannot write trim_binmed del step");
      }
      _ => panic!("Bad elaboration result")
    }
  }
  Ok(())
}

// fn calc_lrat(p: Vec<parser::Clause>, ls: Vec<Lstep>) -> Vec<Lstep> {
//   let k: u64 = p.len().try_into().unwrap();
//   let mut m: Vec<(u64, u64)> = Vec::new();
//   calc_id_map(p, k, &ls, &mut m);
//
//   calc_lrat_core(m, ls)
// }

fn is_perm(v: &Vec<i64>, w: &Vec<i64>) -> bool {
  if v.len() != w.len() { return false }
  for i in v {
    if !w.contains(i) { return false }
  }
  true
}

// fn calc_id_map(p: Vec<parser::Clause>, mut k: u64, lns: &Vec<Lstep>, m: &mut Vec<(u64, u64)>) {
//   for ln in lns {
//     match ln {
//       Lstep::Orig(i, ls) => {
//         if !m.iter().any(|x| x.1 == *i) {
//           //let j = find_cnf_pos(&p, &ls) + 1;
//           let j: u64 = p.iter().position(|x| is_perm(x, ls)).unwrap().try_into().unwrap();
//           m.push((*i, j + 1));
//         }
//       },
//       Lstep::Add(i, _, _) => {
//         k = k + 1;
//         m.push((*i, k));
//       }
//       Lstep::Del(_) => ()
//     }
//   }
// }

// fn map_id(m: &Vec<(u64, u64)>, i: &u64) -> u64 {
//   let j = m.iter().position(|x| x.0 == *i).unwrap();
//   m[j].1
// }
//
// fn calc_lrat_core(m: Vec<(u64, u64)>, ls: Vec<Lstep>) -> Vec<Lstep> {
//   let mut lr: Vec<Lstep> = Vec::new();
//
//   for l in ls {
//     match l {
//       Lstep::Add(i, ls, is) => {
//         let new_i = map_id(&m, &i);
//         let new_is: Vec<u64> = is.iter().map(|x| map_id(&m, &x)).collect();
//         if ls.is_empty() {
//           lr.push(Lstep::Add(new_i, ls, new_is));
//           return lr;
//         } else {
//           lr.push(Lstep::Add(new_i, ls, new_is));
//         }
//       }
//       Lstep::Del(i) => {
//           lr.push(Lstep::Del(map_id(&m, &i)));
//       }
//       Lstep::Orig(_, _) => ()
//     }
//   }
//
//   lr
// }

fn main() -> io::Result<()> {
  let mut args = env::args().skip(1);
  let dimacs = args.next().expect("missing input file");
  let frat_path = args.next().expect("missing proof file");
  let mut lrat = File::create(args.next().expect("missing output path"))?;

  let temp_path = format!("{}{}", frat_path, ".temp");
  let frat = File::open(frat_path)?;
  let mut temp_write = File::create(temp_path.clone())?;
  elab(frat, &mut temp_write)?;

  let temp_read = File::open(temp_path)?;
  let (_vars, cnf) = parse_dimacs(read_to_string(dimacs)?.chars());
  trim_bin(cnf, temp_read, &mut lrat)?;

  Ok(())
}
