#[path="../dimacs.rs"] mod dimacs;
#[path="../parser.rs"] mod parser;
#[path="../backparser.rs"] pub mod backparser;

// use std::process::exit;
// use std::collections::HashMap;
use std::io::{self, Write};
use std::fs::{File, read_to_string};
use std::env;
use std::convert::TryInto;
use dimacs::parse_dimacs;
use backparser::*;
use std::collections::HashMap;

#[derive(Debug, Clone)]
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

// #[derive(Clone, Debug)]
struct IdCla<'a> {
  id: u64,
  _marked: bool,
  used: bool,
  cla: & 'a Clause
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
            Some(Proof::LRAT(is)) => is,
            _ => {
              // v is the valuation obtained by negating all literals in the clause to be added
              let v : Vec<i64> = ls.iter().map(|x| -x).collect();
              // scs is all the potentially vailable clauses (i.e., both active and passive)
              // against which v will be shown to be unsat

              let ics : Vec<IdCla> = cs.iter().map(|x| IdCla {id: *x.0, _marked:(x.1).0, used: false, cla: &(x.1).1}).collect();
              // js is the IDs of clauses used in showing v unsat
              propagate(v, ics)
            }
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

fn trim_bin(cnf: Vec<dimacs::Clause>, temp: File, lrat: &mut File) -> io::Result<()> {
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

// fn calc_lrat(p: Vec<dimacs::Clause>, ls: Vec<Lstep>) -> Vec<Lstep> {
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

// fn calc_id_map(p: Vec<dimacs::Clause>, mut k: u64, lns: &Vec<Lstep>, m: &mut Vec<(u64, u64)>) {
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
