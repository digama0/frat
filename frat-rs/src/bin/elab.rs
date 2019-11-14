#[path="../dimacs.rs"] mod dimacs;
#[path="../parser.rs"] mod parser;
#[path="../serialize.rs"] mod serialize;
#[path="../backparser.rs"] pub mod backparser;

// use std::process::exit;
// use std::collections::HashMap;
use std::io::{self, Write, BufWriter};
use std::fs::{File, read_to_string};
use std::env;
use dimacs::parse_dimacs;
use backparser::*;
use serialize::Serialize;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum ElabStep {
  Orig(u64, Vec<i64>),
  Add(u64, Vec<i64>, Vec<u64>),
  Del(u64),
}

impl Serialize for ElabStep {
  fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
    match *self {
      ElabStep::Orig(idx, ref vec) => ('o', (idx, vec)).write(w),
      ElabStep::Add(idx, ref vec, ref steps) =>
        (('a', (idx, vec)), ('l', steps)).write(w),
      ElabStep::Del(idx) => ('d', (idx, 0u8)).write(w),
    }
  }
}

// #[derive(Copy, Clone, Debug)]
struct IdCla<'a> {
  id: u64,
  _marked: bool,
  used: bool,
  cla: & 'a Clause
}

fn propagate(ls: &Vec<i64>, active: &HashMap<u64, (bool, Clause)>) -> Vec<u64> {
  // v is the valuation obtained by negating all literals in the clause to be added
  let mut v: HashMap<i64, Option<u64>> = ls.iter().map(|&x| (-x, None)).collect();
  // ics is all the potentially vailable clauses (i.e., both active and passive)
  // against which v will be shown to be unsat
  let mut ics: Vec<IdCla> = active.iter()
    .map(|(&id, &(_marked, ref cla))| IdCla {id, _marked, used: false, cla})
    .collect();
  let mut is: Vec<u64> = Vec::new();
  'prop: loop {

    // Derive a new subunit clause and update all arguments accordingly.
    // Return is if a contradiction was found, restart if a unit clause
    // was derived, and panic if neither
    'ic: for ic in &mut ics {
      if !ic.used { // Only consider clauses that have not been used for UP yet

        // 'uf' holds an unfalsified literal of the clause, if one has been found
        let mut uf: Option<i64> = None;

        for &l in ic.cla {
          if !v.contains_key(&-l) {
            if uf.replace(l).is_some() {
              continue 'ic
            }
          }
        }

        is.push(ic.id);
        ic.used = true;
        match uf {
          None => return is,
          Some(l) => {v.insert(l, Some(ic.id)); continue 'prop}
        }
      }
    }

    panic!("Unit progress stuck");
  }
}

fn undelete<W: Write>(is: &Vec<u64>, cs: &mut HashMap<u64, (bool, Clause)>, w: &mut W) {
  for &i in is {
    let v = cs.get_mut(&i).unwrap();
    if !v.0 { // If the necessary clause is not active yet
      v.0 = true; // Make it active
      ElabStep::Del(i).write(w).expect("Failed to write delete step");
    }
  }
}

fn elab(frat: File, temp: File) -> io::Result<()> {
  let w = &mut BufWriter::new(temp);
  let mut bp = BackParser::new(frat)?.peekable();
  let mut active: HashMap<u64, (bool, Clause)> = HashMap::new();

  while let Some(s) = bp.next() {

    match s {

      Step::Orig(i, ls) => {
        if active.get(&i).unwrap().0 {  // If the original clause is active
          ElabStep::Orig(i, ls).write(w).expect("Failed to write orig step");
        }
        active.remove(&i);
      }

      Step::Add(i, ls, p) => {
        if active.remove(&i).unwrap().0 {
          let is: Vec<u64> = match p {
            Some(Proof::LRAT(is)) => is,
            _ => propagate(&ls, &active)
          };
          undelete(&is, &mut active, w);
          ElabStep::Add(i, ls, is).write(w).expect("Failed to write add step");
        }
      },
      Step::Del(i, ls) => {
        assert!(active.insert(i, (false, ls)).is_none(),
          "Encountered a delete step for preexisting clause");
      },
      Step::Final(i, ls) => {
        // Identical to the Del case, except that the clause should be marked if empty
        assert!(active.insert(i, (ls.is_empty(), ls)).is_none(),
          "Encountered a delete step for preexisting clause");
      }
      Step::Todo(_) => ()
    }
  }

  Ok(())
}

fn trim_bin<W: Write>(cnf: Vec<dimacs::Clause>, temp: File, lrat: &mut W) -> io::Result<()> {
  let mut k = cnf.len() as u64; // Counter for the last used ID
  let mut m: HashMap<u64, u64> = HashMap::new(); // Mapping between old and new IDs
  let mut bp = BackParser::new(temp)?;

  loop {
    match bp.next().expect("did not find empty clause") {

      Step::Orig(i, ls) => {
        let j = cnf.iter().position(|x| is_perm(x, &ls)) // Find position of clause in original problem
          .expect("Orig steps refers to nonexistent clause") as u64;
        assert!(m.insert(i, j + 1).is_none(), "Multiple orig steps with duplicate IDs");
      },
      Step::Add(i, ls, Some(Proof::LRAT(is))) => {
        k += 1; // Get the next fresh ID
        m.insert(i, k); // The ID of added clause is mapped to a fresh ID
        let b = ls.is_empty();
        let js: Vec<u64> = is.iter().map(|x| m[x].clone()).collect();
        // lrat.write(&Binary::encode(&ElabStep::Add(j, ls, js)))
        //   .expect("Cannot write trimmed add step");
        write!(lrat, "{}", k)?;
        for x in ls { write!(lrat, " {}", x)? }
        write!(lrat, " 0")?;
        for x in js { write!(lrat, " {}", x)? }
        write!(lrat, " 0\n")?;

        if b {return Ok(())}
      }
      Step::Del(i, ls) => {
        assert!(ls.is_empty(), "Elaboration did not eliminate deletion literals");
        let j = m.remove(&i).unwrap(); // Remove ID mapping to free space
        write!(lrat, "{} d {} 0\n", k, j)?;

        // lrat.write(&Binary::encode(&ElabStep::Del(j)))
        //   .expect("Cannot write trimmed del step");
      }
      _ => panic!("Bad elaboration result")
    }
  }
}

// fn calc_lrat(p: Vec<dimacs::Clause>, ls: Vec<Lstep>) -> Vec<Lstep> {
//   let k: u64 = p.len().try_into().unwrap();
//   let mut m: Vec<(u64, u64)> = Vec::new();
//   calc_id_map(p, k, &ls, &mut m);
//
//   calc_lrat_core(m, ls)
// }

fn is_perm(v: &Vec<i64>, w: &Vec<i64>) -> bool {
  v.len() == w.len() && v.iter().all(|i| w.contains(i))
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

  let temp_path = format!("{}.temp", frat_path);
  let frat = File::open(frat_path)?;
  let temp_write = File::create(&temp_path)?;
  elab(frat, temp_write)?;

  let temp_read = File::open(temp_path)?;
  let (_vars, cnf) = parse_dimacs(read_to_string(dimacs)?.chars());
  if let Some(p) = args.next() {
    trim_bin(cnf, temp_read, &mut File::create(p)?)?;
  } else {
    trim_bin(cnf, temp_read, &mut io::sink())?;
  }

  Ok(())
}
