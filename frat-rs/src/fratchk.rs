use std::fs::File;
use std::process::exit;
use hashbrown::hash_map::HashMap;
use std::io;
use super::parser::{detect_binary, Mode, Ascii, Bin};
use super::backparser::*;

type Clause = Vec<i64>;

fn subsumes(clause: &Clause, clause2: &Clause) -> bool {
  clause2.iter().all(|lit2| clause.contains(lit2))
}

fn check_proof_step(_active: &mut HashMap<u64, (bool, Clause)>, _cl: &Clause, p: Option<Proof>) -> Option<Proof> {
  match p {
    None => Some(Proof::Sorry),
    Some(p) => Some(p)
  }
}

pub fn check_proof(mode: impl Mode, proof: File) -> io::Result<()> {
  let mut bp = StepParser::new(mode, proof)?.peekable();
  let (mut orig, mut added, mut deleted, mut fin) = (0i64, 0i64, 0i64, 0i64);
  let (mut dirty_orig, mut dirty_add, mut double_del, mut double_fin) = (0i64, 0i64, 0i64, 0i64);
  let mut missing = 0i64;
  let mut active: HashMap<u64, (bool, Clause)> = HashMap::new();
  let mut todos = HashMap::new();
  let mut bad = false;
  while let Some(s) = bp.next() {
    match s {
      Step::Orig(i, lits) => {
        orig += 1;
        match active.remove(&i) {
          None => {
            dirty_orig += 1;
            // eprintln!("original clause {} {:?} never finalized", i, lits);
          },
          Some((_, lits2)) => if !subsumes(&lits2, &lits) {
            eprintln!("added {:?}, removed {:?}", lits2, lits);
            bad = true;
          }
        }
      },
      Step::Add(i, lits, p) => {
        added += 1;
        if p.is_none() { missing += 1 }
        if let Some(Step::Todo(_)) = bp.peek() {} else if p.is_none() {
          *todos.entry(0).or_insert(0i64) += 1;
          // eprintln!("added clause {} {:?} has no proof and no todo", i, lits);
        }
        if let Some((need, lits2)) = active.remove(&i) {
          if !subsumes(&lits2, &lits) {
            eprintln!("added {:?}, removed {:?}", lits2, lits);
            bad = true;
          }
          if need {
            if let Some(p) = check_proof_step(&mut active, &lits, p) {
              if let Proof::LRAT(steps) = p {
                for s in steps {
                  let needed = &mut active.get_mut(&s).expect("bad LRAT proof").0;
                  if !*needed {
                    // unimplemented!();
                    *needed = true;
                  }
                }
              }
            } else {
              eprintln!("bad proof for {:?}", lits);
              bad = true;
            }
          }
        } else {
          dirty_add += 1;
          // eprintln!("added clause {} {:?} never finalized", i, lits);
        }
      },
      Step::Reloc(relocs) => {
        let removed: Vec<_> = relocs.iter()
          .map(|(from, to)| (*from, active.remove(to))).collect();
        for (from, o) in removed {
          if let Some(s) = o {
            if active.insert(from, s).is_some() {
              double_del += 1;
              // eprintln!("already deleted clause {} {:?}", i, active[&i]);
            }
          } else {
            dirty_add += 1;
            // eprintln!("added clause {} {:?} never finalized", i, lits);
          }
        }
      },
      Step::Del(i, lits) => {
        deleted += 1;
        if active.insert(i, (false, lits)).is_some() {
          double_del += 1;
          // eprintln!("already deleted clause {} {:?}", i, active[&i]);
        }
      },
      Step::Final(i, lits) => {
        fin += 1;
        if active.insert(i, (lits.is_empty(), lits)).is_some() {
          double_fin += 1;
          // eprintln!("already finalized clause {} {:?}", i, active[&i]);
        }
      },
      Step::Todo(i) => *todos.entry(i).or_insert(0i64) += 1,
    }
  }
  println!("{} orig + {} added - {} deleted - {} finalized = {}",
    orig, added, deleted, fin, orig + added - deleted - fin);
  println!("{} missing proofs ({:.1}%)", missing, 100. * missing as f32 / added as f32);
  let mut todo_vec: Vec<_> = todos.into_iter().collect();
  todo_vec.sort_by_key(|(_, v)| -v);
  for (k, v) in todo_vec.into_iter().take(5).filter(|&(_, v)| v != 0) {
    println!("type {}: {}", k, v);
  }
  if dirty_orig != 0 || dirty_add != 0 {
    eprintln!("{} original + {} added never finalized", dirty_orig, dirty_add);
    bad = true;
  }
  if double_del != 0 || double_fin != 0 {
    eprintln!("{} double deletes + {} double finalized", double_del, double_fin);
    bad = true;
  }
  if !active.is_empty() {
    eprintln!("{} unjustified", active.len());
    bad = true;
  }
  if bad { exit(1) }
  Ok(())
}

pub fn main<I: Iterator<Item=String>>(mut args: I) -> io::Result<()> {
  let mut proof = File::open(args.next().expect("missing proof file"))?;
  let bin = detect_binary(&mut proof)?;
  if bin { check_proof(Bin, proof) }
  else { check_proof(Ascii, proof) }
}