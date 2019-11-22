#[path="../dimacs.rs"] mod dimacs;
#[path="../parser.rs"] mod parser;
#[path="../serialize.rs"] mod serialize;
#[path="../backparser.rs"] pub mod backparser;

// use std::process::exit;
use std::io::{self, Write, BufWriter};
use std::fs::{File, read_to_string};
use std::env;
use dimacs::parse_dimacs;
use backparser::*;
use serialize::Serialize;
use hashbrown::hash_map::{HashMap, Entry};

// #[derive(Copy, Clone, Debug)]
struct IdCla<'a> {
  id: u64,
  _marked: bool,
  used: bool,
  cla: & 'a Clause
}

fn propagate(ls: &Vec<i64>, active: &HashMap<u64, (bool, Clause)>) ->
    (HashMap<i64, Option<usize>>, Vec<u64>) {
  // asn is the assignment obtained by negating all literals in the clause to be added
  let mut asn: HashMap<i64, Option<usize>> = ls.iter().map(|&x| (-x, None)).collect();
  // ics is all the potentially vailable clauses (i.e., both active and passive)
  // against which v will be shown to be unsat
  let mut ics: Vec<IdCla> = active.iter()
    .map(|(&id, &(_marked, ref cla))| IdCla {id, _marked, used: false, cla})
    .collect();
  let mut steps: Vec<u64> = Vec::new();
  'prop: loop {

    // Derive a new subunit clause and update all arguments accordingly.
    // Return is if a contradiction was found, restart if a unit clause
    // was derived, and panic if neither
    'ic: for ic in &mut ics {
      if !ic.used { // Only consider clauses that have not been used for UP yet

        // 'uf' holds an unfalsified literal of the clause, if one has been found
        let mut uf: Option<i64> = None;

        for &l in ic.cla {
          if !asn.contains_key(&-l) {
            if uf.replace(l).is_some() {continue 'ic}
          }
        }

        ic.used = true;
        match uf {
          None => {
            steps.push(ic.id);
            return (asn, steps)
          },
          Some(l) => if let Entry::Vacant(v) = asn.entry(l) {
            v.insert(Some(steps.len()));
            steps.push(ic.id);
            continue 'prop
          }
        }
      }
    }

    panic!("Unit progress stuck");
  }
}

fn propagate_hint(step: u64, ls: &Vec<i64>, active: &HashMap<u64, (bool, Clause)>, is: &Vec<u64>) ->
    Option<(HashMap<i64, Option<usize>>, Vec<u64>)> {
  let mut asn: HashMap<i64, Option<usize>> = ls.iter().map(|&x| (-x, None)).collect();
  let mut steps: Vec<u64> = Vec::new();
  for &c in is {
      let mut uf: Option<i64> = None;
      for &l in &active.get(&c).unwrap_or_else(
        || panic!("bad hint {}: clause {:?} does not exist", step, c)).1 {
        if !asn.contains_key(&-l) {
        assert!(uf.replace(l).is_none(),
          "bad hint {}: clause {:?} is not unit", step, c);
          }
        }
      match uf {
        None => {
          steps.push(c);
          return Some((asn, steps))
        },
        Some(l) => if let Entry::Vacant(v) = asn.entry(l) {
          v.insert(Some(steps.len()));
          steps.push(c);
        }
      }
    }
  panic!("bad hint {}: unit propagation failed to find conflict", step)
  }

fn propagate_minimize(active: &HashMap<u64, (bool, Clause)>,
    asn: HashMap<i64, Option<usize>>, steps: &mut Vec<u64>) {
  let mut need = vec![false; steps.len()];
  *need.last_mut().unwrap() = true;
  for (i, s) in steps.iter().enumerate().rev() {
    if need[i] {
      for &l in &active[s].1 {
        if let Some(&Some(j)) = asn.get(&-l) {need[j] = true}
      }
    }
  }
  let mut i = 0;
  steps.retain(|_| (need[i], i += 1).0);
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

fn elab<M: Mode>(frat: File, temp: File) -> io::Result<()> {
  let w = &mut BufWriter::new(temp);
  let mut bp = StepParser::<M>::new(frat)?;
  let mut active: HashMap<u64, (bool, Clause)> = HashMap::new();

  while let Some(s) = bp.next() {
    // eprintln!("{:?}", s);
    match s {

      Step::Orig(i, ls) => {
        if active.get(&i).unwrap().0 {  // If the original clause is active
          ElabStep::Orig(i, ls).write(w).expect("Failed to write orig step");
        }
        active.remove(&i);
      }

      Step::Add(i, ls, p) => {
        if active.remove(&i).unwrap().0 {
          let (asn, mut steps) = match p {
            Some(Proof::LRAT(is)) => propagate_hint(i, &ls, &active, &is),
            _ => None
          }.unwrap_or_else(|| propagate(&ls, &active));
          propagate_minimize(&active, asn, &mut steps);
          undelete(&steps, &mut active, w);
          ElabStep::Add(i, ls, steps).write(w).expect("Failed to write add step");
        }
      }

      Step::Reloc(mut relocs) => {
        let removed: Vec<_> = relocs.iter().map(|(_, to)| active.remove(to)).collect();
        let mut it = removed.into_iter();
        relocs.retain(|&(from, to)| {
          if let Some(s) = it.next().unwrap() {
            assert!(active.insert(from, s).is_none(),
              "Finalized a step that has been relocated, {} -> {}", from, to);
            true
          } else { false }
        });
        if !relocs.is_empty() {
          ElabStep::Reloc(relocs).write(w).expect("Failed to write add step");
        }
      }

      Step::Del(i, ls) => {
        assert!(active.insert(i, (false, ls)).is_none(),
          "Encountered a delete step for preexisting clause {}", i);
      }

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
  let mut bp = ElabStepParser::<Bin>::new(temp)?.peekable();

  loop {
    match bp.next().expect("did not find empty clause") {

      ElabStep::Orig(i, ls) => {
        let j = cnf.iter().position(|x| is_perm(x, &ls)).unwrap_or_else( // Find position of clause in original problem
          || panic!("Orig step {} refers to nonexistent clause {:?}", i, ls)) as u64 + 1;
        assert!(m.insert(i, j).is_none(), "Multiple orig steps with duplicate IDs");
        if ls.is_empty() {
          write!(lrat, "{} 0 {} 0\n", k+1, j)?;
          return Ok(())
        }
      }

      ElabStep::Add(i, ls, is) => {
        k += 1; // Get the next fresh ID
        m.insert(i, k); // The ID of added clause is mapped to a fresh ID
        let b = ls.is_empty();
        // lrat.write(&Binary::encode(&ElabStep::Add(j, ls, js)))
        //   .expect("Cannot write trimmed add step");
        write!(lrat, "{}", k)?;
        for x in ls { write!(lrat, " {}", x)? }
        write!(lrat, " 0")?;
        for x in is { write!(lrat, " {}", m.get(&x).unwrap_or_else(||
          panic!("step {}: proof step {:?} not found", i, x)))? }
        write!(lrat, " 0\n")?;

        if b {return Ok(())}
      }

      ElabStep::Reloc(relocs) => {
        let removed: Vec<_> = relocs.iter()
          .map(|(from, to)| (*to, m.remove(from))).collect();
        for (to, o) in removed {
          if let Some(s) = o { m.insert(to, s); }
        }
      }

      ElabStep::Del(i) => {
        write!(lrat, "{} d {}", k, m.remove(&i).unwrap())?; // Remove ID mapping to free space
        // agglomerate additional del steps into this block
        while let Some(&ElabStep::Del(i)) = bp.peek() {
          bp.next();
          write!(lrat, " {}", m.remove(&i).unwrap())?
        }
        write!(lrat, " 0\n")?;

        // lrat.write(&Binary::encode(&ElabStep::Del(j)))
        //   .expect("Cannot write trimmed del step");
      }
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
  let mut frat = File::open(frat_path)?;
  let bin = detect_binary(&mut frat)?;
  let temp_write = File::create(&temp_path)?;
  eprintln!("elaborating...");
  if bin { elab::<Bin>(frat, temp_write)? }
  else { elab::<Ascii>(frat, temp_write)? };
  eprintln!("parsing DIMACS...");

  let temp_read = File::open(temp_path)?;
  let (_vars, cnf) = parse_dimacs(read_to_string(dimacs)?.chars());
  eprintln!("trimming...");
  if let Some(p) = args.next() {
    trim_bin(cnf, temp_read, &mut BufWriter::new(File::create(p)?))?;
  } else {
    trim_bin(cnf, temp_read, &mut io::sink())?;
  }

  Ok(())
}
