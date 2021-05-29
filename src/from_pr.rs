use std::collections::HashMap;
use std::convert::TryInto;
use std::fs::{File, read_to_string};
use std::io::{self, Read, Write, Seek, SeekFrom, BufReader, BufWriter};

use crate::dimacs::parse_dimacs;
use crate::midvec::MidVec;
use crate::parser::{Mode, StepRef, ProofRef, Ascii, Bin, DRATParser, DRATStep, detect_binary};
use crate::perm_clause::PermClause;
use crate::serialize::Serialize;

#[repr(u8)] #[derive(Copy, Clone, PartialEq, Eq)]
enum Assign {
  No = 0,
  Minimized = 1,
  Assigned = 2,
}

impl Default for Assign {
  fn default() -> Self { Self::No }
}

struct PrStep {
  assignment: MidVec<Assign>,
  phase4_pfs: MidVec<Vec<i64>>,
  marked: MidVec<i64>,
}


fn add_pr_step(
  PrStep {assignment, phase4_pfs, marked}: &mut PrStep,
  k: &mut u64,
  ctx: &HashMap<PermClause, Vec<u64>>,
  w: &mut impl Write,
  opt: bool,
  (lemma, witness): (&[i64], &[i64]),
  def: i64,
) -> io::Result<()> {
  assignment.clear();
  for &lit in witness {
    assignment[lit] = Assign::Assigned;
  }

  let mut stack = vec![];
  if opt {
    'opt: for (PermClause(clause), is) in ctx {
      let mut forced = 0;
      for &lit in clause {
        if assignment[-lit] != Assign::Assigned {
          if std::mem::replace(&mut forced, lit) != 0 {
            continue 'opt
          }
        }
      }
      if assignment[forced] == Assign::Assigned {
        if let Some(&i) = is.first() {
          stack.push((forced, clause, i));
          assignment[forced] = Assign::Minimized;
        }
      }
    }
  }

  // disabled because the original implementation does not make any sense
  let mflag = false; // lemma.iter().all(|&lit| assignment[lit] != Assign::Assigned) && lemma.len() != 1;

  fn add(k: &mut u64, c: Vec<i64>, pf: Option<&[i64]>, w: &mut impl Write) -> io::Result<(u64, Vec<i64>)> {
    *k += 1;
    StepRef::Add(*k, &c, pf.map(ProofRef::LRAT)).write(w)?;
    Ok((*k, c))
  }
  fn delete((k, c): (u64, Vec<i64>), w: &mut impl Write) -> io::Result<()> {
    StepRef::Del(k, &c).write(w)
  }

  // phase I: add shortened copies of clauses reduced, but not satisfied by omega
  let mut cleanup = vec![];
  if mflag {
    for &lit in lemma {
      // TODO: Why are we pushing def -> -C here?
      cleanup.push(add(k, vec![-def, -lit], Some(&[]), w)?)
    }
  } else {
    'phase1: for (PermClause(clause), is) in ctx {
      let mut red = false;
      for &lit in clause {
        if assignment[lit] != Assign::No { continue 'phase1 }
        if assignment[-lit] == Assign::Assigned { red = true }
      }
      if red {
        let mut c = Vec::with_capacity(clause.len() + 1);
        c.push(-def);
        let it = is.iter().flat_map({
          let k = (*k + 1) as i64;
          move |&i| <_>::into_iter([-(i as i64), k])
        });
        for &lit in clause {
          if assignment[lit] == Assign::No { c.push(lit) }
          if assignment[-lit] == Assign::Assigned {
            phase4_pfs[lit].extend(it.clone());
          }
        }
        cleanup.push(add(k, c, Some(&[]), w)?)
      }
    }
  }

  // phase III: print the weakened PR clause
  let phase3 = {
    let mut c = Vec::with_capacity(lemma.len() + 1);
    c.push(def); c.extend_from_slice(lemma);
    // this is the key step: we don't know the proof but it should be RUP if the step is PR
    add(k, c, None, w)?
  };
  let weak_c = phase3.0;
  for &lit in lemma {
    if assignment[-lit] == Assign::Assigned {
      phase4_pfs[lit].push(-(weak_c as i64));
    }
  }

  // phase II: weaken the involved clauses
  let mut phase2 = vec![];
  for (PermClause(clause), is) in ctx {
    if let Some(&i) = is.first() {
      let (mut sat, mut red) = (false, false);
      for &lit in clause {
        if assignment[lit] != Assign::No { sat = true }
        else if assignment[-lit] == Assign::Assigned { red = true }
      }
      if sat && red {
        let mut c = Vec::with_capacity(clause.len() + 1);
        c.push(def); c.extend_from_slice(clause);
        phase2.push((add(k, c, Some(&[i as _]), w)?, clause, is));
        for &i in is { StepRef::Del(i, clause).write(w)? }
        for &lit in clause {
          if assignment[-lit] == Assign::Assigned {
            phase4_pfs[lit].push(-(*k as i64))
          }
        }
      }
    }
  }

  cleanup.push(phase3);


  // phase IV (a): add the implication x -> omega
  marked.clear();
  for &lit in witness {
    if assignment[lit] == Assign::Assigned {
      let vec = &mut phase4_pfs[lit];
      cleanup.push(add(k, vec![lit, -def], Some(vec), w)?);
      vec.clear();
      marked[lit] = *k as i64;
    }
  }
  let mut pf = vec![];
  if mflag {
    for &lit in lemma {
      // TODO: I don't see why these should be true
      cleanup.push(add(k, vec![-def, -lit], None, w)?)
    }
  } else {
    for (lit, cl, i) in stack.into_iter().rev() {
      for &lit2 in cl { if lit2 != lit { pf.push(marked[-lit2]) } }
      pf.push(i as i64);
      cleanup.push(add(k, vec![-def, lit], Some(&pf), w)?);
      marked[lit] = *k as i64;
      pf.clear();
    }
  }

  // phase IV (b): strengthen the involved clauses
  for (c, clause, old) in phase2 {
    let (&first, rest) = old.split_first().unwrap();
    let lit = clause.iter().copied().find(|&lit| assignment[lit] != Assign::No).unwrap();
    StepRef::Add(first, clause, Some(ProofRef::LRAT(&[c.0 as i64, marked[lit]]))).write(w)?;
    for &i in rest {
      StepRef::Add(i, clause, Some(ProofRef::LRAT(&[first as _]))).write(w)?
    }
    delete(c, w)?
  }

  // phase IV (c): strengthen the weakened PR clause and add it to the formula
  *k += 1;
  let lit = lemma.iter().copied().find(|&lit| assignment[lit] != Assign::No).unwrap();
  StepRef::Add(*k, lemma, Some(ProofRef::LRAT(&[weak_c as i64, marked[lit]]))).write(w)?;

  // phase IV (d): remove the implication x -> omega
  // phase IV (e): remove the clauses that contain the literal -x (which are blocked)
  for c in cleanup { delete(c, w)? }

  Ok(())
}

fn from_pr(mode: impl Mode, (vars, cnf): (usize, Vec<Box<[i64]>>),
  pr: File, frat: File, opt: bool
) -> io::Result<()> {
  let mut pr = DRATParser::from(mode, BufReader::new(pr).bytes().map(Result::unwrap));
  let mut maxvar = vars.try_into().unwrap();
  let w = &mut BufWriter::new(frat);
  let mut k = 0;
  let mut ctx: HashMap<PermClause, Vec<u64>> = HashMap::new();
  for ls in cnf {
    k += 1;
    StepRef::Orig(k, &ls).write(w)?;
    ctx.entry(PermClause(ls.into())).or_default().push(k);
  }

  let mut temp = PrStep {
    assignment: MidVec::with_capacity(maxvar),
    phase4_pfs: MidVec::with_capacity(maxvar),
    marked: MidVec::with_capacity(maxvar),
  };
  for s in &mut pr {
    match s {
      DRATStep::Add(ls) => {
        if let Some(new) = ls.iter().copied().max() {
          maxvar = maxvar.max(new)
        }
        if let Some(i) = ls.split_first()
            .and_then(|(&pivot, rest)| rest.iter().position(|&x| pivot == x)) {
          add_pr_step(&mut temp, &mut k, &ctx, w, opt, ls.split_at(i+1), maxvar + 1)?
        } else {
          k += 1;
          StepRef::Add(k, &ls, None).write(w)?
        }
        ctx.entry(PermClause(ls)).or_default().push(k)
      }
      DRATStep::Del(ls) => {
        let ls = PermClause(ls);
        let vec = ctx.get_mut(&ls).unwrap_or_else(
          || panic!("deleted nonexistent clause {:?}", ls.0));
        let st = vec.pop().expect("deleted nonexistent clause");
        if vec.is_empty() { ctx.remove(&ls); }
        StepRef::Del(st, &ls.0).write(w)?;
      }
    }
  }

  for (PermClause(c), vec) in ctx {
    for st in vec {
      StepRef::Final(st, &c).write(w)?;
    }
  }

  w.flush()?;
  Ok(())
}

pub fn main(mut args: impl Iterator<Item=String>) -> io::Result<()> {
  let dimacs = args.next().expect("missing input file");
  let cnf = parse_dimacs(read_to_string(dimacs)?.bytes());
  let mut pr = File::open(args.next().expect("missing proof file"))?;
  let bin = detect_binary(&mut pr)?;
  pr.seek(SeekFrom::Start(0))?;
  let frat = File::create(args.next().expect("missing output file"))?;
  let opt = if let Some("-O") = args.next().as_deref() {true} else {false};
  if bin { from_pr(Bin, cnf, pr, frat, opt) }
  else { from_pr(Ascii, cnf, pr, frat, opt) }
}