use std::collections::BTreeMap;
use std::convert::TryInto;
use std::fs::{File, read_to_string};
use std::io::{self, Read, Write, Seek, SeekFrom, BufReader, BufWriter};

use crate::HashMap;
use crate::dimacs::parse_dimacs;
use crate::midvec::MidVec;
use crate::parser::{Mode, StepRef, Ascii, Bin, AddKind, DRATParser, DRATStep, detect_binary};
use crate::perm_clause::PermClause;
use crate::serialize::{Serialize, ModeWrite, ModeWriter};

#[repr(u8)] #[derive(Copy, Clone, Debug, PartialEq, Eq)]
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

type M = Bin;

type Context = HashMap<PermClause, Vec<u64>>;

#[allow(clippy::too_many_arguments)]
fn add_pr_step(
  PrStep {assignment, phase4_pfs, marked}: &mut PrStep,
  k: &mut u64,
  ctx: &Context,
  w: &mut impl ModeWrite<M>,
  opt: bool,
  lemma: &[i64], witness: &[i64],
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
        if assignment[-lit] != Assign::Assigned &&
          std::mem::replace(&mut forced, lit) != 0 {
          continue 'opt
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
  let mflag = lemma.iter().all(|&lit| assignment[lit] != Assign::Assigned) && lemma.len() != 1;

  fn add(k: &mut u64, c: Vec<i64>, pf: Option<&[i64]>, w: &mut impl ModeWrite<M>) -> io::Result<(u64, Vec<i64>)> {
    *k += 1;
    StepRef::add(*k, &c, pf).write(w)?;
    Ok((*k, c))
  }
  fn delete((k, c): (u64, Vec<i64>), w: &mut impl ModeWrite<M>) -> io::Result<()> {
    StepRef::Del(k, &c).write(w)
  }

  // phase I: add shortened copies of clauses reduced, but not satisfied by omega
  let mut cleanup = vec![];
  let mut mflag_phase1 = vec![];
  if mflag {
    for &lit in lemma {
      mflag_phase1.push(add(k, vec![-def, -lit], Some(&[]), w)?);
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
          match assignment[-lit] {
            Assign::No => c.push(lit),
            Assign::Assigned => phase4_pfs[-lit].extend(it.clone()),
            _ => {}
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
      phase4_pfs[-lit].push(-(weak_c as i64));
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
            phase4_pfs[-lit].push(-(*k as i64));
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
    for c in mflag_phase1 { delete(c, w)? }
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
    let i = clause.iter().position(|&lit| assignment[lit] != Assign::No).unwrap();
    let lit = clause[i];
    if marked[lit] == 0 {
      // TODO: This dubious situation is reachable:
      // - opt = mflag = true
      // - lit refers to a literal in omega (the witness)
      // - lit is not in omega' (i.e. assignment[lit] == Assign::Minimized)
      // In this case `c` is not usable because it has been weakened,
      // but it was used in the unit propagation proof, so we're stuck.
      // Hope for the best and add it anyway?
      // It seems to be RAT on the provided literal, and `c` shows up in the proof,
      // but this is not a complete proof.
      let mut clause = clause.clone();
      clause.swap(0, i);
      StepRef::add(first, &clause, Some(&[c.0 as i64])).write(w)?
    } else {
      StepRef::add(first, clause, Some(&[c.0 as i64, marked[lit]])).write(w)?
    }
    for &i in rest {
      StepRef::add(i, clause, Some(&[first as _])).write(w)?
    }
    delete(c, w)?
  }

  // phase IV (c): strengthen the weakened PR clause and add it to the formula
  *k += 1;
  let lit = lemma.iter().copied().find(|&lit| assignment[lit] != Assign::No).unwrap();
  StepRef::add(*k, lemma, Some(&[weak_c as i64, marked[lit]])).write(w)?;

  // phase IV (d): remove the implication x -> omega
  // phase IV (e): remove the clauses that contain the literal -x (which are blocked)
  for c in cleanup { delete(c, w)? }

  Ok(())
}

fn from_pr(mode: impl Mode, (vars, cnf): (usize, Vec<Box<[i64]>>),
  pr: File, frat: File, opt: bool
) -> io::Result<()> {
  let pr = DRATParser::from(mode, BufReader::new(pr).bytes().map(Result::unwrap));
  let mut maxvar = vars.try_into().unwrap();
  let w = &mut ModeWriter(M::default(), BufWriter::new(frat));
  let mut k = 0;
  let mut ctx: Context = Context::default();
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
  for s in pr {
    match s {
      DRATStep::Comment(s) => StepRef::Comment(&s).write(w)?,
      DRATStep::Add(add) => {
        if let Some(new) = add.0.iter().copied().max() {
          maxvar = maxvar.max(new)
        }
        let (unsat, lemma) = add.parse_into(|add| {
          if add.lemma().is_empty() { return Ok(true) }
          match add {
            AddKind::RAT(lemma) => { k += 1; StepRef::add(k, lemma, None).write(w) }
            AddKind::PR(lemma, witness) =>
              add_pr_step(&mut temp, &mut k, &ctx, w, opt, lemma, witness, maxvar + 1),
          }.map(|_| false)
        });
        if unsat? { break }
        ctx.entry(PermClause(lemma)).or_default().push(k);
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

  // Some DRAT files accepted by drat-trim stop one step short
  // of the final empty clause step, so we have to insert it here.
  // Note that the empty clause step can never be RAT or PR, only RUP
  k += 1;
  StepRef::add(k, &[], None).write(w)?;
  StepRef::Final(k, &[]).write(w)?;

  let mut sorted = BTreeMap::new();
  for (PermClause(c), vec) in &ctx {
    for &st in vec {
      assert!(sorted.insert(st, c).is_none(), "duplicate step");
    }
  }
  for (st, c) in sorted.into_iter().rev() {
    StepRef::Final(st, c).write(w)?
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
  let opt = matches!(args.next().as_deref(), Some("-O"));
  if bin { from_pr(Bin, cnf, pr, frat, opt) }
  else { from_pr(Ascii, cnf, pr, frat, opt) }
}