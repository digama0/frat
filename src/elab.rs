use std::io::{self, Read, BufReader, Write, BufWriter};
use std::fs::{File, read_to_string};
use std::convert::TryInto;
use std::mem;
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::collections::HashMap;
use slab::Slab;

use super::midvec::MidVec;
use super::dimacs::{parse_dimacs, parse_dimacs_map};
use super::serialize::Serialize;
use super::parser::{detect_binary, Step, StepRef, ElabStep, ElabStepRef, Segment,
  Proof, ProofRef, Mode, Ascii, Bin, LRATParser, LRATStep};
use super::backparser::{VecBackParser, BackParser, StepIter, ElabStepIter};
use super::perm_clause::*;

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
struct Reason(usize);

impl Reason {
  const NONE: Self = Self(0);
  fn new(val: usize) -> Self { Self(val + 1) }
  fn clause(self) -> Option<usize> { self.0.checked_sub(1) }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
enum Assign { No = 0, Yes = 1, Mark = 2 }

impl Default for Assign {
  fn default() -> Self { Self::No }
}
impl Assign {
  #[inline] fn assigned(self) -> bool { self != Self::No }
}

#[derive(Default)]
struct VAssign {
  tru_lits: MidVec<Assign>,
  reasons: MidVec<Reason>,
  tru_stack: Vec<i64>,
  first_hyp: usize,
  first_unprocessed: usize,
  units_processed: bool,
}

impl VAssign {
  fn clear_hyps(&mut self) {
    for i in self.tru_stack.drain(self.first_hyp..) {
      self.tru_lits[i] = Assign::No;
      self.reasons[i] = Reason::NONE;
    }
    self.first_unprocessed = self.first_unprocessed.min(self.first_hyp);
  }

  fn reserve_to(&mut self, max: i64) {
    self.tru_lits.reserve_to(max);
    self.reasons.reserve_to(max);
  }

  fn unsat(&self) -> Option<i64> {
    let k = *self.tru_stack.last()?;
    if self.is_false(k) {Some(k)} else {None}
  }

  #[inline] fn is_true(&self, l: i64) -> bool { self.tru_lits[l].assigned() }
  #[inline] fn is_false(&self, l: i64) -> bool { self.is_true(-l) }

  // Attempt to update the variable assignment and make l true under it.
  // If the update is impossible because l is already false under it, return false.
  // Otherwise, update and return true.
  fn assign(&mut self, l: i64, reason: Reason) -> bool {
    if self.is_true(l) { return true }
    self.reasons[l] = reason;
    self.tru_lits[l] = Assign::Yes;
    self.tru_stack.push(l);
    !self.is_false(l)
  }

  fn unassign(&mut self, lit: i64) {
    debug_assert!(self.first_hyp == self.tru_stack.len(), "uncleared hypotheses");
    if !self.is_true(lit) {return}
    self.first_hyp = self.tru_stack.iter().rposition(|&l| lit == l)
      .expect("couldn't find unit to unassign");
    self.first_unprocessed = 0;
    self.units_processed = false;
    self.clear_hyps();
  }

  fn add_unit(&mut self, l: i64, cl: usize) {
    debug_assert!(self.first_hyp == self.tru_stack.len(), "uncleared hypotheses");
    if self.unsat().is_some() || self.is_true(l) {return}
    self.reasons[l] = Reason::new(cl);
    self.tru_lits[l] = Assign::Yes;
    self.tru_stack.push(l);
    self.first_hyp += 1;
  }

  // Return the next literal to be propagated, and indicate whether
  // its propagation should be limited to marked/unmarked clauses
  fn next_prop_lit(&mut self, unprocessed: &mut [usize; 2]) -> Option<(bool, i64)> {
    if let Some(&l) = self.tru_stack.get(unprocessed[0]) {
      unprocessed[0] += 1; return Some((true, l));
    }
    if let Some(&l) = self.tru_stack.get(unprocessed[1]) {
      unprocessed[1] += 1; return Some((false, l));
    }
    None
  }
}

#[derive(Debug)]
struct Clause {
  marked: bool,
  name: u64,
  lits: Box<[i64]>
}

impl<'a> IntoIterator for &'a Clause {
  type Item = i64;
  type IntoIter = std::iter::Cloned<std::slice::Iter<'a, Self::Item>>;
  fn into_iter(self) -> Self::IntoIter { self.lits.iter().cloned() }
}

impl Deref for Clause {
  type Target = [i64];
  fn deref(&self) -> &[i64] { self.lits.deref() }
}
impl DerefMut for Clause {
  fn deref_mut(&mut self) -> &mut [i64] { self.lits.deref_mut() }
}
impl Index<usize> for Clause {
  type Output = i64;
  fn index(&self, i: usize) -> &i64 { self.lits.index(i) }
}
impl IndexMut<usize> for Clause {
  fn index_mut(&mut self, i: usize) -> &mut i64 { self.lits.index_mut(i) }
}

impl Clause {
  fn check_subsumed(&self, lits: &[i64], step: u64) {
    assert!(lits.iter().all(|lit| self.contains(lit)),
      "at {:?}: Clause {:?} added here will later be deleted as {:?}",
      step, self, lits)
  }
}

#[derive(Default)]
struct Watches([MidVec<Vec<usize>>; 2]);

impl Watches {
  #[inline] fn watch(&self, marked: bool) -> &MidVec<Vec<usize>> {
    &self.0[marked as usize]
  }
  #[inline] fn watch_mut(&mut self, marked: bool) -> &mut MidVec<Vec<usize>> {
    &mut self.0[marked as usize]
  }

  fn del(&mut self, marked: bool, l: i64, i: usize) {
    let vec = &mut self.watch_mut(marked)[l];
    let i = vec.iter().position(|x| *x == i).unwrap();
    vec.swap_remove(i);
  }

  #[inline] fn add(&mut self, marked: bool, l: i64, id: usize) {
    self.watch_mut(marked)[l].push(id);
  }
}

#[derive(Default)]
struct Hint {
  steps: Vec<i64>,
  temp: Vec<i64>,
}

#[derive(Default)]
struct Context {
  max_var: i64,
  clauses: Slab<Clause>,
  names: HashMap<u64, usize>,
  units: HashMap<usize, i64>,
  watch: Watches,
  va: VAssign,
  step: u64,
}

fn dedup_vec<T: PartialEq>(vec: &mut Vec<T>) {
  let mut i = 0;
  while i < vec.len() {
    if vec[..i].contains(&vec[i]) {
      vec.swap_remove(i);
    } else {
      i += 1;
    }
  }
}

impl Context {
  fn sort_size(&self, lits: &mut [i64]) -> (bool, usize) {
    let mut size = 0;
    let mut sat = false;
    for last in 0..lits.len() {
      let lit = lits[last];
      if !self.va.is_false(lit) {
        sat |= self.va.is_true(lit);
        lits.swap(last, size);
        size += 1;
      }
    }
    (sat, size)
  }

  fn insert(&mut self, name: u64, marked: bool, mut lits: Box<[i64]>) {
    for &lit in &*lits {
      self.max_var = self.max_var.max(lit.abs())
    }
    self.va.reserve_to(self.max_var);
    self.watch.0[0].reserve_to(self.max_var);
    self.watch.0[1].reserve_to(self.max_var);
    let unit = self.sort_size(&mut lits) == (false, 1);
    let i = self.clauses.insert(Clause {marked, name, lits});
    assert!(self.names.insert(name, i).is_none(),
      "at {:?}: Clause {} to be inserted already exists", self.step, name);
    let lits = &*self.clauses[i];
    match *lits {
      [] => {}
      [l] => assert!(self.units.insert(i, l).is_none()),
      [l1, l2, ..] => {
        self.watch.add(marked, l1, i);
        self.watch.add(marked, l2, i);
      }
    }
    if unit { self.va.add_unit(lits[0], i); }
  }

  fn remove(&mut self, name: u64) -> Clause {
    let i = self.names.remove(&name).unwrap_or_else(
      || panic!("at {:?}: Clause {} to be removed does not exist", self.step, name));

    let cl = &self.clauses[i];
    match **cl {
      [] => {}
      [l] => {
        self.va.unassign(l);
        self.units.remove(&i).expect("unit not found");
      }
      [l1, l2, ..] => {
        self.watch.del(cl.marked, l1, i);
        self.watch.del(cl.marked, l2, i);
        if self.va.reasons[l1] == Reason::new(i) {
          self.va.unassign(l1)
        }
      }
    }

    self.clauses.remove(i)
  }

  fn reloc(&mut self, relocs: &mut Vec<(u64, u64)>) {
    let mut m = HashMap::new();
    let mut removed = Vec::new();
    relocs.retain(|&(from, to)| {
      if let Some(addr) = self.names.remove(&to) {
        m.insert(from, to);
        removed.push((from, addr));
        true
      } else {false}
    });
    for (from, addr) in removed {
      assert!(self.names.insert(from, addr).is_none(),
        "at {:?}: Clause {} to be inserted already exists", self.step, from);
    }
  }

  fn get(&self, i: u64) -> usize {
    *self.names.get(&i).unwrap_or_else(
      || panic!("at {:?}: Clause {} to be accessed does not exist", self.step, i))
  }

  fn finalize_hint(&mut self, conflict: i64, hint: &mut Hint) {
    struct Finalize<'a> {
      va: &'a mut VAssign,
      clauses: &'a Slab<Clause>,
      hint: &'a mut Hint,
    }

    impl<'a> Finalize<'a> {
      fn mark(&mut self, lit: i64) {
        if let Some(c) = self.va.reasons[lit].clause() {
          let step = self.clauses[c].name as i64;
          for &l in &self.clauses[c].lits[1..] {
            if !matches!(self.va.tru_lits[-l], Assign::Mark) { self.mark(-l) }
          }
          self.hint.steps.push(step);
        }
        self.va.tru_lits[lit] = Assign::Mark;
        self.hint.temp.push(lit);
      }
    }

    let mut fin = Finalize {
      va: &mut self.va,
      clauses: &self.clauses,
      hint,
    };

    fin.mark(conflict);
    fin.mark(-conflict);
    let Finalize {va, hint, ..} = fin;

    for lit in hint.temp.drain(..) {
      va.tru_lits[lit] = Assign::Yes
    }

    va.clear_hyps();
  }

  fn propagate_core(&mut self) -> Option<i64> {
    let root = self.va.first_hyp >= self.va.tru_stack.len();
    let Context {watch, clauses, va, ..} = self;

    debug_assert!(!va.unsat().is_some());

    if !va.units_processed {
      debug_assert!(root);
      for (&c, &l) in &self.units {
        if !va.is_true(l) { va.add_unit(l, c) }
      }
      va.units_processed = true;
    }

    let mut unprocessed = [va.first_unprocessed; 2];
    // Main unit propagation loop
    while let Some((m, l)) = va.next_prop_lit(&mut unprocessed) {
      // m indicates propagation targets (m == true for marked clauses),
      // and l is an unprocessed true literal, meaning that it has been set but
      // we have not yet propagated it.

      // 'is' contains the IDs of all clauses containing -l
      let mut is = &*watch.watch(m)[-l];
      let mut wi = 0..;
      while let Some(&i) = is.get(wi.next().unwrap()) {
        let cl = &mut clauses[i];

        // We process marked and unmarked clauses in two separate passes.
        // If this clause is in the wrong class then skip.
        if m != cl.marked {continue}

        // Watched clauses have two literals at the front, that are being watched.
        if let [a, b, ..] = **cl {
          // If one of the watch literals is satisfied,
          // then this clause is satisfied so skip.
          if va.is_true(a) || va.is_true(b) {
            continue
          }
          // We know that -l is one of the first two literals; make sure
          // it is at cl[1] by swapping with the other watch if necessary.
          if a == -l {cl.swap(0, 1)}
        } else { unreachable!("watched clauses should be at least binary") }

        // Since -l has just been falsified, we need a new watch literal to replace it.
        // Let j be another literal in the clause that has not been falsified.
        if let Some(j) = (2..cl.len()).find(|&i| !va.is_false(cl[i])) {
          cl.swap(1, j); // Replace the -l literal with cl[j]
          let k = cl[1]; // let k be the new literal
          watch.del(m, -l, i); // remove this clause from the -l watch list
          watch.add(m, k, i); // and add it to the k watch list

          // Since we just modified the -l watch list, that we are currently iterating
          // over, we have to tweak the iterator so that we don't miss anything.
          wi.start -= 1; is = &watch.watch(m)[-l];

          // We're done here, we didn't find a new unit
          continue
        }

        // Otherwise, there are no other non-falsified literals in the clause,
        // meaning that this is a binary clause of the form k \/ -l
        // where k is the other watch literal in the clause, so we either
        // have a new unit, or if k is falsified then we proved false and can finish.
        let k = cl[0];

        // Push the new unit on the chain. Note that the pivot literal,
        // the one that this clause is the reason for, must be at index 0.
        if !va.assign(k, Reason::new(i)) {
          // if we find a contradiction then exit
          va.first_unprocessed = va.tru_stack.len();
          if root { va.first_hyp = va.tru_stack.len() }
          return Some(k)
        }

        // Otherwise, go to the next clause.
      }
    }
    va.first_unprocessed = va.tru_stack.len();
    if root { va.first_hyp = va.tru_stack.len() }

    // If there are no more literals to propagate, unit propagation has failed
    None
  }

  fn propagate(&mut self, c: &[i64]) -> Option<i64> {
    if let Some(k) = self.va.unsat() { return Some(k) }

    if !self.va.units_processed || self.va.first_unprocessed < self.va.tru_stack.len() {
      if let Some(k) = self.propagate_core() { return Some(k) }
    }

    if !c.is_empty() {
      for &l in c {
        if !self.va.assign(-l, Reason::NONE) {
          self.va.tru_lits[l] = Assign::Mark;
          return Some(l)
        }
      }

      if let Some(k) = self.propagate_core() { return Some(k) }
    }

    // If there are no more literals to propagate, unit propagation has failed
    None
  }

  fn propagate_hint(&mut self, ls: &[i64], is: &[i64], strict: bool) -> Option<i64> {
    if let Some(k) = self.va.unsat() { return Some(k) }

    if !self.va.units_processed {
      for (&c, &l) in &self.units {
        if !self.va.is_true(l) { self.va.add_unit(l, c) }
      }
      self.va.units_processed = true;
    }

    for &x in ls {
      if !self.va.assign(-x, Reason::NONE) { return Some(x) }
    }

    let mut is: Vec<usize> = is.iter().map(|&i| self.get(i as u64)).collect();
    let Context {va, clauses, watch, ..} = self;
    let mut queue = vec![];
    loop {
      let mut progress = false;
      for c in is.drain(..) {
        let cl = &mut clauses[c];
        if cl.iter().any(|&l| va.is_true(l)) {
          continue
        }
        let k;
        let unsat = if let Some(i) = (1..cl.len()).find(|&i| !va.is_false(cl[i])) {
          let l = cl[0];
          if !va.is_false(l) || cl.lits[i+1..].iter().any(|&l| !va.is_false(l)) {
            assert!(!strict, "at {:?}: clause {:?} is not unit", self.step, cl.name);
            queue.push(c);
            continue
          }
          cl.swap(0, i);
          k = cl[0];
          if i > 1 {
            watch.del(cl.marked, l, c);
            watch.add(cl.marked, k, c);
          }
          false
        } else { k = cl[0]; va.is_false(k) };
        assert!(va.assign(k, Reason::new(c)) == !unsat);
        if unsat { return Some(k) }
        progress = true;
      }
      if !progress {
        self.va.clear_hyps();
        return None
      }
      mem::swap(&mut is, &mut queue);
    }
  }

  fn build_step(&mut self, ls: &[i64], hint: Option<&[i64]>, strict: bool, out: &mut Hint) -> bool {
    if let Some(is) = hint {
      if let Some(k) = self.propagate_hint(ls, is, strict) {
        self.finalize_hint(k, out);
        return true
      }
    }
    if let Some(k) = self.propagate(ls) {
      self.finalize_hint(k, out);
      return true
    }
    false
  }

  fn run_rat_step<'a>(&mut self, ls: &[i64], init: Option<&[i64]>,
      rats: Option<(&'a i64, &'a [i64])>, strict: bool, out: &mut Hint) {
    out.steps.clear();
    if rats.is_none() {
      if self.build_step(ls, init, strict, out) { return }
    }
    unimplemented!("RAT steps are not available in this version, see the master branch")
  }
}

fn elab<M: Mode>(mode: M, full: bool, frat: File, w: &mut impl Write) -> io::Result<()> {
  let mut origs = Vec::new();
  let ctx = &mut Context::default();
  let hint = &mut Hint::default();
  for s in StepIter(BackParser::new(mode, frat)?) {
    match s {

      Step::Orig(i, ls) => {
        ctx.step = i;
        let c = ctx.remove(i);
        c.check_subsumed(&ls, ctx.step);
        if full || c.marked {  // If the original clause is marked
          origs.push((i, c.lits)); // delay origs to the end
        }
      }

      Step::Add(i, ls, p) => {
        ctx.step = i;
        let c = ctx.remove(i);
        c.check_subsumed(&ls, ctx.step);
        if full || c.marked {
          if let Some(Proof::LRAT(is)) = p {
            if let Some(start) = is.iter().position(|&i| i < 0).filter(|_| !ls.is_empty()) {
              let (init, rest) = is.split_at(start);
              ctx.run_rat_step(&c, Some(init), rest.split_first(), false, hint)
            } else {
              ctx.run_rat_step(&c, Some(&is), None, false, hint)
            }
          } else {
            ctx.run_rat_step(&c, None, None, false, hint)
          };
          for &i in &hint.steps {
            let i = i.abs() as u64;
            let c = ctx.get(i);
            let cl = &mut ctx.clauses[c];
            if !cl.marked { // If the necessary clause is not active yet
              cl.marked = true; // Make it active
              if let [a, b, ..] = *cl.lits {
                ctx.watch.del(false, a, c);
                ctx.watch.del(false, b, c);
                ctx.watch.add(true, a, c);
                ctx.watch.add(true, b, c);
              }
              if !full {
                ElabStep::Del(i).write(w).expect("Failed to write delete step");
              }
            }
          }
          ElabStepRef::Add(i, &c.lits, &hint.steps).write(w).expect("Failed to write add step");
        }
      }

      Step::Reloc(mut relocs) => {
        ctx.reloc(&mut relocs);
        if !relocs.is_empty() {
          ElabStep::Reloc(relocs).write(w).expect("Failed to write reloc step");
        }
      }

      Step::Del(i, mut ls) => {
        ctx.step = i;
        dedup_vec(&mut ls);
        ctx.insert(i, false, ls.into());
        if full {
          ElabStep::Del(i).write(w).expect("Failed to write delete step");
        }
      },

      Step::Final(i, mut ls) => {
        ctx.step = i;
        // Identical to the Del case, except that the clause should be marked if empty
        dedup_vec(&mut ls);
        ctx.insert(i, ls.is_empty(), ls.into());
      }

      Step::Todo(_) => ()
    }
  }

  for (i, ls) in origs {
    ElabStep::Orig(i, ls.into()).write(w).expect("Failed to write orig step");
  }

  Ok(())
}

struct DeleteLine<'a, W>(&'a mut W, u64, bool);

impl<'a, W: Write> DeleteLine<'a, W> {
  fn with(lrat: &'a mut W, step: u64,
    f: impl FnOnce(&mut DeleteLine<'a, W>) -> io::Result<()>
  ) -> io::Result<()> {
    let mut l = DeleteLine(lrat, step, false);
    f(&mut l)?;
    if l.2 { writeln!(l.0, " 0")? }
    Ok(())
  }

  fn delete(&mut self, i: u64) -> io::Result<()> {
    if mem::replace(&mut self.2, true) {
      write!(self.0, " {}", i)
    } else {
      write!(self.0, "{} d {}", self.1, i)
    }
  }
}

fn trim(cnf: &[Box<[i64]>], temp_it: impl Iterator<Item=Segment>, lrat: &mut impl Write) -> io::Result<()> {

  let mut k = 0u64; // Counter for the last used ID
  let cnf: HashMap<PermClauseRef, u64> = // original CNF
    cnf.iter().map(|c| (PermClauseRef(c), {k += 1; k})).collect();
  let mut map: HashMap<u64, u64> = HashMap::new(); // Mapping between old and new IDs
  let mut bp = ElabStepIter(temp_it).peekable();
  let origs = k;
  let mut used_origs = vec![0u8; origs as usize];

  while let Some(ElabStep::Orig(_, _)) = bp.peek() {
    if let Some(ElabStep::Orig(i, ls)) = bp.next() {
      let j = *cnf.get(&PermClauseRef(&ls)).unwrap_or_else( // Find position of clause in original problem
        || panic!("Orig step {} refers to nonexistent clause {:?}", i, ls));
      let r = &mut used_origs[j as usize - 1];
      *r = r.saturating_add(1);
      assert!(map.insert(i, j).is_none(), "Multiple orig steps with duplicate IDs");
      if ls.is_empty() {
        writeln!(lrat, "{} 0 {} 0", k+1, j)?;
        return Ok(())
      }
    } else {unreachable!()}
  }

  DeleteLine::with(lrat, k, |line| {
    for (j, &b) in used_origs.iter().enumerate() {
      if b == 0 { line.delete(j as u64 + 1)? }
    }
    Ok(())
  })?;

  while let Some(s) = bp.next() {
    match s {

      ElabStep::Orig(_, _) =>
        panic!("Orig steps must come at the beginning of the temp file"),

      ElabStep::Add(i, ls, is) => {
        k += 1; // Get the next fresh ID
        map.insert(i, k); // The ID of added clause is mapped to a fresh ID
        let done = ls.is_empty();

        write!(lrat, "{}", k)?;
        for &x in &*ls { write!(lrat, " {}", x)? }
        write!(lrat, " 0")?;
        for x in is {
          let ux = x.abs() as u64;
          let lit = *map.get(&ux).unwrap_or_else(||
            panic!("step {}: proof step {:?} not found", i, ux)) as i64;
          write!(lrat, " {}", if x < 0 {-lit} else {lit})?
        }
        writeln!(lrat, " 0")?;

        if done {return Ok(())}
      }

      ElabStep::Reloc(relocs) => {
        let removed: Vec<_> = relocs.iter()
          .map(|(from, to)| (*to, map.remove(from))).collect();
        for (to, o) in removed {
          if let Some(s) = o { map.insert(to, s); }
        }
      }

      ElabStep::Del(i) => DeleteLine::with(lrat, k, |line| {
        let m = &mut map;
        let used_origs = &mut used_origs;
        let mut delete = move |i| -> io::Result<()> {
          let j = m.remove(&i).unwrap();
          if match used_origs.get_mut(j as usize - 1) {
            None => true,
            Some(&mut u8::MAX) => false,
            Some(refc) => { *refc -= 1; *refc == 0 }
          } { line.delete(j)? }
          Ok(())
        };

        // Remove ID mapping to free space
        delete(i)?;
        // agglomerate additional del steps into this block
        while let Some(&ElabStep::Del(i)) = bp.peek() {
          bp.next();
          delete(i)?;
        }
        Ok(())
      })?
    }
  }

  panic!("did not find empty clause");
}

pub fn main(args: impl Iterator<Item=String>) -> io::Result<()> {
  let mut args = args.peekable();
  let full = if args.peek().map_or(false, |s| s == "--full") {
    args.next(); true
  } else {false};
  let dimacs = args.next().expect("missing input file");
  let frat_path = args.next().expect("missing proof file");

  let mut frat = File::open(&frat_path)?;
  let in_mem = match args.peek() {
    Some(arg) if arg.starts_with("-m") => {
      let n = if let Ok(n) = arg[2..].parse() { n }
      else { frat.metadata()?.len().saturating_mul(5) };
      args.next();
      Some(n)
    }
    _ => None
  };

  let bin = detect_binary(&mut frat)?;
  println!("elaborating...");
  if let Some(temp_sz) = in_mem {
    let mut temp = Vec::with_capacity(temp_sz as usize);
    if bin { elab(Bin, full, frat, &mut temp)? }
    else { elab(Ascii, full, frat, &mut temp)? }

    return finish(args, full, dimacs, VecBackParser(temp))
  } else {
    let temp_path = format!("{}.temp", frat_path);
    {
      let mut temp_write = BufWriter::new(File::create(&temp_path)?);
      if bin { elab(Bin, full, frat, &mut temp_write)? }
      else { elab(Ascii, full, frat, &mut temp_write)? };
      temp_write.flush()?;
    }

    let temp_read = BackParser::new(Bin, File::open(temp_path)?)?;
    return finish(args, full, dimacs, temp_read)
  }

  fn finish(mut args: impl Iterator<Item=String>,
    full: bool, dimacs: String,
    temp_read: impl Iterator<Item=Segment>
  ) -> io::Result<()> {
    if !full {
      println!("parsing DIMACS...");
      let (_vars, cnf) = parse_dimacs_map(read_to_string(dimacs)?.bytes(),
        |mut c| {dedup_vec(&mut c); c.into()});
      println!("trimming...");
      let (lrat_file, verify) = match args.next() {
        Some(ref s) if s == "-v" => (None, true),
        Some(lrat_file) => (Some(lrat_file), matches!(args.next(), Some(ref s) if s == "-v")),
        _ => (None, false),
      };
      if let Some(lrat_file) = lrat_file {
        let mut lrat = BufWriter::new(File::create(&lrat_file)?);
        trim(&cnf, temp_read, &mut lrat)?;
        lrat.flush()?;
        if verify {
          println!("verifying...");
          let lrat = File::open(lrat_file)?;
          check_lrat(Ascii, cnf, BufReader::new(lrat).bytes().map(Result::unwrap))?;
          println!("VERIFIED");
        }
      } else if verify {
        println!("verifying...");
        let mut lrat = vec![];
        trim(&cnf, temp_read, &mut lrat)?;
        check_lrat(Ascii, cnf, lrat.into_iter())?;
        println!("VERIFIED");
      } else {
        trim(&cnf, temp_read, &mut io::sink())?;
      }
    }
    Ok(())
  }
}

fn check_lrat(mode: impl Mode, cnf: Vec<Box<[i64]>>, lrat: impl Iterator<Item=u8>) -> io::Result<()> {
  let lp = LRATParser::from(mode, lrat);
  let mut k = 0;
  let ctx = &mut Context::default();
  let hint = &mut Hint::default();

  for c in cnf {
    k += 1;
    ctx.step = k;
    ctx.insert(k, true, c);
  }

  for (i, s) in lp {
    ctx.step = i;
    match s {

      LRATStep::Add(ls, p) => {
        assert!(i > k, "out-of-order LRAT proofs not supported");
        k = i;
        if let Some(start) = p.iter().position(|&i| i < 0).filter(|_| !ls.is_empty()) {
          let (init, rest) = p.split_at(start);
          ctx.run_rat_step(&ls, Some(init), rest.split_first(), true, hint);
        } else {
          ctx.run_rat_step(&ls, Some(&p), None, true, hint);
        }
        if ls.is_empty() { return Ok(()) }
        ctx.insert(i, true, ls.into());
      }

      LRATStep::Del(ls) => {
        assert!(i == k, "out-of-order LRAT proofs not supported");
        for c in ls { ctx.remove(c.try_into().unwrap()); }
      }
    }
  }

  panic!("did not find empty clause")
}

pub fn lratchk(mut args: impl Iterator<Item=String>) -> io::Result<()> {
  let dimacs = args.next().expect("missing input file");
  let (_vars, cnf) = parse_dimacs(read_to_string(dimacs)?.bytes());
  let lrat = File::open(args.next().expect("missing proof file"))?;
  check_lrat(Ascii, cnf, BufReader::new(lrat).bytes().map(Result::unwrap))
}

fn refrat_pass(elab: File, w: &mut impl Write) -> io::Result<()> {

  let mut ctx: HashMap<u64, Vec<i64>> = HashMap::new();
  for s in ElabStepIter(BackParser::new(Bin, elab)?) {
    match s {

      ElabStep::Orig(i, ls) => {
        StepRef::Orig(i, &ls).write(w)?;
        ctx.insert(i, ls);
      }

      ElabStep::Add(i, ls, is) => {
        StepRef::Add(i, &ls, Some(ProofRef::LRAT(&is))).write(w)?;
        ctx.insert(i, ls);
      }

      ElabStep::Reloc(relocs) => {
        StepRef::Reloc(&relocs).write(w)?;
        let removed: Vec<_> = relocs.iter()
          .map(|(from, to)| (*to, ctx.remove(from))).collect();
        for (to, o) in removed {
          if let Some(s) = o { ctx.insert(to, s); }
        }
      }

      ElabStep::Del(i) => {
        Step::Del(i, ctx.remove(&i).unwrap()).write(w)?;
      }
    }
  }

  for (i, s) in ctx { Step::Final(i, s).write(w)? }

  Ok(())
}

pub fn refrat(mut args: impl Iterator<Item=String>) -> io::Result<()> {
  let elab_path = args.next().expect("missing elab file");
  let frat_path = args.next().expect("missing frat file");
  let w = &mut BufWriter::new(File::create(&frat_path)?);
  refrat_pass(File::open(elab_path)?, w)?;
  w.flush()
}
