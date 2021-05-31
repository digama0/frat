use std::io::{self, Read, BufReader, Write, BufWriter};
use std::fs::{File, read_to_string};
use std::convert::TryInto;
use std::mem;
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::collections::HashMap;
use slab::Slab;

use super::midvec::MidVec;
use super::dimacs::{parse_dimacs, parse_dimacs_map};
use super::serialize::{Serialize, ModeWrite, ModeWriter};
use super::parser::{detect_binary, Step, StepRef, ElabStep, ElabStepRef,
  AddStep, AddStepRef, Segment, Proof, Mode, Ascii, Bin, LRATParser, LRATStep};
use super::backparser::{VecBackParser, BackParser, StepIter, ElabStepIter};
use super::perm_clause::*;

// Set this to true to get an error log when unit propagation fails (assumes no RAT steps)
const LOG_UNIT_PROP_ERROR: bool = false;

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
  fn clear_to(&mut self, n: usize) {
    for i in self.tru_stack.drain(n..) {
      self.tru_lits[i] = Assign::No;
      self.reasons[i] = Reason::NONE;
    }
    self.first_unprocessed = self.first_unprocessed.min(n);
  }

  fn clear_hyps(&mut self) {
    let n = self.first_hyp;
    self.clear_to(n)
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
    // eprintln!("remove watch: {:?} for {:?}", l, i);
    let vec = &mut self.watch_mut(marked)[l];
    if let Some(i) = vec.iter().position(|x| *x == i) {
      vec.swap_remove(i);
      return
    }
    panic!("Literal {} not watched in clause {}", l, i);
  }
  #[inline] fn add(&mut self, marked: bool, l: i64, id: usize) {
    // eprintln!("add watch: {:?} for {:?}", l, id);
    self.watch_mut(marked)[l].push(id);
  }
}

#[derive(Default)]
struct Hint {
  steps: Vec<i64>,
  temp: Vec<i64>,
}

#[derive(Default)]
struct RatHint {
  hint: Hint,
  pre_rat: Vec<i64>,
  rat_set: HashMap<usize, bool>,
  witness: Vec<i64>,
  witness_va: MidVec<bool>,
}

#[derive(Default)]
struct Context {
  max_var: i64,
  clauses: Slab<Clause>,
  names: HashMap<u64, usize>,
  units: HashMap<usize, i64>,
  watch: Watches,
  va: VAssign,
  rat_set_lit: i64,
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
    let unit = self.sort_size(&mut lits) == (false, 1);
    let i = self.clauses.insert(Clause {marked, name, lits});
    assert!(self.names.insert(name, i).is_none(),
      "at {:?}: Clause {} to be inserted already exists", self.step, name);
    self.rat_set_lit = 0;
    self.watch.0[0].reserve_to(self.max_var);
    self.watch.0[1].reserve_to(self.max_var);
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
      self.clauses[addr].name = from;
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
      #[cfg(debug)] step: u64,
      clauses: &'a Slab<Clause>,
      hint: &'a mut Hint,
    }

    impl<'a> Finalize<'a> {
      fn mark(&mut self, lit: i64) {
        #[cfg(debug)] {
          assert!(self.va.is_true(lit), "at {:?}: {} is unjustified", self.step, lit);
        }
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
      #[cfg(debug)] step: self.step,
      clauses: &self.clauses,
      hint,
    };

    fin.mark(conflict);
    fin.mark(-conflict);

    debug_assert!(!fin.hint.steps.is_empty(),
      "at {}: empty hint or tautologous clause", self.step);
  }

  fn clear_marks(&mut self, hint: &mut Hint) {
    for lit in hint.temp.drain(..) {
      self.va.tru_lits[lit] = Assign::Yes
    }
  }

  #[allow(unused)]
  fn self_test(&mut self) {
    'a: for (_, c) in &self.clauses {
      let mut lits = 0;
      for lit in c {
        if self.va.is_true(lit) { continue 'a }
        else if !self.va.is_false(lit) { lits += 1 }
      }
      if lits <= 1 {
        let msg = format!("at {}: Unit propagation missed unit {:?}", self.step, c);
        let _ = self.log_status("unit_prop_error.log", &[]);
        panic!("{}", msg);
      }
    }

    for (addr, cl) in &self.clauses {
      if let [a, b, ..] = *cl.lits {
        for &l in &[a, b] {
          if !self.watch.watch_mut(cl.marked)[l].contains(&addr) {
            let msg = format!("at {}: Watch {} not watching clause {}", self.step, l, cl.name);
            let _ = self.log_status("unit_prop_error.log", &[]);
            panic!("{}", msg);
          }
        }
      }
    }
  }

  fn propagate_core(&mut self) -> Option<i64> {
    let root = self.va.first_hyp >= self.va.tru_stack.len();
    // if verb {
    //   println!("{}: propagate_core {} {:?}", self.step, root,
    //     &self.va.tru_stack[self.va.first_unprocessed..]);
    //   let _ = self.log_status("unit_prop_before.log", &[]);
    // }

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
          // eprintln!("Working on clause {}: {:?} at {}", i, c, j);

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

    // self.self_test();

    // if verb {
    //   let _ = self.log_status("unit_prop_error.log", &[]);
    // }

    // If there are no more literals to propagate, unit propagation has failed
    None
  }

  fn propagate(&mut self, c: &[i64]) -> Option<i64> {
    // if verb {
    //   println!("propagate {:?}", c);
    //   let _ = self.log_status("unit_prop_before.log", c);
    // }

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
    if LOG_UNIT_PROP_ERROR {
      let _ = self.log_status("unit_prop_error.log", c);
      panic!("at {}: Unit propagation stuck, cannot add clause {:?}", self.step, c)
    }
    None
  }

  #[allow(unused)]
  fn log_status(&self, file: &str, c: &[i64]) -> io::Result<()> {
    let Self {va, clauses, units, ..} = self;
    // If unit propagation is stuck, write an error log
    let mut log = BufWriter::new(File::create(file)?);
    writeln!(log, "Step {}\n", self.step)?;
    writeln!(log, "Clauses available ((l) means false, [l] means true):")?;
    for (addr, c) in clauses {
      write!(log, "{:?}: {} = ", addr, c.name)?;
      let mut sat = false;
      let mut lits = 0;
      for lit in c {
        if va.is_true(lit) { write!(log, "[{}] ", lit)?; sat = true }
        else if va.is_false(lit) { write!(log, "({}) ", lit)? }
        else { lits += 1; write!(log, "{} ", lit)? }
      }
      if let [l] = **c {
        if units.get(&addr) != Some(&l) {
          write!(log, " (BUG: untracked unit clause)")?
        }
      }
      writeln!(log, "{}", match (sat, lits) {
        (true, _) => " (satisfied)",
        (_, 0) => " (BUG: undetected falsified clause)",
        (_, 1) => " (BUG: undetected unit clause)",
        _ => ""
      })?;
    }
    writeln!(log, "\nObtained unit literals{}:",
      if va.units_processed {""} else {" (not all units have not been populated)"})?;
    for (i, &lit) in va.tru_stack.iter().enumerate() {
      assert!(va.is_true(lit));
      writeln!(log, "[{}] {}: {:?}{}{}{}", i, lit,
        va.reasons[lit].clause().map(|c| &clauses[c]),
        if i >= va.first_unprocessed {" (unprocessed)"} else {""},
        if i >= va.first_hyp {" (hypothetical)"} else {""},
        match va.tru_lits[lit] {
          Assign::No => " (BUG: unassigned)",
          Assign::Yes => "",
          Assign::Mark => " (marked)"
        })?;
    }
    if !c.is_empty() {
      writeln!(log, "\nTarget clause: {:?}", c)?;
    }
    log.flush()
  }

  fn propagate_hint(&mut self, ls: &[i64], is: &[i64], strict: bool) -> Option<i64> {
    // if verb {
    //   println!("propagate_hint {:?} {:?}", ls, is);
    //   let _ = self.log_status("unit_prop_before.log", ls);
    // }

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
      if !progress { return None }
      mem::swap(&mut is, &mut queue);
    }
  }

  fn build_step(&mut self, ls: &[i64], hint: Option<&[i64]>, strict: bool, out: &mut Hint,
    fallback: impl FnOnce(&mut Self) -> Option<()>,
  ) -> bool {
    if let Some(is) = hint {
      if let Some(k) = self.propagate_hint(ls, is, strict) {
        self.finalize_hint(k, out);
        return true
      } else if fallback(self).is_some() { return true }
    }
    if let Some(k) = self.propagate(ls) {
      self.finalize_hint(k, out);
      return true
    }
    false
  }

  fn pr_resolve_one(&mut self,
    ls: &[i64], c: usize, witness_va: &MidVec<bool>, depth: usize,
    hint: Option<&[i64]>, strict: bool,
    out: &mut Hint, pre_rat: &mut Vec<i64>
  ) {
    let step_start = out.steps.len();
    let mark_start = out.temp.len();
    (|| {
      let cl = &self.clauses[c];
      assert!(!strict || hint.is_some(), "Clause {} = {:?} not in LRAT trace", cl.name, cl.lits);
      out.steps.push(-(cl.name as i64));
      if let Some(k) = self.va.unsat() {
        self.finalize_hint(k, out);
        return
      }
      for x in cl {
        if !witness_va[-x] && !self.va.assign(-x, Reason::NONE) {
          self.finalize_hint(x, out);
          return
        }
      }
      assert!(self.build_step(&[], hint, strict, out, |_| None),
        "Unit propagation stuck, cannot resolve clause {:?} with {:?}",
        ls, self.clauses[c]);
    })();

    self.va.clear_to(depth);

    let mut next = out.steps[step_start..].iter_mut().peekable();
    for lit in &mut out.temp[mark_start..] {
      if self.va.is_true(*lit) {
        if let Some(c) = self.va.reasons[*lit].clause() {
          let mut name = self.clauses[c].name as i64;
          while next.peek() != Some(&&mut name) {next.next().unwrap();}
          pre_rat.push(mem::take(next.next().unwrap()))
        }
      } else { *lit = 0 }
    }
  }

  fn run_step<'a>(&mut self, ls: &[i64],
    in_wit: Option<&[i64]>, init: Option<&[i64]>,
    mut rats: Option<(&'a i64, &'a [i64])>, strict: bool,
    RatHint {hint: out, pre_rat, rat_set, witness, witness_va}: &mut RatHint
  ) {
    out.steps.clear();
    witness.clear();
    let success = if rats.is_none() {
      self.build_step(ls, init, strict, out, |this| {
        // Special case: A RAT step which introduces a fresh variable is indistinguishable
        // from a non-RAT step, because there are no negative numbers in the LRAT proof since no
        // clauses contain the negated pivot literal. In this case a correct and optimal hint
        // is present but empty, and RUP fails quickly in this case. So we insert some extra code
        // here to avoid incurring the cost of propagate() in a 100% hints file.
        //
        // We assume that PR steps don't follow this path because any PR step with no touched
        // clauses can be expressed as a PR step with only one witness literal, which is a RAT step.
        if !init?.is_empty() { return None }
        let pivot = *ls.first()?;
        if this.rat_set_lit == pivot {
          if !rat_set.is_empty() { return None }
        } else {
          for (_, cl) in &this.clauses {
            if cl.contains(&-pivot) { return None }
          }
        }
        Some(())
      })
    } else if let Some(k) = self.propagate_hint(ls, init.unwrap_or(&[]), strict) {
      self.finalize_hint(k, out);
      true
    } else { false };

    if success {
      self.clear_marks(out);
      self.va.clear_hyps();
      return
    }

    if let Some(w) = in_wit {
      for &lit in w {
        assert!(!self.va.is_false(lit) ||
            self.va.tru_stack.iter().rposition(|&l| l == -lit).unwrap() >= self.va.first_hyp,
          "step failed, witness literal {} is complement of clause {:?}",
          lit, self.clauses[self.va.reasons[-lit].clause().unwrap()]);
        if !self.va.is_true(lit) { witness.push(lit) }
      }
    } else {
      witness.push(*ls.first().expect("Unit propagation stuck, failed to prove empty clause"))
    }

    let depth = self.va.tru_stack.len();

    if **witness == [self.rat_set_lit] {
      rat_set.values_mut().for_each(|seen| *seen = false);
      witness.iter().for_each(|&w| witness_va[w] = true);
    } else {
      rat_set.clear();
      witness_va.reserve_to(self.max_var);
      witness.iter().for_each(|&w| witness_va[w] = true);
      if let [pivot] = **witness {
        for (c, cl) in &self.clauses {
          if cl.contains(&-pivot) {
            assert!(rat_set.insert(c, false).is_none())
          }
        }
        self.rat_set_lit = pivot
      } else {
        'next_clause: for (c, cl) in &self.clauses {
          let mut red = false;
          for lit in cl {
            if witness_va[lit] { continue 'next_clause }
            if witness_va[-lit] { red = true }
          }
          if red { assert!(rat_set.insert(c, false).is_none()) }
        }
      }
    }
    let mut unseen = rat_set.len();

    mem::swap(&mut out.steps, pre_rat);

    while let Some((&s, rest)) = rats {
      let c = self.get(-s as u64);
      let hint = if let Some(i) = rest.iter().position(|&i| i < 0) {
        let (chain, r) = rest.split_at(i);
        rats = r.split_first();
        chain
      } else {
        rats = None;
        rest
      };
      if let Some(seen @ &mut false) = rat_set.get_mut(&c) {
        self.pr_resolve_one(ls, c, witness_va, depth, Some(hint), strict, out, pre_rat);
        *seen = true;
        unseen -= 1;
      }
    }

    if unseen != 0 {
      for (&c, _) in rat_set.iter().filter(|(_, &seen)| !seen) {
        self.pr_resolve_one(ls, c, witness_va, depth, None, strict, out, pre_rat);
      }
    }

    mem::swap(&mut out.steps, pre_rat);
    for lit in out.temp.drain(..) {
      if lit != 0 {
        self.va.tru_lits[lit] = Assign::Yes
      }
    }
    out.steps.extend(pre_rat.drain(..).filter(|&l| l != 0));
    self.clear_marks(out);
    self.va.clear_hyps();
    witness.iter().for_each(|&w| witness_va[w] = false)
  }
}

fn elab<M: Mode>(mode: M, full: bool, frat: File, w: &mut impl ModeWrite) -> io::Result<()> {
  let mut origs = Vec::new();
  let ctx = &mut Context::default();
  let hint = &mut RatHint::default();
  for s in StepIter(BackParser::new(mode, frat)?) {
    // eprintln!("<- {:?}", s);
    match s {

      Step::Orig(i, ls) => {
        ctx.step = i;
        let c = ctx.remove(i);
        c.check_subsumed(&ls, ctx.step);
        if full || c.marked {  // If the original clause is marked
          origs.push((i, c.lits)); // delay origs to the end
        }
        // else { eprintln!("delete {}", i); }
      }

      Step::Add(i, step, p) => {
        ctx.step = i;
        let mut c = ctx.remove(i);
        let kind = step.parse();
        let ls = kind.lemma();
        c.check_subsumed(ls, ctx.step);
        if full || c.marked {
          let wit = kind.witness();
          if let Some(Proof::LRAT(is)) = p {
            if let Some(start) = is.iter().position(|&i| i < 0).filter(|_| !ls.is_empty()) {
              let (init, rest) = is.split_at(start);
              ctx.run_step(&c, wit, Some(init), rest.split_first(), false, hint)
            } else {
              ctx.run_step(&c, wit, Some(&is), None, false, hint)
            }
          } else {
            ctx.run_step(&c, wit, None, None, false, hint)
          };
          let steps = &*hint.hint.steps;
          for &i in steps {
            let i = i.abs() as u64;
            let c = ctx.get(i);
            let cl = &mut ctx.clauses[c];
            // let v = cs.get_mut(&i).unwrap();
            if !cl.marked { // If the necessary clause is not active yet
              cl.marked = true; // Make it active
              if let [a, b, ..] = *cl.lits {
                ctx.watch.del(false, a, c);
                ctx.watch.del(false, b, c);
                ctx.watch.add(true, a, c);
                ctx.watch.add(true, b, c);
              }
              if !full { ElabStep::Del(i).write(w)? }
            }
          }
          if let Some(&lit) = hint.witness.first() {
            let k = c.lits.iter().position(|&lit2| lit == lit2).unwrap();
            c.lits.swap(0, k);
          }
          let add = if hint.witness.len() <= 1 {
            AddStepRef::One(&c.lits)
          } else {
            AddStepRef::Two(&c.lits, &hint.witness)
          };
          ElabStepRef::Add(i, add, steps).write(w)?
        }
        // else { eprintln!("delete {}", i); }
      }

      Step::Reloc(mut relocs) => {
        ctx.reloc(&mut relocs);
        if !relocs.is_empty() { ElabStep::Reloc(relocs).write(w)? }
      }

      Step::Del(i, mut ls) => {
        ctx.step = i;
        dedup_vec(&mut ls);
        ctx.insert(i, false, ls.into());
        if full { ElabStep::Del(i).write(w)? }
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

  for (i, ls) in origs { ElabStep::Orig(i, ls.into()).write(w)? }

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
      // eprintln!("-> Orig{:?}", (&i, &ls));
      let j = *cnf.get(&PermClauseRef(&ls)).unwrap_or_else( // Find position of clause in original problem
        || panic!("Orig step {} refers to nonexistent clause {:?}", i, ls));
      let r = &mut used_origs[j as usize - 1];
      *r = r.saturating_add(1);
      assert!(map.insert(i, j).is_none(), "Multiple orig steps with duplicate IDs");
      // eprintln!("{} -> {}", i, j);
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
    // eprintln!("-> {:?}", s);

    match s {

      ElabStep::Orig(_, _) =>
        panic!("Orig steps must come at the beginning of the temp file"),

      ElabStep::Add(i, AddStep(ls), is) => {
        k += 1; // Get the next fresh ID
        map.insert(i, k); // The ID of added clause is mapped to a fresh ID
        // eprintln!("{} -> {}", i, k);
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
    let mut temp = ModeWriter(Bin, Vec::with_capacity(temp_sz as usize));
    if bin { elab(Bin, full, frat, &mut temp)? }
    else { elab(Ascii, full, frat, &mut temp)? }

    return finish(args, full, dimacs, VecBackParser(temp.1))
  } else {
    let temp_path = format!("{}.temp", frat_path);
    {
      let mut temp_write = ModeWriter(Bin, BufWriter::new(File::create(&temp_path)?));
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
  let hint = &mut RatHint::default();

  for c in cnf {
    k += 1;
    ctx.step = k;
    // eprintln!("{}: {:?}", k, c);
    ctx.insert(k, true, c);
  }

  for (i, s) in lp {
    ctx.step = i;
    // eprintln!("{}: {:?}", i, s);
    match s {

      LRATStep::Add(add, p) => {
        assert!(i > k, "out-of-order LRAT proofs not supported");
        k = i;
        let add = add.parse_into(|kind| {
          let ls = kind.lemma();
          let wit = kind.witness();
          // eprintln!("{}: {:?} {:?}", k, ls, p);
          if let Some(start) = p.iter().position(|&i| i < 0).filter(|_| !ls.is_empty()) {
            let (init, rest) = p.split_at(start);
            ctx.run_step(ls, wit, Some(init), rest.split_first(), true, hint);
          } else {
            ctx.run_step(ls, wit, Some(&p), None, true, hint);
          }
        }).1;
        if add.is_empty() { return Ok(()) }
        ctx.insert(i, true, add.into());
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

fn refrat_pass(elab: File, w: &mut impl ModeWrite) -> io::Result<()> {

  let mut ctx: HashMap<u64, Vec<i64>> = HashMap::new();
  for s in ElabStepIter(BackParser::new(Bin, elab)?) {
    // eprintln!("-> {:?}", s);

    match s {

      ElabStep::Orig(i, ls) => {
        StepRef::Orig(i, &ls).write(w)?;
        ctx.insert(i, ls);
      }

      ElabStep::Add(i, ls, is) => {
        StepRef::add(i, &ls.0, Some(&is)).write(w)?;
        ctx.insert(i, ls.parse_into(|_| {}).1);
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
  let w = &mut ModeWriter(Bin, BufWriter::new(File::create(&frat_path)?));
  refrat_pass(File::open(elab_path)?, w)?;
  w.flush()
}
