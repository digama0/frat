use std::io::{self, Read, BufReader, Write, BufWriter};
use std::fs::{File, read_to_string};
use std::convert::TryInto;
use std::collections::VecDeque;
use std::mem;
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::collections::HashMap;
use slab::Slab;

use super::midvec::MidVec;
use super::dimacs::{parse_dimacs, parse_dimacs_map};
use super::serialize::Serialize;
use super::parser::{detect_binary, Step, StepRef, ElabStep, Segment,
  Proof, ProofRef, Mode, Ascii, Bin, LRATParser, LRATStep};
use super::backparser::{VecBackParser, BackParser, StepIter, ElabStepIter};
use super::perm_clause::*;

// Set this to true to get an error log when unit propagation fails
const LOG_UNIT_PROP_ERROR: bool = false;

#[derive(Default)]
struct VAssign {
  tru_lits: MidVec<bool>,
  reasons: MidVec<Option<usize>>,
  tru_stack: Vec<i64>,
}

impl VAssign {
  fn clear(&mut self) {
    for i in self.tru_stack.drain(..) {
      self.tru_lits[i] = false;
      self.reasons[i] = None;
    }
  }

  fn reserve_clear(&mut self, max: i64) {
    self.clear();
    self.tru_lits.reserve_cleared(max);
    self.reasons.reserve_cleared(max);
  }

  #[inline] fn is_true(&self, l: i64) -> bool { self.tru_lits[l] }
  #[inline] fn is_false(&self, l: i64) -> bool { self.is_true(-l) }

  // Attempt to update the variable assignment and make l true under it.
  // If the update is impossible because l is already false under it, return false.
  // Otherwise, update and return true.
  fn assign(&mut self, l: i64, reason: Option<usize>) -> bool {
    if self.is_true(l) { return true }
    if self.is_false(l) {
      self.reasons[l] = reason;
      self.tru_stack.push(l);
      return false
    }
    self.reasons[l] = reason;
    self.tru_lits[l] = true;
    self.tru_stack.push(l);
    true
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

  fn check_subsumed(&self, lits: &[i64], step: Option<u64>) {
    assert!(lits.iter().all(|lit| self.contains(lit)),
      "at {:?}: Clause {:?} added here will later be deleted as {:?}",
      step, self, lits)
  }
}

#[derive(Default)]
struct Context {
  max_var: i64,
  clauses: Slab<Clause>,
  names: HashMap<u64, usize>,
  units: HashMap<usize, i64>,
  watch: Option<MidVec<Vec<usize>>>,
  step: Option<u64>
}

fn del_watch(watch: &mut MidVec<Vec<usize>>, l: i64, i: usize, clauses: &Slab<Clause>) {
  // eprintln!("remove watch: {:?} for {:?}", l, i);
  let vec = &mut watch[l];
  if let Some(i) = vec.iter().position(|x| *x == i) {
    vec.swap_remove(i);
    return
  }
  panic!("Literal {} not watched in clause {} = {:?}", l, i, clauses[i].name);
}
#[inline] fn add_watch(watch: &mut MidVec<Vec<usize>>, l: i64, id: usize) {
  // eprintln!("add watch: {:?} for {:?}", l, id);
  watch[l].push(id);
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

fn init_watch<'a, 'b>(w: &'a mut Option<MidVec<Vec<usize>>>, max_var: i64, cl: &Slab<Clause>) -> &'a mut MidVec<Vec<usize>> {
  w.get_or_insert_with(move || {
    let mut watch = MidVec::with_capacity(2 * max_var);
    for (i, c) in cl {
      if let [l1, l2, ..] = **c {
        add_watch(&mut watch, l1, i);
        add_watch(&mut watch, l2, i);
      }
    }
    watch
  })
}

impl Context {

  fn new() -> Context { Default::default() }

  fn insert(&mut self, name: u64, marked: bool, lits: Box<[i64]>) {
    for &lit in &*lits {
      self.max_var = self.max_var.max(lit.abs())
    }
    if let Some(w) = &mut self.watch { w.reserve_to(self.max_var) }
    let i = self.clauses.insert(Clause {marked, name, lits});
    assert!(self.names.insert(name, i).is_none(),
      "at {:?}: Clause {} to be inserted already exists", self.step, name);
    match *self.clauses[i].lits {
      [] => {}
      [l] => { self.units.insert(i, l); }
      [l1, l2, ..] => if let Some(w) = &mut self.watch {
        add_watch(w, l1, i);
        add_watch(w, l2, i);
      }
    }
  }

  fn remove(&mut self, name: u64) -> Clause {
    let i = self.names.remove(&name).unwrap_or_else(
      || panic!("at {:?}: Clause {} to be removed does not exist", self.step, name));

    let clause = self.clauses.remove(i);

    match *clause {
      [] => {}
      [_] => { self.units.remove(&i); }
      [l1, l2, ..] => if let Some(w) = &mut self.watch {
        del_watch(w, l1, i, &self.clauses);
        del_watch(w, l2, i, &self.clauses);
      }
    }

    clause
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
}

// Return the next literal to be propagated, and indicate whether
// its propagation should be limited to marked/unmarked clauses
fn next_prop_lit([ls0, ls1]: &mut [VecDeque<i64>; 2]) -> Option<(bool, i64)> {
  if let Some(l) = ls0.pop_front() { return Some((true, l)); }
  if let Some(l) = ls1.pop_front() { return Some((false, l)); }
  None
}

#[derive(Default)]
struct Propagate {
  ls: [VecDeque<i64>; 2],
  va: VAssign,
  steps: Vec<usize>,
}

impl Propagate {
  fn minimize_hint(&mut self, ctx: &Context) {
    let mut need = vec![false; self.steps.len()];
    *need.last_mut().unwrap_or_else(
      || panic!("at {:?}: minimizing empty hint", ctx.step)) = true;

    for (i, &s) in self.steps.iter().enumerate().rev() {
      if need[i] {
        for &l in &*ctx.clauses[s] {
          if let Some(j) = self.va.reasons[-l] {need[j] = true}
        }
      }
    }
    self.steps.retain({ let mut i = need.into_iter(); move |_| i.next().unwrap() });
  }
}

fn propagate(c: &[i64], ctx: &mut Context, Propagate {ls, va, steps}: &mut Propagate) -> bool {
  ls[0].clear();
  ls[1].clear();
  steps.clear();
  va.reserve_clear(ctx.max_var);

  macro_rules! push {($i:expr) => {(steps.len(), steps.push($i)).0}}

  for l in c {
    ls[0].push_back(-l);
    ls[1].push_back(-l);
    if !va.assign(-l, None) { return true }
  }

  for (&i, &l) in &ctx.units {
    ls[0].push_back(l);
    ls[1].push_back(l);
    if !va.assign(l, Some(push!(i))) { return true }
  }

  let watch = init_watch(&mut ctx.watch, ctx.max_var, &ctx.clauses);

  // Main unit propagation loop
  while let Some((m, l)) = next_prop_lit(ls) {
    // 'is' contains the IDs of all clauses containing -l
    let mut is = &*watch[-l];
    let mut wi = 0..;
    while let Some(&i) = is.get(wi.next().unwrap()) {
      let cl = &mut ctx.clauses[i];

      // m indicates propagation targets (m == true for marked clauses),
      // va is the current variable assignment, and i is the ID of a clause
      // which may potentially be unit under va. If c is verified under va,
      // do nothing and return None. If c is not verified but contains two
      // or more undecided literals, watch them and go to the next clause. Otherwise,
      // let k be a new unit literal.

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

      if cl.iter().any(|&l| va.is_true(l)) {continue}

      // Since -l has just been falsified, we need a new watch literal to replace it.
      // Let j be another literal in the clause that has not been falsified.
      if let Some(j) = (2..cl.len()).find(|&i| !va.is_false(cl[i])) {
        // eprintln!("Working on clause {}: {:?} at {}", i, c, j);

        cl.swap(1, j); // Replace the -l literal with cl[j]
        let k = cl[1]; // let k be the new literal
        del_watch(watch, -l, i, &ctx.clauses); // remove this clause from the -l watch list
        add_watch(watch, k, i); // and add it to the k watch list

        // Since we just modified the -l watch list, that we are currently iterating
        // over, we have to tweak the iterator so that we don't miss anything.
        wi.start -= 1; is = &*watch[-l];

        // We're done here, we didn't find a new unit
        continue
      }

      // Otherwise, there are no other non-falsified literals in the clause,
      // meaning that this is a binary clause of the form k \/ -l
      // where k is the other watch literal in the clause, so we either
      // have a new unit, or if k is falsified then we proved false and can finish.
      let k = cl[0];

      // Push the new unit on the chain
      if !va.assign(k, Some(push!(i))) {
        // if we find a contradiction then exit
        return true
      }

      // Otherwise, put k on the work lists and go to the next clause.
      ls[0].push_back(k);
      ls[1].push_back(k);
    }
  }

  // If there are no more literals to propagate, unit propagation has failed
  if LOG_UNIT_PROP_ERROR {
    let _ = propagate_stuck(ctx, va, steps, c);
    panic!("Unit propagation stuck, cannot add clause {:?}", c)
  }
  false
}

#[allow(unused)]
fn propagate_stuck(ctx: &Context, va: &VAssign, steps: &[usize], c: &[i64]) -> io::Result<()> {
  // If unit propagation is stuck, write an error log
  let mut log = BufWriter::new(File::create("unit_prop_error.log")?);
  writeln!(log, "Clauses available at failure ((l) means false, [l] means true):")?;
  for (addr, c) in &ctx.clauses {
    write!(log, "{:?}: {} = ", addr, c.name)?;
    let mut sat = false;
    let mut lits = 0;
    for lit in c {
      if va.is_true(lit) { write!(log, "[{}] ", lit)?; sat = true }
      else if va.is_false(lit) { write!(log, "({}) ", lit)? }
      else { lits += 1; write!(log, "{} ", lit)? }
    }
    if let [l] = **c {
      if ctx.units.get(&addr) != Some(&l) {
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
  writeln!(log, "\nRecorded steps at failure: {:?}", steps)?;
  writeln!(log, "\nObtained unit literals at failure:")?;
  for &lit in &va.tru_stack {
    assert!(va.is_true(lit));
    writeln!(log, "{}: {:?}", lit, va.reasons[lit].map(|i| steps[i]))?;
  }
  writeln!(log, "\nFailed to add clause: {:?}", c)?;
  log.flush()
}

fn propagate_hint(ls: &[i64], ctx: &mut Context, is: &[i64], strict: bool,
    Propagate {va, steps, ..}: &mut Propagate) -> bool {
  steps.clear();
  va.reserve_clear(ctx.max_var);

  for &x in ls {
    assert!(va.assign(-x, None), "tautologous clause");
  }

  let mut is: Vec<usize> = is.iter().map(|&i| ctx.get(i as u64)).collect();
  let mut queue = vec![];
  loop {
    let len = is.len();
    'a: for c in is.drain(..) {
      let mut uf: Option<i64> = None;
      let cl = &*ctx.clauses[c];
      for &l in cl {
        if !va.is_false(l) && uf.replace(l).is_some() {
          assert!(!strict, "at {:?}: clause {:?} is not unit", ctx.step, c);
          queue.push(c);
          continue 'a
        }
      }
      match uf {
        None => {
          steps.push(c);
          return true
        },
        Some(l) => assert!(
          va.assign(l, (Some(steps.len()), steps.push(c)).0),
          "l is not assigned"),
      }
    }
    if queue.len() >= len {return false}
    mem::swap(&mut is, &mut queue);
  }
}

fn build_step(ls: &[i64], ctx: &mut Context, p: &mut Propagate, hint: Option<&[i64]>, strict: bool) -> Option<Vec<i64>> {
  fn finish(ctx: &Context, p: &mut Propagate) -> Vec<i64> {
    p.minimize_hint(ctx);
    p.steps.iter().map(|&i| ctx.clauses[i].name as i64).collect()
  }
  match hint {
    Some(is) if propagate_hint(&ls, ctx, is, strict, p) => Some(finish(ctx, p)),
    _ if propagate(ls, ctx, p) => Some(finish(ctx, p)),
    _ => None
  }
}

fn run_rat_step<'a>(ls: &[i64], ctx: &mut Context, p: &mut Propagate, init: &[i64],
    mut rats: Option<(&'a i64, &'a [i64])>, strict: bool) -> Vec<i64> {
  if rats.is_none() {
    if let Some(res) = build_step(ls, ctx, p, if init.is_empty() {None} else {Some(init)}, strict) {
      return res
    }
  }
  let _ = propagate_hint(&ls, ctx, init, strict, p);
  let pivot = ls[0];
  let ls2: Vec<i64> = p.va.tru_stack.iter().map(|&i| -i).filter(|&i| i != pivot).collect();
  let mut proofs = HashMap::new();
  let mut order = vec![];
  while let Some((&s, rest)) = rats {
    let step = ctx.get(-s as u64);
    order.push(step);
    match rest.iter().position(|&i| i < 0) {
      None => {
        proofs.insert(step, rest);
        break
      }
      Some(i) => {
        let (chain, r) = rest.split_at(i);
        proofs.insert(step, chain);
        rats = r.split_first();
      }
    }
  }
  let mut steps = vec![];
  let mut todo = vec![];
  for (c, cl) in &ctx.clauses {
    if cl.lits.contains(&-pivot) {
      let mut resolvent = ls2.clone();
      resolvent.extend(cl.lits.iter().cloned().filter(|&i| i != -pivot));
      match proofs.get(&c) {
        Some(&chain) => todo.push((c, resolvent, Some(chain))),
        None if strict => panic!("Clause {:?} not in LRAT trace", cl.lits),
        None => {
          order.push(c);
          todo.push((c, resolvent, None));
        }
      }
    }
  }
  let mut proofs: HashMap<_, _> = todo.into_iter().map(|(c, resolvent, hint)|
    (c, build_step(&resolvent, ctx, p, hint, strict).unwrap_or_else(||
      panic!("Unit propagation stuck, cannot resolve clause {:?}", resolvent)))).collect();

  for c in order {
    let mut chain = proofs.remove(&c).unwrap();
    steps.push(-(ctx.clauses[c].name as i64));
    steps.append(&mut chain);
  }
  steps
}

fn elab<M: Mode>(mode: M, full: bool, frat: File, w: &mut impl Write) -> io::Result<()> {
  let mut ctx: Context = Context::new();
  let mut origs = Vec::new();
  let propagate = &mut Propagate::default();
  for s in StepIter(BackParser::new(mode, frat)?) {
    // eprintln!("<- {:?}", s);
    match s {

      Step::Orig(i, ls) => {
        ctx.step = Some(i);
        let c = ctx.remove(i);
        c.check_subsumed(&ls, ctx.step);
        if full || c.marked {  // If the original clause is marked
          origs.push((i, c.lits)); // delay origs to the end
        }
        // else { eprintln!("delete {}", i); }
      }

      Step::Add(i, ls, p) => {
        ctx.step = Some(i);
        let c = ctx.remove(i);
        c.check_subsumed(&ls, ctx.step);
        if full || c.marked {
          let steps: Vec<i64> = if let Some(Proof::LRAT(is)) = p {
            if let Some(start) = is.iter().position(|&i| i < 0).filter(|_| !ls.is_empty()) {
              let (init, rest) = is.split_at(start);
              run_rat_step(&c, &mut ctx, propagate, init, rest.split_first(), false)
            } else {
              run_rat_step(&c, &mut ctx, propagate, &is, None, false)
            }
          } else {
            run_rat_step(&c, &mut ctx, propagate, &[], None, false)
          };
          for &i in &steps {
            let i = i.abs() as u64;
            let c = ctx.get(i);
            let cl = &mut ctx.clauses[c];
            // let v = cs.get_mut(&i).unwrap();
            if !cl.marked { // If the necessary clause is not active yet
              cl.marked = true; // Make it active
              if !full {
                ElabStep::Del(i).write(w).expect("Failed to write delete step");
              }
            }
          }
          ElabStep::Add(i, c.lits.into(), steps).write(w).expect("Failed to write add step");
        }
        // else { eprintln!("delete {}", i); }
      }

      Step::Reloc(mut relocs) => {
        ctx.step = None;
        ctx.reloc(&mut relocs);
        if !relocs.is_empty() {
          ElabStep::Reloc(relocs).write(w).expect("Failed to write reloc step");
        }
      }

      Step::Del(i, mut ls) => {
        dedup_vec(&mut ls);
        ctx.insert(i, false, ls.into());
        if full {
          ElabStep::Del(i).write(w).expect("Failed to write delete step");
        }
      },

      Step::Final(i, mut ls) => {
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

      ElabStep::Add(i, ls, is) => {
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
  let mut ctx: Context = Context::new();
  let mut k = 0;
  let propagate = &mut Propagate::default();

  for c in cnf {
    k += 1;
    ctx.step = Some(k);
    // eprintln!("{}: {:?}", k, c);
    ctx.insert(k, true, c);
  }

  for (i, s) in lp {
    ctx.step = Some(i);
    // eprintln!("{}: {:?}", i, s);
    match s {

      LRATStep::Add(ls, p) => {
        assert!(i > k, "out-of-order LRAT proofs not supported");
        k = i;
        // eprintln!("{}: {:?} {:?}", k, ls, p);
        if let Some(start) = p.iter().position(|&i| i < 0).filter(|_| !ls.is_empty()) {
          let (init, rest) = p.split_at(start);
          run_rat_step(&ls, &mut ctx, propagate, init, rest.split_first(), true);
        } else {
          run_rat_step(&ls, &mut ctx, propagate, &p, None, true);
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
    // eprintln!("-> {:?}", s);

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
