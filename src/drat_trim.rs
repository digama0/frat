use std::{fmt::{Display, Debug}, io::StdinLock};
use std::io::{self, Read, Write, Seek, SeekFrom, BufReader};
use std::ops::{Deref, DerefMut};
use std::fs::File;
use std::mem;
use std::time::Instant;
use either::Either;
use io::{BufRead, BufWriter, stdout};
use crate::{dimacs, midvec::MidVec, parser::{DRATParser, DRATStep}};

const TIMEOUT: u64 = 40000;
const INIT: usize = 4;
const BIGINIT: usize = 1000000;
const INFOBITS: usize = 2;
const ACTIVE: usize = 1;

#[derive(Copy, Clone)]
enum Mode {
  BackwardUnsat,
  ForwardUnsat,
  ForwardSat,
}

enum VerifyResult {
  Fail,
  Unsat,
  Derivation,
}
enum Warning {
  /// display warning messages
  Normal,
  /// suppress warning messages
  NoWarning,
  /// exit after first warning
  HardWarning,
}

#[repr(u8)] #[derive(Copy, Clone, Debug)]
enum Assign {
  Unassigned,
  Assigned,
  Assumed,
  Mark,
}

impl Default for Assign {
  fn default() -> Self { Self::Unassigned }
}
impl Assign {
  #[inline] fn assigned(self) -> bool { !matches!(self, Assign::Unassigned) }
}
impl From<bool> for Assign {
  #[inline] fn from(b: bool) -> Self {
    if b {Assign::Assigned} else {Assign::Unassigned}
  }
}

fn get_hash(lits: &[i64]) -> usize {
  crate::perm_clause::get_clause_hash(lits).0 as u32 as usize % BIGINIT
}

#[derive(Copy, Clone)]
struct ClauseId(usize);

impl ClauseId {
  fn new(id: usize, active: bool) -> Self { Self(id << 1 | active as usize) }
  #[inline] fn id(self) -> usize { self.0 >> 1 }
  #[inline] fn active(self) -> bool { self.0 & ACTIVE != 0 }
}

impl Debug for ClauseId {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if self.active() { write!(f, "*{}", self.id()) } else { write!(f, "{}", self.id()) }
  }
}

#[derive(Copy, Clone)]
struct Witness(usize);

impl Witness {
  #[inline] fn new(id: Option<usize>) -> Self { Self(id.unwrap_or(usize::MAX)) }
  #[inline] fn get(self) -> Option<usize> {
    if self.0 == usize::MAX {None} else {Some(self.0)}
  }
}

struct Clause {
  ida: ClauseId,
  pivot: i64,
  maxdep: usize,
  witness: Witness,
  lits: Vec<i64>,
}

impl Clause {
  fn as_ref(&self) -> ClauseRef<'_> {
    ClauseRef {ida: self.ida, lits: &self.lits}
  }

  #[inline] fn id(&self) -> usize { self.ida.id() }
  #[inline] fn active(&self) -> bool { self.ida.active() }
  #[inline] fn deactivate(&mut self) { self.ida.0 &= !ACTIVE }
  #[inline] fn activate(&mut self) { self.ida.0 |= ACTIVE }
}

impl Deref for Clause {
  type Target = Vec<i64>;
  fn deref(&self) -> &Vec<i64> { &self.lits }
}
impl DerefMut for Clause {
  fn deref_mut(&mut self) -> &mut Vec<i64> { &mut self.lits }
}

impl Display for Clause {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.as_ref().fmt(f)
  }
}

struct ClauseRef<'a> {ida: ClauseId, lits: &'a [i64]}

impl<'a> Display for ClauseRef<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "[{}] ", self.ida.0)?;
    for &lit in self.lits { write!(f, "{} ", lit)? }
    write!(f, "0")
  }
}

#[derive(Copy, Clone)]
struct Watch(usize);

impl Watch {
  #[inline] fn new(idx: usize, mask: bool) -> Watch {
    Watch(idx << 1 | mask as usize)
  }
  fn clause(self) -> usize { self.0 >> 1 }
  fn mark(&mut self) { self.0 |= ACTIVE }
}

#[derive(Copy, Clone, PartialEq, Eq)]
struct ProofStep(usize);

impl ProofStep {
  const NULL: ProofStep = ProofStep(0);
  #[inline] fn add(idx: usize) -> ProofStep { ProofStep(idx << INFOBITS) }
  #[inline] fn del(idx: usize) -> ProofStep { ProofStep(idx << INFOBITS | 1) }
  #[inline] fn clause(self) -> usize { self.0 >> INFOBITS }
  #[inline] fn is_del(self) -> bool { self.0 & 1 != 0 }
}

struct TrackLen<R>(R, usize);

impl<R> TrackLen<R> {
  fn new(r: R) -> Self { Self(r, 0) }
  fn bytes_read(&self) -> usize { self.1 }
}

impl<R: Read> Read for TrackLen<R> {
  fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
    let n = self.0.read(buf)?;
    self.1 += n;
    Ok(n)
  }
}
impl<R: BufRead> BufRead for TrackLen<R> {
  fn fill_buf(&mut self) -> io::Result<&[u8]> {
    self.0.fill_buf()
  }

  fn consume(&mut self, amt: usize) {
    self.0.consume(amt);
    self.1 += amt;
  }
}

#[derive(Copy, Clone, PartialEq, Eq)]
struct Reason(usize);

impl Reason {
  const NONE: Self = Self(0);
  #[inline] fn new(clause_id: usize) -> Self { Self(clause_id + 1) }
  #[inline] fn get(self) -> Option<usize> { self.0.checked_sub(1) }
}

#[derive(Copy, Clone, PartialEq, Eq)]
struct Dependency(i64);

impl Dependency {
  fn new(id: i64, forced: bool) -> Self { Self(id << 1 | forced as i64) }
  #[inline] fn id(self) -> i64 { self.0 >> 1 }
  #[inline] fn forced(self) -> bool { self.0 & 1 != 0 }
  #[inline] fn is_pos(self) -> bool { self.0 >= 0 }
}

impl Debug for Dependency {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if self.forced() { write!(f, "*{}", self.id()) } else { write!(f, "{}", self.id()) }
  }
}

struct SolverOpts {
  /// prints the core lemmas to the file LEMMAS (LRAT format)
  lrat_file: Option<BufWriter<File>>,
  trace_file: Option<BufWriter<File>>,
  /// prints the active clauses to the file ACTIVE (DIMACS format)
  active_file: Option<BufWriter<File>>,
  /// time limit in seconds
  timeout: u64,
  mask: bool,
  /// if false, run in plain mode (i.e., ignore deletion information)
  delete: bool,
  /// force binary proof parse mode
  bin_mode: bool,
  /// optimize proof till fixpoint by repeating verification
  optimize: bool,
  /// compress core lemmas (emit binary proof)
  bin_output: bool,
  /// show progress bar
  bar: bool,
  backforce: bool,
  /// reduce mode
  reduce: bool,
  mode: Mode,
  /// more verbose output
  verb: bool,
  warning: Warning,
  /// delete proof file after parsing
  del_proof: bool,
  /// prints the unsatisfiable core to the file CORE (DIMACS format)
  core_str: Option<String>,
  /// prints the core lemmas to the file LEMMAS (DRAT format)
  lemma_str: Option<String>,
  start_time: Instant,
}

impl SolverOpts {
  fn new() -> Self {
    Self {
      core_str: None,
      active_file: None,
      lemma_str: None,
      lrat_file: None,
      trace_file: None,
      timeout: TIMEOUT,
      mask: false,
      verb: false,
      del_proof: false,
      backforce: false,
      optimize: false,
      warning: Warning::Normal,
      bar: false,
      mode: Mode::BackwardUnsat,
      delete: true,
      reduce: true,
      bin_mode: false,
      bin_output: false,
      start_time: Instant::now(),
    }
  }

  fn warn(&self, f: impl FnOnce()) {
    match self.warning {
      Warning::Normal => f(),
      Warning::NoWarning => {}
      Warning::HardWarning => {
        f();
        std::process::exit(80);
      }
    }
  }
}

struct LRATLine {
  name: i64,
  clause: Box<[i64]>,
  chain: Box<[i64]>
}
struct Solver {
  opts: SolverOpts,
  db: Vec<Clause>,
  false_stack: Vec<i64>,
  false_a: MidVec<Assign>,
  forced: usize,
  processed: usize,
  count: usize,
  rat_mode: bool,
  rat_count: usize,
  num_active: usize,
  lrat_table: Box<[Option<LRATLine>]>,
  num_lemmas: usize,
  rat_set: Vec<usize>,
  pre_rat: Vec<Dependency>,
  deps: Vec<Dependency>,
  max_var: i64,
  prep: bool,
  current: usize,
  num_removed: usize,
  time: ClauseId,
  num_vars: usize,
  num_clauses: usize,
  unit_stack: Vec<usize>,
  witness: Vec<Vec<i64>>,
  reason: Box<[Reason]>,
  num_resolve: usize,
  watch_list: MidVec<Vec<Watch>>,
  opt_proof: Vec<ProofStep>,
  formula: Vec<ProofStep>,
  proof: Vec<ProofStep>,
}

impl Deref for Solver {
  type Target = SolverOpts;
  fn deref(&self) -> &Self::Target { &self.opts }
}

fn creating(s: &Option<String>, f: impl FnOnce(File) -> io::Result<()>) -> io::Result<()> {
  if let Some(s) = s { f(File::create(s)?) } else {Ok(())}
}

macro_rules! reason {($self:ident, $lit:expr) => { $self.reason[$lit.abs() as usize] }}

macro_rules! assign {($self:ident, $lit:expr) => {{
  let lit = $lit;
  $self.false_a[-lit] = Assign::Assigned;
  $self.false_stack.push(-lit);
}}}

fn pop_ext<T: Clone>(vec: &[T], idx: &mut usize) -> Option<T> {
  *idx = idx.checked_sub(1)?;
  Some(vec[*idx].clone())
}

fn shrink_vec<T>(vec: &mut Vec<T>, size: usize) {
  let old = mem::replace(vec, Vec::with_capacity(size));
  vec.extend(old);
}

fn write_lit(f: &mut impl Write, lit: i64) -> io::Result<()> {
  let mut l = (lit.abs() as u64) << 1;
  if lit < 0 { l += 1 }
  loop {
    f.write_all(&[if l <= 127 {l} else {128 + (l & 127)} as u8])?;
    l >>= 7;
    if l == 0 {return Ok(())}
  }
}

impl Solver {
  #[inline] fn reason(&mut self, lit: i64) -> &mut Reason {
    &mut reason!(self, lit)
  }

  fn assign(&mut self, lit: i64) { assign!(self, lit) }

  #[inline] fn add_watch(&mut self, clause: usize, lit: i64) {
    self.watch_list[lit].push(Watch::new(clause, self.opts.mask))
  }

  fn remove_watch(&mut self, clause: usize, lit: i64) {
    let watch = &mut self.watch_list[lit];
    if watch.len() > INIT && watch.capacity() > 2 * watch.len() {
      shrink_vec(watch, 3 * watch.len() >> 1);
    }
    let i = watch.iter().position(|&w| w.clause() == clause).unwrap();
    watch.swap_remove(i);
  }

  fn add_unit(&mut self, index: usize) {
    self.unit_stack.push(index)
  }

  fn pop_forced(&mut self) -> Option<i64> {
    pop_ext(&self.false_stack, &mut self.forced)
  }

  fn pop_all_forced(&mut self) {
    while self.forced < self.false_stack.len() {
      let lit = self.false_stack.pop().unwrap();
      self.false_a[lit] = Assign::Unassigned;
      reason!(self, lit) = Reason::NONE;
    }
  }

  fn remove_unit(&mut self, lit: i64) {
    if let Some(i) = self.unit_stack.iter()
        .position(|&cl| self.db[cl][0] == lit) {
      self.unit_stack.remove(i);
    }
  }

  fn unassign_unit(&mut self, lit: i64) {
    if self.verb { println!("c removing unit {}", lit) }
    while self.false_a[-lit].assigned() {
      self.forced = self.forced.checked_sub(1).unwrap();
      let old = self.false_stack[self.forced];
      if self.verb { println!("c removing unit {} ({})", old, lit) }
      self.false_a[old] = Assign::Unassigned;
      *self.reason(old) = Reason::NONE;
    }
    self.processed = self.forced;
    self.false_stack.truncate(self.forced);
  }

  fn mark_watch(&mut self, clause: usize, index: usize) {
    self.watch_list[self.db[clause][index]]
      .iter_mut().find(|w| w.clause() == clause)
      .unwrap().mark();
  }

  fn add_dependency(&mut self, dep: Dependency) {
    if true || self.trace_file.is_some() || self.lrat_file.is_some() {
      self.deps.push(dep);
    }
  }

  fn mark_clause(&mut self, clause: usize, skip_index: usize, forced: bool) {
    self.num_resolve += 1;
    let id = self.db[clause].ida;
    self.add_dependency(Dependency::new(id.id() as i64, forced));
    if !id.active() {
      self.num_active += 1;
      self.db[clause].activate();
      match (self.opts.mode, self.db[clause].len() > 1) {
        (Mode::BackwardUnsat, true) => self.opt_proof.push(ProofStep::del(clause)),
        (_, false) => return,
        _ => {}
      }
      self.mark_watch(clause, 0);
      self.mark_watch(clause, 1);
    }
    for &lit in &self.db[clause][skip_index..] {
      self.false_a[lit] = Assign::Mark
    }
  }

  fn analyze(&mut self, clause: usize, skip_index: usize) {
    let mut assigned = self.false_stack.len();
    self.mark_clause(clause, skip_index, assigned > self.forced);
    while let Some(lit) = pop_ext(&self.false_stack, &mut assigned) {
      match self.false_a[lit] {
        Assign::Mark => if let Some(cl) = self.reason(lit).get() {
          self.mark_clause(cl, 1, assigned > self.forced);
        },
        Assign::Assumed if !self.rat_mode && self.reduce => {
          self.num_removed += 1;
          let cl = &mut *self.db[self.current];
          let i = cl.iter().position(|&i| i == lit).unwrap();
          cl.remove(i);
        }
        _ => {}
      }
      let force = assigned < self.forced;
      if !force { *self.reason(lit) = Reason::NONE }
      self.false_a[lit] = force.into();
    }
    self.processed = self.forced;
    self.false_stack.truncate(self.forced);
  }

  fn propagate(&mut self) -> bool {
    let mut check = 0;
    let mode = !self.prep;
    let mut start = [self.processed; 2];
    let mut prev: Option<(i64, (*mut Vec<Watch>, usize))> = None;
    'flip_check: loop {
      check ^= 1;
      while let Some(&lit) = self.false_stack.get(start[check]) {
        start[check] += 1;
        let (watch, mut wi) = match prev {
          Some((_lit, _watch)) if lit == _lit => _watch,
          _ => (&mut self.watch_list[lit] as *mut _, 0),
        };
        // SAFETY: The borrow of self.watch_list[lit] here is disjoint from
        // the borrow of self.watch_list[ci] below because lit != ci
        // (clauses have no duplicates)
        let watch = unsafe {&mut *watch};
        'next_clause: while let Some(&w) = watch.get(wi) {
          if w.0 & mode as usize != check { wi += 1; continue }
          let index = w.clause();
          let cl = &mut *self.db[index];
          let (a, b) = if let [a, b, ..] = **cl {(a, b)} else {panic!()};
          if self.false_a[-a].assigned() ||
             self.false_a[-b].assigned() {
            wi += 1; continue
          }
          if a == lit {cl.swap(0, 1)}
          for i in 2..cl.len() {
            let ci = cl[i];
            if !self.false_a[ci].assigned() {
              cl.swap(1, i);
              debug_assert!(lit != ci);
              self.watch_list[ci].push(watch.swap_remove(wi));
              continue 'next_clause
            }
          }
          let lit2 = cl[0]; wi += 1;
          if !self.false_a[lit2].assigned() {
            self.assign(lit2);
            *self.reason(lit2) = Reason::new(index);
            if check == 0 {
              start[0] -= 1;
              prev = Some((lit, (watch, wi)));
              continue 'flip_check
            }
          } else { self.analyze(index, 0); return true }
        }
      }
      if check == 0 {break}
    }
    self.processed = self.false_stack.len();
    false
  }

  fn propagate_units(&mut self) -> bool {
    while let Some(i) = self.pop_forced() {
      self.false_a[i] = Assign::Unassigned;
      reason!(self, i) = Reason::NONE;
    }
    self.processed = 0; self.false_stack.clear();
    for &c in &self.unit_stack {
      let lit = self.db[c][0];
      reason!(self, lit) = Reason::new(c);
      assign!(self, lit);
    }
    if self.propagate() {return true}
    self.forced = self.processed;
    false
  }

  /// Put falsified literals at the end and returns the size under the current
  /// assignment: `sat = true` means satisfied, `size = 0` means falsified
  fn sort_size(&mut self, lemma: usize) -> (bool, usize) {
    let mut size = 0;
    let lemma = &mut **self.db[lemma];
    let mut sat = false;
    for last in 0..lemma.len() {
      let lit = lemma[last];
      if !self.false_a[lit].assigned() {
        sat |= self.false_a[-lit].assigned();
        lemma.swap(last, size);
        size += 1;
      }
    }
    (sat, size)
  }

  fn core_iter(&self, core: bool) -> impl Iterator<Item=&Clause> {
    self.formula.iter()
      .map(move |step| &self.db[step.clause()])
      .filter(move |cl| cl.active() == core)
  }

  fn print_core(&mut self, core_count: usize) -> io::Result<()> {
    println!("c {} of {} clauses in core                            ",
      core_count, self.num_clauses);

    creating(&self.core_str, |mut f| {
      writeln!(f, "p cnf {} {}", self.num_vars, core_count)?;
      for clause in self.core_iter(true) {
        for i in &**clause {write!(f, "{} ", i)?}
        writeln!(f, "0")?;
      }
      Ok(())
    })
  }

  fn print_lrat_line(&self, f: &mut impl Write, time: usize) -> io::Result<()> {
    let l = self.lrat_table[time].as_ref().unwrap();
    if self.bin_output {
      f.write_all(b"a")?;
      write_lit(f, l.name)?;
      for &lit in &*l.clause { write_lit(f, lit)? }
      write_lit(f, 0)?;
      for &lit in &*l.chain { write_lit(f, lit)? }
      write_lit(f, 0)
    } else {
      write!(f, "{} ", l.name)?;
      for &lit in &*l.clause { write!(f, "{} ", lit)? }
      write!(f, "0 ")?;
      for &lit in &*l.chain { write!(f, "{} ", lit)? }
      writeln!(f, "0")
    }
  }

  fn print_proof(&mut self, core_count: usize) -> io::Result<()> {
    println!("c {} of {} lemmas in core using {} resolution steps",
      self.num_active - core_count + 1, self.num_lemmas + 1, self.num_resolve);
    println!("c {} PR lemmas in core; {} redundant literals in core lemmas",
      self.rat_count, self.num_removed);

    match self.mode {
      Mode::ForwardUnsat => {
        println!("c optimized proofs are not supported for forward checking");
        return Ok(());
      }
      Mode::BackwardUnsat => {
        let mut num_lemmas = 0;
        self.proof = self.opt_proof.iter().copied().rev()
          .inspect(|ad| if !ad.is_del() { num_lemmas += 1 })
          .collect();
        self.num_lemmas = num_lemmas;
      }
      _ => {}
    }

    creating(&self.lemma_str, |mut f| {
      for &ad in &self.proof {
        let lemma = &self.db[ad.clause()];
        if lemma.len() <= 1 && ad.is_del() {continue}
        if self.bin_output {
          f.write_all(if ad.is_del() {b"d"} else {b"a"})?
        } else if ad.is_del() {write!(f, "d ")?}
        let reslit = lemma.pivot;
        for lit in lemma.iter().copied().filter(|&lit| lit == reslit)
            .chain(lemma.iter().copied().filter(|&lit| lit != reslit))
            .chain(lemma.witness.get().map(|w| &*self.witness[w])
              .unwrap_or(&[]).iter().copied()) {
          if self.bin_output { write_lit(&mut f, lit)? }
          else { write!(f, "{} ", lit)? }
        }
        if self.bin_output { write_lit(&mut f, 0)? }
        else { writeln!(f, "0")? }
      }
      if self.bin_output { f.write_all(b"a")?; write_lit(&mut f, 0) }
      else { writeln!(f, "0") }
    })?;

    if let Some(mut f) = self.opts.lrat_file.take() {
      let mut last_added = self.num_clauses;
      for &ad in &self.proof {
        let lemmas = &self.db[ad.clause()];
        if !ad.is_del() {
          if last_added == 0 {
            if self.bin_output { write_lit(&mut f, 0)? }
            else { writeln!(f, "0")? }
          }
          last_added = lemmas.id();
          self.print_lrat_line(&mut f, last_added)?;
        } else if last_added != self.num_clauses && lemmas.len() > 1 {
          if last_added != 0 {
            if self.bin_output { f.write_all(b"d")? }
            else { write!(f, "{} d ", last_added)? }
            last_added = 0;
          }
          if self.bin_output { write_lit(&mut f, lemmas.id() as i64)? }
          else { write!(f, "{} ", lemmas.id())? }
        }
        f.flush()?;
      }
      if last_added != self.num_clauses {
        if self.bin_output { write_lit(&mut f, 0)? }
        else { writeln!(f, "0")? }
      }
      self.print_lrat_line(&mut f, self.count)?;
      f.flush()?;
      let writes = f.seek(SeekFrom::Current(0))?;
      if writes != 0 {
        println!("c wrote optimized proof in LRAT format of {} bytes", writes);
      }
    }

    Ok(())
  }

  fn print_no_core(&mut self) -> io::Result<()> {
    if let Some(lrat) = &mut self.opts.lrat_file {
      if self.opts.bin_output { lrat.write_all(b"d")? }
      else { write!(lrat, "{} d ", self.num_clauses)? }
      for step in &self.formula {
        let clause = &self.db[step.clause()];
        if !clause.active() {
          if self.opts.bin_output { write_lit(lrat, clause.id() as i64)? }
          else { write!(lrat, "{} ", clause.id())? }
        }
      }
      if self.opts.bin_output { write_lit(lrat, 0)? }
      else { writeln!(lrat, "0")? }
    }
    Ok(())
  }

  fn print_trace(&mut self) -> io::Result<()> {
    if let Some(mut f) = self.opts.trace_file.take() {
      for (step, i) in self.formula.iter().zip(1..) {
        let clause = &self.db[step.clause()];
        if clause.active() {
          write!(f, "{} ", i)?;
          for i in &**clause {write!(f, "{} ", i)?}
          writeln!(f, "0 0")?;
        }
      }
      f.flush()?;
    }
    Ok(())
  }

  fn print_active(&mut self) -> io::Result<()> {
    if let Some(active) = &mut self.opts.active_file {
      for lit in (-self.max_var..=self.max_var).filter(|&i| i != 0) {
        for &w in &self.watch_list[lit] {
          let clause = &**self.db[w.clause()];
          if clause[0] == lit {
            for i in clause {write!(active, "{} ", i)?}
            writeln!(active, "0")?;
          }
        }
      }
    }
    Ok(())
  }

  fn postprocess(&mut self) -> io::Result<()> {
    self.print_no_core()?;
    self.print_active()?;
    let core_count = self.core_iter(true).count();
    self.print_core(core_count)?;
    self.print_trace()?;
    self.print_proof(core_count)
  }

  fn print_dependencies_file(&mut self, clause: Option<usize>, mode: bool) -> io::Result<()> {
    if let Some(f) = if mode {&mut self.opts.lrat_file} else {&mut self.opts.trace_file} {
      let db = &self.db;
      let time = clause.map_or(self.count, |c| db[c].id());
      let (name, clause) = if let Some(cl) = clause {
        let cl = &db[cl];
        let mut sorted = cl.to_vec();
        let reslit = cl.pivot;
        sorted.sort_by_key(|&lit| if lit == reslit {0} else {lit.abs()});
        // print the witness for PR
        if let Some(w) = cl.witness.get() { sorted.extend_from_slice(&self.witness[w]) }
        (self.time.id() as i64, sorted.into())
      } else {
        (self.count as i64, Box::new([]) as Box<[_]>)
      };

      let chain = if self.deps.iter().all(|&step| step.is_pos()) {
        self.deps.iter().rev().map(|&step| step.id()).collect::<Box<[_]>>()
      } else {
        let mut chain = Vec::with_capacity(self.deps.len());

        // first print the preRAT units in order of becoming unit
        self.pre_rat.clear();
        let mut last = 0;
        while let Some(len) = self.deps[last..].iter().position(|&step| step.id() < 0) {
          let next = last + len;
          for cls in self.deps[last..next].iter().rev().copied() {
            if !cls.forced() && !self.pre_rat.contains(&cls) {
              self.pre_rat.push(cls);
              chain.push(cls.id());
            }
          }
          last = next + 1;
        }

        // print dependencies in order of becoming unit
        for &cls in self.deps.iter().rev() {
          if mode {
            if cls.forced() {chain.push(cls.id())}
          } else if cls.is_pos() {
            if !self.pre_rat.contains(&cls) {
              self.pre_rat.push(cls);
              chain.push(cls.id());
            }
          }
        }

        chain.into_boxed_slice()
      };

      if !mode {
        write!(f, "{} ", name)?;
        for &lit in &*clause {write!(f, "{} ", lit)?}; write!(f, "0 ")?;
        for &lit in &*chain {write!(f, "{} ", lit)?}; writeln!(f, "0")?;
      }
      self.lrat_table[time] = Some(LRATLine {name, clause, chain})
    }
    Ok(())
  }

  fn print_dependencies(&mut self, clause: Option<usize>) -> io::Result<()> {
    if let Some(idx) = clause {
      let maxdep = self.deps.iter().map(|dep| dep.0).fold(0, i64::max) as usize;
      assert!(maxdep < self.db[idx].ida.0);
      self.db[idx].maxdep = maxdep;
    }
    self.print_dependencies_file(clause, false)?;
    self.print_dependencies_file(clause, true)
  }

  fn get_rat_set(&mut self, mut eligible: impl FnMut(&Clause) -> bool) -> Vec<usize> {
    let mut rat_set = mem::take(&mut self.rat_set);
    rat_set.clear();
    // Loop over all literals to calculate resolution candidates
    for i in (-self.max_var..=self.max_var).filter(|&i| i != 0) {
      // Loop over all watched clauses for literal
      for &w in &self.watch_list[i] {
        let watched = &self.db[w.clause()];
        if watched[0] == i && eligible(watched) { // If watched literal is in first position
          rat_set.push(w.clause());
        }
      }
    }
    rat_set.sort_by_key(|&i| self.db[i].ida.0);
    rat_set
  }

  fn check_one_rat(&mut self,
    cl: usize,
    clear_blocked: bool,
    mut witness: impl FnMut(i64) -> bool
  ) -> bool {
    let mut clause = &self.db[cl];
    let ida = clause.ida;

    let mut blocked = 0;
    let mut reason = Reason::NONE;
    for &lit in &**clause {
      if self.false_a[-lit].assigned() && !witness(-lit) {
        let reason2 = reason!(self, lit);
        let f = |bl: Reason| bl.get().map(|a| self.db[a].ida.0);
        if blocked == 0 || f(reason) > f(reason2) {
          blocked = lit; reason = reason2;
        }
      }
    }

    if blocked != 0 {
      if let Some(reason) = reason.get() {
        self.analyze(reason, 1);
        if clear_blocked { *self.reason(blocked) = Reason::NONE }
      }
    } else {
      for i in 0..clause.len() {
        let lit = clause[i];
        if !self.false_a[lit].assigned() && !witness(-lit) {
          self.assign(-lit);
          *self.reason(lit) = Reason::NONE;
          clause = &self.db[cl];
        }
      }
      if !self.propagate() { return false }
    }
    self.add_dependency(Dependency::new(-(ida.id() as i64), true));
    true
  }

  fn check_pr(&mut self, w: usize) -> bool {
    let mut witness = mem::take(&mut self.witness[w]);

    // remove from omega all literals in alpha+?
    witness.retain(|&lit| !self.false_a[-lit].assigned() || {
      if self.verb { println!("c removing overlap {}", lit) }
      false
    });

    // Calculate the clauses which are reduced but not satisfied by omega
    let rat_set = self.get_rat_set(|watched| {
      let mut reduced = false;
      for &lit in &**watched {
        for &j in &witness {
          if j == lit { return false }
          if j == -lit { reduced = true }
        }
      }
      reduced
    });

    // Check all clauses in rat_set for RUP
    let mut last_active = None;
    loop {
      let p_active = rat_set.iter().map(|&cl| &self.db[cl])
        .filter(|&pr_cls| pr_cls.active()).count();
      if mem::replace(&mut last_active, Some(p_active))
          .map_or(false, |last| last >= p_active) {
        self.rat_set = rat_set;
        self.witness[w] = witness;
        return true
      }

      self.deps.clear();
      for &cl in rat_set.iter().rev() {
        let pr_cls = &self.db[cl];
        if matches!(self.mode, Mode::BackwardUnsat) && !pr_cls.active() {
          if self.verb { println!("c PR check ignores unmarked clause: {}", pr_cls) }
          continue
        }
        if self.verb { println!("c PR clause: {}", pr_cls) }
        if !self.check_one_rat(cl, false, |lit| witness.contains(&lit)) {
          self.rat_set = rat_set;
          self.witness[w] = witness;
          self.pop_all_forced();
          if self.verb { println!("c PR check on witness failed") }
          return false
        }
      }
    }
  }

  fn check_rat(&mut self, pivot: i64) -> bool {
    // Loop over all literals to calculate resolution candidates
    let (mode, verb) = (self.mode, self.verb);
    let rat_set = self.get_rat_set(|watched| watched.contains(&-pivot) && {
      if matches!(mode, Mode::BackwardUnsat) && !watched.active() {
        if verb { println!("c RAT check ignores unmarked clause: {}", watched) }
        return false
      }
      true
    });

    // self.prep = true;
    // Check all clauses in rat_set for RUP
    self.deps.clear();
    for &cl in rat_set.iter().rev() {
      if verb { println!("c RAT clause: {}", self.db[cl]) }
      if !self.check_one_rat(cl, true, |lit| lit == pivot) {
        self.rat_set = rat_set;
        self.pop_all_forced();
        if verb { println!("c RAT check on pivot {} failed", pivot) }
        return false
      }
    }

    true
  }

  fn redundancy_check(&mut self, index: usize, sat: bool, size: usize) -> io::Result<bool> {
    let mut clause = &self.db[index];
    if let Some(w) = clause.witness.get() {
      for &lit in &*self.witness[w] {
        if self.false_a[lit].assigned() {
          println!("c ERROR: witness literal {} complement of units in lemma {}", lit, clause);
          return Ok(false)
        }
      }
    }

    let reslit = clause.pivot;
    let witness = clause.witness;
    if self.verb { println!("c checking lemma ({}, {}) {}", size, reslit, clause) }

    if !matches!(self.mode, Mode::ForwardUnsat) && !clause.active() {return Ok(true)}

    if sat {
      let reason = reason!(self, clause[0]);
      self.db[reason.get().unwrap()].activate();
      return Ok(true)
    }

    let false_pivot = self.false_a[reslit].assigned();
    self.rat_mode = false;
    self.deps.clear();
    for &lit in &clause[..size] {
      if self.false_a[-lit].assigned() { // should only occur in forward mode
        self.warn(|| println!(
          "c WARNING: found a tautological clause in proof: {}", clause));
        self.pop_all_forced();
        return Ok(true)
      }
      self.false_a[lit] = Assign::Assumed;
      self.false_stack.push(lit);
      reason!(self, lit) = Reason::NONE;
    }

    let indegree = self.num_resolve;
    self.current = index;
    if self.propagate() {
      let prep = self.num_resolve - indegree <= 2;
      if prep != self.prep {
        self.prep = prep;
        if self.verb {
          println!("c [{}] preprocessing checking mode {}",
            self.time.0, if prep {"on"} else {"off"})
        }
      }
      if self.verb { println!("c lemma has RUP") }
      self.print_dependencies(Some(index))?;
      return Ok(true)
    }

    // Failed RUP check.  Now test RAT.
    // println!("RUP check failed.  Starting RAT check.");
    if self.verb { println!("c RUP check failed; starting RAT check on pivot {}.", reslit) }

    if false_pivot {return Ok(false)}

    let forced = self.forced;
    self.rat_mode = true;
    self.forced = self.false_stack.len();

    let mut success = if let Some(w) = witness.get() {
      if !self.check_pr(w) { return Ok(false) }
      true
    } else { self.check_rat(reslit) };
    clause = &self.db[index];
    if !success {
      self.warn(|| println!(
        "c WARNING: RAT check on proof pivot failed: {}", clause));
      for i in 0..size {
        let lit = clause[i];
        if lit == reslit {continue}
        if self.check_rat(lit) {
          self.db[index].pivot = lit;
          success = true;
          break
        }
        clause = &self.db[index];
      }
    }

    if success { self.print_dependencies(Some(index))? }

    self.processed = forced;
    self.forced = forced;
    self.pop_all_forced();

    if !success {
      println!("c RAT check failed on all possible pivots");
      return Ok(false)
    }

    self.rat_count += 1;
    if self.verb {
      if witness.get().is_some() { println!("c lemma has PR") }
      else { println!("c lemma has RAT on {}", self.db[index].pivot) }
    }
    Ok(true)
  }

  fn init(&mut self) -> io::Result<bool> {
    self.forced = 0;
    self.processed = 0;
    self.false_stack.clear();
    self.rat_mode = false;
    self.num_removed = 0;
    self.opt_proof.clear();
    self.num_resolve = 0;
    self.rat_count = 0;
    self.num_active = 0;
    self.unit_stack.clear();
    for i in 1..=self.max_var {
      self.reason[i as usize] = Reason::NONE;
      self.false_a[i] = Assign::Unassigned;
      self.false_a[-i] = Assign::Unassigned;
      self.watch_list[i].clear();
      self.watch_list[-i].clear();
    }
    for i in 0..self.formula.len() {
      let c = self.formula[i].clause();
      let clause = &mut self.db[c];
      clause.deactivate();
      match ***clause {
        [] => {
          println!("c formula contains empty clause");
          creating(&self.core_str, |mut f| writeln!(f, "p cnf 0 1\n0"))?;
          creating(&self.lemma_str, |mut f| writeln!(f, "0"))?;
          return Ok(true)
        }
        [i, j, ..] => {
          self.add_watch(c, i);
          self.add_watch(c, j);
        }
        [i] => if self.false_a[i].assigned() {
          println!("c found complementary unit clauses: {}", i);
          creating(&self.core_str, |mut f|
            writeln!(f, "p cnf {} 2\n{} 0\n{} 0", i.abs(), i, -i))?;
          creating(&self.lemma_str, |mut f| writeln!(f, "0"))?;
          if let Some(lrat) = &mut self.opts.lrat_file {
            let db = &self.db;
            let j = self.formula.iter().position(
              |&step| *db[step.clause()] == [-i]).unwrap();
            writeln!(lrat, "{} 0 {} {} 0", self.num_clauses + 1, j + 1, i + 1)?;
          }
          return Ok(true)
        } else if !self.false_a[-i].assigned() {
          self.add_unit(c);
          self.assign(i);
        }
      }
    }
    self.deps.clear();
    self.time = ClauseId(self.count); // Alternative time init
    if self.propagate_units() {
      println!("c UNSAT via unit propagation on the input instance");
      self.print_dependencies(None)?;
      self.postprocess()?;
      return Ok(true)
    }
    Ok(false)
  }

  fn verify(&mut self, end_incl: usize) -> io::Result<VerifyResult> {
    if self.init()? {return Ok(VerifyResult::Unsat)}
    if let Mode::ForwardUnsat = self.mode {
      println!("c start forward verification")
    }

    let mut active = self.num_clauses;
    let mut adds = 0u64;
    let last_step = 'start_verification: loop {
      for step in 0..self.proof.len() {
        let ad = self.proof[step];
        let mut lemmas = &self.db[ad.clause()];

        self.time = lemmas.ida;
        if ad.is_del() { active -= 1 }
        else { active += 1; adds += 1; }
        if matches!(self.mode, Mode::ForwardSat) && self.verb {
          println!("c {} active clauses", active);
        }

        if let [lit] = ***lemmas { // found a unit
          if self.verb {
            println!("c found unit in proof {} [{}]", lit, self.time.0);
          }
          if ad.is_del() {
            if let Mode::ForwardSat = self.mode {
              self.remove_unit(lit);
              self.propagate_units();
            } else { // no need to remove units while checking UNSAT
              if self.verb { println!("c removing proof step: d {}", lemmas) }
              self.proof[step] = ProofStep::NULL;
              continue
            }
          } else if matches!(self.mode, Mode::BackwardUnsat) && self.false_a[-lit].assigned() {
            self.proof[step] = ProofStep::NULL;
            continue
          } else { self.add_unit(ad.clause()) }
          lemmas = &self.db[ad.clause()];
        }

        if ad.is_del() {
          if let [lit, lit2, ..] = ***lemmas { // if delete and not unit
            if *self.reason(lit) == Reason::new(ad.clause()) {
              if let Mode::ForwardSat = self.mode { // also for FORWARD_UNSAT?
                self.remove_watch(ad.clause(), lit);
                self.remove_watch(ad.clause(), lit2);
                self.propagate_units();
              } else { // ignore pseudo unit clause deletion
                if self.verb {
                  println!("c ignoring deletion instruction {}: {}",
                    step, self.db[ad.clause()])
                }
                self.proof[step] = ProofStep::NULL;
              }
            } else {
              self.remove_watch(ad.clause(), lit);
              self.remove_watch(ad.clause(), lit2);
            }
            if let Mode::ForwardSat | Mode::BackwardUnsat = self.mode { continue }
          }
        }

        let (sat, size) = self.sort_size(ad.clause());
        let (sat, size) = match (ad.is_del(), self.mode) {
          (true, Mode::ForwardSat) => {
            if sat { self.propagate_units(); }
            if !self.redundancy_check(ad.clause(), sat, size)? {
              println!("c failed at proof line {} (modulo deletion errors)", step + 1);
              return Ok(VerifyResult::Fail)
            }
            continue
          }
          (false, Mode::ForwardUnsat) if step >= end_incl => {
            if sat {continue} // bus error in drat-trim?
            if !self.redundancy_check(ad.clause(), sat, size)? {
              println!("c failed at proof line {} (modulo deletion errors)", step + 1);
              return Ok(VerifyResult::Fail)
            }
            self.deps.clear();
            self.sort_size(ad.clause())
          }
          _ => (sat, size)
        };
        if let [lit, lit2, ..] = **self.db[ad.clause()] {
          self.add_watch(ad.clause(), lit);
          self.add_watch(ad.clause(), lit2);
        }
        match (sat, size) {
          (_, 0) => {
            println!("c conflict claimed, but not detected");
            return Ok(VerifyResult::Fail)
          }
          (false, 1) => {
            let lit = self.db[ad.clause()][0];
            if self.verb { println!("c found unit {}", lit) }
            self.assign(lit);
            *self.reason(lit) = Reason::new(ad.clause());
            if self.propagate() { break 'start_verification step }
            self.forced = self.processed;
          }
          _ => {}
        }
      }

      match self.mode {
        Mode::ForwardSat => if active == 0 {
          self.postprocess()?;
          return Ok(VerifyResult::Unsat)
        },
        Mode::ForwardUnsat => {
          self.postprocess()?;
          println!("c VERIFIED derivation: all lemmas preserve satisfiability");
          if !matches!(self.warning, Warning::NoWarning) {
            println!("c WARNING: no empty clause detected, this is not a refutation");
          }
          return Ok(VerifyResult::Derivation)
        }
        Mode::BackwardUnsat => {
          if self.backforce {
            for step in 0..self.proof.len() {
              let ad = self.proof[step];
              if !self.sort_size(ad.clause()).0 {
                let clause = &mut self.db[ad.clause()];
                if ad.is_del() { clause.deactivate() }
                else { clause.activate() }
              }
            }
          } else {
            println!("c ERROR: no conflict");
            return Ok(VerifyResult::Fail)
          }
        }
      }

      unreachable!()
    };

    match self.mode {
      Mode::ForwardUnsat => {
        self.print_dependencies(None)?;
        self.postprocess()?;
        return Ok(VerifyResult::Unsat)
      }
      Mode::ForwardSat => {
        if !self.backforce { self.print_dependencies(None)? }
        println!("c ERROR: found empty clause during SAT check");
        return Ok(VerifyResult::Fail)
      }
      Mode::BackwardUnsat => {}
    }

    if !self.backforce { self.print_dependencies(None)? }
    println!("c detected empty clause; start verification via backward checking");
    self.forced = self.processed;
    self.opt_proof.clear();

    let mut _checked = 0;
    let mut _skipped = 0;
    let max = adds as f64;
    let backward_time = Instant::now();
    for step in (0..=last_step).rev() {
      let runtime = Instant::now().saturating_duration_since(backward_time);
      if runtime.as_secs() > self.timeout && !self.optimize {
        println!("s TIMEOUT");
        return Ok(VerifyResult::Fail)
      }
      if self.bar && adds % 1000 == 0 {
        let time = runtime.as_secs_f64();
        let fraction = 1.0 - adds as f64 / max;
        print!("c {:.2}% [", 100.0 * fraction);
        for f in 1..=20 {
          if fraction * 20.0 < f as f64 {print!(" ")} else {print!("=")}
        }
        print!("] time remaining: {:.2} seconds ", time / fraction - time);
        if step == 0 {println!()}
        stdout().flush()?
      }

      let ad = self.proof[step];
      if ad == ProofStep::NULL {continue}
      let clause = &self.db[ad.clause()];
      if ad.is_del() {
        let size = self.sort_size(ad.clause());
        let clause = &self.db[ad.clause()];
        if self.verb { println!("c adding clause ({}) {}",
          if size.0 {-(size.1 as isize)} else {size.1 as isize}, clause) }
        if let [lit, lit2, ..] = ***clause {
          self.add_watch(ad.clause(), lit);
          self.add_watch(ad.clause(), lit2);
        } else {unreachable!()}
      } else {
        adds -= 1;
        match ***clause {
          [lit, lit2, ..] => {
            self.remove_watch(ad.clause(), lit);
            self.remove_watch(ad.clause(), lit2);
            if *self.reason(lit) == Reason::new(ad.clause()) {
              self.unassign_unit(lit)
            }
          }
          [lit] => self.unassign_unit(lit),
          [] => unreachable!()
        }

        let (sat, size) = self.sort_size(ad.clause());
        let clause = &mut self.db[ad.clause()];
        self.time = clause.ida;
        if !self.time.active() {
          _skipped += 1;
          continue
        }
        assert!(!sat && size >= 1);
        self.num_removed += clause.len() - size;
        clause.truncate(size);

        if self.opts.verb {
          println!("c validating clause ({}, {}):  {}", clause.pivot, size, clause);
        }
        if !self.redundancy_check(ad.clause(), sat, size)? {
          println!("c failed at proof line {} (modulo deletion errors)", step + 1);
          return Ok(VerifyResult::Fail)
        }
        _checked += 1;
        self.opt_proof.push(ad);
      }
    }
    self.postprocess()?;
    Ok(VerifyResult::Unsat)
  }

  fn match_clause(db: &[Clause], clause_list: &mut Vec<usize>, lits: &[i64]) -> Option<usize> {
    let i = clause_list.iter().position(|&c| db[c].lits == lits)?;
    Some(clause_list.swap_remove(i))
  }

  fn deactivate(&mut self) {
    self.num_active = 0;
    for &step in &self.proof {
      self.db[step.clause()].deactivate();
    }
  }

  fn shuffle_proof(&mut self, iteration: usize) {
    use rand::Rng;
    let mut rng = rand::thread_rng();
    let mut base = 100_f64;
    for _ in 1..iteration { base *= 1.1 }
    let mut _step = 0;

    // randomly remove clause deletion steps
    let db = &self.db;
    self.proof.retain(|&step| !step.is_del() ||
      rng.gen_range(0.0..1000.0) >=
        base * iteration as f64 / db[step.clause()].len() as f64);

    for step in (1..self.proof.len()).rev() {
      let a = self.proof[step];
      if a.is_del() {continue}
      let b = self.proof[step - 1];
      if b.is_del() { self.proof.swap(step, step - 1) }
      else if a.clause() != b.clause() {
        // SAFETY: the two elements of the array are non-overlapping
        let c = unsafe { &mut *(&mut self.db[a.clause()] as *mut Clause) };
        let d = &mut self.db[b.clause()];
        let coinflip = false;
        // let coinflip = rng.gen();
        if c.maxdep < d.maxdep || coinflip && c.maxdep < d.ida.0 {
          mem::swap(&mut c.ida, &mut d.ida);
          self.proof.swap(step, step - 1)
        }
      }
    }

    for ad in &self.proof {
      if ad.is_del() {continue}
      let clause = &mut self.db[ad.clause()];
      for i in 0..clause.len()-1 {
        let j = rng.gen_range(i+1..clause.len());
        clause.swap(i, j);
      }
    }
  }

  fn parse(opts: SolverOpts, input_file: File, proof_file: impl BufRead) -> (bool, Self) {
    let mut unsat = false;
    let (num_vars, num_clauses, input_file) =
      dimacs::DimacsIter::from(BufReader::new(input_file).bytes().map(|c| c.unwrap()));
    let mut input_file = input_file.zip(1..);
    let mut formula = Vec::with_capacity(num_clauses);
    println!("c parsing input formula with {} variables and {} clauses", num_vars, num_clauses);
    let mut db = Vec::with_capacity(BIGINIT);
    let mut proof = Vec::with_capacity(BIGINIT);
    let mut hash_table: Vec<Vec<usize>> = std::iter::repeat_with(Vec::new).take(BIGINIT).collect();
    let mut witness = Vec::with_capacity(INIT);
    let mut file_switch_flag = false;
    let mut reader = TrackLen::new(proof_file);
    let mut proof_file = DRATParser::from(opts.bin_mode, (&mut reader).bytes().map(|c| c.unwrap())).zip(1..);
    let mut active = 0;
    let mut max_var = 0;
    let mut count = 1;
    let mut num_lemmas = 0;
    loop {
      if !file_switch_flag { file_switch_flag |= formula.len() >= num_clauses }
      let (line, del, mut lits) = if !file_switch_flag {
        let (clause, line) = if let Some(c) = input_file.next() {c} else {
          opts.warn(|| println!("\
            c WARNING: early EOF of the input formula\n\
            c WARNING: {} clauses less than expected", num_clauses - formula.len()));
          file_switch_flag = true;
          continue
        };
        for &lit in &clause {
          assert!(lit.abs() <= num_vars as i64,
            "illegal literal {} due to max var {}", lit, num_vars);
        }
        (line, false, clause)
      } else {
        let (step, line) = if let Some(res) = proof_file.next() {res} else {break};
        match step {
          DRATStep::Add(lits) => (line, false, lits),
          DRATStep::Del(lits) => (line, true, lits)
        }
      };
      max_var = lits.iter().copied().fold(max_var, i64::max);

      // split line into witness (only for PR)
      let (pivot, wit) = if let Some((&pivot, lits1)) = lits.split_first() {
        (pivot, lits1.iter().position(|&lit| lit == pivot)
          .map(|i| lits.drain(i+1..).collect()))
      } else { (0, None) };
      let wit = Witness::new(wit.map(|w| {let n = witness.len(); witness.push(w); n}));
      lits.sort();
      if lits.len() != {lits.dedup(); lits.len()} {
        opts.warn(|| println!(
          "c WARNING: detected and deleted duplicate literals at line {}", line));
      }
      let size = lits.len();
      if size == 0 && !file_switch_flag { unsat = true }
      if del && matches!(opts.mode, Mode::BackwardUnsat) && size <= 1 {
        opts.warn(|| println!(
          "c WARNING: backward mode ignores deletion of (pseudo) unit clause {}",
          ClauseRef {ida: ClauseId(0), lits: &lits}));
        continue
      }
      let hash = get_hash(&lits);
      if del {
        if opts.delete {
          if let Some(idx) = Self::match_clause(&db, &mut hash_table[hash], &lits) {
            if let Mode::ForwardSat = opts.mode {db[idx].pivot = lits[0]}
            active -= 1;
            proof.push(ProofStep::del(idx));
          } else {
            opts.warn(|| println!(
              "c WARNING: deleted clause on line {} does not occur: {}",
              line, ClauseRef {ida: ClauseId(0), lits: &lits}));
          }
        }
      } else {
        let ida = ClauseId::new(count, matches!(opts.mode, Mode::ForwardSat) && formula.len() < num_clauses);
        count += 1;
        let idx = db.len();
        db.push(Clause {ida, lits, pivot, maxdep: 0, witness: wit});
        hash_table[hash].push(idx);
        active += 1;
        if formula.len() < num_clauses {
          formula.push(ProofStep::add(idx));
        } else {
          proof.push(ProofStep::add(idx));
          num_lemmas += 1;
        }
      }
    }
    if matches!(opts.mode, Mode::ForwardSat) && active != 0 {
      opts.warn(|| println!(
        "c WARNING: {} clauses active if proof succeeds", active));
      for list in hash_table {
        for c in list {
          println!("c {}", db[c]);
          proof.push(ProofStep::del(c))
        }
      }
    } else {
      drop(hash_table);
    }
    db.shrink_to_fit();

    println!("c finished parsing, read {} bytes from proof file", reader.bytes_read());
    let n = max_var as usize;
    (unsat, Self {
      opts,
      count,
      db,
      num_vars,
      num_clauses,
      max_var,
      num_lemmas,
      formula,
      proof,
      witness,
      false_stack: Vec::with_capacity(n + 1),
      reason: vec![Reason::NONE; n + 1].into(),
      false_a: MidVec::with_capacity(max_var),
      opt_proof: Vec::with_capacity(2 * num_lemmas + num_clauses),
      rat_set: Vec::with_capacity(INIT),
      pre_rat: Vec::with_capacity(n),
      lrat_table: std::iter::repeat_with(|| None).take(count + 1).collect(),
      deps: Vec::with_capacity(INIT),
      watch_list: MidVec::with_capacity_by(max_var, || Vec::with_capacity(INIT)),
      unit_stack: Vec::with_capacity(n),
      prep: false,
      num_removed: 0,
      num_active: 0,
      forced: 0,
      processed: 0,
      rat_mode: false,
      rat_count: 0,
      num_resolve: 0,
      time: ClauseId(0),
      current: 0,
    })
  }
}

fn print_help() -> ! {
  println!("usage: drat-trim [INPUT] [<PROOF>] [<option> ...]\n\
    \nwhere <option> is one of the following\n\
    \n  -h          print this command line option summary\
    \n  -c CORE     prints the unsatisfiable core to the file CORE (DIMACS format)\
    \n  -a ACTIVE   prints the active clauses to the file ACTIVE (DIMACS format)\
    \n  -l LEMMAS   prints the core lemmas to the file LEMMAS (DRAT format)\
    \n  -L LEMMAS   prints the core lemmas to the file LEMMAS (LRAT format)\
    \n  -r TRACE    resolution graph in the TRACE file (TRACECHECK format)\n\
    \n  -t <lim>    time limit in seconds (default {})\
    \n  -u          default unit propatation (i.e., no core-first)\
    \n  -f          forward mode for UNSAT\
    \n  -v          more verbose output\
    \n  -b          show progress bar\
    \n  -B          ??? undocumented option backforce\
    \n  -O          optimize proof till fixpoint by repeating verification\
    \n  -C          compress core lemmas (emit binary proof)\
    \n  -D          delete proof file after parsing\
    \n  -i          force binary proof parse mode\
    \n  -u          ??? undocumented option mask\
    \n  -w          suppress warning messages\
    \n  -W          exit after first warning\
    \n  -p          run in plain mode (i.e., ignore deletion information)\n\
    \n  -R          turn off reduce mode\n\
    \n  -S          run in SAT check mode (forward checking)\n\
    \nand input and proof are specified as follows\n\
    \n  INPUT       input file in DIMACS format\
    \n  PROOF       proof file in DRAT format (stdin if no argument)\n",
    TIMEOUT);
  std::process::exit(0);
}

pub fn main(mut args: impl Iterator<Item=String>) -> io::Result<()> {
  let mut opts = SolverOpts::new();
  let mut tmp = 0..;
  // input file in DIMACS format
  let mut input_file: Option<File> = None;
  // proof file in DRAT format (stdin if no argument)
  let stdin = io::stdin();
  let mut proof_file: Either<StdinLock, BufReader<File>> = Either::Left(stdin.lock());
  let mut proof_str = None;
  while let Some(arg) = args.next() {
    if arg.starts_with("-") {
      match &arg[1..] {
        "h" => print_help(),
        "c" => opts.core_str = Some(args.next().expect("expected -c CORE")),
        "a" => opts.active_file = Some(BufWriter::new(File::create(args.next().expect("expected -a ACTIVE"))?)),
        "l" => opts.lemma_str = Some(args.next().expect("expected -l LEMMAS")),
        "L" => opts.lrat_file = Some(BufWriter::new(File::create(args.next().expect("expected -L LEMMAS"))?)),
        "r" => opts.trace_file = Some(BufWriter::new(File::create(args.next().expect("expected -r TRACE"))?)),
        "t" => opts.timeout = args.next().expect("expected -t <lim>").parse().expect("expected a number"),
        "b" => opts.bar = true,
        "B" => opts.backforce = true,
        "O" => opts.optimize = true,
        "C" => opts.bin_output = true,
        "D" => opts.del_proof = true,
        "i" => opts.bin_mode = true,
        "u" => opts.mask = true,
        "v" => opts.verb = true,
        "w" => opts.warning = Warning::NoWarning,
        "W" => opts.warning = Warning::HardWarning,
        "p" => opts.delete = false,
        "R" => opts.reduce = false,
        "f" => opts.mode = Mode::ForwardUnsat,
        "S" => opts.mode = Mode::ForwardSat,
        _ => {}
      }
    } else {
      match tmp.next().unwrap() {
        0 => input_file = Some(File::open(arg)?),
        1 => {
          fn detect_binary(file: &str) -> io::Result<bool> {
            fn nonascii(c: u8) -> bool {
              (c != 13) && (c != 32) && (c != 45) && ((c < 48) || (c > 57)) && (c != 99) && (c != 100)
            }
            let mut file = File::open(file)?.bytes();
            let c = if let Some(c) = file.next() {c?} else {return Ok(true)};
            if nonascii(c) { return Ok(true) }
            let mut comment = c == 99;
            let c = if let Some(c) = file.next() {c?} else {return Ok(true)};
            if nonascii(c) { return Ok(true) }
            comment &= c == 32;
            for c in file.take(10) {
              let c = c?;
              if (c != 100) && (c != 10) && (c != 13) && (c != 32) && (c != 45) &&
                ((c < 48) || (c > 57)) && (comment && ((c < 65) || (c > 122))) {
                return Ok(true)
              }
            }
            Ok(false)
          }
          if !opts.bin_mode && detect_binary(&arg)? {
            println!("c turning on binary mode checking");
            opts.bin_mode = true;
          }
          proof_file = Either::Right(BufReader::new(File::open(&arg)?));
          proof_str = Some(arg);
        }
        _ => {}
      }
    }
  }
  let input_file = input_file.unwrap_or_else(|| print_help());
  if proof_file.is_left() {
    println!("c reading proof from stdin")
  }
  opts.reduce &= opts.lrat_file.is_none() && !matches!(opts.mode, Mode::ForwardUnsat);
  let (mut unsat, mut s) = Solver::parse(opts, input_file, proof_file);
  if let Some(proof) = proof_str.filter(|_| s.del_proof) {
    std::fs::remove_file(&proof)?;
    println!("c deleted proof {}", proof);
  }
  if unsat {
    println!("c trivial UNSAT\ns VERIFIED");
  } else {
    match s.verify(0)? {
      VerifyResult::Unsat => {unsat = true; println!("s VERIFIED")},
      VerifyResult::Derivation => println!("s DERIVATION"),
      VerifyResult::Fail => println!("s NOT VERIFIED"),
    }
  }
  let runtime = Instant::now().saturating_duration_since(s.start_time);
  println!("c verification time: {:.3} seconds", runtime.as_secs_f64());
  if s.optimize {
    println!("c proof optimization started (ignoring the timeout)");
    for iteration in 1..1000 {
      if s.num_removed == 0 {break}
      s.deactivate();
      s.shuffle_proof(iteration);
      s.verify(1)?;
    }
  }
  if !unsat {std::process::exit(1)}
  Ok(())
}
