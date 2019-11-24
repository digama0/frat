#[path="../dimacs.rs"] mod dimacs;
#[path="../parser.rs"] mod parser;
#[path="../serialize.rs"] mod serialize;
#[path="../backparser.rs"] pub mod backparser;

// use std::process::exit;
use std::io::{self, Write, BufWriter};
use std::fs::{File, read_to_string};
use std::env;
use std::mem;
use std::hash::{Hash, Hasher};
use std::num::Wrapping;
use std::ops::{Deref, DerefMut, Index, IndexMut};
use dimacs::parse_dimacs;
use backparser::*;
use serialize::Serialize;
use hashbrown::hash_map::{HashMap, Entry};

struct VAssign {
  values: Vec<Option<bool>>
}

fn var(l: i64) -> usize { l.abs() as usize }

impl VAssign {

  fn new() -> VAssign {
    VAssign { values: Vec::new() }
  }

  fn val(&self, l: i64) -> Option<bool> {
    self.values.get(var(l)).unwrap_or(&None).map(|b| (l < 0) ^ b)
  }

  // Attempt to update the variable assignment and make l true under it.
  // If the update is impossible because l is already false under it, return false.
  // Otherwise, update and return true.
  fn set(&mut self, l: i64) -> bool {
    if let Some(v) = self.val(l) { return v }
    let i = var(l);
    if self.values.len() <= i {
      self.values.resize(i + 1, None);
    }
    self.values[i] = Some(0 < l);
    true
  }
}

#[derive(Debug)]
struct Clause {
  marked: bool,
  lits: Vec<i64>
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

#[derive(Default)]
struct Context {
  clauses: HashMap<u64, Clause>,
  units: HashMap<u64, i64>,
  watch: HashMap<i64, HashMap<u64, ()>>,
  step: Option<u64>
}

impl Context {

  fn new() -> Context { Default::default() }

  fn marked(&self, i: u64) -> bool {
    self.clauses[&i].marked
  }

  fn mark(&mut self, i: u64) {
    self.clauses.get_mut(&i).unwrap().marked = true;
  }

  fn del_watch(&mut self, l: i64, i: u64) {
    // eprintln!("remove watch: {:?} for {:?}", l, i);

    assert!(self.watch.get_mut(&l).unwrap().remove(&i).is_some(),
      "Literal {} not watched in clause {:?}", l, i);
  }

  fn add_watch(&mut self, l: i64, id: u64) {
    assert!(self.watch.entry(l).or_insert_with(HashMap::new).insert(id, ()).is_none(),
      "Clause already watched");
  }

  fn insert(&mut self, i: u64, marked: bool, lits: Vec<i64>) {
    let c = Clause {marked, lits};
    match c.len() {
      0 => {}
      1 => { self.units.insert(i, c[0]); }
      _ => {
        self.add_watch(c[0], i);
        self.add_watch(c[1], i);
      }
    }

    assert!(self.clauses.insert(i, c).is_none(),
      "at {:?}: Clause {} to be inserted already exists", self.step, i);
  }

  fn remove(&mut self, i: u64) -> Clause {

    let c: Clause = self.clauses.remove(&i).unwrap_or_else(
      || panic!("at {:?}: Clause {} to be removed does not exist", self.step, i));

    match c.len() {
      0 => {}
      1 => { self.units.remove(&i); }
      _ => {
        self.del_watch(c[0], i);
        self.del_watch(c[1], i);
      }
    }

    c
  }

  fn reloc(&mut self, relocs: &mut Vec<(u64, u64)>) {
    let mut m = HashMap::new();
    let mut removed = Vec::new();
    relocs.retain(|&(from, to)| {
      if let Some(c) = self.clauses.remove(&to) {
        m.insert(from, to);
        removed.push((from, c));
        true
      } else {false}
    });
    for (from, c) in removed {
      assert!(self.clauses.insert(from, c).is_none(),
        "at {:?}: Clause {} to be inserted already exists", self.step, from);
    }
    for (_, ws) in self.watch.iter_mut() {
      for (n, _) in mem::replace(ws, HashMap::new()) {
        ws.insert(m.get(&n).cloned().unwrap_or(n), ());
      }
    }
  }

  fn get(&self, i: u64) -> &Clause {
    self.clauses.get(&i).unwrap_or_else(
      || panic!("at {:?}: Clause {} to be accessed does not exist", self.step, i))
  }

  fn watch_first(&mut self, i: u64, va: &VAssign) -> bool {

    let c = self.clauses.get_mut(&i).unwrap();
    let l = c[0];

    if va.val(l).is_none() { return true }
    if let Some(j) = find_new_watch(c, va) {
      // eprintln!("Working on clause {}: {:?} at {}", i, c, j);
      let k = c[j];
      c[0] = k;
      c[j] = l;
      self.del_watch(l, i);
      self.add_watch(k, i);
      true
    } else {false}
  }

  fn watch_second(&mut self, i: u64, va: &VAssign) -> bool {

    let c = self.clauses.get_mut(&i).unwrap();
    let l = c[1];

    if va.val(l).is_none() { return true }
    if let Some(j) = find_new_watch(c, va) {
      // eprintln!("Working on clause {} second: {:?} at {}", i, c, j);
      let k = c[j];
      c[1] = k;
      c[j] = l;
      self.del_watch(l, i);
      self.add_watch(k, i);
      true
    } else {false}
  }

  // va is the current variable assignment, and i is the ID of a clause
  // which may potentially be unit under va. If c is verified under va,
  // do nothing and return None. If c is not verified but contains two
  // or more undecided literals, watch them and return none. Otherwise,
  // return Some(k), where k is a new unit literal.
  fn propagate(&mut self, i: u64, va: &VAssign) -> Option<i64> {
    if self.get(i).iter().any(|&l| va.val(l) == Some(true)) {return None}
    if !self.watch_first(i, va) {return Some(self.get(i)[1])}
    if !self.watch_second(i, va) {return Some(self.get(i)[0])}
    None
  }
}

#[derive(Debug, Default)]
struct Hint {
  reasons: HashMap<i64, Option<usize>>,
  steps: Vec<u64>
}

impl Hint {
  fn new() -> Hint { Default::default() }

  fn add(&mut self, l: i64, rs: Option<u64>) {
    match rs {
      None => {
        self.reasons.insert(l, None);
      },
      Some(id) => {
        self.reasons.insert(l, Some(self.steps.len()));
        self.steps.push(id);
      }
    }
  }

  fn minimize(&mut self, ctx: &Context) {
    let mut need = vec![false; self.steps.len()];
    match need.last_mut() {
      None => panic!("Failed, found a hint with {:?} reasons, {:?} steps", self.reasons.len(), self.steps.len()),
      Some(last_step) => *last_step = true 
    } 
    for (i, &s) in self.steps.iter().enumerate().rev() {
      if need[i] {
        for l in ctx.get(s) {
          if let Some(&Some(j)) = self.reasons.get(&-l) {need[j] = true}
        }
      }
    }
    self.steps.retain({ let mut i = 0; move |_| (need[i], i += 1).0 });
  }
}

// Propagate literal l. Returns false if a contradiction has been found
fn propagate_one(l: i64, ls: &mut Vec<i64>, ctx: &mut Context, va: &mut VAssign, ht: &mut Hint) -> bool {

  // If l is not watched at all, no new information can be obtained by propagating l
  if let Some(is) = ctx.watch.get(&-l) {
    // 'is' is the (reference to) IDs of all clauses containing -l
    let js: Vec<u64> = is.keys().cloned().collect();
    for j in js {
      if let Some(k) = ctx.propagate(j, va) {
        ls.push(k);
        ht.add(k, Some(j));
        if !va.set(k) { return false }
      }
    }
  }
  true
}

fn propagate(c: &Vec<i64>, ctx: &mut Context) -> Hint {

  let mut ls: Vec<i64> = Vec::new();
  let mut va = VAssign::new();
  let mut ht = Hint::new();

  for l in c {
    ls.push(-l);
    ht.add(-l, None);
    if !va.set(-l) { return ht }
  }

  for (&i, &l) in &ctx.units {
    ls.push(l);
    ht.add(l, Some(i));
    if !va.set(l) { return ht }
  }

  // Main unit propagation loop

  // ctr is the counter which keeps track of the literals of uls that
  // has already been used for unit propagtion. It always points to the
  // next fresh literal to be propagated (a simpler iteration over ls 
  // doesn't work here because ls itself is growing).
  let mut ctr: usize = 0;
  // Main unit propagation loop
  'prop: loop {
    // If there are no more literals to propagate, unit propagation has failed
    if ls.len() <= ctr { propagate_stuck(ctx, &ht, &ls, c)
      .expect("Failed to write unit propagation error log"); }
    if !propagate_one(ls[ctr], &mut ls, ctx, &mut va, &mut ht) { return ht; }
    ctr += 1;
    continue 'prop;
  }
}

fn propagate_stuck(ctx: &Context, ht: &Hint, ls: &Vec<i64>, c: &Vec<i64>) -> io::Result<()> {
  // If unit propagation is stuck, write an error log
  let mut log = File::create("unit_prop_error_log").unwrap();
  writeln!(log, "Clauses available at failure :\n")?;
  for ac in &ctx.clauses {
    writeln!(log, "{:?} : {:?}", ac.0, ac.1.lits)?;
  }
  writeln!(log, "\nDiscovered reasons at failure : {:?}", ht.reasons)?;
  writeln!(log, "\nRecorded steps at failure : {:?}", ht.steps)?;
  writeln!(log, "\nObtained unit literals at failure : {:?}", ls)?;
  writeln!(log, "\nFailed to add clause : {:?}", c)?;
  panic!("Unit propagation stuck, cannot add clause {:?}", c);
}

fn propagate_hint(ls: &Vec<i64>, ctx: &Context, is: &Vec<u64>) -> Option<Hint> {
  let mut ht: Hint = Hint { reasons: ls.iter().map(|&x| (-x, None)).collect(), steps: vec![] };

  let mut first = 0;
  loop {
    let mut progress = false;
    'a: for i in first..is.len() {
      let c = is[i];
      let mut uf: Option<i64> = None;
      for l in ctx.get(c) {
        if !ht.reasons.contains_key(&-l) {
          if uf.replace(l).is_some() {
            // eprintln!("bad hint {}: clause {:?} is not unit", step, c);
            continue 'a
          }
        }
      }
      match uf {
        None => {
          ht.steps.push(c);
          return Some(ht)
        },
        Some(l) => if let Entry::Vacant(v) = ht.reasons.entry(l) {
          v.insert(Some(ht.steps.len()));
          ht.steps.push(c);
        }
      }
      progress = true;
      if first == i { first += 1 }
    }
    assert!(progress,
      "at {:?}: unit propagation failed to find conflict", ctx.step)
  }
}

fn undelete<W: Write>(is: &Vec<u64>, ctx: &mut Context, w: &mut W) {
  for &i in is {
    // let v = cs.get_mut(&i).unwrap();
    if !ctx.marked(i) { // If the necessary clause is not active yet
      ctx.mark(i); // Make it active
      ElabStep::Del(i).write(w).expect("Failed to write delete step");
    }
  }
}

fn elab<M: Mode>(frat: File, temp: File) -> io::Result<()> {
  let w = &mut BufWriter::new(temp);
  let mut bp = StepParser::<M>::new(frat)?;
  let mut ctx: Context = Context::new();

  while let Some(s) = bp.next() {
    // eprintln!("<- {:?}", s);
    match s {

      Step::Orig(i, ls) => {
        ctx.step = Some(i);
        if ctx.marked(i) {  // If the original clause is marked
          ElabStep::Orig(i, ls).write(w).expect("Failed to write orig step");
        }
        ctx.remove(i);
      }

      Step::Add(i, ls, p) => {
        ctx.step = Some(i);
        let c = ctx.remove(i);
        if c.marked {
          let mut ht: Hint = match p {
            Some(Proof::LRAT(is)) => propagate_hint(&ls, &ctx, &is),
            _ => None
          }.unwrap_or_else(|| propagate(&ls, &mut ctx));
          ht.minimize(&ctx);
          undelete(&ht.steps, &mut ctx, w);
          ElabStep::Add(i, ls, ht.steps).write(w).expect("Failed to write add step");
        }
      }

      Step::Reloc(mut relocs) => {
        ctx.step = None;
        ctx.reloc(&mut relocs);
        if !relocs.is_empty() {
          ElabStep::Reloc(relocs).write(w).expect("Failed to write reloc step");
        }
      }

      Step::Del(i, ls) => ctx.insert(i, false, ls),

      Step::Final(i, ls) => {
        // Identical to the Del case, except that the clause should be marked if empty
        ctx.insert(i, ls.is_empty(), ls);
      }

      Step::Todo(_) => ()
    }
  }

  Ok(())
}

fn find_new_watch(c: &Clause, va: &VAssign) -> Option<usize> {
  c.iter().skip(2).position(|x| va.val(*x).is_none()).map(|u| u+2)
}

#[derive(Copy, Clone)]
struct PermClause<'a>(&'a Vec<i64>);

impl<'a> Hash for PermClause<'a> {
  fn hash<H: Hasher>(&self, h: &mut H) {
    // Permutation-stable hash function from drat-trim.c
    let (mut sum, mut prod, mut xor) = (Wrapping(0u64), Wrapping(1u64), Wrapping(0u64));
    for &i in self.0 { let i = Wrapping(i as u64); prod *= i; sum += i; xor ^= i; }
    (Wrapping(1023) * sum + prod ^ (Wrapping(31) * xor)).hash(h)
  }
}

impl<'a> PartialEq for PermClause<'a> {
  fn eq(&self, other: &Self) -> bool { is_perm(&self.0, &other.0) }
}
impl<'a> Eq for PermClause<'a> {}

fn trim<W: Write>(cnf: Vec<Vec<i64>>, temp: File, lrat: &mut W) -> io::Result<()> {

  let mut k = 0 as u64; // Counter for the last used ID
  let cnf: HashMap<PermClause, u64> = // original CNF
    cnf.iter().map(|c| (PermClause(c), (k += 1, k).1)).collect();
  let mut m: HashMap<u64, u64> = HashMap::new(); // Mapping between old and new IDs
  let mut bp = ElabStepParser::<Bin>::new(temp)?.peekable();

  loop {
    let s = bp.next().expect("did not find empty clause");
    // eprintln!("-> {:?}", s);

    match s {

      ElabStep::Orig(i, ls) => {
        let j = *cnf.get(&PermClause(&ls)).unwrap_or_else( // Find position of clause in original problem
          || panic!("Orig step {} refers to nonexistent clause {:?}", i, ls));
        assert!(m.insert(i, j).is_none(), "Multiple orig steps with duplicate IDs");
        // eprintln!("{} -> {}", i, j);
        if ls.is_empty() {
          write!(lrat, "{} 0 {} 0\n", k+1, j)?;
          return Ok(())
        }
      }

      ElabStep::Add(i, ls, is) => {
        k += 1; // Get the next fresh ID
        m.insert(i, k); // The ID of added clause is mapped to a fresh ID
        // eprintln!("{} -> {}", i, k);
        let b = ls.is_empty();

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
      }
    }
  }
}

fn is_perm(v: &Vec<i64>, w: &Vec<i64>) -> bool {
  v.len() == w.len() && v.iter().all(|i| w.contains(i))
}

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
    trim(cnf, temp_read, &mut BufWriter::new(File::create(p)?))?;
  } else {
    trim(cnf, temp_read, &mut io::sink())?;
  }

  Ok(())
}
