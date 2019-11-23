#[path="../dimacs.rs"] mod dimacs;
#[path="../parser.rs"] mod parser;
#[path="../serialize.rs"] mod serialize;
#[path="../backparser.rs"] pub mod backparser;

// use std::process::exit;
use std::io::{self, Write, BufWriter};
use std::fs::{File, read_to_string};
use std::env;
use std::convert::TryFrom;
use dimacs::parse_dimacs;
use backparser::*;
use serialize::Serialize;
use hashbrown::hash_map::{HashMap, Entry};

fn lit_size(l: i64) -> usize {
  usize::try_from(l.abs()).unwrap()
}

// Propagate literal l. Returns false if a contradiction has been found
fn propagate_one(l: i64, ctx: &mut Context, va: &mut Vassign, ht: &mut Hint) -> bool {

  match ctx.watch.get(&-l) { 
    // If l is not watched at all, no new information can be obtained by propagating l
    None => true, 
    // 'is' is the (reference to) IDs of all clauses containing -l
    Some(is) => {
      let js: Vec<u64> = is.keys().map(|x| x.clone()).collect();
      for j in js {
        if let Some(k) = ctx.propagate(j, va) {
          ht.add(k, Some(j));
          if !va.set(k) {
            return false;
          }
        }
      }
      true
    }
  } 
}

fn propagate(c: &Vec<i64>, ctx: &mut Context) -> Hint {

  // ls is the list of obtained unit literals 
  let mut ls: Vec<i64> = Vec::new();
  let mut va = Vassign::new();
  let mut ht = Hint::new();

  for l in c {
    ls.push(-l);
    ht.add(-l, None); 
    if !va.set(-l) {
      return ht;
    }
  }

  for i in ctx.units.keys() {
    let l = ctx.get(*i)[0];
    ls.push(l);
    ht.add(l, Some(*i)); 
    if !va.set(l) {
      return ht;
    }
  }

  // ctr is the counter which keeps track of the literals of uls that 
  // has already been used for unit propagtion. It always points to the 
  // next fresh literal to be propagated.
  let mut ctr: usize = 0;

  // Main unit propagation loop
  'prop: loop {

    // If there are no more literals to propagate, unit propagation has failed
    if ls.len() <= ctr { panic!("Unit propagation stuck"); }

    if propagate_one(ls[ctr], ctx, &mut va, &mut ht) { 
      return ht;
      // let map: HashMap<i64, Option<usize>> = uls.iter().map(|x| x.clone()).collect(); 
      // return (map, sts);
    }

    ctr += 1;
    continue 'prop;
  }
}


fn propagate_hint(step: u64, ls: &Vec<i64>, ctx: &Context, is: &Vec<u64>) -> Option<Hint> {

  let mut ht: Hint = Hint::new(); 

  for l in ls {
    ht.add(-l, None);
  }

  for &c in is {
    let mut uf: Option<i64> = None;
    for &l in ctx.get(c) {
      if !ht.reasons.contains_key(&-l) {
        assert!(uf.replace(l).is_none(),
          "bad hint {}: clause {:?} is not unit", step, c);
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
  }
  panic!("bad hint {}: unit propagation failed to find conflict", step)
}

fn propagate_minimize(ctx: &Context, ht: &mut Hint) {
  let mut need = vec![false; ht.steps.len()];
  *need.last_mut().unwrap() = true;
  for (i, s) in ht.steps.iter().enumerate().rev() {
    if need[i] {
      for l in ctx.get(*s) {
        if let Some(&Some(j)) = ht.reasons.get(&-l) {need[j] = true}
      }
    }
  }
  let mut i = 0;
  ht.steps.retain(|_| (need[i], i += 1).0);
}

fn undelete<W: Write>(is: &Vec<u64>, ctx: &mut Context, w: &mut W) {
  for &i in is {
    // let v = cs.get_mut(&i).unwrap();
    if !ctx.marked(i) { // If the necessary clause is not active yet
      ctx.mark(i, true); // Make it active
      ElabStep::Del(i).write(w).expect("Failed to write delete step");
    }
  }
}

struct Hint {
  reasons: HashMap<i64, Option<usize>>, 
  steps: Vec<u64>
}

impl Hint { 
  fn new() -> Hint {
    Hint { 
      reasons: HashMap::new() ,
      steps: Vec::new()
    }
  }

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
}

struct Vassign {
  values: Vec<Option<bool>>
}

impl Vassign {

  fn new() -> Vassign {
    Vassign { values: Vec::new() }
  }

  fn holds(&self, l: i64) -> Option<bool> {
    *self.values.get(lit_size(l)).unwrap_or(&None)
  }

  // Attempt to update the variable assignment and make l true under it. 
  // If the update is impossible because l is already false under it, return false.
  // Otherwise, update and return true.
  fn set(&mut self, l : i64) -> bool {
    if self.holds(l) == Some(false) {
      return false;
    } else {
      let i = lit_size(l);
      if self.values.len() <= i {
        self.values.resize(i + 1, None);
      }
      self.values[i] = Some(0 < l);
      true
    }
  }
}

struct Context {
  marks: HashMap<u64, bool>,
  clauses: HashMap<u64, Clause>, 
  units: HashMap<u64, ()>,
  watch: HashMap<i64, HashMap<u64, ()>>
}

impl Context {

  fn new() -> Context {
    Context { 
      marks: HashMap::new(), 
      clauses: HashMap::new(), 
      units: HashMap::new(), 
      watch: HashMap::new() 
    }
  }

  fn marked(&self, i: u64) -> bool {
    self.marks[&i]
  }

  fn mark(&mut self, i: u64, m: bool) {
    assert!(self.marks.insert(i, m).is_some(), "Cannot mark a nonexistent clause");
  }

  fn del_watch(&mut self, l: i64, i: u64) {
      assert!(self.watch.get_mut(&l).unwrap().remove(&i).is_some(), "Clause not watched");
  }

  fn add_watch(&mut self, l: i64, id: u64) {

        eprintln!("The ID : {:?}", id);
        eprintln!("The literal : {:?}", l);

    if self.watch.contains_key(&l) {
      if !self.watch.get_mut(&l).unwrap().insert(id, ()).is_none() {
        eprintln!("The clause : {:?}", self.get(id));
        eprintln!("Watch bucket : {:?}", self.watch.get(&l));
        panic!("Clause already watched");
      }
    } else {
      let mut nw: HashMap<u64, ()> = HashMap::new(); 
      nw.insert(id, ());
      self.watch.insert(l, nw);
    }
  }

  fn insert(&mut self, i: u64, m: bool, c: Clause) {
     
    assert!(self.marks.insert(i, m).is_none(), "Clause to be inserted already exists");

    match c.len()  {
      0 => (),
      1 => assert!(self.units.insert(i, ()).is_none(), "Clause to be inserted already exists"),
      _ => {
        self.add_watch(c[0], i);
        self.add_watch(c[1], i);
      }
    }

    assert!(self.clauses.insert(i, c).is_none(), "Clause to be inserted already exists"); 
  }

  fn remove(&mut self, i: u64) -> (bool, Clause) {

    let m: bool = self.marks.remove(&i).expect("Clause to be removed does not exist");
    let c: Clause = self.clauses.remove(&i).expect("Clause to be removed does not exist");

    match c.len()  {
      0 => (),
      1 => assert!(self.units.remove(&i).is_some(), "Clause to be removed does not exist"),
      _ => {
        self.del_watch(c[0], i);
        self.del_watch(c[1], i);
      }
    };

    (m, c)
  }

  fn get(&self, i: u64) -> &Clause {
    self.clauses.get(&i).expect("Clause to be accessed does not exist")
  }

  fn watch_first(&mut self, i: u64, va: &Vassign) -> bool {

    let c = self.clauses.get_mut(&i).unwrap();
    let l = c[0];

    if va.holds(l) == None {
      true
    } else { 
      match c.iter().skip(2).position(|x| va.holds(*x) == None) {
        None => false,
        Some(j) => { 
          eprintln!("Working on clause : {:?}", c);
          let k = c[j];
          c[1] = k;
          c[j] = l; 
          self.del_watch(l, i);
          self.add_watch(k, i);
          true
        }
      }
    }
  }

  fn watch_second(&mut self, i: u64, va: &Vassign) -> bool {

    let c = self.clauses.get_mut(&i).unwrap();
    let l = c[1];

    if va.holds(l) == None {
      true
    } else { 
      match c.iter().skip(2).position(|x| va.holds(*x) == None) {
        None => false,
        Some(j) => { 
          let k = c[j];
          c[1] = k;
          c[j] = l; 
          self.del_watch(l, i);
          self.add_watch(k, i);
          true
        }
      }
    }
  }

  // va is the current variable assignment, and i is the ID of a clause,
  // which may potentially be unit under va. If c is verified under va, 
  // do nothing and return None. If c is not verified but contains two 
  // or more undecided literals, watch them and return none. Otherwise, 
  // return Some(k), where k is a new unit literal.
  fn propagate(&mut self, i: u64, va: &Vassign) -> Option<i64> {
    if self.get(i).iter().any(|x| va.holds(*x) == Some(true)) {
      None
    } else {
      if self.watch_first(i, va) {
        if self.watch_second(i, va) {
          None
        }
        else {
          Some(self.get(i)[0])
        }
      } else {
        Some(self.get(i)[1])
      }
    }
  }
}

fn elab<M: Mode>(frat: File, temp: File) -> io::Result<()> {
  let w = &mut BufWriter::new(temp);
  let mut bp = StepParser::<M>::new(frat)?;
  let mut ctx: Context = Context::new();

  while let Some(s) = bp.next() {
    // eprintln!("{:?}", s);
    match s {

      Step::Orig(i, ls) => {
        if ctx.marked(i) {  // If the original clause is marked
          ElabStep::Orig(i, ls).write(w).expect("Failed to write orig step");
        }
        ctx.remove(i);
      }

      Step::Add(i, ls, p) => {
        if ctx.marked(i) {
          let mut ht: Hint = match p {
            Some(Proof::LRAT(is)) => propagate_hint(i, &ls, &ctx, &is),
            _ => None
          }.unwrap_or_else(|| propagate(&ls, &mut ctx));
          propagate_minimize(&ctx, &mut ht);
          undelete(&ht.steps, &mut ctx, w);
          ElabStep::Add(i, ls, ht.steps).write(w).expect("Failed to write add step");
        }
      }

      Step::Reloc(from, to) => {
        let (m, c) = ctx.remove(to);
        ctx.insert(from, m, c);
      }

      Step::Del(i, ls) => { ctx.insert(i, false, ls); }

      Step::Final(i, ls) => {
        // Identical to the Del case, except that the clause should be marked if empty
        ctx.insert(i, ls.is_empty(), ls);
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
        let j = cnf.iter().position(|x| is_perm(x, &ls)) // Find position of clause in original problem
          .expect("Orig step refers to nonexistent clause") as u64 + 1;
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

        write!(lrat, "{}", k)?;
        for x in ls { write!(lrat, " {}", x)? }
        write!(lrat, " 0")?;
        for x in is { write!(lrat, " {}", m[&x])? }
        write!(lrat, " 0\n")?;

        if b {return Ok(())}
      }

      ElabStep::Reloc(from, to) => if let Some(s) = m.remove(&from) { m.insert(to, s); },

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
    trim_bin(cnf, temp_read, &mut BufWriter::new(File::create(p)?))?;
  } else {
    trim_bin(cnf, temp_read, &mut io::sink())?;
  }

  Ok(())
}
