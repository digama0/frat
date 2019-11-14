#[path="../dimacs.rs"] mod dimacs;
#[path="../parser.rs"] mod parser;

use byteorder::{WriteBytesExt, LittleEndian};
use std::mem;
use std::fmt;
use std::rc::Rc;
use std::convert::{TryInto};
use std::cell::RefCell;
use std::fs::{File, read_to_string};
use std::env;
use std::io::{self, *};
use dimacs::Clause;
use parser::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum StepKind { Add, Del }

pub struct ProofIter<I: Iterator<Item=u8>>(pub I);

impl<I: Iterator<Item=u8>> Iterator for ProofIter<I> {
	type Item = (StepKind, Clause);

	fn next(&mut self) -> Option<Self::Item> {
    const A: u8 = 'a' as u8;
    const D: u8 = 'd' as u8;
    let k = match self.0.next() {
      None => return None,
      Some(A) => StepKind::Add,
      Some(D) => StepKind::Del,
      k => panic!("incorrect step {:?}, is this not a binary file?", k) };
    let mut vec = Vec::new();
    loop {
      match parse_num(&mut self.0).expect("expected literal") {
        0 => return Some((k, Rc::new(vec))),
        lit => vec.push(lit)
      }
    }
  }
}

fn swap_insert<T>(vec: &mut Vec<T>, i: usize, val: T) {
	let val2 = match vec.get_mut(i) {
		None => val,
		Some(p) => mem::replace(p, val)
  };
	vec.push(val2)
}

#[derive(Clone, PartialEq, Eq)]
struct StepToken(Rc<RefCell<(Option<usize>, bool)>>);
impl StepToken {
	fn new() -> StepToken { StepToken(Rc::new(RefCell::new((None, false)))) }
	fn need(&self) { self.0.borrow_mut().1 = true }
	fn needed(&self) -> bool { self.0.borrow().1 }
	fn assign(&self, i: usize) { self.0.borrow_mut().0 = Some(i) }
}
impl fmt::Debug for StepToken {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self.0.borrow().0 {
			None => write!(f, "?"),
			Some(i) => write!(f, "{}", i)
    }
  }
}

enum StepKind2 { Add, Del(usize, Active) }

#[derive(Clone, PartialEq, Eq)]
struct Active {
	step: StepToken,
	cl: Clause,
	hyp: bool
}

pub struct Pass1 {
	steps: Vec<StepKind2>,
	active: Vec<Active>
}

fn is_permutation(cl1: &Clause, cl2: &Clause) -> bool {
	if cl1.len() != cl2.len() { return false }
	for i in cl1.iter() {
		if !cl2.contains(i) { return false }
  }
	true
}

impl Pass1 {
	pub fn new() -> Pass1 {
		Pass1 { steps: Vec::new(), active: Vec::new() }
  }

	pub fn add(&mut self, cl: Clause, hyp: bool) {
		self.steps.push(StepKind2::Add);
		self.active.push(Active {
			step: StepToken::new(), cl, hyp });
  }

	pub fn del(&mut self, cl: Clause) {
		for (i, a) in self.active.iter().enumerate() {
			if is_permutation(&a.cl, &cl) {
				self.steps.push(StepKind2::Del(i, a.clone()));
				self.active.swap_remove(i);
				return
      }
    }
		panic!("could not find clause {:?}", cl)
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Reason {
	Hyp,
 	HR(StepToken, Vec<HRHyp>),
 	RUP(Vec<RUPStep>),
	Sorry
}
use self::Reason::*;

#[derive(Debug, Clone, PartialEq, Eq)]
enum HRHyp { Me, Unit(StepToken) }

#[derive(Debug, Clone, PartialEq, Eq)]
enum RUPStep {
	Hyp(i64),
	UP(StepToken, Clause, i64)
}
impl RUPStep {
	fn _unit(&self) -> i64 {
    match self {
      &RUPStep::Hyp(u) => u,
      &RUPStep::UP(_, _, u) => u
    }
  }
}

struct Pass2 {
	vars: usize,
	active: Vec<Active>,
	steps: Vec<(StepToken, Clause, Reason)>
}

fn var(lit: i64) -> usize { (lit.abs()-1) as usize }
fn _lit(var: usize, val: bool) -> i64 {
	if val {(var + 1) as i64} else {-((var + 1) as i64)}
}

impl Pass2 {
	fn new(vars: usize, mut active: Vec<Active>) -> Pass2 {
		active.last_mut().expect("incomplete proof").step.need();
		Pass2 { vars, active, steps: Vec::new() }
  }

	fn find_hyper_resolution(&mut self, cl: &Clause) -> Option<(StepToken, Vec<HRHyp>)> {
		let mut assign = vec![None; self.vars];
		for a in &self.active {
			if a.cl.len() == 1 {
				assign[var(a.cl[0])] = Some((HRHyp::Unit(a.step.clone()), !(a.cl[0] > 0)))
      }
    }
		for &lit in cl.iter() { assign[var(lit)] = Some((HRHyp::Me, lit > 0)) }
		'cl: for a in self.active.iter().rev() {
			let mut hr = Vec::new();
			for &lit in a.cl.iter() {
				hr.push(match assign[var(lit)] {
					Some((ref s, val)) if val == (lit > 0) => s.clone(),
					_ => continue 'cl
        })
      }
			return Some((a.step.clone(), hr))
    }
		None
  }

	fn find_reverse_unit_propagation(&mut self, cl: &Clause) -> Option<Vec<RUPStep>> {
		let mut assign: Vec<Option<(usize, bool)>> = vec![None; self.vars];
		let mut local_steps: Vec<(RUPStep, bool)> = Vec::new();
		for &lit in cl.iter() {
			assign[var(lit)] = Some((local_steps.len(), lit > 0));
			local_steps.push((RUPStep::Hyp(lit), false));
    }
		let mut process_local = |local_steps: &mut Vec<(RUPStep, bool)>, a: &Active| {
			let mut unit = 0;
			let mut hr = Vec::new();
			for &lit in a.cl.iter() {
				match assign[var(lit)] {
					Some((ref s, val)) if val == (lit > 0) => hr.push(s.clone()),
					_ if unit == 0 => unit = -lit,
					_ => return None
        }
      }
			if unit != 0 {
				let slot = &mut assign[var(unit)];
				if slot.is_some() { return None }
				*slot = Some((local_steps.len(), unit > 0));
      }
			local_steps.push((RUPStep::UP(a.step.clone(), a.cl.clone(), unit), false));
			Some(unit)
    };
		'a: loop {
			let mut progress = false;
			for a in self.active.iter().rev() {
				if a.step.needed() {
					if let Some(i) = process_local(&mut local_steps, &a) {
						if i == 0 { break 'a }
						progress = true
          }
        }
      }
			if progress { continue }
			for a in &self.active {
				if let Some(i) = process_local(&mut local_steps, &a) {
					if i == 0 { break 'a }
					progress = true
        }
      }
			if progress { continue }
			return None
    }
		let mut stack = vec![local_steps.len() - 1];
		while let Some(i) = stack.pop() {
			let r = &mut local_steps[i];
			if !r.1 {
				r.1 = true;
				if let &RUPStep::UP(_, ref cl2, lit) = &r.0 {
					for &lit2 in cl2.iter() {
            if lit2 != lit {
						  stack.push(assign[var(lit2)].unwrap().0)
            }
          }
        }
      }
    }
		Some(local_steps.into_iter()
			.filter_map(|(s, b)| if b { Some(s) } else { None }).collect())
	}

	fn find_reason(&mut self, cl: &Clause) -> Reason {
		if let Some((step, hyps)) = self.find_hyper_resolution(cl) {
			step.need();
			for h in &hyps {
				if let HRHyp::Unit(step) = h { step.need() }
      }
			return HR(step, hyps)
    }

		if let Some(steps) = self.find_reverse_unit_propagation(cl) {
			for s in &steps {
				if let RUPStep::UP(step, _, _) = s { step.need() }
      }
			return RUP(steps)
    }

		Sorry
  }

	fn process_step(&mut self, step: StepKind2) {
		match step {
			StepKind2::Del(i, a) =>
				swap_insert(&mut self.active, i, a),
			StepKind2::Add => {
				let Active {step, cl, hyp} = self.active.pop().unwrap();
				if hyp { self.steps.push((step, cl, Hyp)) }
				else if step.needed() {
					let r = self.find_reason(&cl);
					self.steps.push((step, cl, r))
        }
      }
    }
  }
}

struct Serializer<F: Write>(F, usize);

#[allow(dead_code)]
impl<F: Write> Serializer<F> {
	fn new(f: F) -> Serializer<F> { Serializer(f, 0) }
	fn write_usize(&mut self, i: usize) {
		self.0.write_u64::<LittleEndian>(i as u64).expect("write failed");
		self.1 += 8 }
	fn write_u32(&mut self, i: u32) {
		self.0.write_u32::<LittleEndian>(i).expect("write failed");
		self.1 += 4 }
	fn write_lit(&mut self, i: i64) {
		self.0.write_i64::<LittleEndian>(i.try_into().expect("literal out of range")).expect("write failed");
		self.1 += 4 }
	fn write_clause(&mut self, c: &Clause) {
		for &lit in c.iter() { self.write_lit(lit) }
  }
	fn write_clause0(&mut self, c: &Clause) {
		self.write_clause(c);
    self.write_lit(0)
  }
}

pub fn process_proof<I: Iterator<Item=u8>>(vars: usize, fmla: &Vec<Clause>, drat: ProofIter<I>, frat: bool) {
  let mut pass1 = Pass1::new();
  for cl in fmla { pass1.add(cl.clone(), true) }
  for (k, cl) in drat {
    match k {
      StepKind::Add => pass1.add(cl, false),
      StepKind::Del => pass1.del(cl)
    }
  }

  let Pass1 {steps, active} = pass1;
  let mut pass2 = Pass2::new(vars, active);
  for step in steps.into_iter().rev() {
    pass2.process_step(step)
  }
  for (i, s) in pass2.steps.iter().rev().enumerate() { s.0.assign(i) }

  if frat { // output FRAT binary
    // let mut s = Serializer::new(io::stdout());
    // s.write_usize(fmla.len());
    // s.write_usize(pass2.steps.len());
    // for (_, cl, _) in pass2.steps.iter().rev() {
    // 	for &lit in cl.iter() {
    // 		s.write_usize(pass2.steps.len());
    // 	}
    // }
    // for (step, cl, r) in pass2.steps.iter().rev() {
    // 	for &lit in cl.iter() { print!("{} ", lit) }
    // 	print!("0 ");

    // 	println!("{:?}", (step, cl));
    // }
    unimplemented!()
  } else {
    for (step, cl, r) in pass2.steps.iter().rev() {
      println!("{:?}", (step, cl, r));
    }
  }
}

fn main() -> io::Result<()> {
  let mut args = env::args().skip(1);
	let arg1 = args.next().expect("missing input file");
  let proof = File::open(args.next().expect("missing proof file"))?;
	let (vars, fmla) = dimacs::parse_dimacs(read_to_string(arg1)?.chars());
	let drat = ProofIter(BufReader::new(proof).bytes().map(|r| r.expect("read failed")));
	process_proof(vars, &fmla, drat, match args.next() {
		None => false,
		Some(ref s) if s == "-b" => true,
		_ => panic!("unrecognized option")
	});
	Ok(())
}
