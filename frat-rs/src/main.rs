use std::mem;
use std::env;
use std::fmt;
use std::fs::{read_to_string, File};
use std::rc::Rc;
use std::cell::RefCell;
use std::io::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Token {
	Nat(i64),
	Zero,
	Ident(Ident) }

use self::Token::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Ident { Comment, Problem, Cnf }

use self::Ident::*;

#[derive(Debug, Clone)]
struct Lexer<I> where I: Iterator<Item=char> {
	/// input iterator
	input : I,

	/// internal buffer to map to known keywords
	buffer: String,

	/// the current character that is being dispatched upon
	peek  : char }

impl<I> Lexer<I> where I: Iterator<Item=char> {
	fn from(input: I) -> Lexer<I> {
		let mut lex = Lexer {
			input : input,
			buffer: String::new(),
			peek  : '\0' };
		lex.bump();
		lex }

	fn bump_opt(&mut self) -> Option<char> {
		if let Some(peeked) = self.input.next() {
			self.peek = peeked;
			Some(peeked) }
		else { None } }

	fn bump(&mut self) -> char {
		self.peek = self.bump_opt().unwrap_or('\0');
		self.peek }

	fn skip_line(&mut self) {
		while self.peek != '\n' && self.peek != '\0' {
			self.bump(); } }

	fn scan_comment(&mut self) -> Ident {
		self.skip_line();
		Comment }

	fn scan_keyword(&mut self) -> Ident {
		self.buffer.clear();
		self.buffer.push(self.peek);
		while self.bump().is_alphanumeric() {
			if self.buffer.len() < 3 {
				self.buffer.push(self.peek); }
			else { panic!("unknown keyword") } }
		match self.buffer.as_str() {
			"c"     => self.scan_comment(),
			"p"     => Problem,
			"cnf"   => Cnf,
			_       => panic!("unknown keyword") } }

	fn scan_nat(&mut self) -> i64 {
		let mut val = self.peek.to_digit(10)
			.expect("expected a digit to base 10: (0...9)") as i64;
		while let Some(parsed) = self.bump().to_digit(10) {
			val *= 10;
			val += parsed as i64; }
		val }
}

impl<I> Iterator for Lexer<I> where I: Iterator<Item=char> {
	type Item = Token;

	fn next(&mut self) -> Option<Self::Item> {
		while self.peek.is_whitespace() {
			self.bump(); }
		if self.peek == '\0' { return None; }
		match self.peek {
      'a'..='z' => match self.scan_keyword() {
        Comment => self.next(),
        tk => Some(Ident(tk)) },
      '1'..='9' => Some(Nat(self.scan_nat())),

      '0' => { self.bump(); Some(Zero) },
      '-' => { self.bump(); Some(Nat(-self.scan_nat())) },
      _ => panic!("invalid token start") } }
}

type Clause = Rc<Vec<i64>>;
fn parse_dimacs<I: Iterator<Item=char>>(input: I) -> (usize, Vec<Clause>) {
  let mut lex = Lexer::from(input);
  match (lex.next(), lex.next(), lex.next(), lex.next()) {
    (Some(Ident(Problem)), Some(Ident(Cnf)), Some(Nat(vars)), Some(Nat(clauses))) => {
      let mut fmla = Vec::with_capacity(clauses as usize);
      loop {
        let mut clause = Vec::new();
        loop { match lex.next() {
          Some(Nat(lit)) => clause.push(lit),
          Some(Zero) => break,
          None => return (vars as usize, fmla),
          _ => panic!("parse DIMACS failed") } }
        fmla.push(Rc::new(clause)); } },
    _ => panic!("parse DIMACS failed") } }

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum StepKind { Add, Del }

struct ProofIter<I: Iterator<Item=u8>>(I);

impl<I: Iterator<Item=u8>> ProofIter<I> {
  fn parse_num(&mut self) -> Option<i64> {
    let mut ulit: u64 = 0;
    let mut mul: u8 = 0;
    loop { match self.0.next() {
      None => return None,
      Some(c) => {
        ulit |= ((c & 0x7F) as u64) << mul;
        mul += 7;
        if c & 0x80 == 0 {
          return Some(
            if ulit & 1 != 0 { -((ulit >> 1) as i64) }
            else { (ulit >> 1) as i64 }) } } } } }
}

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
    loop { match self.parse_num().expect("expected literal") {
      0 => return Some((k, Rc::new(vec))),
      lit => vec.push(lit) } } }
}

fn swap_insert<T>(vec: &mut Vec<T>, i: usize, val: T) {
	let val2 = mem::replace(&mut vec[i], val);
	vec.push(val2) }

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
			Some(i) => write!(f, "{}", i) } }
}

enum StepKind2 { Add, Del(usize, Active) }

#[derive(Clone, PartialEq, Eq)]
struct Active {
	step: StepToken,
	cl: Clause,
	hyp: bool }

struct Pass1 {
	steps: Vec<StepKind2>,
	active: Vec<Active> }

fn is_permutation(cl1: &Clause, cl2: &Clause) -> bool {
	if cl1.len() != cl2.len() { return false }
	for i in cl1.iter() {
		if !cl2.contains(i) { return false } }
	true }

impl Pass1 {
	fn new() -> Pass1 {
		Pass1 { steps: Vec::new(), active: Vec::new() } }

	fn add(&mut self, cl: Clause, hyp: bool) {
		self.steps.push(StepKind2::Add);
		self.active.push(Active {
			step: StepToken::new(), cl, hyp }); }

	fn del(&mut self, cl: Clause) {
		for (i, a) in self.active.iter().enumerate() {
			if is_permutation(&a.cl, &cl) {
				self.steps.push(StepKind2::Del(i, a.clone()));
				self.active.swap_remove(i);
				return } }
		panic!("could not find clause {:?}", cl) }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Reason {
	Hyp,
 	HR(StepToken, Vec<HRHyp>),
 	RUP(Vec<RUPStep>),
	Sorry }
use self::Reason::*;

#[derive(Debug, Clone, PartialEq, Eq)]
enum HRHyp { Me, Unit(StepToken) }

#[derive(Debug, Clone, PartialEq, Eq)]
enum RUPStep {
	Hyp(i64),
	UP(StepToken, Clause, i64) }
impl RUPStep {
	fn _unit(&self) -> i64 { match self {
		&RUPStep::Hyp(u) => u,
		&RUPStep::UP(_, _, u) => u } }
}

struct Pass2 {
	vars: usize,
	active: Vec<Active>,
	steps: Vec<(StepToken, Clause, Reason)> }

fn var(lit: i64) -> usize { (lit.abs()-1) as usize }
fn _lit(var: usize, val: bool) -> i64 {
	if val {(var + 1) as i64} else {-((var + 1) as i64)} }

impl Pass2 {
	fn new(vars: usize, mut active: Vec<Active>) -> Pass2 {
		active.last_mut().expect("incomplete proof").step.need();
		Pass2 { vars, active, steps: Vec::new() } }

	fn find_hyper_resolution(&mut self, cl: &Clause) -> Option<(StepToken, Vec<HRHyp>)> {
		let mut assign = vec![None; self.vars];
		for a in &self.active {
			if a.cl.len() == 1 {
				assign[var(a.cl[0])] = Some((HRHyp::Unit(a.step.clone()), !(a.cl[0] > 0))) } }
		for &lit in cl.iter() { assign[var(lit)] = Some((HRHyp::Me, lit > 0)) }
		'cl: for a in self.active.iter().rev() {
			let mut hr = Vec::new();
			for &lit in a.cl.iter() {
				hr.push(match assign[var(lit)] {
					Some((ref s, val)) if val == (lit > 0) => s.clone(),
					_ => continue 'cl }) }
			return Some((a.step.clone(), hr)) }
		None }

	fn find_reverse_unit_propagation(&mut self, cl: &Clause) -> Option<Vec<RUPStep>> {
		let mut assign: Vec<Option<(usize, bool)>> = vec![None; self.vars];
		let mut local_steps: Vec<(RUPStep, bool)> = Vec::new();
		for &lit in cl.iter() {
			assign[var(lit)] = Some((local_steps.len(), lit > 0));
			local_steps.push((RUPStep::Hyp(lit), false)); }
		let mut process_local = |local_steps: &mut Vec<(RUPStep, bool)>, a: &Active| {
			let mut unit = 0;
			let mut hr = Vec::new();
			for &lit in a.cl.iter() {
				match assign[var(lit)] {
					Some((ref s, val)) if val == (lit > 0) => hr.push(s.clone()),
					_ if unit == 0 => unit = -lit,
					_ => return None } }
			if unit != 0 {
				let slot = &mut assign[var(unit)];
				if slot.is_some() { return None }
				*slot = Some((local_steps.len(), unit > 0)); }
			local_steps.push((RUPStep::UP(a.step.clone(), a.cl.clone(), unit), false));
			Some(unit) };
		'a: loop {
			let mut progress = false;
			for a in self.active.iter().rev() {
				if a.step.needed() {
					if let Some(i) = process_local(&mut local_steps, &a) {
						if i == 0 { break 'a }
						progress = true } } }
			if progress { continue }
			for a in &self.active {
				if let Some(i) = process_local(&mut local_steps, &a) {
					if i == 0 { break 'a }
					progress = true } }
			if progress { continue }
			return None }
		let mut stack = vec![local_steps.len() - 1];
		while let Some(i) = stack.pop() {
			let r = &mut local_steps[i];
			if !r.1 {
				r.1 = true;
				if let &RUPStep::UP(_, ref cl2, lit) = &r.0 {
					for &lit2 in cl2.iter() { if lit2 != lit {
						stack.push(assign[var(lit2)].unwrap().0) } } } } }
		Some(local_steps.into_iter()
			.filter_map(|(s, b)| if b { Some(s) } else { None }).collect())
	}

	fn find_reason(&mut self, cl: &Clause) -> Reason {
		if let Some((step, hyps)) = self.find_hyper_resolution(cl) {
			step.need();
			for h in &hyps {
				if let HRHyp::Unit(step) = h { step.need() } }
			return HR(step, hyps) }

		if let Some(steps) = self.find_reverse_unit_propagation(cl) {
			for s in &steps {
				if let RUPStep::UP(step, _, _) = s { step.need() } }
			return RUP(steps) }

		Sorry }

	fn process_step(&mut self, step: StepKind2) {
		match step {
			StepKind2::Del(i, a) =>
				swap_insert(&mut self.active, i, a),
			StepKind2::Add => {
				let Active {step, cl, hyp} = self.active.pop().unwrap();
				if hyp { self.steps.push((step, cl, Hyp)) }
				else if step.needed() {
					let r = self.find_reason(&cl);
					self.steps.push((step, cl, r)) } } } }
}

fn main() {
  let mut args = env::args().skip(1);
  let (vars, fmla) = parse_dimacs(
    read_to_string(args.next().expect("missing input file"))
      .expect("read .cnf failed").chars());
  let drat = ProofIter(BufReader::new(
    File::open(args.next().expect("missing proof file"))
      .expect("read .p failed")).bytes().map(|r| r.expect("read failed")));
  // let mut steps: Vec<(DeletionTime, Clause)> = fmla.iter().map(|cl| (cl.clone(), Hyp)).collect();
	let mut pass1 = Pass1::new();
	for cl in &fmla { pass1.add(cl.clone(), true) }
  for (k, cl) in drat {
		match k {
			StepKind::Add => pass1.add(cl, false),
			StepKind::Del => pass1.del(cl) } }
	let Pass1 {steps, active} = pass1;
	// for cl in fmla { println!("{:?}", cl); }
  // for cl in &pass1.0 { println!("{:?}", cl); }
	let mut pass2 = Pass2::new(vars, active);
	for step in steps.into_iter().rev() {
		pass2.process_step(step) }
	for (i, s) in pass2.steps.iter().rev().enumerate() { s.0.assign(i) }
	for (step, cl, r) in pass2.steps.iter().rev() {
		println!("{:?}", (step, cl, r)); } }
