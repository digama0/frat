use std::env;
use std::fs;
use std::rc::Rc;
use std::io::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Token {
	Nat(i64),
	Zero,
	Ident(Ident),
	EndOfFile }

use self::Token::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Ident { Comment, Problem, Cnf }

use self::Ident::*;

#[derive(Debug, Clone)]
pub struct Lexer<I> where I: Iterator<Item=char> {
	/// input iterator
	input : I,

	/// internal buffer to map to known keywords
	buffer: String,

	/// the current character that is being dispatched upon
	peek  : char }

impl<I> Lexer<I> where I: Iterator<Item=char> {
	pub fn from(input: I) -> Lexer<I> {
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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Reason { Hyp }
use self::Reason::*;

fn main() {
  let mut args = env::args().skip(1);
  let (vars, fmla) = parse_dimacs(
    fs::read_to_string(args.next().expect("missing input file"))
      .expect("read .cnf failed").chars());
  let mut proofit = ProofIter(BufReader::new(
    fs::File::open(args.next().expect("missing proof file"))
      .expect("read .p failed")).bytes().map(|r| r.expect("read failed")));
  let mut steps: Vec<_> = fmla.iter().map(|cl| (cl.clone(), Hyp)).collect();
  for (k, clause) in proofit {
    println!("{:?}", &clause);
    steps.push((clause, Hyp)); }
  for cl in fmla { println!("{:?}", cl); } }
