use std::convert::TryInto;
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Token {
  Nat(i64),
  Ident(Ident)
}

use self::Token::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Ident { Comment, Problem, Cnf, Del }

use self::Ident::*;

#[derive(Debug, Clone)]
struct Lexer<I> {
  /// input iterator
  input: I,

  /// internal buffer to map to known keywords
  buffer: Vec<u8>,

  /// the current character that is being dispatched upon
  peek: u8,
}

impl<I: Iterator<Item=u8>> Lexer<I> {
  fn from(input: I) -> Lexer<I> {
    let mut lex = Lexer {
      input,
      buffer: Vec::new(),
      peek: 0
    };
    lex.bump();
    lex
  }

  fn bump_opt(&mut self) -> Option<u8> {
    let peeked = self.input.next()?;
    self.peek = peeked;
    Some(peeked)
  }

  fn bump(&mut self) -> u8 {
    self.peek = self.bump_opt().unwrap_or(0);
    self.peek
  }

  fn skip_line(&mut self) {
    while self.peek != b'\n' && self.peek != 0 {
      self.bump();
    }
  }

  fn scan_comment(&mut self) -> Ident {
    self.skip_line();
    Comment
  }

  fn scan_keyword(&mut self) -> Ident {
    self.buffer.clear();
    self.buffer.push(self.peek);
    while (self.bump() as char).is_alphanumeric() {
      if self.buffer.len() < 3 {
        self.buffer.push(self.peek);
      } else { panic!("unknown keyword") }
    }
    match &*self.buffer {
      b"c"   => self.scan_comment(),
      b"p"   => Problem,
      b"cnf" => Cnf,
      b"d"   => Del,
      _      => panic!("unknown keyword")
    }
  }

  fn scan_nat(&mut self) -> i64 {
    let mut val = (self.peek as char).to_digit(10)
      .expect("expected a digit to base 10: (0...9)") as i64;
    while let Some(parsed) = (self.bump() as char).to_digit(10) {
      val = val.checked_mul(10).unwrap().checked_add(parsed as i64).unwrap();
    }
    val
  }
}

impl<I: Iterator<Item=u8>> Iterator for Lexer<I> {
  type Item = Token;

  fn next(&mut self) -> Option<Self::Item> {
    while (self.peek as char).is_whitespace() {
      self.bump();
    }
    if self.peek == 0 { return None; }
    match self.peek {
      b'a'..=b'z' => match self.scan_keyword() {
        Comment => self.next(),
        tk => Some(Ident(tk))
      },
      b'0'..=b'9' => Some(Nat(self.scan_nat())),
      b'-' => { self.bump(); Some(Nat(-self.scan_nat())) },
      _ => panic!("invalid token start")
    }
  }
}

pub type Clause = Box<[i64]>;

pub struct DimacsIter<I>(Lexer<I>);

impl<I: Iterator<Item=u8>> DimacsIter<I> {
  pub fn from(input: I) -> (usize, usize, Self) {
    let mut lex = Lexer::from(input);
    match (lex.next(), lex.next(), lex.next(), lex.next()) {
      (Some(Ident(Problem)), Some(Ident(Cnf)), Some(Nat(vars)), Some(Nat(clauses))) =>
        (vars.try_into().unwrap(), clauses.try_into().unwrap(), DimacsIter(lex)),
      _ => panic!("parse DIMACS failed")
    }
  }
}

impl<I: Iterator<Item=u8>> Iterator for DimacsIter<I> {
  type Item = Vec<i64>;
  fn next(&mut self) -> Option<Vec<i64>> {
    let mut clause = Vec::new();
    loop {
      match self.0.next()? {
        Nat(0) => break,
        Nat(lit) => clause.push(lit),
        _ => panic!("parse DIMACS failed")
      }
    }
    Some(clause)
  }
}

pub fn parse_dimacs_map<T>(input: impl Iterator<Item=u8>, f: impl FnMut(Vec<i64>) -> T) -> (usize, Vec<T>) {
  let (vars, clauses, it) = DimacsIter::from(input);
  let mut fmla = Vec::with_capacity(clauses);
  fmla.extend(it.map(f));
  (vars, fmla)
}

pub fn parse_dimacs(input: impl Iterator<Item=u8>) -> (usize, Vec<Clause>) {
  parse_dimacs_map(input, |x| x.into())
}
