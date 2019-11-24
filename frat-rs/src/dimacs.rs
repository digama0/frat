use std::rc::Rc;
use hashbrown::hash_map::{HashMap};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Token {
	Nat(i64),
	Ident(Ident)
}

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
	peek  : char,
}

impl<I> Lexer<I> where I: Iterator<Item=char> {
	fn from(input: I) -> Lexer<I> {
		let mut lex = Lexer {
			input : input,
			buffer: String::new(),
			peek  : '\0' };
		lex.bump();
		lex
  }

	fn bump_opt(&mut self) -> Option<char> {
		if let Some(peeked) = self.input.next() {
			self.peek = peeked;
			Some(peeked)
    } else { None }
  }

	fn bump(&mut self) -> char {
		self.peek = self.bump_opt().unwrap_or('\0');
		self.peek
  }

	fn skip_line(&mut self) {
		while self.peek != '\n' && self.peek != '\0' {
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
		while self.bump().is_alphanumeric() {
			if self.buffer.len() < 3 {
				self.buffer.push(self.peek);
      } else { panic!("unknown keyword") }
    }
		match self.buffer.as_str() {
			"c"     => self.scan_comment(),
			"p"     => Problem,
			"cnf"   => Cnf,
			_       => panic!("unknown keyword")
    }
  }

	fn scan_nat(&mut self) -> i64 {
		let mut val = self.peek.to_digit(10)
			.expect("expected a digit to base 10: (0...9)") as i64;
		while let Some(parsed) = self.bump().to_digit(10) {
			val *= 10;
			val += parsed as i64;
    }
		val
  }
}

impl<I> Iterator for Lexer<I> where I: Iterator<Item=char> {
	type Item = Token;

	fn next(&mut self) -> Option<Self::Item> {
		while self.peek.is_whitespace() {
			self.bump();
    }
		if self.peek == '\0' { return None; }
		match self.peek {
      'a'..='z' => match self.scan_keyword() {
        Comment => self.next(),
        tk => Some(Ident(tk))
      },
      '0'..='9' => Some(Nat(self.scan_nat())),
      '-' => { self.bump(); Some(Nat(-self.scan_nat())) },
      _ => panic!("invalid token start")
    }
  }
}

fn clause_hash(c: &Vec<i64>) -> i64 {
  c.into_iter().sum()
}

pub type Clause = Rc<Vec<i64>>;

pub fn parse_dimacs<I: Iterator<Item=char>>(input: I) -> (usize, HashMap<i64, Vec<(u64, Clause)>>) {

  let mut lex = Lexer::from(input);

  match (lex.next(), lex.next(), lex.next(), lex.next()) {
    (Some(Ident(Problem)), Some(Ident(Cnf)), Some(Nat(_vars)), Some(Nat(clauses))) => {
      let mut fmla: HashMap<i64, Vec<(u64, Clause)>> = HashMap::new();
      let mut ctr: u64 = 1;
      loop {
        let mut clause: Vec<i64> = Vec::new();
        loop {
          match lex.next() {
            Some(Nat(0)) => break,
            Some(Nat(lit)) => clause.push(lit),
            None => return (clauses as usize, fmla),
            _ => panic!("parse DIMACS failed")
          }
        }
		let hs: i64 = clause_hash(&clause);
		match fmla.get_mut(&hs) {
          None => { 
			fmla.insert(hs, vec![(ctr, Rc::new(clause))]); 
			()
		  },
		  Some(bkt) => {
			bkt.push((ctr, Rc::new(clause))); 
			() 
		  }
		}
		ctr += 1;
      }
    },
    _ => panic!("parse DIMACS failed")
  }
}
