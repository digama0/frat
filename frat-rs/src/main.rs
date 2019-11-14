mod dimacs;
mod parser;
mod backparser;
mod dratchk;
mod lratchk;

use std::env;
use std::io;
use std::fs::{read_to_string, File};
use std::io::*;

fn main() -> io::Result<()> {
  let mut args = env::args().skip(1);
	let arg1 = args.next().expect("missing input file");
  let proof = File::open(args.next().expect("missing proof file"))?;
	if arg1 == "-l" {
		// LRAT backward checking for cadical
		lratchk::check_proof(proof)?
	} else {
		let (vars, fmla) = dimacs::parse_dimacs(read_to_string(arg1)?.chars());
		let drat = dratchk::ProofIter(BufReader::new(proof).bytes().map(|r| r.expect("read failed")));
		dratchk::process_proof(vars, &fmla, drat, match args.next() {
			None => false,
			Some(ref s) if s == "-b" => true,
			_ => panic!("unrecognized option")
		})
	}
	Ok(())
}
