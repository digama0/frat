mod parser;
mod dratchk;

use std::env;
use std::io;
use std::fs::{read_to_string, File};
use std::io::*;
use parser::*;
use dratchk::*;

fn main() -> io::Result<()> {
  let mut args = env::args().skip(1);
  let (vars, fmla) = parse_dimacs(
    read_to_string(args.next().expect("missing input file"))?.chars());
  let drat_file = File::open(args.next().expect("missing proof file"))?;
	let arg = args.next();
	if arg.as_ref().map_or(false, |s| s == "-l") {
		// LRAT backward checking for cadical
		unimplemented!()
	} else {
		let drat = ProofIter(BufReader::new(drat_file).bytes().map(|r| r.expect("read failed")));
		dratchk::process_proof(vars, &fmla, drat, match arg {
			None => false,
			Some(ref s) if s == "-b" => true,
			_ => panic!("unrecognized option") }) }
	Ok(()) }
