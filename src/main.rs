mod dimacs;
mod parser;
mod backparser;
mod perm_clause;
mod elab;
mod fratchk;
mod dratchk;
mod serialize;
mod from_drat;
mod strip_frat;

use std::env;
use std::io;

fn main() -> io::Result<()> {
  let mut args = env::args().skip(1);
  match args.next().expect("expected a subcommand").as_str() {
    "elab" => elab::main(args),
    "fratchk" => fratchk::main(args),
    "dratchk" => dratchk::main(args),
    "lratchk" => elab::lratchk(args),
    "refrat" => elab::refrat(args),
    "strip-frat" => strip_frat::main(args),
    "from-drat" => from_drat::main(args),
    _ => panic!("incorrect subcommand, expected {elab, fratchk, dratchk, lratchk, refrat, strip-frat, from-drat}")
  }
}
