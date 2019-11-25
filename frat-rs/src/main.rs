mod dimacs;
mod parser;
mod backparser;
mod elab;
mod fratchk;
mod dratchk;
mod serialize;

use std::env;
use std::io;

fn main() -> io::Result<()> {
  let mut args = env::args().skip(1);
  match args.next().expect("expected a subcommand").as_str() {
    "fratchk" => fratchk::main(args),
    "dratchk" => dratchk::main(args),
    "elab" => elab::main(args),
    _ => panic!("incorrect arguments")
  }
}
