#![allow(clippy::upper_case_acronyms)]

mod dimacs;
mod parser;
mod backparser;
mod perm_clause;
mod midvec;
mod elab;
mod fratchk;
mod dratchk;
mod serialize;
mod from_drat;
mod strip_frat;
mod drat_trim;
mod from_pr;

use std::collections::hash_map::DefaultHasher;
use std::hash::BuildHasherDefault;
use std::{env, io};

pub type HashMap<K, V> = std::collections::HashMap<K, V, BuildHasherDefault<DefaultHasher>>;
pub type HashSet<K> = std::collections::HashSet<K, BuildHasherDefault<DefaultHasher>>;

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
    "drat-trim" => drat_trim::main(args),
    "from-pr" => from_pr::main(args),
    _ => panic!("{}", "incorrect subcommand, expected {\
      elab, fratchk, dratchk, lratchk, refrat, strip-frat, from-drat, from-pr}")
  }
}
