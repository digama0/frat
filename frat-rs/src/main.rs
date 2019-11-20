pub mod dimacs;
mod parser;
pub mod backparser;
mod lratchk;
mod serialize;

use std::env;
use std::io;
use std::fs::File;
use backparser::{Bin, Ascii, detect_binary};

fn main() -> io::Result<()> {
  let mut args = env::args().skip(1);
  let mut proof = File::open(args.next().expect("missing proof file"))?;
  let bin = detect_binary(&mut proof)?;
  if bin { lratchk::check_proof::<Bin>(proof) }
  else { lratchk::check_proof::<Ascii>(proof) }
}
