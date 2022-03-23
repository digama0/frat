use std::{io::{self, SeekFrom, Seek}, fs::File};
use crate::{parser::{FwdParser, Segment, Mode, Ascii, Bin, detect_binary}, HashMap, perm_clause::PermClause};

fn to_cnf<M: Mode>(mode: M, frat: File) -> (HashMap<PermClause, u64>, i64) {
  let mut max_var = 0;
  let mut origs = HashMap::default();
  for step in FwdParser::new(mode, frat) {
    if let Segment::Orig(i, ls) = step {
      for l in &ls { max_var = max_var.max(l.abs()) }
      origs.entry(PermClause(ls)).or_insert(i);
    }
  }
  (origs, max_var)
}

pub fn main(mut args: impl Iterator<Item=String>) -> io::Result<()> {
  let frat_path = args.next().expect("missing frat file");
  let mut frat = File::open(frat_path)?;
  let bin = detect_binary(&mut frat)?;
  frat.seek(SeekFrom::Start(0))?;
  let (origs, max_var) = if bin { to_cnf(Bin, frat) } else { to_cnf(Ascii, frat) };
  println!("p cnf {} {}", max_var, origs.len());
  let mut origs = origs.iter().collect::<Vec<_>>();
  origs.sort_by_key(|p| p.1);
  for (ls, _) in origs {
    for i in &ls.0 { print!("{} ", i); }
    println!("0")
  }
  Ok(())
}
