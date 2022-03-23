use std::io::{self, Seek, SeekFrom, Read, BufReader, Write, BufWriter};
use std::fs::{File, read_to_string};
use crate::HashMap;
use crate::dimacs::parse_dimacs;
use crate::parser::{detect_binary, Mode, Bin, Ascii, DRATParser, DRATStep, StepRef, DefaultMode};
use crate::serialize::{ModeWriter, Serialize};
use crate::perm_clause::*;

fn from_drat(mode: impl Mode, cnf: Vec<Box<[i64]>>, drat: File, frat: File) -> io::Result<()> {
  let drat = DRATParser::from(mode, BufReader::new(drat).bytes().map(Result::unwrap));
  let w = &mut ModeWriter(DefaultMode, BufWriter::new(frat));
  let mut k = 0; // Counter for the last used ID
  let mut ctx: HashMap<PermClause, Vec<u64>> = HashMap::default(); // current context
  for ls in cnf {
    k += 1;
    StepRef::Orig(k, &ls).write(w)?;
    ctx.entry(PermClause(ls.into())).or_default().push(k);
  }

  for s in drat {
    // eprintln!("{:?}", s);

    match s {
      DRATStep::Comment(s) => StepRef::Comment(&s).write(w)?,

      DRATStep::Add(add) => {
        let (unsat, lemma) = add.parse_into(|add| {
          let lemma = add.lemma();
          if lemma.is_empty() { return Ok(true) }
          k += 1; // Get the next fresh ID
          StepRef::Add(k, add.as_ref(), None).write(w).map(|_| false)
        });
        if unsat? { break }
        ctx.entry(PermClause(lemma)).or_default().push(k);
      }

      DRATStep::Del(ls) => {
        let ls = PermClause(ls);
        let vec = ctx.get_mut(&ls).unwrap_or_else(
          || panic!("deleted nonexistent clause {:?}", ls.0));
        let st = vec.pop().expect("deleted nonexistent clause");
        if vec.is_empty() { ctx.remove(&ls); }
        StepRef::Del(st, &ls.0).write(w)?;
      }
    }
  }

  // Some DRAT files accepted by drat-trim stop one step short
  // of the final empty clause step, so we have to insert it here
  k += 1;
  StepRef::add(k, &[], None).write(w)?;
  StepRef::Final(k, &[]).write(w)?;

  for (PermClause(c), vec) in ctx {
    for st in vec {
      StepRef::Final(st, &c).write(w)?;
    }
  }

  w.flush()
}

pub fn main(mut args: impl Iterator<Item=String>) -> io::Result<()> {
  let (_vars, cnf) = parse_dimacs(read_to_string(args.next().expect("missing input file"))?.bytes());
  let mut drat = File::open(args.next().expect("missing proof file"))?;
  let bin = detect_binary(&mut drat)?;
  drat.seek(SeekFrom::Start(0))?;
  let frat = File::create(args.next().expect("missing output file"))?;
  if bin { from_drat(Bin, cnf, drat, frat) }
  else { from_drat(Ascii, cnf, drat, frat) }
}
