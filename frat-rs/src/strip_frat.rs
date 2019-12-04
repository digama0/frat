use std::fs::File;
use std::io::{self, BufReader, BufWriter, Read, Write};

pub fn main(mut args: impl Iterator<Item=String>) -> io::Result<()> {
  let mut r = BufReader::new(File::open(&args.next().expect("missing input file"))?)
    .bytes().map(Result::unwrap);
  let w = &mut BufWriter::new(File::create(&args.next().expect("missing output file"))?);

  loop {
    match r.next() {
      None => return Ok(()),
      Some(c) if c == b't' || c == b'l' => while r.next() != Some(0) {},
      Some(c) => {
        w.write(&[c])?;
        loop {
          let c = r.next().unwrap();
          w.write(&[c])?;
          if c == 0 {break}
        }
      }
    }
  }
}