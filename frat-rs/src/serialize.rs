use arrayvec::ArrayVec;
use std::io::{self, Write};
use super::backparser::{Step, ElabStep, Proof};

pub trait Serialize {
  fn write<W: Write>(&self, w: &mut W) -> io::Result<()>;
}

impl<A: Serialize, B: Serialize> Serialize for (A, B) {
  fn write<W: Write>(&self, w: &mut W) -> io::Result<()> { self.0.write(w)?; self.1.write(w) }
}

impl Serialize for u8 {
  fn write<W: Write>(&self, w: &mut W) -> io::Result<()> { w.write_all(&[*self]) }
}

impl Serialize for char {
  fn write<W: Write>(&self, w: &mut W) -> io::Result<()> { (*self as u8).write(w) }
}

impl<'a, A: Serialize> Serialize for &'a Vec<A> {
  fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
    for v in *self { v.write(w)? }
    0u8.write(w)
  }
}

impl Serialize for u64 {
  fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
    let mut val = *self;
    let mut buf = ArrayVec::<[u8; 10]>::new();
    loop {
      if val & !0x7f == 0 {
        buf.push((val & 0x7f) as u8);
        return w.write_all(&buf)
      } else {
        buf.push((val | 0x80) as u8);
        val >>= 7;
      }
    }
  }
}

impl Serialize for i64 {
  fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
      let u: u64 = if *self < 0 { -*self as u64 * 2 + 1 } else { *self as u64 * 2 };
      u.write(w)
  }
}

impl Serialize for Step {
  fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
    match *self {
      Step::Orig(idx, ref vec) => ('o', (idx, vec)).write(w),
      Step::Add(idx, ref vec, None) => ('a', (idx, vec)).write(w),
      Step::Add(idx, ref vec, Some(Proof::Sorry)) =>
        (('t', (127u8, 0u8)), ('a', (idx, vec))).write(w),
      Step::Add(idx, ref vec, Some(Proof::LRAT(ref steps))) =>
        (('a', (idx, vec)), ('l', steps)).write(w),
      Step::Reloc(ref relocs) => ('r', relocs).write(w),
      Step::Del(idx, ref vec) => ('d', (idx, vec)).write(w),
      Step::Final(idx, ref vec) => ('f', (idx, vec)).write(w),
      Step::Todo(idx) => ('t', (idx, 0u8)).write(w),
    }
  }
}

impl Serialize for ElabStep {
  fn write<W: Write>(&self, w: &mut W) -> io::Result<()> {
    match *self {
      ElabStep::Orig(idx, ref vec) => ('o', (idx, vec)).write(w),
      ElabStep::Add(idx, ref vec, ref steps) =>
        (('a', (idx, vec)), ('l', steps)).write(w),
      ElabStep::Reloc(ref relocs) => ('r', relocs).write(w),
      ElabStep::Del(idx) => ('d', (idx, 0u8)).write(w),
    }
  }
}
