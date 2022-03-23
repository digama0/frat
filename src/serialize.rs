use arrayvec::ArrayVec;
use std::io::{self, Write};
use super::parser::{Ascii, Bin, DefaultMode,
  Step, StepRef, AddStep, AddStepRef, ElabStep, ElabStepRef, ProofRef};

pub trait ModeWrite<M=DefaultMode>: Write {}

pub struct ModeWriter<M, W>(pub M, pub W);

impl<M, W: Write> Write for ModeWriter<M, W> {
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> { self.1.write(buf) }
  fn write_all(&mut self, buf: &[u8]) -> io::Result<()> { self.1.write_all(buf) }
  fn flush(&mut self) -> io::Result<()> { self.1.flush() }
}
impl<M, W: Write> ModeWrite<M> for ModeWriter<M, W> {}

pub trait Serialize<M=DefaultMode> {
  fn write(&self, w: &mut impl ModeWrite<M>) -> io::Result<()>;
}

impl<A: Serialize, B: Serialize> Serialize for (A, B) {
  fn write(&self, w: &mut impl ModeWrite) -> io::Result<()> { self.0.write(w)?; self.1.write(w) }
}

impl Serialize<Bin> for u8 {
  fn write(&self, w: &mut impl ModeWrite<Bin>) -> io::Result<()> { w.write_all(&[*self]) }
}

impl Serialize<Ascii> for u8 {
  fn write(&self, w: &mut impl ModeWrite<Ascii>) -> io::Result<()> { write!(w, "{}", self) }
}

impl<A: Serialize<Bin>> Serialize<Bin> for &[A] {
  fn write(&self, w: &mut impl ModeWrite<Bin>) -> io::Result<()> {
    for v in *self { v.write(w)? }
    0u8.write(w)
  }
}

impl<A: Serialize<Ascii>> Serialize<Ascii> for &[A] {
  fn write(&self, w: &mut impl ModeWrite<Ascii>) -> io::Result<()> {
    for v in *self { v.write(w)?; write!(w, " ")? }
    write!(w, "0")
  }
}

impl Serialize<Bin> for &str {
  fn write(&self, w: &mut impl ModeWrite<Bin>) -> io::Result<()> {
    write!(w, "{}", self)?;
    0u8.write(w)
  }
}

impl Serialize<Bin> for u64 {
  fn write(&self, w: &mut impl ModeWrite<Bin>) -> io::Result<()> {
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
impl Serialize<Ascii> for u64 {
  fn write(&self, w: &mut impl ModeWrite<Ascii>) -> io::Result<()> { write!(w, "{}", self) }
}

impl Serialize<Bin> for i64 {
  fn write(&self, w: &mut impl ModeWrite<Bin>) -> io::Result<()> {
      let u: u64 = if *self < 0 { -*self as u64 * 2 + 1 } else { *self as u64 * 2 };
      u.write(w)
  }
}
impl Serialize<Ascii> for i64 {
  fn write(&self, w: &mut impl ModeWrite<Ascii>) -> io::Result<()> { write!(w, "{}", self) }
}

impl Serialize<Bin> for AddStepRef<'_> {
  fn write(&self, w: &mut impl ModeWrite<Bin>) -> io::Result<()> {
    match *self {
      AddStepRef::One(ls) => ls.iter().try_for_each(|v| v.write(w))?,
      AddStepRef::Two(ls, ls2) => ls.iter().chain(ls2).try_for_each(|v| v.write(w))?,
    }
    0u8.write(w)
  }
}

impl Serialize<Ascii> for AddStepRef<'_> {
  fn write(&self, w: &mut impl ModeWrite<Ascii>) -> io::Result<()> {
    match *self {
      AddStepRef::One(ls) => for v in ls { v.write(w)?; write!(w, " ")? },
      AddStepRef::Two(ls, ls2) => {
        for v in ls { v.write(w)?; write!(w, " ")? }
        write!(w, " ")?;
        for v in ls2 { v.write(w)?; write!(w, " ")? }
      }
    }
    write!(w, "0")
  }
}

impl<M> Serialize<M> for AddStep where for<'a> &'a [i64]: Serialize<M> {
  fn write(&self, w: &mut impl ModeWrite<M>) -> io::Result<()> { (&*self.0).write(w) }
}

impl<'a> Serialize<Bin> for StepRef<'a> {
  fn write(&self, w: &mut impl ModeWrite<Bin>) -> io::Result<()> {
    match *self {
      StepRef::Comment(s) => (b'c', s).write(w),
      StepRef::Orig(idx, vec) => (b'o', (idx, vec)).write(w),
      StepRef::Add(idx, vec, None) => (b'a', (idx, vec)).write(w),
      StepRef::Add(idx, vec, Some(ProofRef::LRAT(steps))) =>
        ((b'a', (idx, vec)), (b'l', steps)).write(w),
      StepRef::Reloc(relocs) => (b'r', relocs).write(w),
      StepRef::Del(idx, vec) => (b'd', (idx, vec)).write(w),
      StepRef::Final(idx, vec) => (b'f', (idx, vec)).write(w),
      StepRef::Todo(idx) => (b't', (idx, 0u8)).write(w),
    }
  }
}

impl<'a> Serialize<Ascii> for StepRef<'a> {
  fn write(&self, w: &mut impl ModeWrite<Ascii>) -> io::Result<()> {
    match *self {
      StepRef::Comment(s) =>
        s.split('\n').try_for_each(|s| writeln!(w, "c {}.", s)),
      StepRef::Orig(idx, vec) => {
        write!(w, "o {}  ", idx)?; vec.write(w)?; writeln!(w)
      }
      StepRef::Add(idx, vec, pf) => {
        write!(w, "a {}  ", idx)?; vec.write(w)?;
        if let Some(ProofRef::LRAT(steps)) = pf {
          write!(w, "  l ")?; steps.write(w)?;
        }
        writeln!(w)
      }
      StepRef::Reloc(relocs) => {
        writeln!(w, "r")?;
        for chunks in relocs.chunks(8) {
          for &(a, b) in chunks {
            write!(w, "  {} {}", a, b)?;
          }
          writeln!(w)?;
        }
        writeln!(w, "  0")
      }
      StepRef::Del(idx, vec) => {
        write!(w, "d {}  ", idx)?; vec.write(w)?; writeln!(w)
      }
      StepRef::Final(idx, vec) => {
        write!(w, "f {}  ", idx)?; vec.write(w)?; writeln!(w)
      }
      StepRef::Todo(idx) => writeln!(w, "t {} 0", idx),
    }
  }
}

impl<M> Serialize<M> for Step where for<'a> StepRef<'a>: Serialize<M> {
  fn write(&self, w: &mut impl ModeWrite<M>) -> io::Result<()> {
    self.as_ref().write(w)
  }
}

impl<'a> Serialize<Bin> for ElabStepRef<'a> {
  fn write(&self, w: &mut impl ModeWrite<Bin>) -> io::Result<()> {
    match *self {
      ElabStepRef::Comment(s) =>
        s.split('\0').try_for_each(|s| (b'c', s).write(w)),
      ElabStepRef::Orig(idx, vec) => (b'o', (idx, vec)).write(w),
      ElabStepRef::Add(idx, vec, steps) =>
        ((b'a', (idx, vec)), (b'l', steps)).write(w),
      ElabStepRef::Reloc(relocs) => (b'r', relocs).write(w),
      ElabStepRef::Del(idx) => (b'd', (idx, 0u8)).write(w),
    }
  }
}

impl<'a> Serialize<Ascii> for ElabStepRef<'a> {
  fn write(&self, w: &mut impl ModeWrite<Ascii>) -> io::Result<()> {
    match *self {
      ElabStepRef::Comment(s) => StepRef::Comment(s).write(w),
      ElabStepRef::Orig(idx, vec) => StepRef::Orig(idx, vec).write(w),
      ElabStepRef::Add(idx, vec, steps) =>
        StepRef::Add(idx, vec, Some(ProofRef::LRAT(steps))).write(w),
      ElabStepRef::Reloc(relocs) => StepRef::Reloc(relocs).write(w),
      ElabStepRef::Del(idx) => writeln!(w, "d {}", idx)
    }
  }
}

impl<M> Serialize<M> for ElabStep where for<'a> ElabStepRef<'a>: Serialize<M> {
  fn write(&self, w: &mut impl ModeWrite<M>) -> io::Result<()> {
    self.as_ref().write(w)
  }
}
