use std::{fmt::Debug, marker::PhantomData, mem::ManuallyDrop, ops::{Index, IndexMut, RangeInclusive}, ptr::NonNull};

pub struct MidVec<T> {
  size: i64,
  center: NonNull<T>,
}

impl<T> Drop for MidVec<T> {
  fn drop(&mut self) {
    drop(unsafe { self.shallow_clone() }.into_box_slice())
  }
}

impl<T: Debug> Debug for MidVec<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.as_slice().fmt(f)
  }
}

impl<T: Default> MidVec<T> {
  pub fn with_capacity(size: i64) -> Self {
    Self::with_capacity_by(size, Default::default)
  }

  pub fn reserve_to(&mut self, n: i64) {
    if n > self.len() {
      let new_size = n.max(self.len().checked_mul(2).unwrap());
      for (i, v) in std::mem::replace(self, Self::with_capacity(new_size)) {
        self[i] = v;
      }
    }
  }

  pub fn reserve_cleared(&mut self, n: i64) {
    if n > self.len() {
      let new_size = n.max(self.len().checked_mul(2).unwrap());
      *self = Self::with_capacity(new_size);
    }
  }

  pub fn clear(&mut self) {
    for v in self.as_slice_mut() { *v = Default::default() }
  }
}

impl<T: Default> Default for MidVec<T> {
  fn default() -> Self { Self::with_capacity(7) }
}

impl<T> MidVec<T> {
  pub fn with_capacity_by(size: i64, f: impl FnMut() -> T) -> Self {
    let n = size as usize;
    let data: Box<[T]> = std::iter::repeat_with(f).take(2 * n + 1).collect();
    Self {
      size,
      center: unsafe {
        NonNull::new_unchecked((Box::into_raw(data) as *mut T).offset(size as isize))
      },
    }
  }

  unsafe fn shallow_clone(&self) -> Self {
    MidVec {size: self.size, center: self.center}
  }

  #[inline] pub fn len(&self) -> i64 { self.size }

  #[inline] pub unsafe fn get_unchecked_ptr(&self, n: i64) -> *mut T {
    self.center.as_ptr().offset(n as isize)
  }

  #[inline] pub unsafe fn get_unchecked(&self, n: i64) -> &T {
    &*self.get_unchecked_ptr(n)
  }

  #[inline] pub unsafe fn get_unchecked_mut(&mut self, n: i64) -> &mut T {
    &mut *self.get_unchecked_ptr(n)
  }

  #[inline] pub fn get(&self, n: i64) -> Option<&T> {
    if n <= self.size as i64 && -n <= self.size as i64 {
      Some(unsafe {self.get_unchecked(n)})
    } else {None}
  }

  #[inline] pub fn get_mut(&mut self, n: i64) -> Option<&mut T> {
    if n <= self.size as i64 && -n <= self.size as i64 {
      Some(unsafe {self.get_unchecked_mut(n)})
    } else {None}
  }

  pub fn into_box_slice(self) -> Box<[T]> {
    let md = ManuallyDrop::new(self);
    unsafe {
      Box::from_raw(std::ptr::slice_from_raw_parts_mut(
        md.get_unchecked_ptr(-md.size), 2 * (md.size as usize) + 1))
    }
  }

  pub fn as_slice(&self) -> &[T] {
    unsafe {
      std::slice::from_raw_parts(
        self.get_unchecked_ptr(-self.size), 2 * (self.size as usize) + 1)
    }
  }

  pub fn as_slice_mut(&mut self) -> &mut [T] {
    unsafe {
      std::slice::from_raw_parts_mut(
        self.get_unchecked_ptr(-self.size), 2 * (self.size as usize) + 1)
    }
  }

  pub fn enum_iter(&self) -> Iter<'_, T> {
    Iter {
      ptr: unsafe { self.get_unchecked_ptr(-self.size) },
      it: -self.size..=self.size,
      _marker: PhantomData,
    }
  }

  pub fn enum_iter_mut(&mut self) -> IterMut<'_, T> {
    IterMut {
      ptr: unsafe { self.get_unchecked_ptr(-self.size) },
      it: -self.size..=self.size,
      _marker: PhantomData,
    }
  }
}

impl<T> Index<i64> for MidVec<T> {
  type Output = T;

  #[inline] fn index(&self, index: i64) -> &T {
    self.get(index).expect("index out of bounds")
  }
}

impl<T> IndexMut<i64> for MidVec<T> {
  #[inline] fn index_mut(&mut self, index: i64) -> &mut T {
    self.get_mut(index).expect("index out of bounds")
  }
}

impl<T> From<MidVec<T>> for Box<[T]> {
  fn from(this: MidVec<T>) -> Self { this.into_box_slice() }
}
impl<T> From<MidVec<T>> for Vec<T> {
  fn from(this: MidVec<T>) -> Self { this.into_box_slice().into() }
}

impl<T> IntoIterator for MidVec<T> {
  type Item = (i64, T);
  type IntoIter = std::iter::Zip<RangeInclusive<i64>, std::vec::IntoIter<T>>;
  fn into_iter(self) -> Self::IntoIter {
    (-self.size..=self.size).zip(Vec::from(self).into_iter())
  }
}

impl<'a, T> IntoIterator for &'a MidVec<T> {
  type Item = (i64, &'a T);
  type IntoIter = Iter<'a, T>;
  fn into_iter(self) -> Self::IntoIter { self.enum_iter() }
}

impl<'a, T> IntoIterator for &'a mut MidVec<T> {
  type Item = (i64, &'a mut T);
  type IntoIter = IterMut<'a, T>;
  fn into_iter(self) -> Self::IntoIter { self.enum_iter_mut() }
}

pub struct Iter<'a, T> {
  ptr: *const T,
  it: RangeInclusive<i64>,
  _marker: PhantomData<&'a T>
}

impl<'a, T> Iterator for Iter<'a, T> {
  type Item = (i64, &'a T);
  fn next(&mut self) -> Option<(i64, &'a T)> {
    let n = self.it.next()?;
    let t = unsafe { &*self.ptr };
    self.ptr = unsafe { self.ptr.offset(1) };
    Some((n, t))
  }
}

pub struct IterMut<'a, T> {
  ptr: *mut T,
  it: RangeInclusive<i64>,
  _marker: PhantomData<&'a mut T>
}

impl<'a, T> Iterator for IterMut<'a, T> {
  type Item = (i64, &'a mut T);
  fn next(&mut self) -> Option<(i64, &'a mut T)> {
    let n = self.it.next()?;
    let t = unsafe { &mut *self.ptr };
    self.ptr = unsafe { self.ptr.offset(1) };
    Some((n, t))
  }
}