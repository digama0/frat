pub fn parse_unum<I: Iterator<Item=u8>>(it: &mut I) -> Option<u64> {
  let mut res: u64 = 0;
  let mut mul: u8 = 0;
  for c in it {
    res |= ((c & 0x7F) as u64) << mul;
    mul += 7;
    if c & 0x80 == 0 {
      return Some(res)
    }
  }
  if res != 0 { panic!("iterator ran out with incomplete number") }
  None
}

pub fn parse_num<I: Iterator<Item=u8>>(it: &mut I) -> Option<i64> {
  parse_unum(it).map(|ulit|
    if ulit & 1 != 0 { -((ulit >> 1) as i64) }
    else { (ulit >> 1) as i64 })
}
