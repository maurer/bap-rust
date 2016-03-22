use bit_vec::BitVec;
use num::bigint::BigUint;
use num::traits::FromPrimitive;
use num::pow;
use std::hash::{Hash, Hasher};

use expert as ex;

use byteorder::{LittleEndian, ByteOrder};
use std::ops::BitAnd;

pub struct BitVector {
    native : BitVec,
    bap    : ex::BitVector,
    unum   : BigUint,
}

impl ::std::fmt::Debug for BitVector {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "BitVector {{ native: {:?}, bap: ?, unum: {:?} }}",
               self.native, self.unum)
    }
}

impl Clone for BitVector {
    fn clone(&self) -> Self {
        BitVector::new(&self.native)
    }
}

impl Hash for BitVector {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.native.hash(state)
    }
}

impl PartialEq for BitVector {
    fn eq(&self, other: &Self) -> bool {
        self.native == other.native
    }
}

impl PartialOrd for BitVector {
    fn partial_cmp(&self, other: &Self) -> Option<::std::cmp::Ordering> {
        self.native.partial_cmp(&other.native)
    }
}

fn loose_64(bv: &BitVec) -> Option<u64> {
    if bv.len() <= 64 {
        let buf = bv.to_bytes();
        Some(LittleEndian::read_uint(&buf, buf.len()))
    } else {
        None
    }
}

fn bitvec_to_bap(bv: &BitVec, ctx: &ex::Context) -> ex::BitVector {
    //TODO support >64-bit conversions
    ex::BitVector::create_64(ctx, loose_64(bv).unwrap(), bv.len() as u16)
}

impl BitVector {
  pub fn to_bap(&self) -> &ex::BitVector {
      &self.bap
  }
  pub fn of_bap(ctx : &ex::Context, bv : &ex::BitVector) -> Self {
    let mut bvn = BitVec::from_bytes(&bv.contents(ctx));
    bvn.truncate(bv.width(ctx) as usize);
    BitVector {
      native: bvn.clone(),
      // Rebuild the bitvector so we own a copy here
      bap: bitvec_to_bap(&bvn, ctx),
      unum: BigUint::from_bytes_le(&bvn.to_bytes()),
    }
  }
  fn new_ex(bv: &BitVec, ctx: &ex::Context) -> Self {
      BitVector {
          native: bv.clone(),
          bap: bitvec_to_bap(bv, ctx),
          unum: BigUint::from_bytes_le(&bv.to_bytes()),
      }
  }
  pub fn new(bv: &BitVec) -> Self {
      ex::with_bap(|ctx| {BitVector::new_ex(bv, &ctx)})
  }
  pub fn new_unsigned(num: BigUint, len: usize) -> Self {
      assert!(num.bits() <= len);
      let mut bv = BitVec::from_bytes(&num.to_bytes_le());
      let bvlen = bv.len();
      bv.grow(len - bvlen, false);
      bv.truncate(len);
      BitVector::new(&bv)
  }
  pub fn into_bitvec(self) -> BitVec {
    self.native
  }
  pub fn to_bitvec(&self) -> &BitVec {
    &self.native
  }
  pub fn one(len : usize) -> Self {
      let mut bv = BitVec::from_elem(len, false);
      bv.set(0, true);
      BitVector::new(&bv)
  }
  pub fn len(&self) -> usize {
      self.native.len()
  }
}

fn overflow(unum: BigUint, len: usize) -> BigUint {
    if unum.bits() > len {
        //We overflowed, and need to truncate the high order bits
        unum.bitand(pow(BigUint::from_u32(2).unwrap(), len))
    } else {
        unum
    }
}

impl<'a> ::std::ops::Add for &'a BitVector {
  type Output = BitVector;
  fn add(self, rhs: &'a BitVector) -> BitVector {
    assert_eq!(self.native.len(), rhs.native.len());
    BitVector::new_unsigned(
        overflow(&self.unum + &rhs.unum,
                 self.native.len()),
        self.native.len())
  }
}

impl<'a> ::std::ops::Add<usize> for &'a BitVector {
  type Output = BitVector;
  fn add(self, rhs: usize) -> BitVector {
    BitVector::new_unsigned(
        overflow(&self.unum + BigUint::from_usize(rhs).unwrap(),
                 self.native.len()),
        self.native.len())
  }
}

impl ::std::ops::Add<usize> for BitVector {
    type Output = BitVector;
    fn add(self, rhs: usize) -> BitVector {
        &self + rhs
    }
}

pub type Addr = BitVector;

impl ::num::traits::ToPrimitive for BitVector {
    // Until we add an inum repr, fail signed generation
    fn to_i64(&self) -> Option<i64> {None}
    fn to_u64(&self) -> Option<u64> {
        self.unum.to_u64()
    }
}
