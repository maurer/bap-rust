//! The `bitvector` module contains code useful for talking about arbitrary-but-fixed width
//! numbers, like `basic::word`, but in a native representation.
use bit_vec::BitVec;
use num::bigint::BigUint;
use num::traits::FromPrimitive;
use num::pow;

use std::ops::BitAnd;
use basic;

/// A `BitVector` is a wrapper around a `BitVec` allowing it to do perform arbitrary-but-fixed
/// width two's complement arithmetic. This is useful when talking about CPU-level values, which
/// may be odd things like 31 bits, or things larger than traditional integer types like 128 bits.
#[derive(Clone, Hash, PartialEq, PartialOrd, Eq)]
pub struct BitVector {
    unum: BigUint,
    native: BitVec,
}

#[cfg(feature = "json")]
use rustc_serialize::{Encoder, Decoder, Encodable, Decodable};
#[cfg(feature = "json")]
impl Encodable for BitVector {
    fn encode<S: Encoder>(&self, s: &mut S) -> Result<(), S::Error> {
        s.emit_struct("BitVector", 2, |s| {
            try!(s.emit_struct_field("unum", 0, |s| self.unum.encode(s)));
            s.emit_struct_field("len", 1, |s| self.native.len().encode(s))
        })
    }
}

#[cfg(feature = "json")]
impl Decodable for BitVector {
    fn decode<D: Decoder>(d: &mut D) -> Result<Self, D::Error> {
        let (unum, len): (BigUint, usize) = try!(d.read_struct("BitVector", 2, |d| {
            let unum = try!(d.read_struct_field("unum", 0, |d| BigUint::decode(d)));
            let len = try!(d.read_struct_field("len", 1, |d| usize::decode(d)));
            Ok((unum, len))
        }));
        Ok(BitVector::new_unsigned(unum, len))
    }
}

impl ::std::fmt::Debug for BitVector {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(
            f,
            "BitVector {{ native: {:?}, unum: {:?} }}",
            self.native,
            self.unum
        )
    }
}

impl BitVector {
    /// Converts a `BitVector` into a Bap-style `basic::Word`
    pub fn to_basic<'a>(&self, bap: &'a basic::Bap) -> basic::Word<'a> {
        basic::Word::from_bitvec(bap, &self.native)
    }
    /// Converts a a Bap-style `basic::Word` into a native `BitVector`
    pub fn from_basic<'a>(bap_word: &basic::Word<'a>) -> Self {
        let mut bvn = BitVec::from_bytes(&bap_word.contents());
        bvn.truncate(bap_word.width());
        BitVector::new(&bvn)
    }
    /// Creates a new `BitVector` from a `BitVec` container
    pub fn new(bv: &BitVec) -> Self {
        BitVector {
            native: bv.clone(),
            unum: BigUint::from_bytes_le(&bv.to_bytes()),
        }
    }
    /// Creates a new `BitVector` from the number it is to represent and its length in bits
    pub fn new_unsigned(num: BigUint, len: usize) -> Self {
        assert!(num.bits() <= len);
        let mut bv = BitVec::from_bytes(&num.to_bytes_le());
        let bvlen = bv.len();
        if len > bvlen {
            bv.grow(len - bvlen, false);
        } else {
            bv.truncate(len);
        }
        BitVector::new(&bv)
    }
    /// Produces the empty bitvector
    pub fn nil() -> Self {
        BitVector::new(&BitVec::new())
    }
    /// Convert the `BitVector` into a `BitVec`, consuming it
    pub fn into_bitvec(self) -> BitVec {
        self.native
    }
    /// Get a reference to the `BitVec` this is based on
    pub fn to_bitvec(&self) -> &BitVec {
        &self.native
    }
    /// Create a `BitVector` of numeric value 1, of the provided length
    pub fn one(len: usize) -> Self {
        let mut bv = BitVec::from_elem(len, false);
        bv.set(0, true);
        BitVector::new(&bv)
    }
    /// Get the length in bits of the `BitVector`
    pub fn len(&self) -> usize {
        self.native.len()
    }
    /// Get the value of the `BitVector` as an unsigned bignum
    pub fn unum(&self) -> BigUint {
        self.unum.clone()
    }
    /// Create a `BitVector` from a `u64` value and the target length.
    /// Length must be long enough to contain the `u64` value.
    pub fn from_u64(val: u64, len: usize) -> Self {
        let unum = BigUint::from_u64(val).unwrap();
        Self::new_unsigned(unum, len)
    }
}

// Compute the twos-complement overflowed version of thie `BigUint`
fn overflow(unum: BigUint, len: usize) -> BigUint {
    if unum.bits() > len {
        // We overflowed, and need to truncate the high order bits
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
            overflow(&self.unum + &rhs.unum, self.native.len()),
            self.native.len(),
        )
    }
}

impl<'a> ::std::ops::Add<usize> for &'a BitVector {
    type Output = BitVector;
    fn add(self, rhs: usize) -> BitVector {
        BitVector::new_unsigned(
            overflow(
                &self.unum + BigUint::from_usize(rhs).unwrap(),
                self.native.len(),
            ),
            self.native.len(),
        )
    }
}

impl ::std::ops::Add<usize> for BitVector {
    type Output = BitVector;
    fn add(self, rhs: usize) -> BitVector {
        &self + rhs
    }
}

impl ::num::traits::ToPrimitive for BitVector {
    // Until we add an inum repr, fail signed generation
    fn to_i64(&self) -> Option<i64> {
        None
    }
    fn to_u64(&self) -> Option<u64> {
        self.unum.to_u64()
    }
}

#[test]
fn bv_gt() {
    let bv_lo = BitVector::from_u64(0x123456789, 64);
    let bv_hi = BitVector::from_u64(0x987654321, 64);
    assert!(bv_hi > bv_lo);
}
