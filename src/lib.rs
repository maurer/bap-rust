extern crate bap_sys;
extern crate libc;
#[macro_use] extern crate enum_primitive;
extern crate bit_vec;
extern crate byteorder;
extern crate num;

pub mod expert;

pub use expert::Expr;
pub use expert::BinOp;
pub use expert::UnOp;
pub use expert::BitSize;
pub use expert::Endian;
pub use expert::Arch;
pub use expert::CastKind;

use bit_vec::BitVec;

use expert as ex;

use byteorder::{LittleEndian, ReadBytesExt};
use std::io::Cursor;

#[derive(Clone,Debug)]
pub struct BitVector {
  inner : BitVec
}

impl BitVector {
  fn to_bap(&self, ctx : &ex::Context) -> ex::BitVector {
    //TODO support >64bit conversions
    ex::BitVector::create_64(ctx, self.to_u64().unwrap(),
                                  self.inner.len() as u16)
  }
  fn of_bap(ctx : &ex::Context, bv : &ex::BitVector) -> Self {
    let mut bvn = BitVec::from_bytes(&bv.contents(&ctx));
    bvn.truncate(bv.width(&ctx) as usize);
    BitVector {
      inner : bvn
    }
  }
  pub fn to_u32(&self) -> Option<u32> {
    if self.inner.len() <= 32 {
      let mut rdr = Cursor::new(self.inner.to_bytes());
      rdr.read_u32::<LittleEndian>().ok()
    } else {
      None
    }
  }
  pub fn to_u64(&self) -> Option<u64> {
    if self.inner.len() <= 64 {
      let mut rdr = Cursor::new(self.inner.to_bytes());
      rdr.read_u64::<LittleEndian>().ok()
    } else {
      None
    }
  }
  pub fn into_bitvec(self) -> BitVec {
    self.inner
  }
  pub fn to_bitvec(&self) -> BitVec {
    self.inner.clone()
  }
  pub fn from_bitvec(bv : &BitVec) -> Self {
    BitVector { inner : bv.clone() }
  }
  pub fn one(len : usize) -> Self {
    BitVector { inner : {
      let mut bv = BitVec::from_elem(len, false);
      bv.set(0, true);
      bv
    }}
  }
}

impl ::std::ops::Add for BitVector {
  type Output = Self;
  fn add(self, rhs : BitVector) -> Self {
    //TODO accelerate by keeping a bignum repr too
    assert_eq!(self.inner.len(), rhs.inner.len());
    let mut bv = self.inner;
    for i in 0..rhs.inner.len() {
      let mut flip = i;
      while (bv[flip] == true) && flip < bv.len() {
        bv.set(flip, false);
        flip += 1;
      }

      if flip < bv.len() {
        bv.set(flip, true);
      }
    }
    BitVector { inner : bv }
  }
}

pub type Addr = BitVector;

pub type Stmt = ex::Stmt<BitVector>;

#[derive(Debug)]
pub struct Symbol {
  pub name  : String,
  pub func  : bool,
  pub debug : bool,
  pub start : Addr,
  pub end   : Option<Addr>
}

impl Symbol {
  pub fn of_bap(ctx : &ex::Context, sym : &ex::Symbol) -> Self {
    Symbol {
      name  : sym.name.clone(),
      func  : sym.func,
      debug : sym.debug,
      start : BitVector::of_bap(ctx, &sym.start),
      end   : sym.end.as_ref().map(|bv| {
        BitVector::of_bap(ctx, &bv)
      })
    }
  }
  pub fn from_file_contents(contents : &[u8]) -> Vec<Self> {
    ex::with_bap(|ctx| {
      ex::Symbol::from_file_contents(&ctx, contents).iter().map(|sym|{Symbol::of_bap(&ctx, sym)}).collect()
    })
  }
}

pub struct Segment {
  pub name : String,
  pub r : bool,
  pub w : bool,
  pub x : bool,
  pub start : Addr,
  pub end : Addr,
  pub data : Vec<u8>
}


impl Segment {
  pub fn from_file_contents(contents : &[u8]) -> Vec<Self> {
    ex::with_bap(|ctx| {
      let ex_segs = ex::Segment::from_file_contents(&ctx, contents);
      ex_segs.iter().map(|ex_seg| {
        let mem_local = ex_seg.mem.project(&ctx);
        Segment {
          name  : ex_seg.name.clone(),
          r     : ex_seg.r,
          w     : ex_seg.w,
          x     : ex_seg.x,
          start : BitVector::of_bap(&ctx, &mem_local.start),
          end   : BitVector::of_bap(&ctx, &mem_local.end),
          data  : mem_local.data
        }
      }).collect()
    })
  }
  pub fn byteweight(&self, arch : Arch) -> Vec<Symbol> {
    ex::with_bap(|ctx| {
      let base  = self.start.to_bap(&ctx);
      let bs    = ex::BigString::new(&ctx, &self.data);
      //TODO track endianness in segments
      let mem   = ex::MemRegion::new(&ctx, &bs, 0, self.data.len(), Endian::Little, &base);
      let ex_syms = ex::Symbol::byteweight(&ctx, arch, &mem);
      ex_syms.iter().map(|sym|{Symbol::of_bap(&ctx, &sym)}).collect()
    })
  }
}

pub fn lift(addr : &BitVector,
            endian : Endian, arch : Arch,
            bin : &[u8]) -> Vec<(BitVector, BitVector, Vec<Stmt>, bool)> {
  ex::with_bap(|ctx| {
    let base  = addr.to_bap(&ctx);
    let bs    = ex::BigString::new(&ctx, bin);
    let mem   = ex::MemRegion::new(&ctx, &bs, 0, bin.len(), endian, &base);
    let disas = ex::Disasm::mem(&ctx, Vec::new(), arch, mem);
    let insns = disas.instructions(&ctx).into_iter();
    insns.map(|di|{(BitVector::of_bap(&ctx, &di.start),
                    BitVector::of_bap(&ctx, &di.end),
                    di.insn.stmts(&ctx).iter().map(|i|{i.map_bv(&|x|{
                        BitVector::of_bap(&ctx, x)
                    })}).collect(),
                    di.insn.is_call(&ctx))}).collect()
  })
}

#[test]
fn dump_syms() {
  let buf = include_bytes!("../test_data/elf_x86");
  let syms = Symbol::from_file_contents(buf);
  let main_sym = syms.iter().filter(|x| {x.name == "main"}).next().unwrap();
  let f_sym = syms.iter().filter(|x| {x.name == "f"}).next().unwrap();
  assert_eq!(main_sym.start.to_u32().unwrap(), 0x080483f5);
  assert_eq!(f_sym.start.to_u32().unwrap(), 0x080483eb);
}
