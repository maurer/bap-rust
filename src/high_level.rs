pub use low_level::Expr;
pub use low_level::BinOp;
pub use low_level::UnOp;
pub use low_level::BitSize;
pub use low_level::Endian;
pub use low_level::Arch;
pub use low_level::CastKind;

use num::bigint::BigUint;
use num::traits::ToPrimitive;

use low_level as ll;

pub struct BitVector {
  pub val   : BigUint,
  pub width : BitSize
}

impl BitVector {
  fn to_bap(&self, ctx : &ll::Context) -> ll::BitVector {
    //TODO support >64bit conversions
    ll::BitVector::create_64(ctx, self.val.to_u64().unwrap(), self.width)
  }
  fn of_bap(ctx : &ll::Context, bv : &ll::BitVector) -> Self {
    BitVector {
      val   : BigUint::from_bytes_le(&bv.contents(&ctx)),
      width : bv.width(&ctx)
    }
  }
}
pub type Addr = BitVector;

pub type Stmt = ll::Stmt<BitVector>;

pub struct Symbol {
  pub name  : String,
  pub func  : bool,
  pub debug : bool,
  pub start : Addr,
  pub end   : Option<Addr>
}

impl Symbol {
  pub fn of_bap(ctx : &ll::Context, sym : &ll::Symbol) -> Self {
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
    ll::with_bap(|ctx| {
      ll::Symbol::from_file_contents(&ctx, contents).iter().map(|sym|{Symbol::of_bap(&ctx, sym)}).collect()
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
    ll::with_bap(|ctx| {
      let ll_segs = ll::Segment::from_file_contents(&ctx, contents);
      ll_segs.iter().map(|ll_seg| {
        let mem_local = ll_seg.mem.project(&ctx);
        Segment {
          name  : ll_seg.name.clone(),
          r     : ll_seg.r,
          w     : ll_seg.w,
          x     : ll_seg.x,
          start : BitVector::of_bap(&ctx, &mem_local.start),
          end   : BitVector::of_bap(&ctx, &mem_local.end),
          data  : mem_local.data
        }
      }).collect()
    })
  }
  pub fn byteweight(&self, arch : Arch) -> Vec<Symbol> {
    ll::with_bap(|ctx| {
      let base  = self.start.to_bap(&ctx);
      let bs    = ll::BigString::new(&ctx, &self.data);
      //TODO track endianness in segments
      let mem   = ll::MemRegion::new(&ctx, &bs, 0, self.data.len(), Endian::Little, &base);
      let ll_syms = ll::Symbol::byteweight(&ctx, arch, &mem);
      ll_syms.iter().map(|sym|{Symbol::of_bap(&ctx, &sym)}).collect()
    })
  }
}

pub fn lift(addr : &BitVector,
            endian : Endian, arch : Arch,
            bin : &[u8]) -> Vec<(BitVector, BitVector, Vec<Stmt>)> {
  ll::with_bap(|ctx| {
    let base  = addr.to_bap(&ctx);
    let bs    = ll::BigString::new(&ctx, bin);
    let mem   = ll::MemRegion::new(&ctx, &bs, 0, bin.len(), endian, &base);
    let disas = ll::Disasm::mem(&ctx, Vec::new(), arch, mem);
    let insns = disas.instructions(&ctx).into_iter();
    insns.map(|di|{(BitVector::of_bap(&ctx, &di.start),
                    BitVector::of_bap(&ctx, &di.end),
                    di.insn.stmts(&ctx).iter().map(|i|{i.map_bv(&|x|{
                        BitVector::of_bap(&ctx, x)
                    })}).collect())}).collect()
  })
}
