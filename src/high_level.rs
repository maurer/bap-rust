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

pub type Stmt = ll::Stmt<BitVector>;

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
