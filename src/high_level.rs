pub use low_level::Stmt;
pub use low_level::Expr;
pub use low_level::BinOp;
pub use low_level::UnOp;
pub use low_level::BitSize;
pub use low_level::Endian;
pub use low_level::Arch;
pub use low_level::CastKind;

use low_level as ll;

pub fn lift(addr : u64, width : BitSize,
        endian : Endian, arch : Arch,
        bin : &[u8]) -> Vec<(ll::BitVector, ll::BitVector, Vec<Stmt>)> {
  ll::with_bap(|ctx| {
    let base  = ll::BitVector::create_64(&ctx, addr, width);
    let bs    = ll::BigString::new(&ctx, bin);
    let mem   = ll::MemRegion::new(&ctx, &bs, 0, bin.len(), endian, &base);
    let disas = ll::Disasm::mem(&ctx, Vec::new(), arch, mem);
    let insns = disas.instructions(&ctx).into_iter();
    insns.map(|di|{(di.start, di.end, di.insn.stmts(&ctx))}).collect()
  })
}
