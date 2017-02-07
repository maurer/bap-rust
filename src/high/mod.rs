//! The `high` module contains higher level, native abstractions for working with BAP.
//! At the moment, this consists of `bitvector` for manipulating `basic::Word`, and
//! `bil` for interacting with BIL code.
pub mod bitvector;
pub mod bil;

#[test]
fn high_smoke() {
    use basic;
    use self::bitvector::BitVector;
    use self::bil::Statement;
    use num::ToPrimitive;
    let path = "test_data/elf_x86";
    basic::Bap::with(|bap| -> basic::Result<()> {
            let image = basic::Image::from_file(&bap, path)?;
            let syms = image.symbols();
            let f_sym = syms.iter().filter(|sym| &sym.name() == "f").next().unwrap();
            let f_mem = f_sym.memory();
            let f_data = f_mem.data();
            let f_addr = BitVector::from_basic(&f_mem.min_addr());
            let f_end = BitVector::from_basic(&f_mem.max_addr());
            let disas = basic::BasicDisasm::new(&bap, basic::Arch::X86)?;
            let mut index = 0;
            let mut cur_addr = f_addr;
            while cur_addr < f_end {
                let code = disas.disasm(&f_data[index..], cur_addr.to_u64().unwrap())?;
                let len = code.len();
                index += len;
                cur_addr = cur_addr + len;
                let insn = code.insn();
                let sema = insn.semantics();
                let stmts: Vec<_> = sema.iter().map(|bb| Statement::from_basic(&bb)).collect();
                for stmt in stmts {
                    println!("{:?}", stmt);
                }
            }
            Ok(())
        })
        .unwrap()
}
