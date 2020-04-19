use std::fmt::{Display, Error, Formatter};
use std::result::Result;
use crate::basic::Arch;
use crate::high::bitvector::BitVector;
use crate::high::bil::{Type, Variable};

impl Display for Arch {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        use crate::basic::Arch::*;
        match *self {
            X86 => write!(f, "x86"),
            X86_64 => write!(f, "x86_64"),
            ArmV7 => write!(f, "ARMv7"),
            // For uncommon cases, cascade to debug repr
            a => write!(f, "{:?}", a),
        }
    }
}

impl Display for BitVector {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        write!(f, "0x{:x}:{}", self.unum(), self.len())
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        match *self {
            Type::Immediate(n) => write!(f, "bv{}", n),
            Type::Memory {
                addr_size,
                cell_size,
            } => write!(f, "mem[{}:{}]", addr_size, cell_size),
        }
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        let tmp_str = if self.tmp { "~" } else { "" };
        write!(f, "{}.{}:{}{}", self.name, self.index, self.type_, tmp_str)
    }
}
