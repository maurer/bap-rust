use std::fmt::{Formatter, Display, Error};
use std::result::Result;
use basic::Arch;
use high::bitvector::BitVector;

impl Display for Arch {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        use basic::Arch::*;
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
