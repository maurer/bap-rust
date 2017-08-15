//! This module provides the basic interace to BAP
//! It essentially re-exports all functions from `bap-bindings` with
//! safety wrappers.

use bap_sys;
use std::ffi::{CStr, CString};
use std::ptr::{null_mut, null};
use std::sync::{Once, ONCE_INIT};
use std::result;
use std::cell::Cell;
use std::marker::PhantomData;
use std::slice;
use std::rc::Rc;
use enum_primitive::FromPrimitive;
use std::sync::{Mutex, MutexGuard};
use bit_vec::BitVec;

#[allow(non_camel_case_types)]
type char = ::std::os::raw::c_char;
#[allow(non_camel_case_types)]
type size_t = ::std::os::raw::c_int;
#[allow(non_camel_case_types)]
type int = ::std::os::raw::c_int;

/// Type representing a data size in bits
pub type BitSize = u16;

// Bail out with the most recent error (for cases we can't report cleanly, like init)
unsafe fn bap_panic() {
    panic!(
        "bap unrecoverable error: {}",
        CStr::from_ptr(bap_sys::bap_error_get()).to_string_lossy()
    )
}

/// Type alias for `Result` with a BAP error
pub type Result<T> = result::Result<T, String>;

// Rust doesn't have a trait for `as` for some reason
trait CastFrom<T> {
    fn cast(T) -> Self;
}

impl CastFrom<int> for usize {
    fn cast(v: int) -> Self {
        v as Self
    }
}
impl CastFrom<int> for u64 {
    fn cast(v: int) -> Self {
        v as Self
    }
}
impl CastFrom<int> for BitSize {
    fn cast(v: int) -> Self {
        v as Self
    }
}

// Wraps a potentially errored BAP value into a `Result` type
unsafe fn bap_error<T>(v: *mut T) -> Result<*mut T> {
    if v == null_mut() {
        let out = Err(
            CStr::from_ptr(bap_sys::bap_error_get())
                .to_string_lossy()
                .into_owned(),
        );
        bap_sys::bap_error_clean();
        out
    } else {
        Ok(v)
    }
}

// Wraps a nullable BAP value into an `Option` type
unsafe fn bap_option<T>(v: *mut T) -> Option<*mut T> {
    if v == null_mut() { None } else { Some(v) }
}

// Copies a string from BAP to Rust
unsafe fn bap_string(v: *mut char) -> String {
    let out = CStr::from_ptr(v).to_string_lossy().into_owned();
    bap_release(v);
    out
}

// Converts a BAP optional integer into a rust optional unsigned
fn bap_opt_int<T: CastFrom<int>>(v: int) -> Option<T> {
    match v {
        -1 => None,
        _ => Some(CastFrom::<int>::cast(v)),
    }
}

// Ensures `bap_init` and `bap_load_plugins` are called exactly once
static BAP_INIT: Once = ONCE_INIT;
lazy_static! {
static ref BAP_LOCK: Mutex<()> = Mutex::new(());
}

/// This is a context struct to prove you are on the unique query thread without
/// performing work for each function call.
pub struct Bap {
    _phantom: PhantomData<*mut Bap>,
    _lock: MutexGuard<'static, ()>,
}

impl Bap {
    /// Performs initialization if not done, and returns a `Bap` context object if
    /// you are on the query thread.
    pub fn get() -> Bap {
        BAP_INIT.call_once(|| unsafe {
            bap_sys::bap_init(1, ["bap".as_ptr() as *const char, null()].as_mut_ptr());
            if bap_sys::bap_load_plugins() < 0 {
                bap_panic()
            }
        });
        Bap {
            _phantom: PhantomData,
            _lock: BAP_LOCK.lock().unwrap(),
        }
    }
    /// With-style wrapper around a `Bap` context object
    pub fn with<F, A>(f: F) -> A
    where
        F: Fn(&Bap) -> A,
    {
        f(&Bap::get())
    }
}

enum_from_primitive!{
/// Native enum for BAP architectures
#[allow(missing_docs)]
#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Debug, Hash, PartialEq, PartialOrd)]
#[cfg_attr(feature = "json", derive(RustcEncodable,RustcDecodable))]
#[repr(i16)]
pub enum Arch {
    AArch64Be = 0,
    ArmV7 = 1,
    ArmV6 = 2,
    ArmV5 = 3,
    ArmV4 = 4,
    NvPTX = 5,
    ThumbV7Eb = 6,
    ThumbV6Eb = 7,
    ThumbV5Eb = 8,
    ThumbV4Eb = 9,
    Hexagon = 10,
    PPC64Le = 11,
    SparcV9 = 12,
    SystemZ = 13,
    ThumbV7 = 14,
    ThumbV6 = 15,
    ThumbV5 = 16,
    ThumbV4 = 17,
    MIPS64El = 18,
    SPARC = 19,
    X86 = 20,
    PPC = 21,
    AArch64 = 22,
    ArmV7Eb = 23,
    ArmV6Eb = 24,
    ArmV5Eb = 25,
    ArmV4Eb = 26,
    X86_64 = 27,
    XCore = 28,
    NvPTX64 = 29,
    MIPSEl = 30,
    MIPS64 = 31,
    R600 = 32,
    MIPS = 33,
    PPC64 = 34,
}
}

impl Arch {
    #[cfg(feature = "holmes_support")]
    /// Gets a reference to the Arch as an `i16` (you probably don't want this)
    // Only legal due to #[repr(i16)]. If that changes, this type+name must change
    pub fn i16_ref(&self) -> &i16 {
        unsafe { ::std::mem::transmute(self) }
    }

    fn from_bap(a: bap_sys::bap_arch_t) -> Option<Self> {
        Arch::from_i32(a as i32)
    }
    fn to_bap(&self) -> bap_sys::bap_arch_t {
        unsafe { ::std::mem::transmute(*self as i32) }
    }
}

// Convenience function to make `bap_release` polymorphic
#[inline]
unsafe fn bap_release<T>(arg: *mut T) {
    bap_sys::bap_release(arg as *mut ::std::os::raw::c_void)
}

fn rc1() -> Rc<Cell<usize>> {
    Rc::new(Cell::new(1))
}


type PU<'a> = PhantomData<&'a ()>;

// This macro declares a RAII wrapper type for a BAP foreign
// pointer
macro_rules! abs_type {
    ($c_name:ident, $cap_name:ident) => {
        abs_type!($c_name, $cap_name, PU);
    };
    ($c_name:ident, $cap_name:ident, $extra:ident) => {
        #[allow(missing_docs)]
        pub struct $cap_name<'a> {
            bap_sys: *mut bap_sys::$c_name,
            rc: Rc<Cell<usize>>,
            extra: $extra<'a>,
        }
        impl<'a> Clone for $cap_name<'a> {
            fn clone(&self) -> Self {
                self.rc.set(self.rc.get() + 1);
                $cap_name {
                    bap_sys: self.bap_sys,
                    rc: self.rc.clone(),
                    extra: self.extra.clone()
                }
            }
        }
        impl<'a> Drop for $cap_name<'a> {
            fn drop(&mut self) ->() {
                let rc = self.rc.get();
                if rc == 1 {
                    unsafe {
                        bap_release(self.bap_sys);
                    }
                } else {
                    self.rc.set(rc - 1)
                }
            }
        }
    };
}

#[derive(Clone)]
struct ImageBacking<'a> {
    _backing: Option<&'a [u8]>,
}

/// BAP type representing a loaded program image
abs_type!(bap_image_t, Image, ImageBacking);
/// BAP type representing an arbitrary length bitvector
abs_type!(bap_word_t, Word, PU);
/// BAP type representing a sequence of segments
abs_type!(bap_segment_seq_t, SegmentSequence, Image);
/// BAP type representing an iterator of a segment sequence
abs_type!(
    bap_segment_seq_iterator_t,
    SegmentSequenceIterator,
    SegmentSequence
);
/// BAP type representing a sequence of symbols
abs_type!(bap_symbol_seq_t, SymbolSequence, Image);
/// BAP type representing an iterator of a segment sequence
abs_type!(
    bap_symbol_seq_iterator_t,
    SymbolSequenceIterator,
    SymbolSequence
);
/// BAP type representing a segment
abs_type!(bap_segment_t, Segment, Image);
/// BAP type representing a symbol
abs_type!(bap_symbol_t, Symbol, Image);
/// BAP type representing a region of memory
abs_type!(bap_memory_t, Memory);
/// BAP type representing a single instruction + associated data
abs_type!(bap_code_t, Code);
/// BAP type representing an instruction
abs_type!(bap_insn_t, Instruction);
/// BAP type repsenting a sequence of statements
abs_type!(bap_stmt_seq_t, StatementSequence);
/// BAP type representing an iterator of a segment sequence
abs_type!(
    bap_stmt_seq_iterator_t,
    StatementSequenceIterator,
    StatementSequence
);
/// BAP type repsenting BIL semantic statement
abs_type!(bap_stmt_t, Statement);
/// BAP type representing a BIL expression
abs_type!(bap_exp_t, Expression);
/// BAP type representing a BIL variable
abs_type!(bap_var_t, Variable);
/// BAP type representing a BIL type
abs_type!(bap_type_t, Type);

impl<'a> Image<'a> {
    /// Create an `Image` by having BAP read a file from disk
    pub fn from_file(_bap: &'a Bap, path: &str) -> Result<Self> {
        unsafe {
            let path_c = CString::new(path).unwrap();
            Ok(Image {
                bap_sys: bap_error(bap_sys::bap_image_create(
                    path_c.as_ptr() as *mut char,
                    null_mut(),
                ))?,
                rc: rc1(),
                extra: ImageBacking { _backing: None },
            })
        }
    }

    /// Create an `Image` from a file's contents
    pub fn from_data(_bap: &'a Bap, data: &'a [u8]) -> Result<Self> {
        unsafe {
            Ok(Image {
                bap_sys: bap_error(bap_sys::bap_image_of_data(
                    data.as_ptr() as *mut char,
                    data.len() as size_t,
                    null_mut(),
                ))?,
                rc: rc1(),
                extra: ImageBacking { _backing: Some(data) },
            })
        }
    }

    /// Get the entrypoint of an `Image`
    pub fn entry(&self) -> Word {
        unsafe {
            Word {
                bap_sys: bap_sys::bap_image_entry_point(self.bap_sys),
                rc: rc1(),
                extra: PhantomData,
            }
        }
    }

    /// Get the filename of record for an `Image` (may not be meaningful if `of_data` was used)
    pub fn filename(&self) -> String {
        unsafe { bap_string(bap_sys::bap_image_filename(self.bap_sys)) }
    }

    /// Get the architecture of the `Image`
    pub fn arch(&self) -> Option<Arch> {
        Arch::from_bap(unsafe { bap_sys::bap_image_arch(self.bap_sys) })
    }

    /// Retrieve the contents of the file used to create the `Image`
    pub fn data(&self) -> Vec<u8> {
        unsafe {
            let len = bap_sys::bap_image_length(self.bap_sys) as usize;
            // Returned pointer is borrowed, don't free it
            let data = bap_sys::bap_image_data(self.bap_sys) as *mut u8;
            slice::from_raw_parts(data, len).to_owned()
        }
    }

    /// Get the sequence of segments in the `Image`
    pub fn segments(&self) -> SegmentSequence {
        unsafe {
            SegmentSequence {
                bap_sys: bap_sys::bap_image_segments(self.bap_sys),
                rc: rc1(),
                extra: self.clone(),
            }
        }
    }

    /// Get the sequence of symbols in the `Image`
    pub fn symbols(&self) -> SymbolSequence {
        unsafe {
            SymbolSequence {
                bap_sys: bap_sys::bap_image_symbols(self.bap_sys),
                rc: rc1(),
                extra: self.clone(),
            }
        }
    }
}

#[test]
fn load_test() {
    use std::fs::File;
    use std::io::Read;
    let bap = Bap::get();
    let path = "test_data/elf_x86";
    let mut data = Vec::new();
    File::open(path).unwrap().read_to_end(&mut data).unwrap();
    (|| -> Result<()> {
         let image = Image::from_file(&bap, path)?;
         assert_eq!(path, &image.filename());
         let image2 = Image::from_data(&bap, &data)?;
         assert_eq!(data, image.data());
         assert_eq!(data, image2.data());
         Ok(())
     })().unwrap()
}

#[test]
fn sym_test() {
    let path = "test_data/elf_x86";
    Bap::with(|bap| -> Result<()> {
        let image = Image::from_file(&bap, path)?;
        let syms = image.symbols();
        let sym_names: Vec<String> = syms.iter().map(|sym| sym.name()).collect();
        let expected_names: Vec<String> = [
            "__x86.get_pc_thunk.bx",
            "f",
            "main",
            "__libc_csu_init",
            "__libc_csu_fini",
        ].iter()
            .map(|x| x.to_string())
            .collect();
        assert_eq!(sym_names, expected_names);
        Ok(())
    }).unwrap()
}

impl<'a> SegmentSequence<'a> {
    /// Get an iterator for the SegmentSequence
    pub fn iter(&self) -> SegmentSequenceIterator<'a> {
        unsafe {
            SegmentSequenceIterator {
                bap_sys: bap_sys::bap_segment_seq_iterator_create(self.bap_sys),
                rc: rc1(),
                extra: self.clone(),
            }
        }
    }
}

impl<'a> Iterator for SegmentSequenceIterator<'a> {
    type Item = Segment<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let raw = bap_sys::bap_segment_seq_iterator_next(self.bap_sys);
            if raw == null_mut() {
                None
            } else {
                Some(Segment {
                    bap_sys: raw,
                    rc: rc1(),
                    extra: self.extra.extra.clone(),
                })
            }
        }
    }
}

impl<'a> SymbolSequence<'a> {
    /// Get an iterator for the SymbolSequence
    pub fn iter(&self) -> SymbolSequenceIterator {
        unsafe {
            SymbolSequenceIterator {
                bap_sys: bap_sys::bap_symbol_seq_iterator_create(self.bap_sys),
                rc: rc1(),
                extra: self.clone(),
            }
        }
    }
}

impl<'a> Iterator for SymbolSequenceIterator<'a> {
    type Item = Symbol<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let raw = bap_sys::bap_symbol_seq_iterator_next(self.bap_sys);
            if raw == null_mut() {
                None
            } else {
                Some(Symbol {
                    bap_sys: raw,
                    rc: rc1(),
                    extra: self.extra.extra.clone(),
                })
            }
        }
    }
}

impl<'a> Segment<'a> {
    /// Retrieves the name of a segment
    pub fn name(&self) -> String {
        unsafe { bap_string(bap_sys::bap_segment_name(self.bap_sys)) }
    }
    /// Indicates whether the segment is loaded as writable
    pub fn is_writable(&self) -> bool {
        unsafe { bap_sys::bap_segment_is_writable(self.bap_sys) }
    }
    /// Indicates whether the segment is loaded as readable
    pub fn is_readable(&self) -> bool {
        unsafe { bap_sys::bap_segment_is_writable(self.bap_sys) }
    }
    /// Indicates whether the segment is loaded as executable
    pub fn is_executable(&self) -> bool {
        unsafe { bap_sys::bap_segment_is_writable(self.bap_sys) }
    }
    /// Gets the memory region associated with this segment
    pub fn memory(&self) -> Memory {
        unsafe {
            Memory {
                bap_sys: bap_sys::bap_image_memory_of_segment(self.extra.bap_sys, self.bap_sys),
                rc: rc1(),
                extra: PhantomData,
            }
        }
    }
    /// Gets the list of symbols associated with this segment
    pub fn symbols(&self) -> SymbolSequence {
        unsafe {
            SymbolSequence {
                bap_sys: bap_sys::bap_image_symbols_of_segment(self.extra.bap_sys, self.bap_sys),
                rc: rc1(),
                extra: self.extra.clone(),
            }
        }
    }
}

impl<'a> Symbol<'a> {
    /// Provides the memory contents of the symbol if it is contiguous.
    /// If it is not, provides the beginning of the symbol.
    pub fn memory(&self) -> Memory<'a> {
        unsafe {
            Memory {
                bap_sys: bap_sys::bap_image_memory_of_contiguous_symbol(
                    self.extra.bap_sys,
                    self.bap_sys,
                ),
                rc: rc1(),
                extra: PhantomData,
            }
        }
    }
    /// Provides the name of the symbol
    pub fn name(&self) -> String {
        unsafe { bap_string(bap_sys::bap_symbol_name(self.bap_sys)) }
    }
    /// Indicates whether the symbol is a function
    pub fn is_function(&self) -> bool {
        unsafe { bap_sys::bap_symbol_is_function(self.bap_sys) }
    }
    /// Indicates whether the symbol is debug information
    pub fn is_debug(&self) -> bool {
        unsafe { bap_sys::bap_symbol_is_debug(self.bap_sys) }
    }
}

impl<'a> Word<'a> {
    /// Gives the width in bits of the word
    pub fn width(&self) -> usize {
        (unsafe { bap_sys::bap_word_bitwidth(self.bap_sys) }) as usize
    }
    /// Gives the raw bits as little endian bytes
    pub fn contents(&self) -> Vec<u8> {
        let bit_len = self.width();
        let mut buf: Vec<u8> = Vec::new();
        let byte_len = bit_len * 8;
        buf.resize(byte_len, 0);
        unsafe {
            bap_sys::bap_word_copy_bytes(
                self.bap_sys,
                bap_sys::bap_endian_t::BAP_ENDIAN_LITTLE,
                buf.as_mut_ptr() as *mut i8,
                buf.len() as size_t,
            );
        }
        buf
    }
    /// Makes a `Word` out of a `BitVec`
    pub fn from_bitvec(_bap: &'a Bap, bits: &BitVec) -> Self {
        Word {
            bap_sys: unsafe {
                bap_sys::bap_word_of_binary(
                    bits.len() as size_t,
                    bap_sys::bap_endian_t::BAP_ENDIAN_LITTLE,
                    bits.to_bytes().as_mut_ptr() as *mut i8,
                )
            },
            rc: rc1(),
            extra: PhantomData,
        }
    }
    /// Create a `BitVec` out of a `Word`
    pub fn to_bitvec(&self) -> BitVec {
        let mut bv = BitVec::from_bytes(&self.contents());
        bv.truncate(self.width());
        bv
    }
}

/// Representation of a BAP Basic Disassembler
pub struct BasicDisasm<'a> {
    bap_sys: *mut bap_sys::bap_disasm_basic_t,
    rc: Rc<Cell<usize>>,
    extra: PhantomData<&'a ()>,
}

impl<'a> Clone for BasicDisasm<'a> {
    fn clone(&self) -> Self {
        self.rc.set(self.rc.get() + 1);
        BasicDisasm {
            bap_sys: self.bap_sys,
            rc: self.rc.clone(),
            extra: self.extra.clone(),
        }
    }
}

impl<'a> Drop for BasicDisasm<'a> {
    fn drop(&mut self) -> () {
        let rc = self.rc.get();
        if rc == 1 {
            unsafe {
                self.close();
                bap_release(self.bap_sys);
            }
        } else {
            self.rc.set(rc - 1)
        }
    }
}

impl<'a> BasicDisasm<'a> {
    /// Creates a new disassembler for the givne architecture
    pub fn new(_bap: &'a Bap, arch: Arch) -> Result<Self> {
        Ok(unsafe {
            BasicDisasm {
                bap_sys: bap_error(bap_sys::bap_disasm_basic_create(arch.to_bap()))?,
                rc: rc1(),
                extra: PhantomData,
            }
        })
    }
    /// Attempts to disassemble from the beginning of the provided buffer,
    /// assuming it begins at `addr` in vmem
    pub fn disasm(&self, data: &[u8], addr: u64) -> Result<Code> {
        Ok(Code {
            bap_sys: unsafe {
                bap_error(bap_sys::bap_disasm_basic_next(
                    self.bap_sys,
                    data.as_ptr() as *mut i8,
                    data.len() as size_t,
                    addr as i64,
                ))?
            },
            rc: rc1(),
            extra: PhantomData,
        })
    }
    unsafe fn close(&self) {
        bap_sys::bap_disasm_basic_close(self.bap_sys)
    }
}

impl<'a> Code<'a> {
    /// Get a BAP memory object of the region containing this instruction
    pub fn memory(&self) -> Memory<'a> {
        Memory {
            bap_sys: unsafe { bap_sys::bap_code_mem(self.bap_sys) },
            rc: rc1(),
            extra: PhantomData,
        }
    }
    /// Get the single instruction in this code
    pub fn insn(&self) -> Instruction<'a> {
        Instruction {
            bap_sys: unsafe { bap_sys::bap_code_insn(self.bap_sys) },
            rc: rc1(),
            extra: PhantomData,
        }
    }
    /// Get the length of this instruction in bytes
    pub fn len(&self) -> usize {
        unsafe { bap_sys::bap_code_length(self.bap_sys) as usize }
    }
    /// Get the address this instruction was lifted at
    pub fn addr(&self) -> u64 {
        unsafe { bap_sys::bap_code_addr(self.bap_sys) as u64 }
    }
    /// Get a string representation of the code
    pub fn to_string(&self) -> String {
        unsafe { bap_string(bap_sys::bap_code_to_string(self.bap_sys)) }
    }
}

impl<'a> Instruction<'a> {
    /// Get a string representation of the instruction
    pub fn to_string(&self) -> String {
        unsafe { bap_string(bap_sys::bap_insn_to_string(self.bap_sys)) }
    }
    /// Get the name of the instruction
    pub fn name(&self) -> String {
        unsafe { bap_string(bap_sys::bap_insn_name(self.bap_sys)) }
    }
    /// Get an assembly representation of the instruction
    pub fn asm(&self) -> String {
        unsafe { bap_string(bap_sys::bap_insn_asm(self.bap_sys)) }
    }
    /// Get the semantics for the instruction as BIL
    pub fn semantics(&self) -> StatementSequence {
        StatementSequence {
            bap_sys: unsafe { bap_sys::bap_insn_bil(self.bap_sys) },
            rc: rc1(),
            extra: PhantomData,
        }
    }
    /// Get whether this is a return
    pub fn is_return(&self) -> bool {
        unsafe { bap_sys::bap_insn_is_return(self.bap_sys) }
    }
    /// Get whether this is a call
    pub fn is_call(&self) -> bool {
        unsafe { bap_sys::bap_insn_is_call(self.bap_sys) }
    }
}

impl<'a> StatementSequence<'a> {
    /// Get an iterator for the StatementSequence
    pub fn iter(&self) -> StatementSequenceIterator<'a> {
        unsafe {
            StatementSequenceIterator {
                bap_sys: bap_sys::bap_stmt_seq_iterator_create(self.bap_sys),
                rc: rc1(),
                extra: self.clone(),
            }
        }
    }
}

impl<'a> Iterator for StatementSequenceIterator<'a> {
    type Item = Statement<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let raw = bap_sys::bap_stmt_seq_iterator_next(self.bap_sys);
            if raw == null_mut() {
                None
            } else {
                Some(Statement {
                    bap_sys: raw,
                    rc: rc1(),
                    extra: self.extra.extra.clone(),
                })
            }
        }
    }
}

/// Tag describing what kind of statement a BIL statement is
pub enum StatementTag {
    /// var := exp
    Move,
    /// jmp(exp)
    Jmp,
    /// Uninterpretable instruction
    Special,
    /// while(exp) {stmts}
    While,
    /// if(exp) {true_stmts} else {false_stmts}
    If,
    /// Cpu Exception (e.g. div0)
    /// cpu_exn(int)
    CpuExn,
}

impl StatementTag {
    /// Convert a BAP tag to a native one
    fn from_bap(tag: bap_sys::bap_stmt_tag_t) -> Option<Self> {
        use self::StatementTag::*;
        use bap_sys::bap_stmt_tag_t::*;
        match tag {
            BAP_STMT_TAG_INVALID => None,
            BAP_STMT_TAG_MOVE => Some(Move),
            BAP_STMT_TAG_SPECIAL => Some(Special),
            BAP_STMT_TAG_JMP => Some(Jmp),
            BAP_STMT_TAG_IF => Some(If),
            BAP_STMT_TAG_WHILE => Some(While),
            BAP_STMT_TAG_CPUEXN => Some(CpuExn),
        }
    }
}

impl<'a> Statement<'a> {
    /// Gets the kind of BIL statement this is
    pub fn tag(&self) -> Option<StatementTag> {
        unsafe { StatementTag::from_bap(bap_sys::bap_stmt_tag(self.bap_sys)) }
    }
    /// Gets the expression argument of the BIL statement, if present
    pub fn exp(&self) -> Option<Expression> {
        unsafe {
            bap_option(bap_sys::bap_stmt_exp(self.bap_sys)).map(|exp| {
                Expression {
                    bap_sys: exp,
                    rc: rc1(),
                    extra: PhantomData,
                }
            })
        }
    }
    /// Gets the variable argument of the BIL statement, if present
    pub fn var(&self) -> Option<Variable> {
        unsafe {
            bap_option(bap_sys::bap_stmt_var(self.bap_sys)).map(|var| {
                Variable {
                    bap_sys: var,
                    rc: rc1(),
                    extra: PhantomData,
                }
            })
        }
    }
    /// Gets the block of statements for the BIL statement, if present
    pub fn stmts(&self) -> Option<StatementSequence> {
        unsafe {
            bap_option(bap_sys::bap_stmt_stmts(self.bap_sys)).map(|stmts| {
                StatementSequence {
                    bap_sys: stmts,
                    rc: rc1(),
                    extra: PhantomData,
                }
            })
        }
    }
    /// Gets the true-branch block of statements for the BIL statement, if present
    pub fn true_stmts(&self) -> Option<StatementSequence> {
        unsafe {
            bap_option(bap_sys::bap_stmt_true_stmts(self.bap_sys)).map(|stmts| {
                StatementSequence {
                    bap_sys: stmts,
                    rc: rc1(),
                    extra: PhantomData,
                }
            })
        }
    }
    /// Gets the false-branch block of statements for the BIL statement, if present
    pub fn false_stmts(&self) -> Option<StatementSequence> {
        unsafe {
            bap_option(bap_sys::bap_stmt_false_stmts(self.bap_sys)).map(|stmts| {
                StatementSequence {
                    bap_sys: stmts,
                    rc: rc1(),
                    extra: PhantomData,
                }
            })
        }
    }
    /// Gets the cpu exception number, if present
    pub fn cpuexn(&self) -> Option<u64> {
        bap_opt_int(unsafe { bap_sys::bap_stmt_cpuexn(self.bap_sys) })
    }
    /// Gets the jump target expression, if present
    pub fn jmp(&self) -> Option<Expression> {
        unsafe {
            bap_option(bap_sys::bap_stmt_jmp(self.bap_sys)).map(|jmp| {
                Expression {
                    bap_sys: jmp,
                    rc: rc1(),
                    extra: PhantomData,
                }
            })
        }
    }
}

/// Tag indicating which variety of expression something is
#[derive(Copy, Clone, Debug, Hash, PartialEq, PartialOrd)]
#[cfg_attr(feature = "json", derive(RustcEncodable, RustcDecodable))]
pub enum ExpressionTag {
    /// Unary operation
    /// unop(exp)
    UnOp,
    /// Memory load
    /// mem[addr:addr+size@endian]
    Load,
    /// Unknown value
    Unknown,
    /// cast size (expr)
    Cast,
    /// mem[addr:addr+size@endian <- rhs]
    Store,
    /// var
    Var,
    /// let var = rhs in exp
    Let,
    /// if (exp) {lhs} else {rhs}
    ITE,
    /// value
    Int,
    /// lhs ++ rhs
    Concat,
    /// exp[lobit:hibit]
    Extract,
    /// lhs binop rhs
    BinOp,
}

impl ExpressionTag {
    fn from_bap(tag: bap_sys::bap_exp_tag_t) -> Option<ExpressionTag> {
        use bap_sys::bap_exp_tag_t::*;
        use self::ExpressionTag::*;
        match tag {
            BAP_EXP_TAG_INVALID => None,
            BAP_EXP_TAG_UNOP => Some(UnOp),
            BAP_EXP_TAG_LOAD => Some(Load),
            BAP_EXP_TAG_UNKNOWN => Some(Unknown),
            BAP_EXP_TAG_CAST => Some(Cast),
            BAP_EXP_TAG_STORE => Some(Store),
            BAP_EXP_TAG_VAR => Some(Var),
            BAP_EXP_TAG_LET => Some(Let),
            BAP_EXP_TAG_ITE => Some(ITE),
            BAP_EXP_TAG_INT => Some(Int),
            BAP_EXP_TAG_CONCAT => Some(Concat),
            BAP_EXP_TAG_EXTRACT => Some(Extract),
            BAP_EXP_TAG_BINOP => Some(BinOp),
        }
    }
}

/// Unary Operations
#[derive(Copy, Clone, Debug, Hash, PartialEq, PartialOrd)]
#[cfg_attr(feature = "json", derive(RustcEncodable, RustcDecodable))]
pub enum UnOp {
    /// Bitwise not
    Not,
    /// Numeric negation
    Neg,
}

impl UnOp {
    fn from_bap(op: bap_sys::bap_unop_t) -> Option<UnOp> {
        use bap_sys::bap_unop_t::*;
        use self::UnOp::*;
        match op {
            BAP_UNOP_INVALID => None,
            BAP_UNOP_NOT => Some(Not),
            BAP_UNOP_NEG => Some(Neg),
        }
    }
}

/// Binary Operations
#[derive(Copy, Clone, Debug, Hash, PartialEq, PartialOrd)]
#[cfg_attr(feature = "json", derive(RustcEncodable, RustcDecodable))]
pub enum BinOp {
    /// Signed less than or equal
    SignedLessEqual,
    /// Signed less than
    SignedLess,
    /// Unsigned less than or equal
    LessEqual,
    /// Unsigned less than
    Less,
    /// Not equal
    NotEqual,
    /// Equal
    Equal,
    /// Bitwise exclusive or
    Xor,
    /// Bitwise or
    Or,
    /// Bitwise and
    And,
    /// Arithmetic right shift (preserve sign bit)
    ArithmeticRightShift,
    /// Right shift
    RightShift,
    /// Left shift
    LeftShift,
    /// Signed modulo/rem
    SignedModulo,
    /// Modulo
    Modulo,
    /// Signed division
    SignedDivide,
    /// Unsigned division
    Divide,
    /// Multiplication
    Multiply,
    /// Subtraction
    Subtract,
    /// Addition
    Add,
}

impl BinOp {
    fn from_bap(op: bap_sys::bap_binop_t) -> Option<Self> {
        use self::BinOp::*;
        use bap_sys::bap_binop_t::*;
        match op {
            BAP_BINOP_INVALID => None,
            BAP_BINOP_SLE => Some(SignedLessEqual),
            BAP_BINOP_SLT => Some(SignedLess),
            BAP_BINOP_LT => Some(Less),
            BAP_BINOP_LE => Some(LessEqual),
            BAP_BINOP_NEQ => Some(NotEqual),
            BAP_BINOP_EQ => Some(Equal),
            BAP_BINOP_XOR => Some(Xor),
            BAP_BINOP_OR => Some(Or),
            BAP_BINOP_AND => Some(And),
            BAP_BINOP_ARSHIFT => Some(ArithmeticRightShift),
            BAP_BINOP_RSHIFT => Some(RightShift),
            BAP_BINOP_LSHIFT => Some(LeftShift),
            BAP_BINOP_SMOD => Some(SignedModulo),
            BAP_BINOP_MOD => Some(Modulo),
            BAP_BINOP_SDIVIDE => Some(SignedDivide),
            BAP_BINOP_DIVIDE => Some(Divide),
            BAP_BINOP_TIMES => Some(Multiply),
            BAP_BINOP_MINUS => Some(Subtract),
            BAP_BINOP_PLUS => Some(Add),
        }
    }
}

/// BIL Cast kinds
#[derive(Copy, Clone, Debug, Hash, PartialEq, PartialOrd)]
#[cfg_attr(feature = "json", derive(RustcEncodable, RustcDecodable))]
pub enum Cast {
    /// Cast prefers low bits
    Low,
    /// Cast prefers high bits
    High,
    /// Sign-preserving least significant
    Signed,
    /// Sign-ignoring least significant
    Unsigned,
}

impl Cast {
    fn from_bap(cast: bap_sys::bap_cast_t) -> Option<Self> {
        use bap_sys::bap_cast_t::*;
        use self::Cast::*;
        match cast {
            BAP_CAST_INVALID => None,
            BAP_CAST_LOW => Some(Low),
            BAP_CAST_HIGH => Some(High),
            BAP_CAST_SIGNED => Some(Signed),
            BAP_CAST_UNSIGNED => Some(Unsigned),
        }
    }
}

/// Byte order
#[derive(Copy, Clone, Debug, Hash, PartialEq, PartialOrd)]
#[cfg_attr(feature = "json", derive(RustcEncodable, RustcDecodable))]
pub enum Endian {
    /// Least significant first
    Little,
    /// Most significant first
    Big,
}

impl Endian {
    fn from_bap(endian: bap_sys::bap_endian_t) -> Option<Self> {
        use bap_sys::bap_endian_t::*;
        use self::Endian::*;
        match endian {
            BAP_ENDIAN_INVALID => None,
            BAP_ENDIAN_LITTLE => Some(Little),
            BAP_ENDIAN_BIG => Some(Big),
        }
    }
}

impl<'a> Expression<'a> {
    /// Get the tag indicating what kind of expression this is
    pub fn tag(&self) -> Option<ExpressionTag> {
        ExpressionTag::from_bap(unsafe { bap_sys::bap_exp_tag(self.bap_sys) })
    }
    /// Gets the memory argument for the expression, if present
    pub fn mem(&self) -> Option<Expression> {
        unsafe {
            bap_option(bap_sys::bap_exp_mem(self.bap_sys)).map(|exp| {
                Expression {
                    bap_sys: exp,
                    rc: rc1(),
                    extra: PhantomData,
                }
            })
        }
    }
    /// Gets the size of a memory read/write for the expression, if present
    pub fn size(&self) -> Option<BitSize> {
        bap_opt_int(unsafe { bap_sys::bap_exp_size(self.bap_sys) })
    }
    /// Gets the address argument for the expression, if present
    pub fn addr(&self) -> Option<Expression> {
        unsafe {
            bap_option(bap_sys::bap_exp_addr(self.bap_sys)).map(|exp| {
                Expression {
                    bap_sys: exp,
                    rc: rc1(),
                    extra: PhantomData,
                }
            })
        }
    }
    /// Gets the expression argument for the expression, if present
    pub fn exp(&self) -> Option<Expression> {
        unsafe {
            bap_option(bap_sys::bap_exp_exp(self.bap_sys)).map(|exp| {
                Expression {
                    bap_sys: exp,
                    rc: rc1(),
                    extra: PhantomData,
                }
            })
        }
    }
    /// Gets the variable argument of the BIL statement, if present
    pub fn var(&self) -> Option<Variable> {
        unsafe {
            bap_option(bap_sys::bap_exp_var(self.bap_sys)).map(|var| {
                Variable {
                    bap_sys: var,
                    rc: rc1(),
                    extra: PhantomData,
                }
            })
        }
    }

    /// Gets the left hand side for the expression, if present
    pub fn lhs(&self) -> Option<Expression> {
        unsafe {
            bap_option(bap_sys::bap_exp_lhs(self.bap_sys)).map(|exp| {
                Expression {
                    bap_sys: exp,
                    rc: rc1(),
                    extra: PhantomData,
                }
            })
        }
    }
    /// Gets the right hand side for the expression, if present
    pub fn rhs(&self) -> Option<Expression> {
        unsafe {
            bap_option(bap_sys::bap_exp_rhs(self.bap_sys)).map(|exp| {
                Expression {
                    bap_sys: exp,
                    rc: rc1(),
                    extra: PhantomData,
                }
            })
        }
    }
    /// Gets the unary operation for the expression, if present
    pub fn unop(&self) -> Option<UnOp> {
        unsafe { UnOp::from_bap(bap_sys::bap_exp_unop(self.bap_sys)) }
    }
    /// Gets the binary operation for the statement, if present
    pub fn binop(&self) -> Option<BinOp> {
        unsafe { BinOp::from_bap(bap_sys::bap_exp_binop(self.bap_sys)) }
    }
    /// Gets the cast kind for the statement, if present
    pub fn cast(&self) -> Option<Cast> {
        unsafe { Cast::from_bap(bap_sys::bap_exp_cast(self.bap_sys)) }
    }
    /// Gets the value for the expression, if present
    pub fn value(&self) -> Option<Word> {
        unsafe {
            bap_option(bap_sys::bap_exp_value(self.bap_sys)).map(|value| {
                Word {
                    bap_sys: value,
                    rc: rc1(),
                    extra: PhantomData,
                }
            })
        }
    }
    /// Gets the target width of the cast, if present
    pub fn cast_size(&self) -> Option<BitSize> {
        bap_opt_int(unsafe { bap_sys::bap_exp_cast_size(self.bap_sys) })
    }
    /// Gets the low bit of the extraction, if present
    pub fn extract_lobit(&self) -> Option<BitSize> {
        bap_opt_int(unsafe { bap_sys::bap_exp_extract_lobit(self.bap_sys) })
    }
    /// Gets the high bit of the extraction, if present
    pub fn extract_hibit(&self) -> Option<BitSize> {
        bap_opt_int(unsafe { bap_sys::bap_exp_extract_hibit(self.bap_sys) })
    }
    /// Gets the endianness of a store or load, if present
    pub fn endian(&self) -> Option<Endian> {
        Endian::from_bap(unsafe { bap_sys::bap_exp_endian(self.bap_sys) })
    }
    /// Gets the description of an unknown expression, if present
    pub fn unknown_msg(&self) -> Option<String> {
        unsafe { bap_option(bap_sys::bap_exp_unknown_msg(self.bap_sys)).map(|msg| bap_string(msg)) }
    }
    /// Gets the type of an unknown expression, if present
    pub fn unknown_type(&self) -> Option<Type> {
        unsafe {
            bap_option(bap_sys::bap_exp_unknown_typ(self.bap_sys)).map(|type_| {
                Type {
                    bap_sys: type_,
                    rc: rc1(),
                    extra: PhantomData,
                }
            })
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
/// Which kind of type a BAP `Type` is
pub enum TypeTag {
    /// Type represents a memory object mapping addresses to values
    Memory,
    /// Type represents an immediate vector of bits
    Immediate,
}

impl TypeTag {
    fn from_bap(tag: bap_sys::bap_type_tag_t) -> Option<Self> {
        use bap_sys::bap_type_tag_t::*;
        use self::TypeTag::*;
        match tag {
            BAP_TYPE_TAG_INVALID => None,
            BAP_TYPE_TAG_MEM => Some(Memory),
            BAP_TYPE_TAG_IMM => Some(Immediate),
        }
    }
}

impl<'a> Type<'a> {
    /// Find out what kind of type this is
    pub fn tag(&self) -> Option<TypeTag> {
        TypeTag::from_bap(unsafe { bap_sys::bap_type_tag(self.bap_sys) })
    }
    /// Get the size of an `Immediate` type in bits
    pub fn imm(&self) -> Option<BitSize> {
        bap_opt_int(unsafe { bap_sys::bap_type_imm_size(self.bap_sys) })
    }
    /// Get the address size for a `Memory` type
    pub fn addr_size(&self) -> Option<BitSize> {
        bap_opt_int(unsafe { bap_sys::bap_type_addr_size(self.bap_sys) })
    }
    /// Get the cell size for a `Memory` type
    pub fn cell_size(&self) -> Option<BitSize> {
        bap_opt_int(unsafe { bap_sys::bap_type_value_size(self.bap_sys) })
    }
}

impl<'a> Variable<'a> {
    /// Get the variable's name
    pub fn name(&self) -> String {
        unsafe { bap_string(bap_sys::bap_var_name(self.bap_sys)) }
    }
    /// Get the variable's type
    pub fn type_(&self) -> Type {
        Type {
            bap_sys: unsafe { bap_sys::bap_var_type(self.bap_sys) },
            rc: rc1(),
            extra: PhantomData,
        }
    }
    /// Whether the variable is a temporary
    pub fn is_temp(&self) -> bool {
        unsafe { bap_sys::bap_var_is_virtual(self.bap_sys) }
    }
    /// Which definition of the variable this is
    pub fn index(&self) -> u64 {
        (unsafe { bap_sys::bap_var_index(self.bap_sys) }) as u64
    }
}

impl<'a> Memory<'a> {
    /// Get the beginning of the memory
    pub fn min_addr(&self) -> Word<'a> {
        Word {
            bap_sys: unsafe { bap_sys::bap_memory_min_addr(self.bap_sys) },
            rc: rc1(),
            extra: PhantomData,
        }
    }
    /// Get the end of the memory
    pub fn max_addr(&self) -> Word<'a> {
        Word {
            bap_sys: unsafe { bap_sys::bap_memory_max_addr(self.bap_sys) },
            rc: rc1(),
            extra: PhantomData,
        }
    }
    /// Get the length of the memory
    pub fn len(&self) -> usize {
        (unsafe { bap_sys::bap_memory_length(self.bap_sys) }) as usize
    }
    /// Get the data backing the memory
    pub fn data(&self) -> Vec<u8> {
        unsafe {
            let len = self.len();
            // Returned pointer is borrowed, don't free it
            let data = bap_sys::bap_memory_data(self.bap_sys) as *mut u8;
            slice::from_raw_parts(data, len).to_owned()
        }
    }
}

pub fn roots<'a>(data: &[u8]) -> Vec<Word<'a>> {
    unsafe {
        // This is actually very bad - currently, the C-bindings force me to construct an
        // entire project to access a rooter. However, project construction risks overhead from
        // random analyses, so this can't be allowed to stay.
        let rooter_source = bap_sys::bap_rooter_factory_find("byteweight".as_ptr() as *mut i8);
        let mut proj_args = bap_sys::bap_project_parameters_t {
            rooter: rooter_source,
            reconstructor: null_mut(),
            brancher: null_mut(),
            symbolizer: null_mut(),
            // Spelling error, but it also occurs in bap_bindings, so we just have to deal with
            // it
            disassember: null_mut(),
        };
        // Evidently bap projects refuse to load from anywhere other than disk. FML
        let bap_temp = ::mktemp::Temp::new_file().unwrap();
        {
            use std::io::Write;
            let mut bap_fd = ::std::fs::File::create(&bap_temp).unwrap();
            bap_fd.write(data).unwrap();
        }
        let bap_path_buf = bap_temp.to_path_buf();
        //NORELEASE leaks memory
        let proj_input = bap_sys::bap_project_input_file(
            bap_path_buf.to_str().unwrap().as_ptr() as *mut i8,
            null_mut(),
        );
        let proj = bap_error(bap_sys::bap_project_create(
            proj_input,
            (&mut proj_args) as *mut bap_sys::bap_project_parameters_t,
        )).unwrap();
        let symtab = bap_sys::bap_project_symbols(proj);
        let seq = bap_sys::bap_symbtab_enum(symtab);
        let seq_iter = bap_sys::bap_symbtab_fn_seq_iterator_create(seq);
        let mut out = Vec::new();
        while bap_sys::bap_symbtab_fn_seq_iterator_has_next(seq_iter) {
            out.push(Word {
                bap_sys: bap_sys::bap_block_addr(bap_sys::bap_symtab_fn_entry(
                    bap_sys::bap_symbtab_fn_seq_iterator_next(seq_iter),
                )),
                rc: rc1(),
                extra: PhantomData,
            })


        }
        out
    }
}
