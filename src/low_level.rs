use raw;
use std::sync::{Once, ONCE_INIT};
use std::marker::PhantomData;

pub struct Context {
  stamp: PhantomData<*const Context>
}

impl Drop for Context {
  fn drop(&mut self) {
    unsafe {raw::bap_release()}
  }
}

struct ThreadContext {
  stamp: PhantomData<*const ThreadContext>
}

impl Drop for ThreadContext {
  fn drop(&mut self) {
    unsafe {assert!(raw::bap_thread_unregister())}
  }
}

impl ThreadContext {
  fn lock(&self) -> Context {
    unsafe {raw::bap_acquire()}
    Context { stamp : PhantomData }
  }
  unsafe fn init() -> Self {
    let mut bap_init_ran = false;
    BAP_INIT.call_once(|| {
      raw::bap_init();
      raw::bap_release();
      bap_init_ran = true;
    });
    if !bap_init_ran {
      assert!(raw::bap_thread_register());
    }
    ThreadContext { stamp : PhantomData }
  }
}


thread_local!(static BAP_CTX : ThreadContext = unsafe {ThreadContext::init()});
static BAP_INIT : Once = ONCE_INIT;

pub fn with_bap<A, F>(f : F) -> A
  where F : Fn(Context) -> A {
 BAP_CTX.with(|ctx| {
    f(ctx.lock())
  })
}

macro_rules! abs_type {
  ($name:ident, $c_name:ident, $c_free_name:ident, $cap_name:ident) => {
    pub struct $cap_name {
      raw : raw::$c_name
    }
    impl Drop for $cap_name {
      fn drop(&mut self) ->() {
        unsafe {
          raw::$c_free_name(self.raw);
        }
      }
    }
  };
}

abs_type!(disasm, bap_disasm, bap_free_disasm, Disasm);
abs_type!(mem, bap_mem, bap_free_mem, MemRegion);
abs_type!(bitvector, bap_bitvector, bap_free_bitvector, BitVector);
pub type Addr = BitVector;
abs_type!(insn, bap_insn, bap_free_insn, Instruction);
abs_type!(bigstring, bap_bigstring, bap_free_bigstring, BigString);

pub struct DisasmInsn {
  pub start : Addr,
  pub end   : Addr,
  pub insn  : Instruction
}

impl DisasmInsn {
  pub fn to_string(&self, ctx : &Context) -> String {
    format!("{} -> {}: {}", self.start.to_string(ctx),
                            self.end.to_string(ctx),
                            self.insn.to_string(ctx))
  }
}

pub enum Endian {
  Little,
  Big
}

#[allow(non_camel_case_types)]
pub enum Arch {
  ARM,
  X86,
  X86_64
}

impl Arch {
  fn to_bap(&self) -> raw::bap_arch {
    use self::Arch::*;
    match *self {
      ARM    => raw::BAP_ARM,
      X86    => raw::BAP_X86,
      X86_64 => raw::BAP_X86_64
    }
  }
}

pub type BitSize = u16;

pub enum Type {
  BitVector(BitSize),
  Memory{addr_size : BitSize, cell_size : BitSize}
}

pub struct Var {
  pub name    : String,
  pub typ     : Type,
  pub tmp     : bool,
  pub version : i64,
}

pub enum BinOp {
  Plus,
  Minus,
  Times,
  Divide,
  SignedDivide,
  Modulo,
  SignedModulo,
  LeftShift,
  RightShift,
  ArithmeticRightShift,
  And,
  Or,
  Xor,
  Equal,
  NotEqual,
  LessThan,
  LessThanEqual,
  SignedLessThan,
  SignedLessThanEqual
}

pub enum UnOp {
  ArithmeticNegation,
  BinaryNegation
}

pub enum CastKind {
  Unsigned,
  Signed,
  HighBits,
  LowBits
}

pub enum Expr {
  Var(Var),
  BitVector(BitVector),
  Load       {memory       : Box<Expr>,
              index        : Box<Expr>,
              value        : Box<Expr>,
              endian       : Endian,
              size         : BitSize},
  Store      {memory       : Box<Expr>,
              index        : Box<Expr>,
              value        : Box<Expr>,
              endian       : Endian,
              size         : BitSize},
  BinOp      {op           : BinOp,
              lhs          : Box<Expr>,
              rhs          : Box<Expr>},
  UnOp       {op           : UnOp,
              arg          : Box<Expr>},
  Cast       {kind         : CastKind,
              width        : BitSize,
              val          : Box<Expr>},
  Let        {bound_var    : Var,
              bound_expr   : Box<Expr>,
              body_expr    : Box<Expr>},
  Unknown    {description  : String,
              typ          : Type},
  IfThenElse {cond         : Box<Expr>,
              true_branch  : Box<Expr>,
              false_branch : Box<Expr>},
  Extract    {low_bit      : BitSize,
              high_bit     : BitSize,
              arg          : Box<Expr>},
  Concat     {low          : BitSize,
              high         : BitSize}
}

pub enum Stmt {
  Jump(Expr),
  Special(String),
  CPUException(u64),
  Move       {lhs         : Var,
              rhs         : Expr},
  While      {cond        : Expr,
              body        : Vec<Stmt>},
  IfThenElse {cond        : Expr,
              then_clause : Vec<Stmt>,
              else_clause : Vec<Stmt>}
}

impl BitVector {
  pub fn create_64(_ctx : &Context, val : u64, width : BitSize) -> Self {
    unsafe {
      BitVector {raw : raw::bap_create_bitvector64(val as i64, width as i16)}
    }
  }
  pub fn to_string(&self, _ctx : &Context) -> String {
    unsafe {
      use std::ffi::CStr;
      use libc::types::common::c95::c_void;
      let ptr = raw::bap_bitvector_to_string(self.raw);
      let res = String::from_utf8_lossy(CStr::from_ptr(ptr).to_bytes())
                .into_owned();
      raw::bap_free(ptr as *mut c_void);
      res
    }
  }
}

impl BigString {
  pub fn new(_ctx : &Context, buf : &[u8]) -> BigString {
    BigString {
      raw : unsafe {
        raw::bap_create_bigstring(buf.as_ptr(),
                                  buf.len() as raw::bindings_compat::size_t)
      }
    }
  }
}

impl Endian {
  fn to_bap(&self) -> raw::bap_endian {
    match *self {
      Endian::Little => raw::BAP_LITTLE_ENDIAN,
      Endian::Big    => raw::BAP_BIG_ENDIAN
    }
  }
}

impl MemRegion {
  pub fn new(_ctx : &Context,
             bs : &BigString,
             off : usize, len : usize,
             endian : Endian, addr : &Addr) -> MemRegion {
    use raw::bindings_compat::size_t;
    MemRegion {
      raw : unsafe {
        raw::bap_create_mem(off as size_t,
                            len as size_t,
                            endian.to_bap(),
                            addr.raw,
                            bs.raw)
      }
    }
  }
  pub fn to_string(&self, _ctx : &Context) -> String {
    unsafe {
      use std::ffi::CStr;
      use libc::types::common::c95::c_void;
      let ptr = raw::bap_mem_to_string(self.raw);
      let res = String::from_utf8_lossy(CStr::from_ptr(ptr).to_bytes())
                .into_owned();
      raw::bap_free(ptr as *mut c_void);
      res
    }
  }
}

impl Instruction {
  pub fn to_string(&self, _ctx : &Context) -> String {
    unsafe {
      use std::ffi::CStr;
      use libc::types::common::c95::c_void;
      let ptr = raw::bap_insn_to_asm(self.raw);
      let res = String::from_utf8_lossy(CStr::from_ptr(ptr).to_bytes())
                .into_owned();
      raw::bap_free(ptr as *mut c_void);
      res
    }
  }
}



impl Disasm {
  pub fn mem(_ctx  : &Context,
             roots : Vec<Addr>,
             arch  : Arch,
             mem   : MemRegion) -> Self {
    Disasm {
      raw : unsafe {
        let mut roots_backing = Vec::new();
        let roots_ptr = if roots.len() == 0 {
            ::std::ptr::null_mut()
          } else {
            for root in roots {
              roots_backing.push(root.raw);
            }
            roots_backing.push(::std::ptr::null_mut());
            roots_backing.as_mut_ptr()
          };
        raw::bap_disasm_mem(roots_ptr,
                            arch.to_bap(),
                            mem.raw)
      }
    }
  }
  pub fn to_string(&self, _ctx : &Context) -> String {
    unsafe {
      use std::ffi::CStr;
      use libc::types::common::c95::c_void;
      let ptr = raw::bap_disasm_to_string(self.raw);
      let res = String::from_utf8_lossy(CStr::from_ptr(ptr).to_bytes())
                .into_owned();
      raw::bap_free(ptr as *mut c_void);
      res
    }
  }
  pub fn instructions(&self, _ctx : &Context) -> Vec<DisasmInsn> {
    unsafe {
      let narr = raw::bap_disasm_get_insns(self.raw);
      let mut index = 0;
      let mut res = Vec::new();
      while !(*narr.offset(index)).is_null() {
        res.push(DisasmInsn {
          start : BitVector { raw : (**narr.offset(index)).start },
          end   : BitVector { raw : (**narr.offset(index)).end },
          insn  : Instruction { raw : (**narr.offset(index)).insn}
        });
        index += 1;
      }
      res
    }
  }
}

#[test]
fn create_and_print_bitvector() {
  with_bap(|ctx| {
    assert_eq!(&BitVector::create_64(&ctx, 37, 9).to_string(&ctx),
               "0x25:9")
  })
}

#[test]
fn create_and_print_mem() {
  with_bap(|ctx| {
    let base = BitVector::create_64(&ctx, 32, 64);
    let shell = b"\x31\xc0\x50\x68//sh\x68/bin\x89\xe3\x50\x53\x89\xe1\x99\xb0\x0b\xcd\x80";
    let bs = BigString::new(&ctx, shell);
    let mem = MemRegion::new(&ctx, &bs, 0, shell.len(), Endian::Little, &base);
    assert_eq!(&mem.to_string(&ctx), "00000020  31 C0 50 68 2F 2F 73 68 68 2F 62 69 6E 89 E3 50 |1.Ph//shh/bin..P|\n00000030  53 89 E1 99 B0 0B CD 80                         |S.......        |\n")
  })
}

#[test]
fn create_and_disasm_mem() {
  with_bap(|ctx| {
    let base = BitVector::create_64(&ctx, 32, 64);
    let shell = b"\x31\xc0\x50\x68//sh\x68/bin\x89\xe3\x50\x53\x89\xe1\x99\xb0\x0b\xcd\x80";
    let bs = BigString::new(&ctx, shell);
    let mem = MemRegion::new(&ctx, &bs, 0, shell.len(), Endian::Little, &base);
    let disas = Disasm::mem(&ctx, Vec::new(), Arch::X86, mem);
    assert_eq!(&disas.to_string(&ctx), "xorl %eax, %eax; XOR32rr(EAX,EAX,EAX)\npushl %eax; PUSH32r(EAX)\npushl $0x68732f2f; PUSHi32(0x68732f2f)\npushl $0x6e69622f; PUSHi32(0x6e69622f)\nmovl %esp, %ebx; MOV32rr(EBX,ESP)\npushl %eax; PUSH32r(EAX)\npushl %ebx; PUSH32r(EBX)\nmovl %esp, %ecx; MOV32rr(ECX,ESP)\ncltd; CDQ()\nmovb $0xb, %al; MOV8ri(AL,0xb)\nint $-0x80; INT(-0x80)\n")
  })
}

#[test]
fn iter_insns() {
  with_bap(|ctx| {
    let base = BitVector::create_64(&ctx, 32, 64);
    let shell = b"\x31\xc0\x50\x68//sh\x68/bin\x89\xe3\x50\x53\x89\xe1\x99\xb0\x0b\xcd\x80";
    let bs = BigString::new(&ctx, shell);
    let mem = MemRegion::new(&ctx, &bs, 0, shell.len(), Endian::Little, &base);
    let disas = Disasm::mem(&ctx, Vec::new(), Arch::X86, mem);
    let insns = disas.instructions(&ctx);
    assert_eq!(insns[2].to_string(&ctx), "0x23:64 -> 0x27:64: pushl $0x68732f2f")
  })
}
