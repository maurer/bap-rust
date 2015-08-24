use raw;
use std::cell::RefCell;
use std::sync::{Once, ONCE_INIT};
use std::marker::PhantomData;

pub struct Context {
  stamp: PhantomData<*const Context>
}

impl Drop for Context {
  fn drop(&mut self) {
    unsafe {assert!(raw::bap_thread_unregister())}
  }
}

thread_local!(static BAP_CTX : RefCell<Option<Context>> = RefCell::new(None));
thread_local!(static BAP_THREAD_REGISTER : Once = ONCE_INIT);
static BAP_INIT : Once = ONCE_INIT;

pub fn with_bap<A, F>(f : F) -> A
  where F : Fn(&Context) -> A {
  BAP_THREAD_REGISTER.with(|t| {
    let t = unsafe {
      //with has too tight a bound on the functions, cast the reference
      ::std::mem::transmute::<&Once, &'static Once>(t)
    };
    t.call_once(|| {
      BAP_INIT.call_once(|| {
        unsafe {
          raw::bap_init();
          raw::bap_release();
        }
        BAP_CTX.with(|ctx| {
          *ctx.borrow_mut() = Some(Context { stamp : PhantomData });
        })
      });
      BAP_CTX.with(|ctx| {
        let mut r = ctx.borrow_mut();
        match *r {
          Some(_) => (),
          None => {
            unsafe {assert!(raw::bap_thread_register())};
            *r = Some(Context { stamp : PhantomData })
          }
        }
      })
    })
  });
  BAP_CTX.with(|ctx| {
    match *ctx.borrow() {
      Some(ref c) => {
        unsafe {raw::bap_acquire()};
        let r = f(c);
        unsafe {raw::bap_release()};
        r
      },
      None    => panic!("Empty context?")
    }
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
}

#[test]
fn create_and_print_bitvector() {
  with_bap(|ctx| {
    assert_eq!(&BitVector::create_64(ctx, 37, 9).to_string(ctx),
               "0x25:9")
  })
}

#[test]
fn create_and_print_mem() {
  with_bap(|ctx| {
    let base = BitVector::create_64(ctx, 32, 64);
    let shell = b"\x31\xc0\x50\x68//sh\x68/bin\x89\xe3\x50\x53\x89\xe1\x99\xb0\x0b\xcd\x80";
    let bs = BigString::new(ctx, shell);
    let mem = MemRegion::new(ctx, &bs, 0, shell.len(), Endian::Little, &base);
    ()
  })
}
