use raw;
use std::sync::{Once, ONCE_INIT};
use std::marker::PhantomData;
use num::FromPrimitive;

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

#[derive(Copy, Clone)]
pub enum Endian {
  Little,
  Big
}

#[allow(non_camel_case_types)]
#[derive(Copy, Clone)]
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

#[derive(Copy, Clone)]
pub enum Type {
  BitVector(BitSize),
  Memory{addr_size : BitSize, cell_size : BitSize}
}

impl Type {
  unsafe fn of_bap(typ : *mut raw::bap_type) -> Type {
    let mut typ = *typ;
    match typ.kind {
      raw::BAP_TYPE_IMM => Type::BitVector(*typ.imm() as BitSize),
      raw::BAP_TYPE_MEM => Type::Memory {
          addr_size : (*typ.mem()).addr_size as BitSize,
          cell_size : (*typ.mem()).cell_size as BitSize
      },
      x => panic!("Unknown type kind: {}", x)
    }
  }
}

#[derive(Clone)]
pub struct Var {
  pub name    : String,
  pub typ     : Type,
  pub tmp     : bool,
  pub version : u64,
}

impl Var {
  unsafe fn of_bap(var : *mut raw::bap_var) -> Self {
    use std::ffi::CStr;
    let var = *var;
    Var {
      name    : String::from_utf8_lossy(CStr::from_ptr(var.name).to_bytes()).into_owned(),
      typ     : Type::of_bap(var._type),
      tmp     : var.tmp != 0,
      version : var.version as u64
    }
  }
}

enum_from_primitive! {
#[derive(Copy, Clone)]
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
}

enum_from_primitive! {
#[derive(Copy, Clone)]
pub enum UnOp {
  ArithmeticNegation,
  BinaryNegation
}
}

enum_from_primitive! {
#[derive(Copy, Clone)]
pub enum CastKind {
  Unsigned,
  Signed,
  HighBits,
  LowBits
}
}

pub enum Expr<BV> {
  Var(Var),
  BitVector(BV),
  Load       {memory       : Box<Expr<BV>>,
              index        : Box<Expr<BV>>,
              endian       : Endian,
              size         : BitSize},
  Store      {memory       : Box<Expr<BV>>,
              index        : Box<Expr<BV>>,
              value        : Box<Expr<BV>>,
              endian       : Endian,
              size         : BitSize},
  BinOp      {op           : BinOp,
              lhs          : Box<Expr<BV>>,
              rhs          : Box<Expr<BV>>},
  UnOp       {op           : UnOp,
              arg          : Box<Expr<BV>>},
  Cast       {kind         : CastKind,
              width        : BitSize,
              val          : Box<Expr<BV>>},
  Let        {bound_var    : Var,
              bound_expr   : Box<Expr<BV>>,
              body_expr    : Box<Expr<BV>>},
  Unknown    {description  : String,
              typ          : Type},
  IfThenElse {cond         : Box<Expr<BV>>,
              true_branch  : Box<Expr<BV>>,
              false_branch : Box<Expr<BV>>},
  Extract    {low_bit      : BitSize,
              high_bit     : BitSize,
              arg          : Box<Expr<BV>>},
  Concat     {low          : Box<Expr<BV>>,
              high         : Box<Expr<BV>>}
}

impl <BV> Expr<BV> {
  pub fn map_bv<BV2, F>(&self, f : &F) -> Expr<BV2>
    where F : Fn(&BV) -> BV2 {
    match *self {
      Expr::BitVector(ref bv) => Expr::BitVector(f(bv)),
      Expr::Load       {ref memory, ref index, endian, size}
        => Expr::Load {memory : Box::new(memory.map_bv(f)),
                       index  : Box::new(index.map_bv(f)),
                       endian : endian,
                       size   : size},
      Expr::Store      {ref memory, ref index, ref value, endian, size}
        => Expr::Store {memory : Box::new(memory.map_bv(f)),
                        index  : Box::new(index.map_bv(f)),
                        value  : Box::new(value.map_bv(f)),
                        endian : endian,
                        size   : size},
      Expr::BinOp      {op, ref lhs, ref rhs}
        => Expr::BinOp {op  : op,
                        lhs : Box::new(lhs.map_bv(f)),
                        rhs : Box::new(rhs.map_bv(f))},
      Expr::UnOp       {op, ref arg}
        => Expr::UnOp  {op  : op,
                        arg : Box::new(arg.map_bv(f))},
      Expr::Cast       {kind, width, ref val}
        => Expr::Cast  {kind  : kind,
                        width : width,
                        val   : Box::new(val.map_bv(f))},
      Expr::Let        {ref bound_var, ref bound_expr, ref body_expr}
        => Expr::Let   {bound_var  : bound_var.clone(),
                        bound_expr : Box::new(bound_expr.map_bv(f)),
                        body_expr  : Box::new(body_expr.map_bv(f))},
      Expr::IfThenElse {ref cond, ref true_branch, ref false_branch}
        => Expr::IfThenElse
                       {cond         : Box::new(cond.map_bv(f)),
                        true_branch  : Box::new(true_branch.map_bv(f)),
                        false_branch : Box::new(false_branch.map_bv(f))},
      Expr::Extract    {low_bit, high_bit, ref arg}
        => Expr::Extract
                       {low_bit  : low_bit,
                        high_bit : high_bit,
                        arg      : Box::new(arg.map_bv(f))},
      Expr::Concat     {ref low, ref high}
        => Expr::Concat
                       {low  : Box::new(low.map_bv(f)),
                        high : Box::new(high.map_bv(f))},
      Expr::Unknown    {ref description, typ}
        => Expr::Unknown {description : description.clone(),
                          typ         : typ},
      Expr::Var(ref v) => Expr::Var(v.clone())
    }
  }
}

impl Expr<BitVector> {
  unsafe fn of_bap(expr : *mut raw::bap_expr) -> Self {
    let mut expr = *expr;
    match expr.kind {
      raw::BAP_EXPR_LOAD    => Expr::Load {
        memory : Box::new(Expr::of_bap((*expr.load()).memory)),
        index  : Box::new(Expr::of_bap((*expr.load()).index)),
        endian : Endian::of_bap((*expr.load()).endian),
        size   : (*expr.load()).size as BitSize
      },
      raw::BAP_EXPR_STORE   => Expr::Store {
        memory : Box::new(Expr::of_bap((*expr.store()).memory)),
        index  : Box::new(Expr::of_bap((*expr.store()).index)),
        value  : Box::new(Expr::of_bap((*expr.store()).value)),
        endian : Endian::of_bap((*expr.store()).endian),
        size   : (*expr.store()).size as BitSize
      },
      raw::BAP_EXPR_BINOP   => Expr::BinOp {
        op  : BinOp::from_u32((*expr.binop()).op).unwrap(),
        lhs : Box::new(Expr::of_bap((*expr.binop()).lhs)),
        rhs : Box::new(Expr::of_bap((*expr.binop()).rhs))
      },
      raw::BAP_EXPR_UNOP    => Expr::UnOp {
        op  : UnOp::from_u32((*expr.unop()).op).unwrap(),
        arg : Box::new(Expr::of_bap((*expr.unop()).arg))
      },
      raw::BAP_EXPR_VAR     => Expr::Var(Var::of_bap(*expr.var())),
      raw::BAP_EXPR_IMM     => Expr::BitVector(BitVector::of_bap(*expr.imm())),
      raw::BAP_EXPR_CAST    => Expr::Cast {
        kind  : CastKind::from_u32((*expr.cast())._type).unwrap(),
        width : (*expr.cast()).width as BitSize,
        val   : Box::new(Expr::of_bap((*expr.cast()).val))
      },
      raw::BAP_EXPR_LET     => Expr::Let {
        bound_var  : Var::of_bap((*expr._let()).bound_var),
        bound_expr : Box::new(Expr::of_bap((*expr._let()).bound_expr)),
        body_expr  : Box::new(Expr::of_bap((*expr._let()).body_expr))
      },
      raw::BAP_EXPR_UNK     => Expr::Unknown {
        description :
          String::from_utf8_lossy(
            ::std::ffi::CStr::from_ptr((*expr.unknown()).descr).to_bytes())
          .into_owned(),
        typ : Type::of_bap((*expr.unknown())._type)
      },
      raw::BAP_EXPR_ITE     => Expr::IfThenElse {
        cond         : Box::new(Expr::of_bap((*expr.ite()).cond)),
        true_branch  : Box::new(Expr::of_bap((*expr.ite()).t)),
        false_branch : Box::new(Expr::of_bap((*expr.ite()).f))
      },
      raw::BAP_EXPR_EXTRACT => Expr::Extract {
        arg      : Box::new(Expr::of_bap((*expr.extract()).val)),
        high_bit : (*expr.extract()).high_bit as BitSize,
        low_bit  : (*expr.extract()).low_bit as BitSize
      },
      raw::BAP_EXPR_CONCAT  => Expr::Concat {
        low  : Box::new(Expr::of_bap((*expr.concat()).low)),
        high : Box::new(Expr::of_bap((*expr.concat()).high))
      },
      x => panic!("Unknown expr kind {}", x)
    }
  }
}

pub enum Stmt<BV> {
  Jump(Expr<BV>),
  Special(String),
  CPUException(u64),
  Move       {lhs         : Var,
              rhs         : Expr<BV>},
  While      {cond        : Expr<BV>,
              body        : Vec<Stmt<BV>>},
  IfThenElse {cond        : Expr<BV>,
              then_clause : Vec<Stmt<BV>>,
              else_clause : Vec<Stmt<BV>>}
}

impl Stmt<BitVector> {
  unsafe fn of_bap(stmt : *mut raw::bap_stmt) -> Self {
    use std::ffi::CStr;
    let mut stmt = *stmt;
    match stmt.kind {
      raw::BAP_STMT_MOVE => Stmt::Move {
        lhs : Var::of_bap((*stmt._move()).lhs),
        rhs : Expr::of_bap((*stmt._move()).rhs)
      },
      raw::BAP_STMT_JMP => Stmt::Jump(Expr::of_bap(*stmt.jmp())),
      raw::BAP_STMT_SPECIAL => Stmt::Special(String::from_utf8_lossy(
              CStr::from_ptr(*stmt.special()).to_bytes()).into_owned()),
      raw::BAP_STMT_WHILE => Stmt::While {
          cond : Expr::of_bap((*stmt.s_while()).cond),
          body : Stmt::of_stmts((*stmt.s_while()).body)
      },
      raw::BAP_STMT_IF => Stmt::IfThenElse {
          cond : Expr::of_bap((*stmt.ite()).cond),
          then_clause : Stmt::of_stmts((*stmt.ite()).t),
          else_clause : Stmt::of_stmts((*stmt.ite()).f)
      },
      raw::BAP_STMT_CPU_EXN => Stmt::CPUException(*stmt.cpu_exn() as u64),
      n => panic!("Unknown statement type: {}", n)
    }
  }
  unsafe fn of_stmts(stmts : *mut *mut raw::bap_stmt) -> Vec<Self> {
    let mut index = 0;
    let mut res = Vec::new();
    while !(*stmts.offset(index)).is_null() {
      res.push(Stmt::of_bap(*stmts.offset(index)));
      index += 1;
    }
    res
  }
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
  unsafe fn of_bap(raw : raw::bap_bitvector) -> Self {
    BitVector { raw : raw }
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
  fn of_bap(e : raw::bap_endian) -> Self {
    match e {
      raw::BAP_LITTLE_ENDIAN => Endian::Little,
      raw::BAP_BIG_ENDIAN => Endian::Big,
      x => panic!("Unknown endian value: {}", x)
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
  pub fn stmts(&self, _ctx : &Context) -> Vec<Stmt<BitVector>> {
    unsafe {
      let narr = raw::bap_insn_get_stmts(self.raw);
      Stmt::of_stmts(narr)
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
