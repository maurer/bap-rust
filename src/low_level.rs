use raw;
use raw::size_t;
use std::sync::{Once, ONCE_INIT};
use std::marker::PhantomData;
use num::FromPrimitive;
use std::ffi::CStr;

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
    unsafe {assert!(raw::bap_thread_unregister() != 0)}
  }
}

unsafe fn bap_free<T>(arg : *mut T) {
  raw::bap_free(arg as *mut ::libc::c_void)
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
      assert!(raw::bap_thread_register() != 0);
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

pub struct Segment {
  pub name : String,
  pub r : bool,
  pub w : bool,
  pub x : bool,
  pub mem : MemRegion
}

impl Segment {
  pub fn from_file_contents(_ctx : &Context, contents : &[u8]) -> Vec<Self> {
    unsafe {
      let raw_segs = raw::bap_get_segments(
        contents.as_ptr() as *mut ::libc::c_char,
        contents.len() as size_t);
      let mut index = 0;
      let mut res = Vec::new();
      while !(*raw_segs.offset(index)).is_null() {
        {
          let cur = &(**raw_segs.offset(index));
          res.push(Segment {
            name : (String::from_utf8_lossy(CStr::from_ptr(cur.name).to_bytes()))
                     .into_owned(),
            r    : cur.r != 0,
            w    : cur.w != 0,
            x    : cur.x != 0,
            mem  : MemRegion::of_bap(cur.mem),
          });
        }
        bap_free(*raw_segs.offset(index));
        index += 1;
      }
      bap_free(raw_segs);
      res
    }
  }

  pub fn to_string(&self, ctx : &Context) -> String {
    format!("{}|{}{}{}\n{}", self.name,
                             if self.r {"r"} else {""},
                             if self.w {"w"} else {""},
                             if self.x {"x"} else {""},
                             self.mem.to_string(ctx))
  }
}

#[test]
fn extract_arch() {
  let x86_buf = include_bytes!("../test_data/elf_x86");
  let x86_64_buf = include_bytes!("../test_data/elf_x86_64");
  with_bap(|ctx| {
    assert_eq!(Arch::ll_from_file_contents(x86_buf, &ctx), Arch::X86);
    assert_eq!(Arch::ll_from_file_contents(x86_64_buf, &ctx), Arch::X86_64);
  })
}

#[test]
fn extract_segments() {
  let buf = include_bytes!("../test_data/elf_x86");
  with_bap(|ctx| {
    let segs = Segment::from_file_contents(&ctx, buf);
    assert_eq!(segs.len(), 2);
    assert!(segs[0].r);
    assert!(!segs[0].w);
    assert!(segs[0].x);
    assert!(segs[1].r);
    assert!(!segs[1].x);
    assert!(segs[1].w);
  })
}

pub struct Symbol {
  pub name  : String,
  pub func  : bool,
  pub debug : bool,
  pub start : Addr,
  pub end   : Option<Addr>
}

impl Symbol {
  pub fn from_file_contents(_ctx : &Context, contents : &[u8]) -> Vec<Self> {
    unsafe {
      let raw_syms = raw::bap_get_symbols(
        contents.as_ptr() as *mut ::libc::c_char,
        contents.len() as size_t);
      let mut index = 0;
      let mut res = Vec::new();
      while !(*raw_syms.offset(index)).is_null() {
        {
          let cur = &(**raw_syms.offset(index));
          res.push(Symbol {
            name  : (String::from_utf8_lossy(CStr::from_ptr(cur.name).to_bytes()))
                     .into_owned(),
            func  : cur.func != 0,
            debug : cur.debug != 0,
            start : BitVector::of_bap(cur.start),
            end   : Some(BitVector::of_bap(cur.end)),
          });
        }
        bap_free(*raw_syms.offset(index));
        index += 1;
      }
      bap_free(raw_syms);
      res
    }
  }
  pub fn byteweight(ctx : &Context, arch : Arch, mem : &MemRegion) -> Vec<Self> {
    unsafe {
      let raw_addrs = raw::bap_byteweight(arch.to_bap(), mem.raw);
      let mut index = 0;
      let mut res = Vec::new();
      while !(*raw_addrs.offset(index)).is_null() {
        {
          let cur = *raw_addrs.offset(index);
          let addr = BitVector::of_bap(cur);
          let name = format!("byteweight_{}", addr.to_string(ctx));
          res.push(Symbol {
            name  : name,
            func  : true,
            debug : false,
            start : addr,
            end   : None,
          });
        }
        index += 1;
      }
      bap_free(raw_addrs);
      res
    }
  }
  pub fn to_string(&self, ctx : &Context) -> String {
    format!("{}|{},{}|{}->{}", self.name,
                             if self.func {"func"} else {"data"},
                             if self.debug {"debug"} else {"nodebug"},
                             self.start.to_string(ctx),
                             match self.end {
                               Some(ref end) => end.to_string(ctx),
                               None => "?".to_string()
                             })
  }
}

#[test]
fn extract_symbols() {
  let buf = include_bytes!("../test_data/elf_x86");
  with_bap(|ctx| {
    let syms = Symbol::from_file_contents(&ctx, buf);
    let main_sym = syms.iter().filter(|x| {x.name == "main"}).next().unwrap();
    let f_sym = syms.iter().filter(|x| {x.name == "f"}).next().unwrap();
    assert!(main_sym.func);
    assert!(f_sym.func);
  })
}

#[test]
fn run_byteweight() {
  let buf = include_bytes!("../test_data/elf_x86");
  with_bap(|ctx| {
    let segs = Segment::from_file_contents(&ctx, buf);
    let _syms : Vec<Symbol> = segs.iter().flat_map(|seg| {Symbol::byteweight(&ctx, Arch::X86, &seg.mem)}).collect();
  })
}

#[derive(Copy, Clone)]
pub enum Endian {
  Little,
  Big
}

#[allow(non_camel_case_types)]
#[derive(Copy, Clone, PartialEq, Debug)]
pub enum Arch {
  ARM,
  X86,
  X86_64
}

impl Arch {
  fn to_bap(&self) -> raw::bap_arch {
    use self::Arch::*;
    use raw::Enum_bap_arch::*;
    match *self {
      ARM    => BAP_ARM,
      X86    => BAP_X86,
      X86_64 => BAP_X86_64
    }
  }
  fn of_bap(raw : raw::bap_arch) -> Self {
    use self::Arch::*;
    use raw::Enum_bap_arch::*;
    match raw {
      BAP_ARM    => ARM,
      BAP_X86    => X86,
      BAP_X86_64 => X86_64
    }
  }
  pub fn ll_from_file_contents(contents : &[u8], _ctx : &Context) -> Self {
    Self::of_bap(unsafe {
      raw::bap_get_arch(contents.as_ptr() as *mut ::libc::c_char,
                        contents.len() as size_t)
    })
  }
  pub fn from_file_contents(contents : &[u8]) -> Self {
    with_bap(|ctx|{Arch::ll_from_file_contents(contents, &ctx)})
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
    use raw::Enum_bap_type_kind::*;
    let mut typ = *typ;
    match typ.kind {
      BAP_TYPE_IMM => Type::BitVector(*typ.imm() as BitSize),
      BAP_TYPE_MEM => Type::Memory {
          addr_size : (*typ.mem()).addr_size as BitSize,
          cell_size : (*typ.mem()).cell_size as BitSize
      },
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
    use raw::Enum_bap_expr_kind::*;
    let mut expr = *expr;
    match expr.kind {
      BAP_EXPR_LOAD    => Expr::Load {
        memory : Box::new(Expr::of_bap((*expr.load()).memory)),
        index  : Box::new(Expr::of_bap((*expr.load()).index)),
        endian : Endian::of_bap((*expr.load()).endian),
        size   : (*expr.load()).size as BitSize
      },
      BAP_EXPR_STORE   => Expr::Store {
        memory : Box::new(Expr::of_bap((*expr.store()).memory)),
        index  : Box::new(Expr::of_bap((*expr.store()).index)),
        value  : Box::new(Expr::of_bap((*expr.store()).value)),
        endian : Endian::of_bap((*expr.store()).endian),
        size   : (*expr.store()).size as BitSize
      },
      BAP_EXPR_BINOP   => Expr::BinOp {
        op  : BinOp::from_u32((*expr.binop()).op as u32).unwrap(),
        lhs : Box::new(Expr::of_bap((*expr.binop()).lhs)),
        rhs : Box::new(Expr::of_bap((*expr.binop()).rhs))
      },
      BAP_EXPR_UNOP    => Expr::UnOp {
        op  : UnOp::from_u32((*expr.unop()).op as u32).unwrap(),
        arg : Box::new(Expr::of_bap((*expr.unop()).arg))
      },
      BAP_EXPR_VAR     => Expr::Var(Var::of_bap(*expr.var())),
      BAP_EXPR_IMM     => Expr::BitVector(BitVector::of_bap(*expr.imm())),
      BAP_EXPR_CAST    => Expr::Cast {
        kind  : CastKind::from_u32((*expr.cast())._type as u32).unwrap(),
        width : (*expr.cast()).width as BitSize,
        val   : Box::new(Expr::of_bap((*expr.cast()).val))
      },
      BAP_EXPR_LET     => Expr::Let {
        bound_var  : Var::of_bap((*expr._let()).bound_var),
        bound_expr : Box::new(Expr::of_bap((*expr._let()).bound_expr)),
        body_expr  : Box::new(Expr::of_bap((*expr._let()).body_expr))
      },
      BAP_EXPR_UNK     => Expr::Unknown {
        description :
          String::from_utf8_lossy(
            ::std::ffi::CStr::from_ptr((*expr.unknown()).descr).to_bytes())
          .into_owned(),
        typ : Type::of_bap((*expr.unknown())._type)
      },
      BAP_EXPR_ITE     => Expr::IfThenElse {
        cond         : Box::new(Expr::of_bap((*expr.ite()).cond)),
        true_branch  : Box::new(Expr::of_bap((*expr.ite()).t)),
        false_branch : Box::new(Expr::of_bap((*expr.ite()).f))
      },
      BAP_EXPR_EXTRACT => Expr::Extract {
        arg      : Box::new(Expr::of_bap((*expr.extract()).val)),
        high_bit : (*expr.extract()).high_bit as BitSize,
        low_bit  : (*expr.extract()).low_bit as BitSize
      },
      BAP_EXPR_CONCAT  => Expr::Concat {
        low  : Box::new(Expr::of_bap((*expr.concat()).low)),
        high : Box::new(Expr::of_bap((*expr.concat()).high))
      },
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
    use raw::Enum_bap_stmt_kind::*;
    let mut stmt = *stmt;
    match stmt.kind {
      BAP_STMT_MOVE => Stmt::Move {
        lhs : Var::of_bap((*stmt._move()).lhs),
        rhs : Expr::of_bap((*stmt._move()).rhs)
      },
      BAP_STMT_JMP => Stmt::Jump(Expr::of_bap(*stmt.jmp())),
      BAP_STMT_SPECIAL => Stmt::Special(String::from_utf8_lossy(
              CStr::from_ptr(*stmt.special()).to_bytes()).into_owned()),
      BAP_STMT_WHILE => Stmt::While {
          cond : Expr::of_bap((*stmt.s_while()).cond),
          body : Stmt::of_stmts((*stmt.s_while()).body)
      },
      BAP_STMT_IF => Stmt::IfThenElse {
          cond : Expr::of_bap((*stmt.ite()).cond),
          then_clause : Stmt::of_stmts((*stmt.ite()).t),
          else_clause : Stmt::of_stmts((*stmt.ite()).f)
      },
      BAP_STMT_CPU_EXN => Stmt::CPUException(*stmt.cpu_exn() as u64),
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

impl <BV> Stmt<BV> {
  pub fn map_bv<BV2, F>(&self, f : &F) -> Stmt<BV2>
    where F : Fn(&BV) -> BV2 {
    match *self {
      Stmt::Jump(ref e) => Stmt::Jump(e.map_bv(f)),
      Stmt::Special(ref s) => Stmt::Special(s.clone()),
      Stmt::CPUException(n) => Stmt::CPUException(n),
      Stmt::Move {ref lhs, ref rhs} =>
          Stmt::Move {lhs : lhs.clone(),
                      rhs : rhs.map_bv(f)},
      Stmt::While {ref cond, ref body} => Stmt::While
        {cond : cond.map_bv(f),
         body : body.iter().map(|x|{x.map_bv(f)}).collect()},
      Stmt::IfThenElse {ref cond, ref then_clause, ref else_clause} =>
        Stmt::IfThenElse
        {cond        : cond.map_bv(f),
         then_clause : then_clause.iter().map(|x|{x.map_bv(f)}).collect(),
         else_clause : else_clause.iter().map(|x|{x.map_bv(f)}).collect()}
    }
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
      let ptr = raw::bap_bitvector_to_string(self.raw);
      let res = String::from_utf8_lossy(CStr::from_ptr(ptr).to_bytes())
                .into_owned();
      bap_free(ptr);
      res
    }
  }
  unsafe fn of_bap(raw : raw::bap_bitvector) -> Self {
    BitVector { raw : raw }
  }
  pub fn contents(&self, ctx : &Context) -> Vec<u8> {
    unsafe {
      let ptr = raw::bap_bitvector_contents(self.raw);
      let byte_count = {
        let width = self.width(ctx);
        (width / 8) + (if width % 8 != 0 {1} else {0})
      } as isize;
      let mut res = Vec::new();
      for i in 0..byte_count {
        res.push(*(ptr.offset(i)) as u8);
      };
      bap_free(ptr);
      res
    }
  }
  pub fn width(&self, _ctx : &Context) -> BitSize {
    unsafe {raw::bap_bitvector_size(self.raw) as BitSize}
  }
}

impl BigString {
  pub fn new(_ctx : &Context, buf : &[u8]) -> BigString {
    BigString {
      raw : unsafe {
        raw::bap_create_bigstring(buf.as_ptr() as *mut ::libc::c_char,
                                  buf.len() as size_t)
      }
    }
  }
}

impl Endian {
  fn to_bap(&self) -> raw::bap_endian {
    use raw::Enum_bap_endian::*;
    match *self {
      Endian::Little => BAP_LITTLE_ENDIAN,
      Endian::Big    => BAP_BIG_ENDIAN
    }
  }
  fn of_bap(e : raw::bap_endian) -> Self {
    use raw::Enum_bap_endian::*;
    match e {
      BAP_LITTLE_ENDIAN => Endian::Little,
      BAP_BIG_ENDIAN => Endian::Big,
    }
  }
}

pub struct MemLocal {
  pub start : Addr,
  pub end   : Addr,
  pub data  : Vec<u8>
}

impl MemRegion {
  pub fn new(_ctx : &Context,
             bs : &BigString,
             off : usize, len : usize,
             endian : Endian, addr : &Addr) -> Self {
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
      let ptr = raw::bap_mem_to_string(self.raw);
      let res = String::from_utf8_lossy(CStr::from_ptr(ptr).to_bytes())
                .into_owned();
      bap_free(ptr);
      res
    }
  }
  pub fn project(&self, _ctx : &Context) -> MemLocal {
    unsafe {
      let p = &(*raw::bap_project_mem(self.raw));
      MemLocal {
        start : BitVector::of_bap(p.start),
        end   : BitVector::of_bap(p.end),
        data  : ::std::slice::from_raw_parts(p.data, p.len as usize).iter().map(|x| {*x as u8}).collect()
      }
    }
  }
  unsafe fn of_bap(raw : raw::bap_mem) -> Self {
    MemRegion { raw : raw }
  }
}

impl Instruction {
  pub fn to_string(&self, _ctx : &Context) -> String {
    unsafe {
      use std::ffi::CStr;
      let ptr = raw::bap_insn_to_asm(self.raw);
      let res = String::from_utf8_lossy(CStr::from_ptr(ptr).to_bytes())
                .into_owned();
      bap_free(ptr);
      res
    }
  }
  pub fn is_call(&self, _ctx : &Context) -> bool {
    unsafe {
      raw::bap_insn_is_call(self.raw) != 0
    }
  }
  pub fn stmts(&self, _ctx : &Context) -> Vec<Stmt<BitVector>> {
    unsafe {
      let narr = raw::bap_insn_get_stmts(self.raw);
      Stmt::of_stmts(narr)
    }
  }
  unsafe fn of_bap(raw : raw::bap_insn) -> Self {
    Instruction { raw : raw }
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
      let ptr = raw::bap_disasm_to_string(self.raw);
      let res = String::from_utf8_lossy(CStr::from_ptr(ptr).to_bytes())
                .into_owned();
      bap_free(ptr);
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
          start : BitVector::of_bap((**narr.offset(index)).start),
          end   : BitVector::of_bap((**narr.offset(index)).end),
          insn  : Instruction::of_bap((**narr.offset(index)).insn)
        });
        bap_free(*narr.offset(index));
        index += 1;
      }
      bap_free(narr);
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
    assert_eq!(&disas.to_string(&ctx), "XOR32rr(EAX,EAX,EAX)\nPUSH32r(EAX)\nPUSHi32(0x68732f2f)\nPUSHi32(0x6e69622f)\nMOV32rr(EBX,ESP)\nPUSH32r(EAX)\nPUSH32r(EBX)\nMOV32rr(ECX,ESP)\nCDQ()\nMOV8ri(AL,0xb)\nINT(-0x80)\n")
  })
}

#[test]
fn call_or_not() {
  with_bap(|ctx| {
    let base = BitVector::create_64(&ctx, 32, 64);
    {
      let nocall = b"\x31\xc0\x50\x68//sh\x68/bin\x89\xe3\x50\x53\x89\xe1\x99\xb0\x0b\xcd\x80";
      let nocall_bs = BigString::new(&ctx, nocall);
      let nocall_mem = MemRegion::new(&ctx, &nocall_bs, 0, nocall.len(), Endian::Little, &base);
      let nocall_disas = Disasm::mem(&ctx, Vec::new(), Arch::X86, nocall_mem);
      let nocall_insns = nocall_disas.instructions(&ctx);
      assert!(nocall_insns.iter().all(|d_insn| {!d_insn.insn.is_call(&ctx)}));
    }
    {
      let call = b"\xff\xd0";
      let call_bs = BigString::new(&ctx, call);
      let call_mem = MemRegion::new(&ctx, &call_bs, 0, call.len(), Endian::Little, &base);
      let call_disas = Disasm::mem(&ctx, Vec::new(), Arch::X86, call_mem);
      let call_insns = call_disas.instructions(&ctx);
      assert!(call_insns.iter().all(|d_insn| {d_insn.insn.is_call(&ctx)}));
    }
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
