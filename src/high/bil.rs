//! This module provides utilities for working with a native rust form of BIL
pub use basic::BinOp;
pub use basic::UnOp;
pub use basic::Endian;
pub use basic::Arch;
pub use basic::Cast;
pub use basic::BitSize;
pub use super::bitvector::BitVector;
use basic;

/// Native representation of a BIL statement
#[derive(Debug, Clone, Hash, PartialEq, PartialOrd)]
#[cfg_attr(feature = "json", derive(RustcEncodable, RustcDecodable))]
pub enum Statement {
    /// Transfers control to the address its argument resolves to
    Jump(Expression),
    /// Unmodelable transition
    Special,
    /// Generates a CPU exception of the corresponding number
    CPUException(u64),
    /// Assigns the value of `rhs` to the variable in `lhs`
    Move {
        /// Assignment target (left hand side)
        lhs: Variable,
        /// Assignment value (right hand side)
        rhs: Expression,
    },
    /// If `cond` evaluates to true, repeatedly executes the statements in `body` until `cond` is
    /// false.
    While {
        /// Loop condition
        cond: Expression,
        /// Loop body
        body: Vec<Statement>,
    },
    /// If `cond` is true, executes the statements in `then_clause`, otherwise, executes the
    /// statements in `else_clause`
    IfThenElse {
        /// If condition
        cond: Expression,
        /// Then clause (`cond` = true)
        then_clause: Vec<Statement>,
        /// Else clause (`cond` = false)
        else_clause: Vec<Statement>,
    },
}

fn stmts(stmts: Option<basic::StatementSequence>) -> Vec<Statement> {
    stmts
        .unwrap()
        .iter()
        .map(|s| Statement::from_basic(&s))
        .collect()
}

impl Statement {
    /// Create a native statement from a BAP one
    pub fn from_basic(stmt: &basic::Statement) -> Statement {
        use basic::StatementTag;
        use self::Statement::*;
        match stmt.tag().unwrap() {
            StatementTag::Move => {
                Move {
                    lhs: Variable::from_basic(&stmt.var().unwrap()),
                    rhs: Expression::from_basic(&stmt.exp().unwrap()),
                }
            }
            StatementTag::Jmp => Jump(Expression::from_basic(&stmt.exp().unwrap())),
            StatementTag::Special => Special,
            StatementTag::While => {
                While {
                    cond: Expression::from_basic(&stmt.exp().unwrap()),
                    body: stmts(stmt.stmts()),
                }
            }
            StatementTag::If => {
                IfThenElse {
                    cond: Expression::from_basic(&stmt.exp().unwrap()),
                    then_clause: stmts(stmt.true_stmts()),
                    else_clause: stmts(stmt.false_stmts()),
                }
            }
            StatementTag::CpuExn => CPUException(stmt.cpuexn().unwrap()),
        }
    }
}

/// Native representation of a BIL expression
#[derive(Debug, Clone, Hash, PartialEq, PartialOrd)]
#[cfg_attr(feature = "json", derive(RustcEncodable, RustcDecodable))]
pub enum Expression {
    /// Takes the value of the argument variable
    Var(Variable),
    /// Evaluates to the provided `BitVector`
    Const(BitVector),
    /// Loads from `memory`, at `index`, `size` bits, in `endian` byte order
    Load {
        /// Memory to load from
        memory: Box<Expression>,
        /// Address to access
        index: Box<Expression>,
        /// Byte order to access with
        endian: Endian,
        /// Bits to access
        size: BitSize,
    },
    /// Creates a new memory value from `memory`, with `index` updated to have `size` bits
    /// overwritten by `value` in `endian` byte order
    Store {
        /// Memory to use as template for new memory
        memory: Box<Expression>,
        /// Address to update
        index: Box<Expression>,
        /// Value to write
        value: Box<Expression>,
        /// Byte order to write in
        endian: Endian,
        /// Bits to write
        size: BitSize,
    },
    /// Evaluates `lhs` `op` `rhs`
    BinOp {
        /// Binary operation to perform
        op: BinOp,
        /// First argument (left hand side)
        lhs: Box<Expression>,
        /// Second argument (right hand side)
        rhs: Box<Expression>,
    },
    /// Evaluates `op`(`arg`)
    UnOp {
        /// Unary operation to perform
        op: UnOp,
        /// Argument to unary operation
        arg: Box<Expression>,
    },
    /// Performs a cast to another bit length
    Cast {
        /// Kind of cast
        kind: Cast,
        /// Target size, in bits
        width: BitSize,
        /// Expression to be cast
        arg: Box<Expression>,
    },
    /// Allows scoped variable binding in expressions, e.g. `let bound_var = bound_expr in
    /// body_expr`
    Let {
        /// Bound variable
        bound_var: Variable,
        /// Definition of bound variable
        bound_expr: Box<Expression>,
        /// Expression to be evaluated with the additional bound variable
        body_expr: Box<Expression>,
    },
    /// Expression resolves to an unknown value
    Unknown {
        /// Description of why this is unknown/what this should be
        description: String,
        /// Type of the unknown value
        type_: Type,
    },
    /// If then else, expression level (e.g. `cond ? true_expr : false_expr`)
    IfThenElse {
        /// Condition expression
        cond: Box<Expression>,
        /// Expression to evaluate to if `cond` is true
        true_expr: Box<Expression>,
        /// Expression to evaluate to if `cond` is false
        false_expr: Box<Expression>,
    },
    /// Take a sub-bitvector out of the one the argument evaluates to, e.g. `arg[low_bit:hi_bit]`
    Extract {
        /// Lowest bit (inclusive) to include in the output
        low_bit: BitSize,
        /// Highest bit (inclusive) to include in the output
        high_bit: BitSize,
        /// Bitvector to take a subvector of
        arg: Box<Expression>,
    },
    /// Concatenate two bitvectors
    Concat {
        /// First bitvector. Assuming little endian, the low bits
        low: Box<Expression>,
        /// Second bitvector. Assuming little endian, the high bits
        high: Box<Expression>,
    },
}

fn exp(e: Option<basic::Expression>) -> Box<Expression> {
    Box::new(Expression::from_basic(&e.unwrap()))
}

impl Expression {
    /// Creates a native `Expression` from a BAP representation
    pub fn from_basic(e: &basic::Expression) -> Self {
        use basic::ExpressionTag;
        use self::Expression::*;
        match e.tag().unwrap() {
            ExpressionTag::UnOp => {
                UnOp {
                    op: e.unop().unwrap(),
                    arg: exp(e.exp()),
                }
            }
            ExpressionTag::Load => {
                Load {
                    memory: exp(e.mem()),
                    index: exp(e.addr()),
                    endian: e.endian().unwrap(),
                    size: e.size().unwrap(),
                }
            }
            ExpressionTag::Unknown => {
                Unknown {
                    description: e.unknown_msg().unwrap(),
                    type_: Type::from_basic(&e.unknown_type().unwrap()),
                }
            }
            ExpressionTag::Cast => {
                Cast {
                    kind: e.cast().unwrap(),
                    width: e.cast_size().unwrap(),
                    arg: exp(e.exp()),
                }
            }
            ExpressionTag::Store => {
                Store {
                    memory: exp(e.mem()),
                    index: exp(e.addr()),
                    endian: e.endian().unwrap(),
                    size: e.size().unwrap(),
                    value: exp(e.rhs()),
                }
            }
            ExpressionTag::Var => Var(Variable::from_basic(&e.var().unwrap())),
            ExpressionTag::Let => {
                Let {
                    bound_var: Variable::from_basic(&e.var().unwrap()),
                    bound_expr: exp(e.rhs()),
                    body_expr: exp(e.exp()),
                }
            }
            ExpressionTag::ITE => {
                IfThenElse {
                    cond: exp(e.exp()),
                    true_expr: exp(e.lhs()),
                    false_expr: exp(e.rhs()),
                }
            }
            ExpressionTag::Int => Const(BitVector::from_basic(&e.value().unwrap())),
            ExpressionTag::Concat => {
                Concat {
                    low: exp(e.lhs()),
                    high: exp(e.rhs()),
                }
            }
            ExpressionTag::Extract => {
                Extract {
                    low_bit: e.extract_lobit().unwrap(),
                    high_bit: e.extract_hibit().unwrap(),
                    arg: exp(e.exp()),
                }
            }
            ExpressionTag::BinOp => {
                BinOp {
                    op: e.binop().unwrap(),
                    lhs: exp(e.lhs()),
                    rhs: exp(e.rhs()),
                }
            }
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, PartialOrd)]
#[cfg_attr(feature = "json", derive(RustcEncodable, RustcDecodable))]
/// Native representation of a variable
pub struct Variable {
    /// Variable name
    pub name: String,
    /// Type of value the variable holds
    pub type_: Type,
    /// Whether this variable is a temporary. Temporary variables are used only to make
    /// implementing semantics of a single instruction easier, and do not survive jumps or
    /// fallthroughs.
    pub tmp: bool,
    /// Variable index - primarily used in SSA forms to differentiate each definition site of a
    /// given register
    pub index: u64,
}

impl Variable {
    /// Construct a native variable from a BAP one
    pub fn from_basic(var: &basic::Variable) -> Self {
        Variable {
            name: var.name(),
            type_: Type::from_basic(&var.type_()),
            tmp: var.is_temp(),
            index: var.index(),
        }
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, PartialOrd)]
#[cfg_attr(feature = "json", derive(RustcEncodable, RustcDecodable))]
/// Native representation of BAP types, which just describe the raw shape of the data rather than
/// properties about it.
pub enum Type {
    /// Bitvector of the provided length
    Immediate(BitSize),
    /// Memory object with specified address and memory cell sizes
    Memory {
        /// Size of addresses in this memory bank
        addr_size: BitSize,
        /// Granularity of read/written values in this memory bank
        cell_size: BitSize,
    },
}

impl Type {
    /// Extract a basic BAP type to a native one
    pub fn from_basic(type_: &basic::Type) -> Self {
        use basic::TypeTag;
        match type_.tag().unwrap() {
            TypeTag::Memory => {
                Type::Memory {
                    addr_size: type_.addr_size().unwrap(),
                    cell_size: type_.cell_size().unwrap(),
                }
            }
            TypeTag::Immediate => Type::Immediate(type_.imm().unwrap()),
        }
    }
}
