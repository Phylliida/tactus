//! Tactus intermediate representation for Lean generation.
//!
//! This is a simplified IR that mirrors the subset of VIR we need for Lean translation.
//! It's decoupled from VIR to keep lean_verify dependency-free.
//! At integration time, VIR types are converted to these types before Lean generation.

/// Source span for error mapping.
#[derive(Debug, Clone)]
pub struct Span {
    pub file: String,
    pub start_line: usize,
    pub start_col: usize,
    pub end_line: usize,
    pub end_col: usize,
}

/// Integer range (matches VIR's IntRange).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntRange {
    Int,
    Nat,
    U(u32),
    I(u32),
    USize,
    ISize,
}

/// Tactus type (simplified from VIR's TypX).
#[derive(Debug, Clone)]
pub enum Typ {
    Bool,
    Int(IntRange),
    /// Named type (datatype, type parameter, etc.)
    Named(String),
    /// Tuple type
    Tuple(Vec<Typ>),
    /// Function type (params → return)
    Fun(Vec<Typ>, Box<Typ>),
    /// Type parameter
    TypParam(String),
}

/// Binary operators.
#[derive(Debug, Clone, Copy)]
pub enum BinOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    EuclideanDiv,
    EuclideanMod,
    // Comparison
    Eq,
    Ne,
    Le,
    Lt,
    Ge,
    Gt,
    // Logical
    And,
    Or,
    Implies,
}

/// Unary operators.
#[derive(Debug, Clone, Copy)]
pub enum UnOp {
    Not,
    Neg,
}

/// Expression (simplified from VIR's ExprX).
#[derive(Debug, Clone)]
pub enum Expr {
    /// Boolean constant
    Bool(bool),
    /// Integer constant
    IntLit(String),
    /// Variable reference
    Var(String),
    /// Binary operation
    Binary(BinOp, Box<Expr>, Box<Expr>),
    /// Unary operation
    Unary(UnOp, Box<Expr>),
    /// Function call: function name + arguments
    Call(String, Vec<Expr>),
    /// If-then-else
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// Let binding: name, value, body
    Let(String, Box<Expr>, Box<Expr>),
    /// Forall quantifier: binders (name, type), body
    Forall(Vec<(String, Typ)>, Box<Expr>),
    /// Exists quantifier: binders (name, type), body
    Exists(Vec<(String, Typ)>, Box<Expr>),
}

/// A parameter with name and type.
#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub typ: Typ,
}

/// A spec function definition.
#[derive(Debug, Clone)]
pub struct SpecFn {
    /// Fully qualified name segments (e.g., ["my_crate", "my_module", "double"])
    pub name: Vec<String>,
    /// Type parameters
    pub typ_params: Vec<String>,
    /// Parameters
    pub params: Vec<Param>,
    /// Return type
    pub ret_typ: Typ,
    /// Body expression
    pub body: Expr,
    /// Whether this is `open spec fn` (transparent) vs `spec fn` (irreducible)
    pub is_open: bool,
    /// Decreases clause (for recursive functions)
    pub decreases: Vec<Expr>,
}

/// A proof function (theorem) definition.
#[derive(Debug, Clone)]
pub struct ProofFn {
    /// Fully qualified name segments
    pub name: Vec<String>,
    /// Type parameters
    pub typ_params: Vec<String>,
    /// Parameters
    pub params: Vec<Param>,
    /// Requires clauses (become hypotheses)
    pub requires: Vec<Expr>,
    /// Ensures clauses (become the goal — conjoined if multiple)
    pub ensures: Vec<Expr>,
    /// Named return: (name, type) if the fn has `-> (result: T)`
    pub named_return: Option<(String, Typ)>,
    /// Tactic body (raw Lean text, passed through verbatim)
    pub tactic_body: String,
}

/// Top-level item in a Tactus file.
#[derive(Debug, Clone)]
pub enum Item {
    SpecFn(SpecFn),
    ProofFn(ProofFn),
}
