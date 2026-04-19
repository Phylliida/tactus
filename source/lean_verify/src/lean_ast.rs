//! Typed AST for the subset of Lean 4 we emit.
//!
//! Replaces ad-hoc `String::push_str` construction. Precedence is handled
//! by the pretty-printer, not by callers sprinkling defensive parens.
//!
//! The scope is intentionally narrow: we *emit* Lean, we don't parse it.
//! `Tactic::Raw` and `Command::Raw` are escape hatches for user-authored
//! tactic bodies and the verbatim prelude.
//!
//! Identifier strings passed to `Var`, `name` fields, etc., are assumed to
//! already be valid Lean identifiers (sanitized of `%` / `@` / `#`, dotted
//! path separators preserved, keywords optionally quoted with `«…»`). Name
//! construction is the caller's responsibility — see `to_lean_type::lean_name`.
//!
//! See `lean_pp.rs` for how these nodes render.
//!
//! Note: there's no span field here yet. When we wire Lean-position →
//! Rust-span mapping for exec-fn diagnostics, the field and the pp-side
//! tracking land together.

// ── Commands (top-level declarations) ──────────────────────────────────

#[derive(Debug, Clone)]
pub enum Command {
    /// Verbatim Lean source. Used for the prelude and similar literal
    /// content we don't want to model node-by-node.
    Raw(String),
    Import(String),
    SetOption { name: String, value: String },
    NamespaceOpen(String),
    NamespaceClose(String),
    Def(Def),
    Theorem(Theorem),
    Datatype(Datatype),
    Class(Class),
    Instance(Instance),
    /// `mutual … end` wrapping a list of commands. Used for mutually
    /// recursive spec fn groups.
    Mutual(Vec<Command>),
}

#[derive(Debug, Clone)]
pub struct Def {
    /// Bracketed attributes emitted before the keyword, e.g. `@[irreducible]`.
    pub attrs: Vec<String>,
    pub name: String,
    pub binders: Vec<Binder>,
    pub ret_ty: Expr,
    pub body: Expr,
    /// `termination_by d₁` if one measure, `termination_by (d₁, d₂, …)` for
    /// lexicographic. Empty `Vec` means no termination clause.
    pub termination_by: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub struct Theorem {
    pub name: String,
    pub binders: Vec<Binder>,
    pub goal: Expr,
    pub tactic: Tactic,
}

#[derive(Debug, Clone)]
pub struct Datatype {
    pub name: String,
    pub typ_params: Vec<String>,
    pub kind: DatatypeKind,
}

#[derive(Debug, Clone)]
pub enum DatatypeKind {
    /// Single-variant datatype → Lean `structure`.
    Structure { fields: Vec<Field> },
    /// Multi-variant datatype → Lean `inductive`.
    Inductive { variants: Vec<Variant> },
}

#[derive(Debug, Clone)]
pub struct Field {
    pub name: String,
    pub ty: Expr,
}

#[derive(Debug, Clone)]
pub struct Variant {
    pub name: String,
    pub fields: Vec<Field>,
}

#[derive(Debug, Clone)]
pub struct Class {
    pub name: String,
    /// Positional type params, including `Self`, trait-level type params,
    /// and outParam-marked associated types (via `BinderKind::OutParam`).
    pub typ_params: Vec<Binder>,
    /// Trait-level bounds, emitted as `[Trait T …]` instance binders.
    pub bounds: Vec<Binder>,
    pub methods: Vec<ClassMethod>,
}

#[derive(Debug, Clone)]
pub struct ClassMethod {
    pub name: String,
    pub ty: Expr,
}

#[derive(Debug, Clone)]
pub struct Instance {
    /// Generic and bound binders: `{T : Type}`, `[Bound T]`.
    pub binders: Vec<Binder>,
    /// The trait instance target applied to its type arguments, e.g.
    /// `HasValue (Container T) Int`. Represented as a single `Expr::App`.
    pub target: Expr,
    pub methods: Vec<InstanceMethod>,
}

#[derive(Debug, Clone)]
pub struct InstanceMethod {
    pub name: String,
    pub body: Expr,
}

// ── Binders ─────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct Binder {
    /// `None` for purely instance-style bracket binders like `[Ring T]`.
    pub name: Option<String>,
    pub ty: Expr,
    pub kind: BinderKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinderKind {
    /// `(name : Type)`
    Explicit,
    /// `{name : Type}`
    Implicit,
    /// `[name : Type]` or `[Type]` when name is `None`.
    Instance,
    /// `(name : outParam Type)` — Lean tag for associated types in classes.
    OutParam,
}

// ── Expressions / types / propositions ─────────────────────────────────
//
// Lean is dependently typed: types *are* expressions. We use one Expr
// enum for both terms and types. `Expr::TypeAnnot` emits `(e : T)`.

#[derive(Debug, Clone)]
pub struct Expr {
    pub node: ExprNode,
}

impl Expr {
    pub fn new(node: ExprNode) -> Self { Expr { node } }
}

#[derive(Debug, Clone)]
pub enum ExprNode {
    /// Simple identifier (possibly dotted, like `List.length`).
    /// Caller is responsible for having already sanitized segments.
    Var(String),
    /// Integer literal as a string (supports big ints). Leading `-` means
    /// negative; pp will parenthesize negatives.
    Lit(String),
    LitBool(bool),
    LitStr(String),
    LitChar(char),

    BinOp { op: BinOp, lhs: Box<Expr>, rhs: Box<Expr> },
    UnOp { op: UnOp, arg: Box<Expr> },

    /// Left-associative function application. `head args[0] args[1] …`.
    App { head: Box<Expr>, args: Vec<Expr> },

    /// `let name := value; body`. Lean's goal-type let.
    Let { name: String, value: Box<Expr>, body: Box<Expr> },
    Lambda { binders: Vec<Binder>, body: Box<Expr> },
    Forall { binders: Vec<Binder>, body: Box<Expr> },
    Exists { binders: Vec<Binder>, body: Box<Expr> },

    /// `if cond then t else e`. `else_` is optional — `if` without `else`
    /// renders without the keyword (rare in spec code, but VIR supports it).
    If { cond: Box<Expr>, then_: Box<Expr>, else_: Option<Box<Expr>> },
    /// `match scr with | p1 => b1 | p2 => b2 …`.
    Match { scrutinee: Box<Expr>, arms: Vec<MatchArm> },

    /// `(expr : ty)` — explicit type annotation.
    TypeAnnot { expr: Box<Expr>, ty: Box<Expr> },

    /// `e.field` — field projection (not function application).
    FieldProj { expr: Box<Expr>, field: String },

    /// `{ base with f1 := v1, f2 := v2, … }` structure update.
    StructUpdate {
        base: Box<Expr>,
        updates: Vec<(String, Expr)>,
    },

    /// `[a, b, c]` array literal.
    ArrayLit(Vec<Expr>),

    /// `base[idx]` — array/slice indexing as a dedicated form so pp can
    /// parenthesize the base against application precedence.
    Index { base: Box<Expr>, idx: Box<Expr> },

    /// Escape hatch: verbatim Lean text. Used sparingly for forms we don't
    /// yet model (Block statements, Multi, type-level `×` tuples).
    Raw(String),
}

/// Structural binary operators.
///
/// Anything that Lean doesn't treat as a real binary operator (xor,
/// bitvector ops that are actually function calls, …) is built via
/// `ExprNode::App` with a `Var` head, not squeezed into this enum.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    And, Or, Implies, Iff,
    Eq, Ne, Lt, Le, Gt, Ge,
    Add, Sub, Mul, Div, Mod,
    BitAnd, BitOr, BitXor, Shr, Shl,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Not, Neg, BitNot,
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub enum Pattern {
    Var(String),
    Wildcard,
    /// `Name arg1 arg2 …`. Used for both data constructors and nested patterns.
    Ctor { name: String, args: Vec<Pattern> },
    Or(Box<Pattern>, Box<Pattern>),
    /// `name@pattern`.
    Binding { name: String, sub: Box<Pattern> },
    /// Literal patterns (integers, strings, etc.). Reuses `ExprNode` literals.
    Lit(ExprNode),
}

// ── Tactics ─────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub enum Tactic {
    /// Verbatim Lean tactic source, typically from a user's `by { … }`
    /// block. Keeping this as a String is deliberate — Tactus doesn't
    /// parse user tactics.
    Raw(String),
    /// A single named tactic like `omega`, `rfl`, or `tactus_auto`.
    Named(String),
    /// Sequence of tactics, pretty-printed one per line.
    Seq(Vec<Tactic>),
}

// ── Constructors ──────────────────────────────────────────────────────

/// Right-associative conjunction over a list of AST Exprs. Empty → `True`.
///
/// Used by both proof-fn and exec-fn builders to fold ensures clauses into
/// a single goal. Lean's `∧` is right-associative, so folding from the
/// right keeps the first clause leftmost in the printed output.
pub fn and_all(mut exprs: Vec<Expr>) -> Expr {
    if exprs.is_empty() {
        return Expr::new(ExprNode::LitBool(true));
    }
    let mut acc = exprs.pop().unwrap();
    while let Some(e) = exprs.pop() {
        acc = Expr::new(ExprNode::BinOp {
            op: BinOp::And,
            lhs: Box::new(e),
            rhs: Box::new(acc),
        });
    }
    acc
}
