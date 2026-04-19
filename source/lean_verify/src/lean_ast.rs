//! Typed AST for the subset of Lean 4 we emit.
//!
//! Replaces ad-hoc `String::push_str` construction. Benefits:
//!   * Precedence is handled by the pretty-printer, not by callers
//!     sprinkling defensive parens.
//!   * Every node carries an optional `vir::messages::Span` so Lean-position
//!     diagnostics can be mapped back to Rust source locations. (The
//!     pretty-printer records which span is active at each output
//!     character; see `lean_pp.rs`.)
//!   * New syntax (match arms, `have` in tactics, …) is added in one place.
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

use vir::messages::Span;

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
    pub noncomputable: bool,
    pub name: String,
    pub binders: Vec<Binder>,
    pub ret_ty: Expr,
    pub body: Expr,
    pub termination_by: Option<Expr>,
    pub span: Option<Span>,
}

#[derive(Debug, Clone)]
pub struct Theorem {
    pub name: String,
    pub binders: Vec<Binder>,
    pub goal: Expr,
    pub tactic: Tactic,
    pub span: Option<Span>,
}

#[derive(Debug, Clone)]
pub struct Datatype {
    pub name: String,
    pub typ_params: Vec<String>,
    pub kind: DatatypeKind,
    pub span: Option<Span>,
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
    pub span: Option<Span>,
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
    pub span: Option<Span>,
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
    pub span: Option<Span>,
}

impl Expr {
    pub fn new(node: ExprNode) -> Self {
        Expr { node, span: None }
    }
    pub fn with_span(self, span: Option<Span>) -> Self {
        Expr { node: self.node, span }
    }
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

    /// `if cond then t else e`.
    If { cond: Box<Expr>, then_: Box<Expr>, else_: Box<Expr> },
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

    /// Escape hatch: verbatim Lean text. Used sparingly for forms we don't
    /// yet model (e.g., `Classical.epsilon`-style closures).
    Raw(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    And, Or, Implies, Iff, Xor,
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
