//! Typed AST for the subset of Lean 4 we emit.
//!
//! Replaces ad-hoc `String::push_str` construction. Precedence is handled
//! by the pretty-printer, not by callers sprinkling defensive parens.
//!
//! The scope is intentionally narrow: we *emit* Lean, we don't parse it.
//! `Tactic::Raw` and `Command::Raw` are escape hatches for user-authored
//! tactic bodies and the verbatim prelude.
//!
//! ## Names
//!
//! Variable-bearing nodes (`Var`, `Let.name`, `Binder.name`, pattern
//! bindings) hold a [`LeanName`] rather than a raw `String`. `LeanName` is
//! a newtype with no `From<String>` impl — the only way to construct one
//! is through an explicit constructor in `lean_name.rs`:
//!
//! * [`LeanName::from_var_ident`] — for VarIdent → name (always includes
//!   the disambiguator id; this is the chained-compare-shadowing fix).
//! * [`LeanName::from_path`] / [`LeanName::from_path_short`] — for VIR
//!   `Path` → dotted Lean name.
//! * [`LeanName::lit`] — for hardcoded prelude refs (`"Nat"`, `"omega"`).
//! * [`LeanName::synthetic`] — for codegen-generated names.
//! * [`LeanName::from_field`] — for struct/enum field-name strings that
//!   arrive as `&str` from VIR.
//!
//! The compiler enforces: any VarIdent → name conversion that flows into
//! `ExprNode::Var(LeanName)` must go through `from_var_ident`. A future
//! contributor can't accidentally `ExprNode::Var(sanitize(&v.0))` (that's
//! a type error). See the `lean_name` module docs for the soundness story.
//!
//! Top-level command names (`Def.name`, `Theorem.name`, etc.) and
//! field-name-shaped `String`s (`FieldProj.field`, `Pattern::Ctor.name`,
//! `StructUpdate` keys) stay `String` — those are codegen-synthesized or
//! path-derived and don't have the same shadowing concerns.
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
    /// Curried-form definition with pattern-matched equations:
    /// `def name : T → R | pat₁ => body₁ | pat₂ => body₂ | …`.
    /// Used for recursive structural-recursion fns where Lean's
    /// equation compiler needs the curried shape (e.g.,
    /// `T.height` for non-int decreases). The `match`-on-binder
    /// form (`Def`) works for non-recursive defs but the curried
    /// form is more reliable for WF analysis.
    DefCurried(DefCurried),
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

/// Curried-form definition with pattern-matched equations.
///
/// Renders as:
/// ```text
/// @[attr₁] @[attr₂] noncomputable def name : ty
///   | pat₁ => body₁
///   | pat₂ => body₂
/// ```
///
/// `ty` is the full function type — typically `T → R` for a
/// single-arg fn. The patterns match the implicit binder.
/// Lean's equation compiler infers WF-recursion from the
/// pattern shape; works more reliably than the match-on-binder
/// form (`Def`) for recursive datatypes.
///
/// `binders` go BEFORE the `:` in the emitted Lean (e.g.,
/// `def Name {A : Type} : T A → Nat`). For non-generic curried
/// defs this is empty and the form is just `def Name : T → Nat`.
/// For generic recursive defs (#108), the implicit type-param
/// binder lives here so equations can match only on the value
/// arg (Lean infers the implicit) — putting `∀ {A : Type}, …`
/// inside `ty` confuses the equation compiler.
#[derive(Debug, Clone)]
pub struct DefCurried {
    pub attrs: Vec<String>,
    pub name: String,
    pub binders: Vec<Binder>,
    pub ty: Expr,
    pub equations: Vec<MatchArm>,
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
    /// `deriving` clause class names (e.g., `"Inhabited"`). Emitted
    /// as `deriving <cls1>, <cls2>` after the variants/fields.
    /// `datatype_to_cmds` adds `Inhabited` for non-generic datatypes
    /// so that auto-generated accessors' `default` fallback
    /// resolves — particularly for self-referential types where
    /// the accessor's return type is the datatype itself.
    pub derives: Vec<String>,
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
    pub name: Option<crate::lean_name::LeanName>,
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

    // ── Smart constructors ─────────────────────────────────────────────
    //
    // The AST's wire format puts every non-leaf field behind a `Box<Expr>`
    // so recursive construction quickly becomes `Box::new(Expr::new(
    // ExprNode::BinOp { ... }))` chains. Callers can use these helpers
    // to build trees readably — `Expr::and(l, r)` instead of the full
    // three-line incantation.
    //
    // Naming follows the ExprNode variants where that's clearest
    // (`binop`, `unop`, `app`, `let_bind`, `field_proj`, `anon`); binary
    // operators also get shorthand aliases (`and`, `or`, `implies`,
    // `eq`, `lt`, `le`, `gt`, `ge`, `add`, `sub`, `mul`). Unary ops get
    // `not` and `neg`.

    pub fn var(name: crate::lean_name::LeanName) -> Self {
        Expr::new(ExprNode::Var(name))
    }
    /// Convenience for hardcoded literal Lean identifiers (`"Nat"`,
    /// `"omega"`, `"Int.toNat"`). Wraps the string in `LeanName::lit`
    /// internally — caller guarantees the string is a valid Lean
    /// identifier already (no special chars to sanitize, no
    /// disambiguation needed).
    pub fn var_lit(name: &str) -> Self {
        Expr::new(ExprNode::Var(crate::lean_name::LeanName::lit(name)))
    }
    /// Convenience for already-processed name strings (path-derived
    /// names from `lean_name(&path)`, sanitized synthetic temps, etc.).
    /// Wraps in `LeanName::synthetic` — the caller is asserting the
    /// string is a valid Lean identifier. Use `var(LeanName::from_var_ident(v))`
    /// when constructing from a VarIdent.
    pub fn var_synthetic(name: impl Into<String>) -> Self {
        Expr::new(ExprNode::Var(crate::lean_name::LeanName::synthetic(name)))
    }
    pub fn lit_bool(b: bool) -> Self { Expr::new(ExprNode::LitBool(b)) }
    pub fn lit_true() -> Self { Expr::lit_bool(true) }
    pub fn lit_false() -> Self { Expr::lit_bool(false) }
    /// Integer literal from a pre-formatted decimal or hex string. The
    /// pp doesn't inspect the contents; it just embeds the text.
    pub fn lit_int(s: impl Into<String>) -> Self {
        Expr::new(ExprNode::Lit(s.into()))
    }

    pub fn binop(op: BinOp, lhs: Expr, rhs: Expr) -> Self {
        Expr::new(ExprNode::BinOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs) })
    }
    pub fn and(lhs: Expr, rhs: Expr) -> Self { Expr::binop(BinOp::And, lhs, rhs) }
    pub fn or(lhs: Expr, rhs: Expr) -> Self { Expr::binop(BinOp::Or, lhs, rhs) }
    pub fn implies(lhs: Expr, rhs: Expr) -> Self { Expr::binop(BinOp::Implies, lhs, rhs) }
    pub fn eq(lhs: Expr, rhs: Expr) -> Self { Expr::binop(BinOp::Eq, lhs, rhs) }
    pub fn ne(lhs: Expr, rhs: Expr) -> Self { Expr::binop(BinOp::Ne, lhs, rhs) }
    pub fn lt(lhs: Expr, rhs: Expr) -> Self { Expr::binop(BinOp::Lt, lhs, rhs) }
    pub fn le(lhs: Expr, rhs: Expr) -> Self { Expr::binop(BinOp::Le, lhs, rhs) }
    pub fn gt(lhs: Expr, rhs: Expr) -> Self { Expr::binop(BinOp::Gt, lhs, rhs) }
    pub fn ge(lhs: Expr, rhs: Expr) -> Self { Expr::binop(BinOp::Ge, lhs, rhs) }
    pub fn add(lhs: Expr, rhs: Expr) -> Self { Expr::binop(BinOp::Add, lhs, rhs) }
    pub fn sub(lhs: Expr, rhs: Expr) -> Self { Expr::binop(BinOp::Sub, lhs, rhs) }
    pub fn mul(lhs: Expr, rhs: Expr) -> Self { Expr::binop(BinOp::Mul, lhs, rhs) }

    pub fn unop(op: UnOp, arg: Expr) -> Self {
        Expr::new(ExprNode::UnOp { op, arg: Box::new(arg) })
    }
    pub fn not(arg: Expr) -> Self { Expr::unop(UnOp::Not, arg) }
    pub fn neg(arg: Expr) -> Self { Expr::unop(UnOp::Neg, arg) }

    /// `head args[0] args[1] …`. Zero args collapses to `head` — App
    /// with an empty arg list is meaningless and confuses the pp.
    pub fn app(head: Expr, args: Vec<Expr>) -> Self {
        if args.is_empty() {
            head
        } else {
            Expr::new(ExprNode::App { head: Box::new(head), args })
        }
    }
    /// `head arg` — shorthand for the common unary-application case.
    pub fn app1(head: Expr, arg: Expr) -> Self { Expr::app(head, vec![arg]) }

    pub fn let_bind(name: crate::lean_name::LeanName, value: Expr, body: Expr) -> Self {
        Expr::new(ExprNode::Let {
            name,
            value: Box::new(value),
            body: Box::new(body),
        })
    }
    /// Convenience for already-processed name strings. See [`Expr::var_synthetic`].
    pub fn let_bind_synthetic(name: impl Into<String>, value: Expr, body: Expr) -> Self {
        Expr::new(ExprNode::Let {
            name: crate::lean_name::LeanName::synthetic(name),
            value: Box::new(value),
            body: Box::new(body),
        })
    }

    pub fn field_proj(expr: Expr, field: impl Into<String>) -> Self {
        Expr::new(ExprNode::FieldProj { expr: Box::new(expr), field: field.into() })
    }

    pub fn anon(elems: Vec<Expr>) -> Self { Expr::new(ExprNode::Anon(elems)) }

    /// Wrap `inner` with a source-location marker carrying the
    /// obligation's semantic kind. Transparent at the Lean level;
    /// pp emits a `/- @rust:LOC -/` block before `inner` and
    /// records `(line, loc, kind)` in landmarks for #51 error
    /// formatting.
    pub fn span_mark(rust_loc: impl Into<String>, kind: AssertKind, inner: Expr) -> Self {
        Expr::new(ExprNode::SpanMark {
            rust_loc: rust_loc.into(),
            kind,
            inner: Box::new(inner),
        })
    }

    pub fn type_annot(expr: Expr, ty: Expr) -> Self {
        Expr::new(ExprNode::TypeAnnot { expr: Box::new(expr), ty: Box::new(ty) })
    }

    pub fn forall(binders: Vec<Binder>, body: Expr) -> Self {
        Expr::new(ExprNode::Forall { binders, body: Box::new(body) })
    }
    pub fn exists_(binders: Vec<Binder>, body: Expr) -> Self {
        Expr::new(ExprNode::Exists { binders, body: Box::new(body) })
    }
    pub fn lambda(binders: Vec<Binder>, body: Expr) -> Self {
        Expr::new(ExprNode::Lambda { binders, body: Box::new(body) })
    }
}

#[derive(Debug, Clone)]
pub enum ExprNode {
    /// Simple identifier (possibly dotted, like `List.length`).
    /// `LeanName` enforces that the name went through one of the
    /// explicit constructors — `from_var_ident` for VarIdent-derived
    /// names, `lit` for hardcoded prelude refs, etc.
    Var(crate::lean_name::LeanName),
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
    Let { name: crate::lean_name::LeanName, value: Box<Expr>, body: Box<Expr> },
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

    /// `base[idx]` or `base[idx]!` — array/slice indexing as a dedicated form
    /// so pp can parenthesize the base against application precedence.
    /// `bang: true` emits Lean's panic-on-out-of-bounds variant
    /// (`getElem!`, requires `Inhabited`); `false` emits plain `[idx]`
    /// which Lean elaborates with an inferred bounds proof.
    Index { base: Box<Expr>, idx: Box<Expr>, bang: bool },

    /// `⟨a, b, c⟩` — Lean's anonymous constructor. Used for tuples and for
    /// inferred data constructors where the target type is unambiguous.
    Anon(Vec<Expr>),

    /// Escape hatch: verbatim Lean text. Reserved for VIR forms that have
    /// no direct Lean analogue (effectless markers, exotic shapes). The
    /// goal is to keep this set small; prefer adding a real node.
    Raw(String),

    /// Source-span annotation (#51). Transparent at the Lean level —
    /// pp emits a leading `/- @rust:LOC -/` block comment and
    /// records `(line, loc, kind)` in landmarks. `LeanSourceMap`
    /// consumes the landmarks at error time to map Lean lines
    /// back to Rust source positions.
    ///
    /// `kind` carries the semantic class of the obligation
    /// (precondition / loop invariant / termination check /
    /// etc.) so error messages can include a label like
    /// "(precondition)" alongside `at <loc>:`. Set by the
    /// wrapping site in `lower_wp` / `lower_loop` / `lower_call`
    /// / etc.
    SpanMark {
        rust_loc: String,
        kind: AssertKind,
        inner: Box<Expr>,
    },
}

/// Semantic class of a `SpanMark`'s annotated expression.
///
/// SpanMarks fall into two structural roles, encoded as the
/// outer-level enum split (#102):
///
/// * **`Obligation(_)`** — wrapped around the expression that
///   IS the proof goal of an emitted theorem. `find_span_mark`
///   returns these when looking up the kind label for a Lean
///   error: the failing tactic's `pos.line` is just after the
///   goal, and the obligation's mark is the closest preceding.
///
/// * **`Hypothesis(_)`** — wrapped around an expression used as
///   a hypothesis frame in the OblCtx (e.g., a loop's `cond` or
///   `¬cond`, an `if`'s branch condition). These appear earlier
///   in the goal than the obligation's own mark, so they're
///   structurally shadowed for `find_span_mark`. They still
///   produce `/- @rust:LOC -/` comments in the generated `.lean`
///   for visual debugging, but never fire as error labels.
///
/// **Why a sum type instead of a flat enum + `is_obligation_kind()`
/// helper?** Pre-#102, `AssertKind` was flat with eight variants
/// and a runtime `is_obligation_kind()` method. Adding a new
/// variant required remembering to update the discriminator;
/// forgetting silently miscategorized the new variant. The sum
/// type makes the choice structural — adding a new variant
/// means picking which arm it lives in. Filtering becomes
/// `matches!(kind, AssertKind::Obligation(_))` which compile-
/// errors cleanly if a future contributor changes the enum
/// shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssertKind {
    /// Fires as an error label via `find_span_mark` — wraps the
    /// goal expression of an emitted theorem.
    Obligation(ObligationKind),
    /// Provides a `/- @rust:LOC -/` debug comment but never
    /// surfaces as an error label — wraps a hypothesis-frame
    /// expression (loop cond, branch cond, etc.).
    Hypothesis(HypothesisKind),
}

/// Obligation-side kinds: each fires as an error label.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObligationKind {
    /// User-written `assert(P)`, or an obligation without a
    /// more specific class.
    Plain,
    /// `ensures` clause of a fn — wrapped at WpCtx::new time
    /// per-clause, so multi-clause ensures becomes one
    /// theorem per clause via `emit_done_or_split`.
    Postcondition,
    /// Loop invariant: init theorem (entry check), or one
    /// conjunct of a maintain theorem (split from the body's
    /// `inv_conj ∧ decrease` terminator).
    LoopInvariant,
    /// Loop decrease measure (`D_new < D_old`) — the
    /// decrease conjunct of a maintain theorem.
    LoopDecrease,
    /// Precondition of a callee at the call site.
    CallPrecondition,
    /// Termination check for a recursive call
    /// (`CheckDecreaseHeight` lowering).
    Termination,
}

/// Hypothesis-side kinds: documentation-only, never fire as
/// error labels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HypothesisKind {
    /// Loop condition expression — appears as a hypothesis
    /// (`cond` for maintain, `¬cond` for use). Provides a
    /// `/- @rust:LOC -/` comment in the generated `.lean` for
    /// visual debugging; never an error label (any obligation
    /// in scope has its own obligation-kind mark which
    /// shadows this).
    LoopCondition,
    /// `if` / `match` branch condition — appears as a
    /// hypothesis. Same documentation-only role as
    /// `LoopCondition`.
    BranchCondition,
}

impl AssertKind {
    /// Short user-visible label for the `at <loc> (<label>):`
    /// prefix in error messages. Empty string for `Plain`
    /// (no extra label needed). Hypothesis kinds also return
    /// labels — they show up via `/- @rust:LOC -/` comments,
    /// but `find_span_mark` filters them out so they never
    /// reach the error label path.
    pub fn label(&self) -> &'static str {
        match self {
            AssertKind::Obligation(o) => match o {
                ObligationKind::Plain => "",
                ObligationKind::Postcondition => "postcondition",
                ObligationKind::LoopInvariant => "loop invariant",
                ObligationKind::LoopDecrease => "loop decrease",
                ObligationKind::CallPrecondition => "precondition",
                ObligationKind::Termination => "termination",
            },
            AssertKind::Hypothesis(h) => match h {
                HypothesisKind::LoopCondition => "loop condition",
                HypothesisKind::BranchCondition => "branch condition",
            },
        }
    }

    /// Whether a `SpanMark` with this kind should fire as an
    /// error label via `find_span_mark`. Structurally `true`
    /// for `Obligation(_)`, `false` for `Hypothesis(_)` — no
    /// need to enumerate variants (#102).
    pub fn is_obligation_kind(&self) -> bool {
        matches!(self, AssertKind::Obligation(_))
    }
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
    /// Type-level Cartesian product `×`. Right-associative at ~35 in Lean.
    /// Used for tuple types, including Verus `FnDef` encodings.
    Prod,
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
    Var(crate::lean_name::LeanName),
    Wildcard,
    /// `Name arg1 arg2 …`. Used for both data constructors and nested patterns.
    /// `name` stays `String` — it's the constructor name (e.g.,
    /// `MyType.Variant`), path-derived and not subject to VarIdent
    /// shadowing.
    Ctor { name: String, args: Vec<Pattern> },
    Or(Box<Pattern>, Box<Pattern>),
    /// `name@pattern`.
    Binding { name: crate::lean_name::LeanName, sub: Box<Pattern> },
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
}

// ── Constructors ──────────────────────────────────────────────────────

/// Substitute free `Var(name)` occurrences in `expr` according to
/// `subst`. Respects lexical scoping: a binder (`Let` / `Lambda` /
/// `Forall` / `Exists` / match-arm pattern) whose name appears in
/// `subst` removes that key from the substitution before recursing
/// into its body, so shadowing works correctly.
///
/// **Capture avoidance via alpha-renaming (#116).** If a binder
/// would capture a name appearing free in an active substitution
/// value, we **alpha-rename** the colliding binder to a fresh name
/// (`<base>_α<N>`) and rewrite the body's references in lockstep
/// before applying the main substitution. Detection is lazy per-
/// scope: we only consider names free in the **current** inner
/// substitution at the binder, not names free in the original top-
/// level substitution. This avoids false positives like
/// `(∀ y. z) + x` with `{x: y}` — the outer `∀ y.` can't capture
/// anything because `x` never appears inside its scope, so no
/// substitution happens there.
///
/// The fresh name is chosen to avoid collisions with: every name
/// (free or bound) in the body, every free name in active
/// substitution values, and every sibling binder name in the same
/// multi-binder shape (`∀ x y. ...`). Alpha-rename also walks each
/// renamed binder's type expression so dependent types like
/// `∀ (x : Nat) (h : x > 0), ...` stay consistent. See
/// `compute_alpha_renames` and `apply_renames_to_binders`.
///
/// **Per-variant boilerplate.** Adding a new `ExprNode` variant
/// touches `walk_children` + `map_children` (both right above this
/// fn) and the pretty-printer. The walkers (`substitute_impl`,
/// `collect_free_vars`, `collect_all_names`, `strip_span_marks_node`,
/// `mentions_free_var`) all delegate non-special variants to
/// `walk_children` / `map_children` via a `_ =>` arm, so they pick up
/// the new variant automatically. Pattern walkers
/// (`pattern_bound_names_impl`, `rename_in_pattern`) similarly
/// delegate to `walk_pattern_children` / `map_pattern_children`. See
/// the "Generic structural walkers" section header below for the
/// design rationale.
///
/// Used by exec-fn codegen to substitute call-site args for callee
/// params in inlined `require` / `ensure` / `decrease` expressions.
/// This replaces the older `let p := arg; body` wrapping — direct
/// substitution produces Lean that's both cleaner (no nested let
/// shadowing) and tractable for omega (no zeta-reduction needed).
pub fn substitute(
    expr: &Expr,
    subst: &std::collections::HashMap<crate::lean_name::LeanName, Expr>,
) -> Expr {
    if subst.is_empty() { return expr.clone(); }
    substitute_impl(expr, subst)
}

/// Recursively strip `ExprNode::SpanMark` wrappers from an
/// expression tree, returning a structurally-equivalent tree
/// with all source-mapping metadata removed. Used by tests
/// (`pp_eq`) to compare semantic-equivalent expressions where
/// one side carries `SpanMark` wrappers from `lower_wp` and the
/// other doesn't. Strips are reasonable here because `SpanMark`
/// is transparent at the Lean level — the wrapping affects only
/// the pp output (a leading `/- @rust:LOC -/` comment) and the
/// landmark side-channel, never semantics.
// ── Generic structural walkers (#98) ──────────────────────────────────
//
// `ExprNode` and `Pattern` have many variants, most of which contain
// nested sub-expressions or sub-patterns. Walkers that recurse over the
// whole tree (substitute, collect_free_vars, collect_all_names,
// strip_span_marks, mentions_free_var, plus pattern_bound_names and
// rename_in_pattern on the pattern side) used to spell out per-variant
// dispatch in full — five Expr walkers at ~40-80 lines each plus two
// Pattern walkers, ~370 lines of structurally parallel match arms.
//
// `walk_children` and `map_children` (and their Pattern siblings)
// concentrate that dispatch in one place — they walk every direct
// child Expr without caring about scope. Used by transforms that
// recurse uniformly (`strip_span_marks_node` for non-SpanMark cases,
// `substitute_impl` for non-special cases) and by collectors for
// non-special variants.
//
// The split between `walk_*` (read-only) and `map_*` (transforming) is
// because consumer return types differ — collectors thread a `&mut
// HashSet`/`&mut Vec` while transforms produce a new node. A single
// visitor trait would force a unified `Out` parameter, which doesn't
// exist here.
//
// **Compile-time enforcement of binder semantics: `ScopeKind`.** A
// secondary risk shows up at scope-tracking consumers
// (`substitute_impl`, `collect_free_vars`, `collect_all_names`):
// these need to know which variants introduce binders so they can
// extend their scope/subst tracking before recursing. A naive
// "match Let/Lambda/.../Match explicitly, fall through to
// walk_children for the rest" leaves the door open: a future binder
// variant added to `ExprNode` would silently slip through the
// fallthrough, mis-tracking scope.
//
// The fix is `ScopeKind` (defined below) plus the `scope_kind()`
// method on `ExprNode`. Every variant categorizes into one of:
//
// * `Var(name)` — substitution leaf;
// * `Let { … }` — single-name binder;
// * `Quantified { kind, binders, body }` — Lambda/Forall/Exists
//   (`kind: QuantifierKind` distinguishes them for transform
//   consumers that need to rebuild);
// * `Match { … }` — per-arm pattern-bound names;
// * `Other` — non-binder compounds and leaves other than `Var`.
//
// `scope_kind()` is an exhaustive match on `ExprNode` (no catch-all),
// so a new variant is a compile error there. The contributor must
// either pick an existing `ScopeKind` (which propagates correct
// scope semantics to every consumer automatically) OR add a new
// `ScopeKind` variant — which compile-errors in every consumer's
// match, forcing them to decide what scope semantics the new
// variant has.
//
// The structural lock: a new BINDER ExprNode variant cannot ship
// without the contributor positively claiming a scope category.
// Implicit inheritance via `_ =>` is gone.

/// Categorization of an `ExprNode` for scope-tracking walks.
///
/// Returned by `ExprNode::scope_kind()`. Consumers
/// (`substitute_impl`, `collect_free_vars`, `collect_all_names`)
/// match on this exhaustively (no catch-all) so adding a new
/// scope shape compile-errors at every consumer.
///
/// Borrows from the underlying `ExprNode` so the consumer can use
/// the bound fields without re-matching on the original variant.
enum ScopeKind<'a> {
    /// `ExprNode::Var(_)` — substitution leaf. Substitution looks up
    /// in subst and replaces; collectors check against the bound set.
    Var(&'a crate::lean_name::LeanName),
    /// `ExprNode::Let { … }` — single-name binder. `value` is in
    /// outer scope; `body` is in scope extended by `name`.
    Let {
        name: &'a crate::lean_name::LeanName,
        value: &'a Expr,
        body: &'a Expr,
    },
    /// `ExprNode::Lambda` / `Forall` / `Exists` — quantifier-shaped
    /// multi-binder. `kind` distinguishes the three for transforms
    /// that rebuild; collectors don't care which.
    Quantified {
        kind: QuantifierKind,
        binders: &'a [Binder],
        body: &'a Expr,
    },
    /// `ExprNode::Match { … }` — per-arm scope extended by the
    /// arm's pattern-bound names.
    Match {
        scrutinee: &'a Expr,
        arms: &'a [MatchArm],
    },
    /// Non-binder compounds and leaves other than `Var`. Walkers
    /// delegate to `walk_children` / `map_children` for these — no
    /// scope tracking required.
    Other,
}

/// Discriminator for `ScopeKind::Quantified` so transforms (e.g.,
/// `substitute_impl`) can rebuild the right `ExprNode` constructor.
/// Collectors that don't rebuild can ignore this.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum QuantifierKind {
    Lambda,
    Forall,
    Exists,
}

impl QuantifierKind {
    /// Build the corresponding `ExprNode` variant from substituted
    /// binders + body. Used by `substitute_impl`'s `ScopeKind::Quantified`
    /// arm to dispatch back to the right constructor without
    /// re-matching on the original ExprNode.
    fn build(self, binders: Vec<Binder>, body: Box<Expr>) -> ExprNode {
        match self {
            QuantifierKind::Lambda => ExprNode::Lambda { binders, body },
            QuantifierKind::Forall => ExprNode::Forall { binders, body },
            QuantifierKind::Exists => ExprNode::Exists { binders, body },
        }
    }
}

impl ExprNode {
    /// Categorize this node for scope-tracking walks. **Exhaustive
    /// — no catch-all.** A new `ExprNode` variant is a compile error
    /// here, forcing the contributor to categorize it (or add a new
    /// `ScopeKind` variant, which then compile-errors in every
    /// consumer that matches on `ScopeKind`).
    fn scope_kind(&self) -> ScopeKind<'_> {
        match self {
            ExprNode::Var(n) => ScopeKind::Var(n),
            ExprNode::Let { name, value, body } => ScopeKind::Let {
                name,
                value,
                body,
            },
            ExprNode::Lambda { binders, body } => ScopeKind::Quantified {
                kind: QuantifierKind::Lambda,
                binders,
                body,
            },
            ExprNode::Forall { binders, body } => ScopeKind::Quantified {
                kind: QuantifierKind::Forall,
                binders,
                body,
            },
            ExprNode::Exists { binders, body } => ScopeKind::Quantified {
                kind: QuantifierKind::Exists,
                binders,
                body,
            },
            ExprNode::Match { scrutinee, arms } => ScopeKind::Match {
                scrutinee,
                arms,
            },
            // Non-binder compounds + leaves other than Var.
            // Listed explicitly (no `_ =>`) so a new variant
            // compile-errors here, forcing categorization.
            ExprNode::Lit(_)
            | ExprNode::LitBool(_)
            | ExprNode::LitStr(_)
            | ExprNode::LitChar(_)
            | ExprNode::Raw(_)
            | ExprNode::BinOp { .. }
            | ExprNode::UnOp { .. }
            | ExprNode::App { .. }
            | ExprNode::If { .. }
            | ExprNode::TypeAnnot { .. }
            | ExprNode::FieldProj { .. }
            | ExprNode::StructUpdate { .. }
            | ExprNode::ArrayLit(_)
            | ExprNode::Index { .. }
            | ExprNode::Anon(_)
            | ExprNode::SpanMark { .. } => ScopeKind::Other,
        }
    }
}

/// Call `f` once on each direct child `Expr` of `node`. Recurses into
/// every Expr-typed field including binder types (`Lambda`/`Forall`/
/// `Exists` ty fields) and match-arm bodies. Does NOT walk binder names,
/// constructor names, or non-Expr metadata.
///
/// Used by `collect_all_names`, `collect_free_vars`, and
/// `pattern_bound_names_impl` (via `walk_pattern_children`) — walks
/// that thread state via a `&mut` parameter rather than rebuilding
/// the tree.
fn walk_children<F>(node: &ExprNode, mut f: F)
where
    F: FnMut(&Expr),
{
    match node {
        ExprNode::Var(_)
        | ExprNode::Lit(_)
        | ExprNode::LitBool(_)
        | ExprNode::LitStr(_)
        | ExprNode::LitChar(_)
        | ExprNode::Raw(_) => {}
        ExprNode::BinOp { lhs, rhs, .. } => {
            f(lhs);
            f(rhs);
        }
        ExprNode::UnOp { arg, .. } => f(arg),
        ExprNode::App { head, args } => {
            f(head);
            for a in args {
                f(a);
            }
        }
        ExprNode::Let { value, body, .. } => {
            f(value);
            f(body);
        }
        ExprNode::Lambda { binders, body }
        | ExprNode::Forall { binders, body }
        | ExprNode::Exists { binders, body } => {
            for b in binders {
                f(&b.ty);
            }
            f(body);
        }
        ExprNode::If { cond, then_, else_ } => {
            f(cond);
            f(then_);
            if let Some(e) = else_ {
                f(e);
            }
        }
        ExprNode::Match { scrutinee, arms } => {
            f(scrutinee);
            for arm in arms {
                f(&arm.body);
            }
        }
        ExprNode::TypeAnnot { expr, ty } => {
            f(expr);
            f(ty);
        }
        ExprNode::FieldProj { expr, .. } => f(expr),
        ExprNode::StructUpdate { base, updates } => {
            f(base);
            for (_, e) in updates {
                f(e);
            }
        }
        ExprNode::ArrayLit(es) | ExprNode::Anon(es) => {
            for e in es {
                f(e);
            }
        }
        ExprNode::Index { base, idx, .. } => {
            f(base);
            f(idx);
        }
        ExprNode::SpanMark { inner, .. } => f(inner),
    }
}

/// Rebuild a node by mapping each direct child `Expr` through `f`.
/// Non-Expr fields (binder names, constructor names, op codes, span-mark
/// metadata) are cloned/copied as-is. Binder kinds (`Lambda`/`Forall`/
/// `Exists`) keep their binder list shape — types get mapped, names
/// stay.
///
/// Used by transforms that recurse uniformly into all sub-expressions
/// (`strip_span_marks_node` for the non-SpanMark fallthrough,
/// `substitute_impl` for the non-binder, non-Var fallthrough). Binder-
/// aware consumers (substitute_impl on Let / Lambda / etc.) handle
/// those variants explicitly before falling through to `map_children`.
fn map_children<F>(node: &ExprNode, mut f: F) -> ExprNode
where
    F: FnMut(&Expr) -> Expr,
{
    match node {
        ExprNode::Var(n) => ExprNode::Var(n.clone()),
        ExprNode::Lit(s) => ExprNode::Lit(s.clone()),
        ExprNode::LitBool(b) => ExprNode::LitBool(*b),
        ExprNode::LitStr(s) => ExprNode::LitStr(s.clone()),
        ExprNode::LitChar(c) => ExprNode::LitChar(*c),
        ExprNode::Raw(s) => ExprNode::Raw(s.clone()),
        ExprNode::BinOp { op, lhs, rhs } => {
            let lhs = Box::new(f(lhs));
            let rhs = Box::new(f(rhs));
            ExprNode::BinOp { op: *op, lhs, rhs }
        }
        ExprNode::UnOp { op, arg } => ExprNode::UnOp {
            op: *op,
            arg: Box::new(f(arg)),
        },
        ExprNode::App { head, args } => {
            let head = Box::new(f(head));
            let args = args.iter().map(|a| f(a)).collect();
            ExprNode::App { head, args }
        }
        ExprNode::Let { name, value, body } => {
            let value = Box::new(f(value));
            let body = Box::new(f(body));
            ExprNode::Let { name: name.clone(), value, body }
        }
        ExprNode::Lambda { binders, body } => {
            let binders = map_binders(binders, &mut f);
            ExprNode::Lambda { binders, body: Box::new(f(body)) }
        }
        ExprNode::Forall { binders, body } => {
            let binders = map_binders(binders, &mut f);
            ExprNode::Forall { binders, body: Box::new(f(body)) }
        }
        ExprNode::Exists { binders, body } => {
            let binders = map_binders(binders, &mut f);
            ExprNode::Exists { binders, body: Box::new(f(body)) }
        }
        ExprNode::If { cond, then_, else_ } => {
            let cond = Box::new(f(cond));
            let then_ = Box::new(f(then_));
            let else_ = else_.as_ref().map(|e| Box::new(f(e)));
            ExprNode::If { cond, then_, else_ }
        }
        ExprNode::Match { scrutinee, arms } => {
            let scrutinee = Box::new(f(scrutinee));
            let arms = arms
                .iter()
                .map(|a| MatchArm {
                    pattern: a.pattern.clone(),
                    body: f(&a.body),
                })
                .collect();
            ExprNode::Match { scrutinee, arms }
        }
        ExprNode::TypeAnnot { expr, ty } => {
            let expr = Box::new(f(expr));
            let ty = Box::new(f(ty));
            ExprNode::TypeAnnot { expr, ty }
        }
        ExprNode::FieldProj { expr, field } => ExprNode::FieldProj {
            expr: Box::new(f(expr)),
            field: field.clone(),
        },
        ExprNode::StructUpdate { base, updates } => {
            let base = Box::new(f(base));
            let updates = updates
                .iter()
                .map(|(fld, e)| (fld.clone(), f(e)))
                .collect();
            ExprNode::StructUpdate { base, updates }
        }
        ExprNode::ArrayLit(es) => {
            ExprNode::ArrayLit(es.iter().map(|e| f(e)).collect())
        }
        ExprNode::Index { base, idx, bang } => {
            let base = Box::new(f(base));
            let idx = Box::new(f(idx));
            ExprNode::Index { base, idx, bang: *bang }
        }
        ExprNode::Anon(es) => ExprNode::Anon(es.iter().map(|e| f(e)).collect()),
        ExprNode::SpanMark { rust_loc, kind, inner } => ExprNode::SpanMark {
            rust_loc: rust_loc.clone(),
            kind: *kind,
            inner: Box::new(f(inner)),
        },
    }
}

/// Helper for `map_children`: rebuild a binder list with each binder's
/// type mapped through `f`. Names and `kind` stay; only `ty` gets the
/// transform applied. Takes `&mut F` so a single mutable borrow flows
/// across the three quantifier arms (Lambda/Forall/Exists) plus the
/// outer `body` call without lifetime gymnastics.
fn map_binders<F>(binders: &[Binder], f: &mut F) -> Vec<Binder>
where
    F: FnMut(&Expr) -> Expr,
{
    binders
        .iter()
        .map(|b| Binder {
            name: b.name.clone(),
            ty: f(&b.ty),
            kind: b.kind,
        })
        .collect()
}

/// Call `f` once on each direct sub-`Pattern` of `pat`. Recurses into
/// `Ctor` args, `Or` alternatives, and the `sub` of `Binding`. Does
/// NOT walk pattern-bound names.
fn walk_pattern_children<F>(pat: &Pattern, mut f: F)
where
    F: FnMut(&Pattern),
{
    match pat {
        Pattern::Var(_) | Pattern::Wildcard | Pattern::Lit(_) => {}
        Pattern::Ctor { args, .. } => {
            for a in args {
                f(a);
            }
        }
        Pattern::Or(l, r) => {
            f(l);
            f(r);
        }
        Pattern::Binding { sub, .. } => f(sub),
    }
}

/// Rebuild a `Pattern` by mapping each direct sub-pattern through `f`.
/// Pattern-bound names and constructor names stay as-is.
fn map_pattern_children<F>(pat: &Pattern, mut f: F) -> Pattern
where
    F: FnMut(&Pattern) -> Pattern,
{
    match pat {
        Pattern::Var(n) => Pattern::Var(n.clone()),
        Pattern::Wildcard => Pattern::Wildcard,
        Pattern::Lit(node) => Pattern::Lit(node.clone()),
        Pattern::Ctor { name, args } => Pattern::Ctor {
            name: name.clone(),
            args: args.iter().map(|a| f(a)).collect(),
        },
        Pattern::Or(l, r) => Pattern::Or(Box::new(f(l)), Box::new(f(r))),
        Pattern::Binding { name, sub } => Pattern::Binding {
            name: name.clone(),
            sub: Box::new(f(sub)),
        },
    }
}

pub fn strip_span_marks(expr: &Expr) -> Expr {
    Expr::new(strip_span_marks_node(&expr.node))
}

fn strip_span_marks_node(node: &ExprNode) -> ExprNode {
    match node {
        // SpanMark unwraps — recurse into inner without rebuilding the
        // SpanMark wrapper.
        ExprNode::SpanMark { inner, .. } => strip_span_marks_node(&inner.node),
        // All other variants: uniformly recurse into children.
        _ => map_children(node, |c| strip_span_marks(c)),
    }
}

fn substitute_impl(
    expr: &Expr,
    subst: &std::collections::HashMap<crate::lean_name::LeanName, Expr>,
) -> Expr {
    let node = match expr.node.scope_kind() {
        // Var: substitution leaf — replace if the name is in `subst`,
        // otherwise rebuild as-is. The `replacement.clone()` early-
        // returns because the result type is `Expr`, not `ExprNode`.
        ScopeKind::Var(name) => match subst.get(name) {
            Some(replacement) => return replacement.clone(),
            None => ExprNode::Var(name.clone()),
        },
        // Let: alpha-rename if the binder would capture a free var
        // from the substitution (#116). Same logic as the
        // Quantified arm (factored into `substitute_quantified`),
        // but `Let` is single-binder and lacks the `ty`/`kind` fields
        // that `Binder` carries — so we open-code rather than synthesize
        // a fake `Binder` for `apply_renames_to_binders`.
        ScopeKind::Let { name, value, body } => {
            let new_value = substitute_impl(value, subst);
            let inner_subst = subst_without(subst, name);
            let renames = compute_alpha_renames(&[name], &inner_subst, body);
            let (final_name, body_for_subst) = if let Some(fresh) = renames.get(name) {
                let rename_subst = rename_map_to_subst(&renames);
                let renamed_body = substitute_impl(body, &rename_subst);
                (fresh.clone(), renamed_body)
            } else {
                (name.clone(), body.clone())
            };
            ExprNode::Let {
                name: final_name,
                value: Box::new(new_value),
                body: Box::new(substitute_impl(&body_for_subst, &inner_subst)),
            }
        }
        // Quantified (Lambda/Forall/Exists): unified alpha-rename +
        // body subst via `substitute_quantified`. `kind.build` rebuilds
        // the right ExprNode constructor.
        ScopeKind::Quantified { kind, binders, body } => substitute_quantified(
            binders,
            body,
            subst,
            |bs, body| kind.build(bs, body),
        ),
        // Match: per-arm alpha-rename + remove pattern-bound names from
        // subst for the arm body. Factored into `substitute_match_arm`
        // (parallel to `substitute_quantified`).
        ScopeKind::Match { scrutinee, arms } => ExprNode::Match {
            scrutinee: Box::new(substitute_impl(scrutinee, subst)),
            arms: arms.iter().map(|a| substitute_match_arm(a, subst)).collect(),
        },
        // Non-binder compounds + leaves other than Var — uniformly
        // substitute into children. `map_children` preserves
        // `SpanMark` metadata, op codes, field names, etc.
        ScopeKind::Other => map_children(&expr.node, |c| substitute_impl(c, subst)),
    };
    Expr::new(node)
}

/// Compute an alpha-rename map for binders that would otherwise
/// capture a free variable from the substitution (#116).
///
/// Returns an empty map when no rename is needed. Otherwise the map
/// keys are the colliding binder names; the values are fresh
/// replacement names that:
/// * don't appear free OR bound anywhere in `body` (so the rename
///   substitution itself can't introduce new captures);
/// * don't appear free in any active substitution value (so the
///   subsequent main substitution won't re-capture);
/// * are distinct from all sibling binder names being kept unchanged
///   (multi-binder cases like `∀ x y, …` where only one collides).
///
/// Detection is the same lazy precision as the prior `check_capture_lazy`:
/// we only consider substitution values for keys that actually appear
/// free in the body, then check those values' free vars against the
/// binder names.
fn compute_alpha_renames(
    binder_names: &[&crate::lean_name::LeanName],
    inner_subst: &std::collections::HashMap<crate::lean_name::LeanName, Expr>,
    body: &Expr,
) -> std::collections::HashMap<crate::lean_name::LeanName, crate::lean_name::LeanName> {
    use std::collections::{HashMap, HashSet};
    if inner_subst.is_empty() {
        return HashMap::new();
    }
    let body_free: HashSet<String> = {
        let mut out = HashSet::new();
        collect_free_vars(body, &HashSet::new(), &mut out);
        out
    };
    let live_keys: Vec<&crate::lean_name::LeanName> = inner_subst.keys()
        .filter(|k| body_free.contains(k.as_str()))
        .collect();
    if live_keys.is_empty() {
        return HashMap::new();
    }
    let mut free_in_live_values: HashSet<String> = HashSet::new();
    for k in &live_keys {
        collect_free_vars(&inner_subst[*k], &HashSet::new(), &mut free_in_live_values);
    }
    // Find which binder names actually collide with a free var in
    // some live substitution value.
    let collisions: Vec<&crate::lean_name::LeanName> = binder_names.iter()
        .copied()
        .filter(|n| free_in_live_values.contains(n.as_str()))
        .collect();
    if collisions.is_empty() {
        return HashMap::new();
    }
    // Build the forbidden set for fresh-name generation:
    // - all names appearing anywhere in body (including bound ones,
    //   so the rename's `Var(fresh)` doesn't accidentally hit an
    //   inner shadow)
    // - all free vars of live substitution values
    // - all sibling binder names being kept unchanged (so multi-
    //   binder ∀x y. doesn't rename x and accidentally pick `y`)
    let mut forbidden: HashSet<String> = HashSet::new();
    collect_all_names(body, &mut forbidden);
    forbidden.extend(free_in_live_values.iter().cloned());
    for n in binder_names {
        forbidden.insert(n.as_str().to_string());
    }
    let mut renames: HashMap<crate::lean_name::LeanName, crate::lean_name::LeanName> =
        HashMap::new();
    for coll in collisions {
        let fresh = fresh_name(coll.as_str(), &forbidden);
        forbidden.insert(fresh.clone());  // keep distinctness across multi-collision
        renames.insert(coll.clone(), crate::lean_name::LeanName::synthetic(fresh));
    }
    renames
}

/// Collect every name (free or bound) that appears anywhere in `expr`.
/// Distinct from `collect_free_vars` — this includes names introduced
/// by inner binders, because a rename target `fresh` must not collide
/// with ANY name in `body` (an inner binder named `fresh` would
/// capture our just-renamed references).
fn collect_all_names(expr: &Expr, out: &mut std::collections::HashSet<String>) {
    match expr.node.scope_kind() {
        ScopeKind::Var(n) => {
            out.insert(n.as_str().to_string());
        }
        ScopeKind::Let { name, .. } => {
            out.insert(name.as_str().to_string());
            walk_children(&expr.node, |c| collect_all_names(c, out));
        }
        ScopeKind::Quantified { binders, .. } => {
            for b in binders {
                if let Some(n) = &b.name {
                    out.insert(n.as_str().to_string());
                }
            }
            walk_children(&expr.node, |c| collect_all_names(c, out));
        }
        ScopeKind::Match { arms, .. } => {
            for arm in arms {
                for n in pattern_bound_names(&arm.pattern) {
                    out.insert(n);
                }
            }
            walk_children(&expr.node, |c| collect_all_names(c, out));
        }
        ScopeKind::Other => walk_children(&expr.node, |c| collect_all_names(c, out)),
    }
}

/// Generate a fresh name by appending `_α<N>` to `base`, picking the
/// smallest N >= 1 such that the result is not in `forbidden`. Naming
/// uses `α` (Greek alpha) to make the alpha-renaming origin obvious
/// in error messages and generated Lean — Tactus's other gensym
/// prefixes use `_tactus_*`, so `_α<N>` is unambiguous.
fn fresh_name(base: &str, forbidden: &std::collections::HashSet<String>) -> String {
    for n in 1u64.. {
        let candidate = format!("{}_α{}", base, n);
        if !forbidden.contains(&candidate) {
            return candidate;
        }
    }
    unreachable!("fresh_name: ran out of u64 candidates");
}

/// Apply a rename map to a `Pattern`'s `Var` / `Binding` nodes.
/// Used by Match-arm alpha-renaming: when a pattern binds a name
/// that would capture, we rewrite both the pattern (so the bound
/// occurrence reflects the new name) AND the arm body (so the
/// references are kept consistent).
///
/// Pattern's `Ctor.name` is a constructor name (path-derived), not
/// a value-binding — left unchanged.
fn rename_in_pattern(
    pat: &Pattern,
    renames: &std::collections::HashMap<crate::lean_name::LeanName, crate::lean_name::LeanName>,
) -> Pattern {
    match pat {
        Pattern::Var(n) => {
            let new_name = renames.get(n).cloned().unwrap_or_else(|| n.clone());
            Pattern::Var(new_name)
        }
        Pattern::Binding { name, sub } => {
            let new_name = renames.get(name).cloned().unwrap_or_else(|| name.clone());
            Pattern::Binding {
                name: new_name,
                sub: Box::new(rename_in_pattern(sub, renames)),
            }
        }
        // Wildcard / Lit / Ctor / Or — no name to rewrite at this level;
        // recurse into sub-patterns.
        _ => map_pattern_children(pat, |p| rename_in_pattern(p, renames)),
    }
}

/// Build a substitution that maps each `old → Var(new)` from a
/// rename map. Used by all alpha-rename sites to prepare the
/// rename-pass on the body.
fn rename_map_to_subst(
    renames: &std::collections::HashMap<crate::lean_name::LeanName, crate::lean_name::LeanName>,
) -> std::collections::HashMap<crate::lean_name::LeanName, Expr> {
    renames.iter()
        .map(|(old, new)| (old.clone(), Expr::new(ExprNode::Var(new.clone()))))
        .collect()
}

/// Run the full alpha-rename + substitution dance for a multi-binder
/// `Lambda` / `Forall` / `Exists` shape. The three arms differ only
/// in their final `ExprNode` constructor; everything else is shared:
/// remove binders from the inner subst, compute renames, apply renames,
/// recurse on the body. `mk_node` is the per-arm constructor closure.
fn substitute_quantified(
    binders: &[Binder],
    body: &Expr,
    subst: &std::collections::HashMap<crate::lean_name::LeanName, Expr>,
    mk_node: impl FnOnce(Vec<Binder>, Box<Expr>) -> ExprNode,
) -> ExprNode {
    let inner_subst = subst_remove_binders(subst, binders);
    let binder_names: Vec<&crate::lean_name::LeanName> = binders.iter()
        .filter_map(|b| b.name.as_ref())
        .collect();
    let renames = compute_alpha_renames(&binder_names, &inner_subst, body);
    let (new_binders, body_for_subst) = apply_renames_to_binders(
        binders, body, &renames,
    );
    mk_node(new_binders, Box::new(substitute_impl(&body_for_subst, &inner_subst)))
}

/// Apply alpha-renames to a multi-binder `Lambda` / `Forall` / `Exists`
/// shape. Returns the rewritten binder list (with renamed names where
/// applicable) and the body cloned (renamed if any binder collided).
///
/// **Why also substitute into binder types.** Lean has dependent
/// types — `∀ (x : Nat) (h : x > 0), …` is legal. If `x` gets renamed
/// to `x_α1`, the second binder's type `x > 0` must also get its
/// `x` renamed to `x_α1` to stay consistent. Substituting the rename
/// map into each binder's type is idempotent for non-dependent types
/// (they don't reference earlier binders) and correct for dependent
/// types.
///
/// Returns the new binders + the body to feed into the next
/// substitution pass. When no renames apply, returns the original
/// binders and a clone of the body — keeps the caller-side code
/// uniform (always feeds the result back into `substitute_impl`).
fn apply_renames_to_binders(
    binders: &[Binder],
    body: &Expr,
    renames: &std::collections::HashMap<crate::lean_name::LeanName, crate::lean_name::LeanName>,
) -> (Vec<Binder>, Expr) {
    if renames.is_empty() {
        return (binders.to_vec(), body.clone());
    }
    let rename_subst = rename_map_to_subst(renames);
    let new_binders: Vec<Binder> = binders.iter().map(|b| {
        let new_name = b.name.as_ref().map(|n| {
            renames.get(n).cloned().unwrap_or_else(|| n.clone())
        });
        // Apply rename map to the binder's type — handles dependent
        // types where a later binder's type references an earlier
        // (renamed) binder.
        let new_ty = substitute_impl(&b.ty, &rename_subst);
        Binder { name: new_name, ty: new_ty, kind: b.kind }
    }).collect();
    let renamed_body = substitute_impl(body, &rename_subst);
    (new_binders, renamed_body)
}

/// Run alpha-rename + substitution for a single `MatchArm`. Mirrors
/// `substitute_quantified` for Lambda/Forall/Exists: extract the
/// arm's pattern-bound names, remove them from the substitution map,
/// compute alpha-renames if any pattern-bound name would capture a
/// free var of the live substitution, then recurse on the body.
///
/// The pattern is rewritten via `rename_in_pattern` in lockstep with
/// the body, so a renamed binding (`Pattern::Var(x) → Pattern::Var(x_α1)`)
/// stays consistent with body references (`Var(x) → Var(x_α1)`).
fn substitute_match_arm(
    arm: &MatchArm,
    subst: &std::collections::HashMap<crate::lean_name::LeanName, Expr>,
) -> MatchArm {
    let bound: Vec<crate::lean_name::LeanName> = pattern_bound_names(&arm.pattern)
        .into_iter()
        .map(crate::lean_name::LeanName::synthetic)
        .collect();
    let mut inner = subst.clone();
    for n in &bound {
        inner.remove(n);
    }
    let bound_refs: Vec<&crate::lean_name::LeanName> = bound.iter().collect();
    let renames = compute_alpha_renames(&bound_refs, &inner, &arm.body);
    let (final_pattern, body_for_subst) = if renames.is_empty() {
        (arm.pattern.clone(), arm.body.clone())
    } else {
        let rename_subst = rename_map_to_subst(&renames);
        let renamed_body = substitute_impl(&arm.body, &rename_subst);
        (rename_in_pattern(&arm.pattern, &renames), renamed_body)
    };
    MatchArm {
        pattern: final_pattern,
        body: substitute_impl(&body_for_subst, &inner),
    }
}

fn subst_without(
    subst: &std::collections::HashMap<crate::lean_name::LeanName, Expr>,
    name: &crate::lean_name::LeanName,
) -> std::collections::HashMap<crate::lean_name::LeanName, Expr> {
    let mut out = subst.clone();
    out.remove(name);
    out
}

fn subst_remove_binders(
    subst: &std::collections::HashMap<crate::lean_name::LeanName, Expr>,
    binders: &[Binder],
) -> std::collections::HashMap<crate::lean_name::LeanName, Expr> {
    let mut out = subst.clone();
    for b in binders {
        if let Some(n) = &b.name { out.remove(n); }
    }
    out
}

fn collect_free_vars(
    expr: &Expr,
    bound: &std::collections::HashSet<String>,
    out: &mut std::collections::HashSet<String>,
) {
    match expr.node.scope_kind() {
        ScopeKind::Var(n) => {
            if !bound.contains(n.as_str()) {
                out.insert(n.as_str().to_string());
            }
        }
        // Let: value is in outer scope, body is in scope extended with name.
        ScopeKind::Let { name, value, body } => {
            collect_free_vars(value, bound, out);
            let mut inner = bound.clone();
            inner.insert(name.as_str().to_string());
            collect_free_vars(body, &inner, out);
        }
        // Quantified (Lambda/Forall/Exists): binder types are in OUTER
        // scope (not yet bound by their own binder), body is in
        // extended scope. Lean's dependent types DO let later binder
        // types reference earlier binders, but this function (used for
        // capture detection in alpha-renaming) treats binder types
        // conservatively as outer-scope; the caller scopes them later
        // if needed.
        ScopeKind::Quantified { binders, body, .. } => {
            let mut inner = bound.clone();
            for b in binders {
                if let Some(n) = &b.name {
                    inner.insert(n.as_str().to_string());
                }
            }
            collect_free_vars(body, &inner, out);
        }
        // Match: scrutinee in outer scope, each arm body in scope
        // extended with the arm's pattern-bound names.
        ScopeKind::Match { scrutinee, arms } => {
            collect_free_vars(scrutinee, bound, out);
            for arm in arms {
                let mut inner = bound.clone();
                for n in pattern_bound_names(&arm.pattern) {
                    inner.insert(n);
                }
                collect_free_vars(&arm.body, &inner, out);
            }
        }
        // No-binder variants: walk children with the same scope.
        ScopeKind::Other => walk_children(&expr.node, |c| collect_free_vars(c, bound, out)),
    }
}

/// Does `expr` reference `target` as a *free* variable anywhere?
///
/// "Free" means not shadowed by an enclosing `Let` / `Lambda` /
/// `Forall` / `Exists` / `Match`-pattern binder. Used by callers
/// that need to detect substitution loops or self-references —
/// e.g., `sst_to_lean::extract_top_level_eq_for` (#128) rejects
/// `r == E` clauses where E mentions r as a free variable, because
/// substituting `r → E` in such patterns would loop.
///
/// Implemented as a thin wrapper over the private `collect_free_vars`
/// — same walk, same scope tracking — to avoid duplicating the
/// per-variant dispatch. The HashSet allocation is fine at our
/// call rate (a few times per fn at codegen); a future
/// allocation-free early-exit variant could be added if profiling
/// shows it matters.
pub fn mentions_free_var(expr: &Expr, target: &str) -> bool {
    let mut found = std::collections::HashSet::new();
    collect_free_vars(expr, &std::collections::HashSet::new(), &mut found);
    found.contains(target)
}

fn pattern_bound_names(pat: &Pattern) -> Vec<String> {
    let mut out = Vec::new();
    pattern_bound_names_impl(pat, &mut out);
    out
}

fn pattern_bound_names_impl(pat: &Pattern, out: &mut Vec<String>) {
    match pat {
        Pattern::Var(n) => out.push(n.as_str().to_string()),
        Pattern::Binding { name, sub } => {
            out.push(name.as_str().to_string());
            pattern_bound_names_impl(sub, out);
        }
        // Wildcard / Lit / Ctor / Or — no name introduced at this level;
        // recurse into sub-patterns (Wildcard / Lit have none).
        _ => walk_pattern_children(pat, |p| pattern_bound_names_impl(p, out)),
    }
}

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

#[cfg(test)]
mod substitute_tests {
    //! Direct unit tests for `substitute`. Covers:
    //!   - basic Var sub + no-op cases
    //!   - binder shadowing (Let / Forall / Exists / Lambda / Match)
    //!   - lazy capture panics (real capture detected)
    //!   - lazy capture does NOT panic when binder is out of subst scope
    //!   - TypeAnnot substitutes in type position
    //!   - recursive structure (nested binders, if/match)
    use super::*;
    use std::collections::HashMap;

    use crate::lean_name::LeanName;

    fn var(n: &str) -> Expr { Expr::new(ExprNode::Var(LeanName::lit(n))) }
    fn lit(n: i64) -> Expr { Expr::new(ExprNode::Lit(n.to_string())) }
    fn add(l: Expr, r: Expr) -> Expr {
        Expr::new(ExprNode::BinOp { op: BinOp::Add, lhs: Box::new(l), rhs: Box::new(r) })
    }
    fn let_bind(name: &str, val: Expr, body: Expr) -> Expr {
        Expr::new(ExprNode::Let {
            name: LeanName::lit(name), value: Box::new(val), body: Box::new(body),
        })
    }
    fn forall(binder_name: &str, body: Expr) -> Expr {
        Expr::new(ExprNode::Forall {
            binders: vec![Binder {
                name: Some(LeanName::lit(binder_name)),
                ty: var("Int"),
                kind: BinderKind::Explicit,
            }],
            body: Box::new(body),
        })
    }
    fn exists(binder_name: &str, body: Expr) -> Expr {
        Expr::new(ExprNode::Exists {
            binders: vec![Binder {
                name: Some(LeanName::lit(binder_name)),
                ty: var("Int"),
                kind: BinderKind::Explicit,
            }],
            body: Box::new(body),
        })
    }
    fn lambda(binder_name: &str, body: Expr) -> Expr {
        Expr::new(ExprNode::Lambda {
            binders: vec![Binder {
                name: Some(LeanName::lit(binder_name)),
                ty: var("Int"),
                kind: BinderKind::Explicit,
            }],
            body: Box::new(body),
        })
    }
    fn subst_of(pairs: &[(&str, Expr)]) -> HashMap<crate::lean_name::LeanName, Expr> {
        pairs.iter().map(|(k, v)| (LeanName::lit(*k), v.clone())).collect()
    }
    fn node_eq(a: &Expr, b: &Expr) -> bool {
        // Printed form as a rough structural-equality check — the
        // pretty-printer is deterministic so equivalent ASTs produce
        // identical strings.
        crate::lean_pp::pp_expr(a) == crate::lean_pp::pp_expr(b)
    }

    #[test]
    fn empty_subst_is_noop() {
        let e = add(var("x"), var("y"));
        let out = substitute(&e, &HashMap::new());
        assert!(node_eq(&out, &e));
    }

    #[test]
    fn simple_var_substitution() {
        // x + y with {x: 1, y: 2}  →  1 + 2
        let e = add(var("x"), var("y"));
        let s = subst_of(&[("x", lit(1)), ("y", lit(2))]);
        let expected = add(lit(1), lit(2));
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn leaves_unsubstituted_vars_alone() {
        // x + y with {x: 1}  →  1 + y
        let e = add(var("x"), var("y"));
        let s = subst_of(&[("x", lit(1))]);
        let expected = add(lit(1), var("y"));
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn literals_pass_through() {
        let e = add(lit(1), lit(2));
        let s = subst_of(&[("x", lit(99))]);
        assert!(node_eq(&substitute(&e, &s), &e));
    }

    #[test]
    fn let_shadows_subst_key() {
        // let x := 3; x + y  with {x: 1, y: 2}
        //   inside let, x is re-bound, so x stays; y becomes 2
        //   →  let x := 3; x + 2
        // (value of x := 3 is the new binding; y substitutes normally.)
        let e = let_bind("x", lit(3), add(var("x"), var("y")));
        let s = subst_of(&[("x", lit(1)), ("y", lit(2))]);
        let expected = let_bind("x", lit(3), add(var("x"), lit(2)));
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn let_value_uses_outer_subst() {
        // let y := x; body  with {x: 42}  →  let y := 42; body
        // The value side sees the outer substitution; the body sees
        // the let-bound `y`.
        let e = let_bind("y", var("x"), var("y"));
        let s = subst_of(&[("x", lit(42))]);
        let expected = let_bind("y", lit(42), var("y"));
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn forall_shadows() {
        // ∀ x. x + y  with {x: 1, y: 2}  →  ∀ x. x + 2
        let e = forall("x", add(var("x"), var("y")));
        let s = subst_of(&[("x", lit(1)), ("y", lit(2))]);
        let expected = forall("x", add(var("x"), lit(2)));
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn exists_shadows() {
        let e = exists("x", add(var("x"), var("y")));
        let s = subst_of(&[("x", lit(1)), ("y", lit(2))]);
        let expected = exists("x", add(var("x"), lit(2)));
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn lambda_shadows() {
        let e = lambda("x", add(var("x"), var("y")));
        let s = subst_of(&[("x", lit(1)), ("y", lit(2))]);
        let expected = lambda("x", add(var("x"), lit(2)));
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn capture_alpha_renames_forall_binder() {
        // ∀ y. x + y  with {x: y}
        // x is free inside ∀ y.; substituting x→y would capture the
        // substituted `y` inside the ∀. Post-#116: the binder `y`
        // alpha-renames to `y_α1` (fresh), the body's bound `y`
        // becomes `y_α1`, then x → y substitutes cleanly. Result:
        // ∀ y_α1. y + y_α1.
        let e = forall("y", add(var("x"), var("y")));
        let s = subst_of(&[("x", var("y"))]);
        let result = substitute(&e, &s);
        let printed = crate::lean_pp::pp_expr(&result);
        // Binder must have been renamed (no longer just `y`).
        assert!(printed.contains("y_α1"),
            "expected alpha-rename suffix in result; got: {}", printed);
        // Substituted x must still appear as the free `y`.
        // We check by structural shape: the result should be
        // ∀ y_α1. y + y_α1
        let expected = forall("y_α1", add(var("y"), var("y_α1")));
        assert!(node_eq(&result, &expected),
            "expected alpha-renamed structure; got: {}", printed);
    }

    #[test]
    fn capture_false_positive_avoided_when_binder_out_of_subst_scope() {
        // (∀ y. z) + x  with {x: y}
        // The outer binder `∀ y.` doesn't contain `x`, so substitution
        // never enters its scope — no capture is possible. Old eager
        // check would panic; lazy check correctly passes.
        let e = add(forall("y", var("z")), var("x"));
        let s = subst_of(&[("x", var("y"))]);
        // No panic expected.
        let expected = add(forall("y", var("z")), var("y"));
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn capture_false_positive_avoided_when_binder_shadows_all_subst_keys() {
        // ∀ x. x  with {x: y}
        // Inside the ∀, `x` is re-bound; subst key `x` is removed from
        // inner_subst which becomes empty. No capture risk even though
        // `y` (free in the subst value) might match a hypothetical
        // binder — because subst is empty inside the binder.
        let e = forall("x", var("x"));
        let s = subst_of(&[("x", var("y"))]);
        let expected = forall("x", var("x"));
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn nested_binders_respected() {
        // let x := 1; ∀ y. x + y   with {x: 99, y: 77}
        //   x on the value side → 99 (not shadowed yet)
        //   inside let: x now re-bound, ∀ y re-binds y
        //   → let x := 99; ∀ y. x + y
        let e = let_bind("x", var("x"), forall("y", add(var("x"), var("y"))));
        let s = subst_of(&[("x", lit(99)), ("y", lit(77))]);
        let expected = let_bind("x", lit(99), forall("y", add(var("x"), var("y"))));
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn if_substitutes_in_all_branches() {
        // if c then x else y   with {c: True, x: 1, y: 2}
        //   → if True then 1 else 2
        let e = Expr::new(ExprNode::If {
            cond: Box::new(var("c")),
            then_: Box::new(var("x")),
            else_: Some(Box::new(var("y"))),
        });
        let s = subst_of(&[
            ("c", Expr::new(ExprNode::LitBool(true))),
            ("x", lit(1)),
            ("y", lit(2)),
        ]);
        let expected = Expr::new(ExprNode::If {
            cond: Box::new(Expr::new(ExprNode::LitBool(true))),
            then_: Box::new(lit(1)),
            else_: Some(Box::new(lit(2))),
        });
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn type_annot_substitutes_in_type_position() {
        // (x : T)  with {x: 42, T: Int}
        //   → (42 : Int)
        let e = Expr::new(ExprNode::TypeAnnot {
            expr: Box::new(var("x")),
            ty: Box::new(var("T")),
        });
        let s = subst_of(&[("x", lit(42)), ("T", var("Int"))]);
        let expected = Expr::new(ExprNode::TypeAnnot {
            expr: Box::new(lit(42)),
            ty: Box::new(var("Int")),
        });
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn field_proj_preserves_field_name() {
        // e.foo  with {e: x}  →  x.foo  (field name unchanged)
        let e = Expr::new(ExprNode::FieldProj {
            expr: Box::new(var("e")),
            field: "foo".to_string(),
        });
        let s = subst_of(&[("e", var("x")), ("foo", lit(999))]);
        let expected = Expr::new(ExprNode::FieldProj {
            expr: Box::new(var("x")),
            field: "foo".to_string(),
        });
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn app_substitutes_head_and_args() {
        // f x y  with {f: g, x: 1, y: 2}  →  g 1 2
        let e = Expr::new(ExprNode::App {
            head: Box::new(var("f")),
            args: vec![var("x"), var("y")],
        });
        let s = subst_of(&[("f", var("g")), ("x", lit(1)), ("y", lit(2))]);
        let expected = Expr::new(ExprNode::App {
            head: Box::new(var("g")),
            args: vec![lit(1), lit(2)],
        });
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn match_arm_pattern_shadows() {
        // match scrut with | Some(x) => x + y | None => y
        //   with {x: 99, y: 42}
        //   In the Some arm: `x` is pattern-bound, so stays; y→42.
        //   In the None arm: no bindings, y→42.
        //   → match scrut with | Some(x) => x + 42 | None => 42
        let e = Expr::new(ExprNode::Match {
            scrutinee: Box::new(var("scrut")),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Ctor {
                        name: "Some".to_string(),
                        args: vec![Pattern::Var(LeanName::lit("x"))],
                    },
                    body: add(var("x"), var("y")),
                },
                MatchArm {
                    pattern: Pattern::Ctor { name: "None".to_string(), args: vec![] },
                    body: var("y"),
                },
            ],
        });
        let s = subst_of(&[("x", lit(99)), ("y", lit(42))]);
        let out = substitute(&e, &s);
        // Spot-check printed form has x surviving in the Some arm
        // and y→42 in both arms.
        let printed = crate::lean_pp::pp_expr(&out);
        assert!(printed.contains("Some x"), "Some arm should keep x: {}", printed);
        assert!(printed.contains("x + 42"), "Some arm body should read x + 42: {}", printed);
        assert!(!printed.contains("+ y"), "y should be substituted: {}", printed);
    }

    // ── Audit-driven tests: per-variant coverage ────────────────

    #[test]
    fn unop_substitutes_into_arg() {
        // ¬x  with {x: True}  →  ¬True
        let e = Expr::new(ExprNode::UnOp {
            op: UnOp::Not,
            arg: Box::new(var("x")),
        });
        let s = subst_of(&[("x", Expr::new(ExprNode::LitBool(true)))]);
        let expected = Expr::new(ExprNode::UnOp {
            op: UnOp::Not,
            arg: Box::new(Expr::new(ExprNode::LitBool(true))),
        });
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn struct_update_substitutes_base_and_updates() {
        // {base with f1 := x, f2 := y}  with {base: b, x: 1, y: 2}
        //   → {b with f1 := 1, f2 := 2}
        let e = Expr::new(ExprNode::StructUpdate {
            base: Box::new(var("base")),
            updates: vec![
                ("f1".to_string(), var("x")),
                ("f2".to_string(), var("y")),
            ],
        });
        let s = subst_of(&[
            ("base", var("b")),
            ("x", lit(1)),
            ("y", lit(2)),
        ]);
        let expected = Expr::new(ExprNode::StructUpdate {
            base: Box::new(var("b")),
            updates: vec![
                ("f1".to_string(), lit(1)),
                ("f2".to_string(), lit(2)),
            ],
        });
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn array_lit_substitutes_each_element() {
        // [x, y, z]  with {x: 1, y: 2}  →  [1, 2, z]
        let e = Expr::new(ExprNode::ArrayLit(vec![var("x"), var("y"), var("z")]));
        let s = subst_of(&[("x", lit(1)), ("y", lit(2))]);
        let expected = Expr::new(ExprNode::ArrayLit(vec![lit(1), lit(2), var("z")]));
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn anon_substitutes_each_element() {
        // ⟨x, y⟩  with {x: 1, y: 2}  →  ⟨1, 2⟩
        let e = Expr::new(ExprNode::Anon(vec![var("x"), var("y")]));
        let s = subst_of(&[("x", lit(1)), ("y", lit(2))]);
        let expected = Expr::new(ExprNode::Anon(vec![lit(1), lit(2)]));
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn index_substitutes_base_and_idx() {
        // base[i]  with {base: arr, i: 0}  →  arr[0]
        let e = Expr::new(ExprNode::Index {
            base: Box::new(var("base")),
            idx: Box::new(var("i")),
            bang: false,
        });
        let s = subst_of(&[("base", var("arr")), ("i", lit(0))]);
        let expected = Expr::new(ExprNode::Index {
            base: Box::new(var("arr")),
            idx: Box::new(lit(0)),
            bang: false,
        });
        assert!(node_eq(&substitute(&e, &s), &expected));
    }

    #[test]
    fn raw_is_opaque_to_substitution() {
        // `Raw` is verbatim Lean text — we don't parse into it, so no
        // substitution can apply. Even if a subst key happens to match
        // the text, Raw stays literal.
        let e = Expr::new(ExprNode::Raw("x + y".to_string()));
        let s = subst_of(&[("x", lit(1)), ("y", lit(2))]);
        let out = substitute(&e, &s);
        let printed = crate::lean_pp::pp_expr(&out);
        // The Raw text is preserved verbatim; no x→1 or y→2 inside.
        assert!(printed.contains("x + y"), "Raw should preserve contents: {}", printed);
    }

    // ── Multi-binder shadowing ──────────────────────────────────

    #[test]
    fn multi_binder_forall_shadows_all() {
        // ∀ x y. x + y + z   with {x: 1, y: 2, z: 99}
        //   Inner scope: x and y re-bound; z subst fires.
        //   → ∀ x y. x + y + 99
        let e = Expr::new(ExprNode::Forall {
            binders: vec![
                Binder {
                    name: Some(LeanName::lit("x")),
                    ty: var("Int"),
                    kind: BinderKind::Explicit,
                },
                Binder {
                    name: Some(LeanName::lit("y")),
                    ty: var("Int"),
                    kind: BinderKind::Explicit,
                },
            ],
            body: Box::new(add(add(var("x"), var("y")), var("z"))),
        });
        let s = subst_of(&[("x", lit(1)), ("y", lit(2)), ("z", lit(99))]);
        let out = substitute(&e, &s);
        let printed = crate::lean_pp::pp_expr(&out);
        // Binders `x` and `y` survive; body shows `+ 99` (from z→99).
        assert!(printed.contains("∀") || printed.contains("forall"),
            "should still be a Forall: {}", printed);
        assert!(printed.contains("99"), "z should be substituted to 99: {}", printed);
        // Crucially, x and y should NOT have been substituted.
        assert!(!printed.contains("1 + 2"), "x,y should stay bound: {}", printed);
    }

    #[test]
    fn multi_binder_forall_capture_panics_on_first_offending_binder() {
        // ∀ x y. x + y   with {z: x}  — z doesn't occur in body, so
        // no substitution inside; binders `x` and `y` happen to match
        // free vars in subst values but that's a false positive and
        // the lazy check should pass.
        let e = Expr::new(ExprNode::Forall {
            binders: vec![
                Binder {
                    name: Some(LeanName::lit("x")),
                    ty: var("Int"),
                    kind: BinderKind::Explicit,
                },
                Binder {
                    name: Some(LeanName::lit("y")),
                    ty: var("Int"),
                    kind: BinderKind::Explicit,
                },
            ],
            body: Box::new(add(var("x"), var("y"))),
        });
        let s = subst_of(&[("z", var("x"))]);
        // z doesn't occur free in the body, so the capture check
        // short-circuits on the "live keys" emptiness check.
        let _ = substitute(&e, &s);
    }

    #[test]
    fn capture_alpha_renames_let_binder() {
        // let y := 5; x + y   with {x: y}
        //   x is free in the body; substituting x→y would capture
        //   the let's bound y. Alpha-rename: let y_α1 := 5; y + y_α1.
        let body = add(var("x"), var("y"));
        let e = let_bind("y", lit(5), body);
        let s = subst_of(&[("x", var("y"))]);
        let result = substitute(&e, &s);
        let expected = let_bind("y_α1", lit(5), add(var("y"), var("y_α1")));
        let p = crate::lean_pp::pp_expr(&result);
        assert!(node_eq(&result, &expected),
            "expected alpha-renamed let; got: {}", p);
    }

    #[test]
    fn capture_alpha_renames_lambda_binder() {
        // (fun y => x + y)   with {x: y}
        //   Same shape as forall case, lambda flavor.
        let body = add(var("x"), var("y"));
        let e = Expr::new(ExprNode::Lambda {
            binders: vec![Binder {
                name: Some(LeanName::lit("y")),
                ty: var("Int"),
                kind: BinderKind::Explicit,
            }],
            body: Box::new(body),
        });
        let s = subst_of(&[("x", var("y"))]);
        let result = substitute(&e, &s);
        let p = crate::lean_pp::pp_expr(&result);
        // Lambda's bound y should rename to y_α1; body's reference
        // becomes y_α1; substituted x becomes free y.
        assert!(p.contains("y_α1"),
            "expected lambda binder renamed; got: {}", p);
        assert!(mentions_free_var(&result, "y"),
            "expected substituted free y in body; got: {}", p);
    }

    #[test]
    fn capture_alpha_renames_exists_binder() {
        // ∃ y. x + y   with {x: y}
        let body = add(var("x"), var("y"));
        let e = Expr::new(ExprNode::Exists {
            binders: vec![Binder {
                name: Some(LeanName::lit("y")),
                ty: var("Int"),
                kind: BinderKind::Explicit,
            }],
            body: Box::new(body),
        });
        let s = subst_of(&[("x", var("y"))]);
        let result = substitute(&e, &s);
        let p = crate::lean_pp::pp_expr(&result);
        assert!(p.contains("y_α1"),
            "expected exists binder renamed; got: {}", p);
        assert!(mentions_free_var(&result, "y"),
            "expected free y after substitution; got: {}", p);
    }

    #[test]
    fn capture_alpha_renames_match_pattern_var() {
        // match scr with | Var(y) => x + y    with {x: y}
        //   Pattern `y` would capture the substituted y. Rename
        //   pattern to `y_α1` and rewrite arm body.
        let arm_body = add(var("x"), var("y"));
        let e = Expr::new(ExprNode::Match {
            scrutinee: Box::new(var("scr")),
            arms: vec![MatchArm {
                pattern: Pattern::Var(LeanName::lit("y")),
                body: arm_body,
            }],
        });
        let s = subst_of(&[("x", var("y"))]);
        let result = substitute(&e, &s);
        let p = crate::lean_pp::pp_expr(&result);
        assert!(p.contains("y_α1"),
            "expected match pattern var renamed; got: {}", p);
        assert!(mentions_free_var(&result, "y"),
            "expected free y after substitution (the substituted-x value); got: {}", p);
    }

    #[test]
    fn capture_alpha_renames_match_ctor_args() {
        // match scr with | Ctor(y, z) => x + y    with {x: y}
        //   Pattern's nested `y` binding would capture. Rename y →
        //   y_α1 in pattern AND body, leave `z` alone.
        let arm_body = add(var("x"), var("y"));
        let e = Expr::new(ExprNode::Match {
            scrutinee: Box::new(var("scr")),
            arms: vec![MatchArm {
                pattern: Pattern::Ctor {
                    name: "MyCtor".into(),
                    args: vec![
                        Pattern::Var(LeanName::lit("y")),
                        Pattern::Var(LeanName::lit("z")),
                    ],
                },
                body: arm_body,
            }],
        });
        let s = subst_of(&[("x", var("y"))]);
        let result = substitute(&e, &s);
        let p = crate::lean_pp::pp_expr(&result);
        assert!(p.contains("y_α1"),
            "expected ctor pattern arg renamed; got: {}", p);
        // z should NOT be renamed (no collision).
        // Pretty-printer prints `MyCtor y_α1 z` so look for ` z`.
        assert!(p.contains(" z "),
            "expected non-colliding ctor arg z unchanged; got: {}", p);
    }

    #[test]
    fn capture_alpha_renames_dependent_type_in_forall() {
        // ∀ (x : Nat) (h : x > 0), x + h   with {z: x}
        //   z doesn't appear in body, so no real substitution. Use
        //   a different shape: body references z, subst z→x.
        // ∀ (x : Nat) (h : x > 0), z   with {z: x}
        //   Binder x would capture substituted x; second binder's
        //   type `x > 0` references that x. Rename x → x_α1: the
        //   second binder's type becomes `x_α1 > 0`, the body's
        //   substituted z becomes the free x. Result: ∀ (x_α1 : Nat)
        //   (h : x_α1 > 0), x.
        let e = Expr::new(ExprNode::Forall {
            binders: vec![
                Binder {
                    name: Some(LeanName::lit("x")),
                    ty: var("Nat"),
                    kind: BinderKind::Explicit,
                },
                Binder {
                    name: Some(LeanName::lit("h")),
                    ty: Expr::new(ExprNode::BinOp {
                        op: BinOp::Gt,
                        lhs: Box::new(var("x")),
                        rhs: Box::new(lit(0)),
                    }),
                    kind: BinderKind::Explicit,
                },
            ],
            body: Box::new(var("z")),
        });
        let s = subst_of(&[("z", var("x"))]);
        let result = substitute(&e, &s);
        let p = crate::lean_pp::pp_expr(&result);
        // x renamed; second binder's type also references the renamed name.
        assert!(p.contains("x_α1"),
            "expected x renamed to x_α1; got: {}", p);
        // The expected dependent-type rewrite: `x_α1 > 0`.
        assert!(p.contains("x_α1 > 0"),
            "expected dependent-type to track rename; got: {}", p);
    }

    #[test]
    fn capture_alpha_rename_preserves_non_colliding_siblings() {
        // ∀ x y. z + y   with {z: x}
        //   x renames to x_α1; y stays y. Sibling y must NOT also rename.
        let e = Expr::new(ExprNode::Forall {
            binders: vec![
                Binder {
                    name: Some(LeanName::lit("x")),
                    ty: var("Int"),
                    kind: BinderKind::Explicit,
                },
                Binder {
                    name: Some(LeanName::lit("y")),
                    ty: var("Int"),
                    kind: BinderKind::Explicit,
                },
            ],
            body: Box::new(add(var("z"), var("y"))),
        });
        let s = subst_of(&[("z", var("x"))]);
        let result = substitute(&e, &s);
        let p = crate::lean_pp::pp_expr(&result);
        assert!(p.contains("x_α1"),
            "expected x renamed; got: {}", p);
        assert!(!p.contains("y_α"),
            "expected y NOT renamed (no collision); got: {}", p);
    }

    #[test]
    fn capture_alpha_rename_avoids_existing_freshness() {
        // ∀ y. x + y_α1 + y   with {x: y}
        //   Body already mentions `y_α1` (just a free var); fresh
        //   should pick `y_α2` instead, not collide.
        let body = add(add(var("x"), var("y_α1")), var("y"));
        let e = forall("y", body);
        let s = subst_of(&[("x", var("y"))]);
        let result = substitute(&e, &s);
        let p = crate::lean_pp::pp_expr(&result);
        assert!(p.contains("y_α2"),
            "expected fresh to skip taken y_α1; got: {}", p);
    }

    #[test]
    fn capture_alpha_rename_multi_binder_collision() {
        // ∀ x y. z1 + z2   with {z1: x, z2: y}
        //   Both binders collide. Both should rename.
        let e = Expr::new(ExprNode::Forall {
            binders: vec![
                Binder {
                    name: Some(LeanName::lit("x")),
                    ty: var("Int"),
                    kind: BinderKind::Explicit,
                },
                Binder {
                    name: Some(LeanName::lit("y")),
                    ty: var("Int"),
                    kind: BinderKind::Explicit,
                },
            ],
            body: Box::new(add(var("z1"), var("z2"))),
        });
        let s = subst_of(&[("z1", var("x")), ("z2", var("y"))]);
        let result = substitute(&e, &s);
        let p = crate::lean_pp::pp_expr(&result);
        assert!(p.contains("x_α1"),
            "expected x renamed; got: {}", p);
        assert!(p.contains("y_α1"),
            "expected y renamed; got: {}", p);
    }

    #[test]
    fn multi_binder_real_capture_alpha_renames() {
        // ∀ x y. z + y   with {z: x}
        //   z occurs free in the body and subst z→x; binder `x` would
        //   capture the substituted x. Post-#116: the colliding `x`
        //   binder alpha-renames to `x_α1`, body's bound `x` becomes
        //   `x_α1` (no body refs to x except via subst), then z → x
        //   substitutes. Sibling `y` stays `y` since no collision.
        //   Result: ∀ x_α1 y. x + y.
        let e = Expr::new(ExprNode::Forall {
            binders: vec![
                Binder {
                    name: Some(LeanName::lit("x")),
                    ty: var("Int"),
                    kind: BinderKind::Explicit,
                },
                Binder {
                    name: Some(LeanName::lit("y")),
                    ty: var("Int"),
                    kind: BinderKind::Explicit,
                },
            ],
            body: Box::new(add(var("z"), var("y"))),
        });
        let s = subst_of(&[("z", var("x"))]);
        let result = substitute(&e, &s);
        let printed = crate::lean_pp::pp_expr(&result);
        // Result should be ∀ x_α1 y. x + y — x renamed, y unchanged.
        assert!(printed.contains("x_α1"),
            "expected x to be alpha-renamed; got: {}", printed);
        // Pretty-printer prints the binders as `(x_α1 : Int) (y : Int)`,
        // so we look for both forms.
        assert!(printed.contains("y : Int"),
            "expected y binder unchanged; got: {}", printed);
        // Body should now reference free `x` (the substituted z) and
        // bound `y`. Verify x is mentioned free post-substitution.
        // (This is the substituted-z path.)
        // Free-vars check: result mentions `x` free.
        assert!(mentions_free_var(&result, "x"),
            "expected free `x` (substituted from z) in result; got: {}", printed);
    }

    // ── mentions_free_var ──────────────────────────────────────────────

    #[test]
    fn mentions_free_var_finds_free_occurrence() {
        let e = add(var("x"), lit(1));
        assert!(mentions_free_var(&e, "x"));
        assert!(!mentions_free_var(&e, "y"));
    }

    #[test]
    fn mentions_free_var_skips_let_shadowed() {
        // `let x := 1; x + 2` — the inner `x` is bound by the let, not free.
        let body = add(var("x"), lit(2));
        let e = let_bind("x", lit(1), body);
        // Outer `x` reference (the let's name) is bound, body's `x` is bound by it.
        // From outside, `x` is not free anywhere.
        assert!(!mentions_free_var(&e, "x"));
    }

    #[test]
    fn mentions_free_var_finds_free_in_let_value() {
        // `let y := x; y + 1` — `x` IS free (it's in the let's value position).
        let val = var("x");
        let body = add(var("y"), lit(1));
        let e = let_bind("y", val, body);
        assert!(mentions_free_var(&e, "x"));
    }

    #[test]
    fn mentions_free_var_skips_forall_shadowed() {
        // `∀ x, x + 1` — `x` is bound by the forall.
        let body = add(var("x"), lit(1));
        let e = forall("x", body);
        assert!(!mentions_free_var(&e, "x"));
    }

    #[test]
    fn mentions_free_var_skips_exists_shadowed() {
        let body = add(var("x"), lit(1));
        let e = exists("x", body);
        assert!(!mentions_free_var(&e, "x"));
    }

    #[test]
    fn mentions_free_var_finds_through_compound_shapes() {
        // `if c then x + 1 else y` — both c and x and y are free.
        let then_e = add(var("x"), lit(1));
        let else_e = var("y");
        let e = Expr::new(ExprNode::If {
            cond: Box::new(var("c")),
            then_: Box::new(then_e),
            else_: Some(Box::new(else_e)),
        });
        assert!(mentions_free_var(&e, "c"));
        assert!(mentions_free_var(&e, "x"));
        assert!(mentions_free_var(&e, "y"));
        assert!(!mentions_free_var(&e, "z"));
    }

    // ── walk_children / map_children regression guards (#98) ─────────

    /// `map_children` with the identity function should round-trip
    /// every variant — locks in that no field is dropped or duplicated
    /// when adding a variant. If a future contributor adds an
    /// `ExprNode` variant to `map_children` but accidentally swaps
    /// `lhs`/`rhs` or forgets to clone a metadata field, this test
    /// surfaces it as a structural mismatch on the variant.
    #[test]
    fn map_children_identity_roundtrips_all_variants() {
        // A composite expression touching every ExprNode variant —
        // walk inwards through map_children with the identity mapper
        // and assert pp equality.
        let exprs: Vec<Expr> = vec![
            var("x"),
            lit(42),
            Expr::new(ExprNode::LitBool(true)),
            Expr::new(ExprNode::LitStr("hello".into())),
            Expr::new(ExprNode::LitChar('a')),
            Expr::new(ExprNode::Raw("raw_lean".into())),
            add(var("a"), var("b")),
            Expr::new(ExprNode::UnOp { op: UnOp::Not, arg: Box::new(var("p")) }),
            Expr::new(ExprNode::App {
                head: Box::new(var("f")),
                args: vec![var("x"), var("y")],
            }),
            let_bind("x", lit(1), var("x")),
            forall("y", var("y")),
            exists("z", var("z")),
            lambda("w", var("w")),
            Expr::new(ExprNode::If {
                cond: Box::new(var("c")),
                then_: Box::new(lit(1)),
                else_: Some(Box::new(lit(2))),
            }),
            Expr::new(ExprNode::If {
                cond: Box::new(var("c")),
                then_: Box::new(lit(1)),
                else_: None,
            }),
            Expr::new(ExprNode::Match {
                scrutinee: Box::new(var("x")),
                arms: vec![MatchArm {
                    pattern: Pattern::Var(LeanName::lit("a")),
                    body: var("a"),
                }],
            }),
            Expr::new(ExprNode::TypeAnnot {
                expr: Box::new(var("x")),
                ty: Box::new(var("Nat")),
            }),
            Expr::new(ExprNode::FieldProj {
                expr: Box::new(var("p")),
                field: "x".into(),
            }),
            Expr::new(ExprNode::StructUpdate {
                base: Box::new(var("p")),
                updates: vec![("x".into(), lit(1))],
            }),
            Expr::new(ExprNode::ArrayLit(vec![lit(1), lit(2), lit(3)])),
            Expr::new(ExprNode::Index {
                base: Box::new(var("a")),
                idx: Box::new(lit(0)),
                bang: true,
            }),
            Expr::new(ExprNode::Anon(vec![var("a"), var("b")])),
            Expr::new(ExprNode::SpanMark {
                rust_loc: "test.rs:1:1".into(),
                kind: AssertKind::Hypothesis(HypothesisKind::BranchCondition),
                inner: Box::new(var("inner")),
            }),
        ];
        for e in &exprs {
            // Build a structurally-equivalent rebuild via map_children
            // with identity. Wrapping in `Expr::new` because
            // map_children returns ExprNode.
            let rebuilt = Expr::new(map_children(&e.node, |c| c.clone()));
            assert!(node_eq(e, &rebuilt),
                "map_children(identity) round-trip failed for variant: {:?}", e.node);
        }
    }

    /// `walk_children` visits the expected number of direct children
    /// per variant. Locks in that the helper doesn't accidentally skip
    /// or duplicate a child slot.
    #[test]
    fn walk_children_counts_match_expected() {
        fn count(e: &Expr) -> usize {
            let mut n = 0;
            walk_children(&e.node, |_| n += 1);
            n
        }
        // Leaves: zero children.
        assert_eq!(count(&var("x")), 0);
        assert_eq!(count(&lit(1)), 0);
        assert_eq!(count(&Expr::new(ExprNode::LitBool(true))), 0);
        assert_eq!(count(&Expr::new(ExprNode::Raw("r".into()))), 0);
        // BinOp: 2.
        assert_eq!(count(&add(var("a"), var("b"))), 2);
        // UnOp: 1.
        assert_eq!(count(&Expr::new(
            ExprNode::UnOp { op: UnOp::Not, arg: Box::new(var("p")) },
        )), 1);
        // App: 1 (head) + N (args).
        assert_eq!(count(&Expr::new(ExprNode::App {
            head: Box::new(var("f")),
            args: vec![var("x"), var("y"), var("z")],
        })), 4);
        // Let: value + body = 2.
        assert_eq!(count(&let_bind("x", lit(1), var("x"))), 2);
        // Lambda/Forall/Exists: 1 ty per binder + body.
        assert_eq!(count(&forall("y", var("y"))), 2);
        // If with else: 3; without else: 2.
        assert_eq!(count(&Expr::new(ExprNode::If {
            cond: Box::new(var("c")),
            then_: Box::new(lit(1)),
            else_: Some(Box::new(lit(2))),
        })), 3);
        assert_eq!(count(&Expr::new(ExprNode::If {
            cond: Box::new(var("c")),
            then_: Box::new(lit(1)),
            else_: None,
        })), 2);
        // Match: scrutinee + N arm bodies.
        assert_eq!(count(&Expr::new(ExprNode::Match {
            scrutinee: Box::new(var("x")),
            arms: vec![
                MatchArm { pattern: Pattern::Var(LeanName::lit("a")), body: var("a") },
                MatchArm { pattern: Pattern::Wildcard, body: lit(0) },
            ],
        })), 3);
        // SpanMark: 1 (inner).
        assert_eq!(count(&Expr::new(ExprNode::SpanMark {
            rust_loc: "x".into(),
            kind: AssertKind::Hypothesis(HypothesisKind::BranchCondition),
            inner: Box::new(var("y")),
        })), 1);
    }

    /// `map_pattern_children`/`walk_pattern_children` regression
    /// guard — same shape as the Expr-side tests above.
    #[test]
    fn pattern_helpers_handle_all_variants() {
        fn count(p: &Pattern) -> usize {
            let mut n = 0;
            walk_pattern_children(p, |_| n += 1);
            n
        }
        // Leaves: zero children.
        assert_eq!(count(&Pattern::Var(LeanName::lit("a"))), 0);
        assert_eq!(count(&Pattern::Wildcard), 0);
        assert_eq!(count(&Pattern::Lit(ExprNode::Lit("0".into()))), 0);
        // Ctor: N args.
        assert_eq!(count(&Pattern::Ctor {
            name: "C".into(),
            args: vec![Pattern::Wildcard, Pattern::Var(LeanName::lit("x"))],
        }), 2);
        // Or: 2.
        assert_eq!(count(&Pattern::Or(
            Box::new(Pattern::Wildcard),
            Box::new(Pattern::Wildcard),
        )), 2);
        // Binding: 1 (sub).
        assert_eq!(count(&Pattern::Binding {
            name: LeanName::lit("a"),
            sub: Box::new(Pattern::Wildcard),
        }), 1);
        // map_pattern_children identity round-trip.
        let pats = vec![
            Pattern::Var(LeanName::lit("x")),
            Pattern::Wildcard,
            Pattern::Lit(ExprNode::Lit("42".into())),
            Pattern::Ctor {
                name: "Foo".into(),
                args: vec![Pattern::Var(LeanName::lit("a")), Pattern::Wildcard],
            },
            Pattern::Or(
                Box::new(Pattern::Var(LeanName::lit("a"))),
                Box::new(Pattern::Var(LeanName::lit("b"))),
            ),
            Pattern::Binding {
                name: LeanName::lit("p"),
                sub: Box::new(Pattern::Wildcard),
            },
        ];
        for p in &pats {
            let rebuilt = map_pattern_children(p, |q| q.clone());
            // Pattern doesn't have a pp wrapper handy; compare debug
            // strings (deterministic for our shapes).
            assert_eq!(format!("{:?}", p), format!("{:?}", rebuilt),
                "map_pattern_children identity round-trip failed: {:?}", p);
        }
    }
}
