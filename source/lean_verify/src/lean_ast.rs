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

    pub fn var(name: impl Into<String>) -> Self {
        Expr::new(ExprNode::Var(name.into()))
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

    pub fn let_bind(name: impl Into<String>, value: Expr, body: Expr) -> Self {
        Expr::new(ExprNode::Let {
            name: name.into(),
            value: Box::new(value),
            body: Box::new(body),
        })
    }

    pub fn field_proj(expr: Expr, field: impl Into<String>) -> Self {
        Expr::new(ExprNode::FieldProj { expr: Box::new(expr), field: field.into() })
    }

    pub fn anon(elems: Vec<Expr>) -> Self { Expr::new(ExprNode::Anon(elems)) }

    /// Wrap `inner` with a source-location marker. Transparent at
    /// the Lean level; pp emits a `/-! @rust:LOC -/` block before
    /// `inner` so error-time scanning can map Lean lines back to
    /// Rust positions (#51 source mapping).
    pub fn span_mark(rust_loc: impl Into<String>, inner: Expr) -> Self {
        Expr::new(ExprNode::SpanMark { rust_loc: rust_loc.into(), inner: Box::new(inner) })
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

    /// `⟨a, b, c⟩` — Lean's anonymous constructor. Used for tuples and for
    /// inferred data constructors where the target type is unambiguous.
    Anon(Vec<Expr>),

    /// Escape hatch: verbatim Lean text. Reserved for VIR forms that have
    /// no direct Lean analogue (effectless markers, exotic shapes). The
    /// goal is to keep this set small; prefer adding a real node.
    Raw(String),

    /// Source-span annotation (#51). Transparent at the Lean level —
    /// pp emits just `inner`'s text — but the pp records
    /// `(current_line, rust_loc)` in `PpOutput::span_marks` as it
    /// visits the node. `LeanSourceMap::from_marks` consumes this
    /// to map Lean error lines back to Rust source positions.
    /// `lower_wp` wraps `Wp::Assert` / `Wp::Branch.cond` /
    /// `Wp::Loop.cond` / `Wp::Call` etc. with this carrying the
    /// underlying SST `Exp.span.as_string`.
    SpanMark { rust_loc: String, inner: Box<Expr> },
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
}

// ── Constructors ──────────────────────────────────────────────────────

/// Substitute free `Var(name)` occurrences in `expr` according to
/// `subst`. Respects lexical scoping: a binder (`Let` / `Lambda` /
/// `Forall` / `Exists` / match-arm pattern) whose name appears in
/// `subst` removes that key from the substitution before recursing
/// into its body, so shadowing works correctly.
///
/// **Capture avoidance (first-cut).** If a binder would capture a
/// name appearing free in an active substitution value, we **panic**
/// with a clear message. The check is *lazy per-scope*: we only
/// consider names free in the **current** inner substitution at the
/// binder, not names free in the original top-level substitution.
/// This avoids false positives like `(∀ y. z) + x` with `{x: y}` —
/// the outer `∀ y.` can't capture anything because `x` never appears
/// inside its scope, so no substitution happens there. Alpha-
/// renaming is the proper fix when a real capture is detected; panic
/// over silent miscompilation until that's implemented.
///
/// **Per-variant boilerplate.** Adding a new `ExprNode` variant
/// requires editing three places: `substitute_impl`, `collect_free_vars`,
/// and the pretty-printer. Not painful enough yet to justify a
/// proc-macro `walk_children` helper, but worth documenting as a
/// smell — if the variant count climbs, a folding abstraction would
/// collapse ~130 lines of per-arm dispatch to ~30.
///
/// Used by exec-fn codegen to substitute call-site args for callee
/// params in inlined `require` / `ensure` / `decrease` expressions.
/// This replaces the older `let p := arg; body` wrapping — direct
/// substitution produces Lean that's both cleaner (no nested let
/// shadowing) and tractable for omega (no zeta-reduction needed).
pub fn substitute(expr: &Expr, subst: &std::collections::HashMap<String, Expr>) -> Expr {
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
pub fn strip_span_marks(expr: &Expr) -> Expr {
    Expr::new(strip_span_marks_node(&expr.node))
}

fn strip_span_marks_node(node: &ExprNode) -> ExprNode {
    match node {
        ExprNode::SpanMark { inner, .. } => strip_span_marks_node(&inner.node),
        ExprNode::Var(s) => ExprNode::Var(s.clone()),
        ExprNode::Lit(s) => ExprNode::Lit(s.clone()),
        ExprNode::LitBool(b) => ExprNode::LitBool(*b),
        ExprNode::LitStr(s) => ExprNode::LitStr(s.clone()),
        ExprNode::LitChar(c) => ExprNode::LitChar(*c),
        ExprNode::Raw(s) => ExprNode::Raw(s.clone()),
        ExprNode::BinOp { op, lhs, rhs } => ExprNode::BinOp {
            op: *op,
            lhs: Box::new(strip_span_marks(lhs)),
            rhs: Box::new(strip_span_marks(rhs)),
        },
        ExprNode::UnOp { op, arg } => ExprNode::UnOp {
            op: *op,
            arg: Box::new(strip_span_marks(arg)),
        },
        ExprNode::App { head, args } => ExprNode::App {
            head: Box::new(strip_span_marks(head)),
            args: args.iter().map(strip_span_marks).collect(),
        },
        ExprNode::Let { name, value, body } => ExprNode::Let {
            name: name.clone(),
            value: Box::new(strip_span_marks(value)),
            body: Box::new(strip_span_marks(body)),
        },
        ExprNode::Lambda { binders, body } => ExprNode::Lambda {
            binders: binders.clone(),
            body: Box::new(strip_span_marks(body)),
        },
        ExprNode::Forall { binders, body } => ExprNode::Forall {
            binders: binders.clone(),
            body: Box::new(strip_span_marks(body)),
        },
        ExprNode::Exists { binders, body } => ExprNode::Exists {
            binders: binders.clone(),
            body: Box::new(strip_span_marks(body)),
        },
        ExprNode::If { cond, then_, else_ } => ExprNode::If {
            cond: Box::new(strip_span_marks(cond)),
            then_: Box::new(strip_span_marks(then_)),
            else_: else_.as_ref().map(|e| Box::new(strip_span_marks(e))),
        },
        ExprNode::Match { scrutinee, arms } => ExprNode::Match {
            scrutinee: Box::new(strip_span_marks(scrutinee)),
            arms: arms.iter().map(|a| MatchArm {
                pattern: a.pattern.clone(),
                body: strip_span_marks(&a.body),
            }).collect(),
        },
        ExprNode::TypeAnnot { expr, ty } => ExprNode::TypeAnnot {
            expr: Box::new(strip_span_marks(expr)),
            ty: Box::new(strip_span_marks(ty)),
        },
        ExprNode::FieldProj { expr, field } => ExprNode::FieldProj {
            expr: Box::new(strip_span_marks(expr)),
            field: field.clone(),
        },
        ExprNode::StructUpdate { base, updates } => ExprNode::StructUpdate {
            base: Box::new(strip_span_marks(base)),
            updates: updates.iter().map(|(f, e)| (f.clone(), strip_span_marks(e))).collect(),
        },
        ExprNode::ArrayLit(es) => ExprNode::ArrayLit(es.iter().map(strip_span_marks).collect()),
        ExprNode::Index { base, idx } => ExprNode::Index {
            base: Box::new(strip_span_marks(base)),
            idx: Box::new(strip_span_marks(idx)),
        },
        ExprNode::Anon(es) => ExprNode::Anon(es.iter().map(strip_span_marks).collect()),
    }
}

fn substitute_impl(
    expr: &Expr,
    subst: &std::collections::HashMap<String, Expr>,
) -> Expr {
    let node = match &expr.node {
        ExprNode::Var(name) => match subst.get(name) {
            Some(replacement) => return replacement.clone(),
            None => ExprNode::Var(name.clone()),
        },
        ExprNode::Lit(s) => ExprNode::Lit(s.clone()),
        ExprNode::LitBool(b) => ExprNode::LitBool(*b),
        ExprNode::LitStr(s) => ExprNode::LitStr(s.clone()),
        ExprNode::LitChar(c) => ExprNode::LitChar(*c),
        ExprNode::Raw(s) => ExprNode::Raw(s.clone()),
        ExprNode::BinOp { op, lhs, rhs } => ExprNode::BinOp {
            op: *op,
            lhs: Box::new(substitute_impl(lhs, subst)),
            rhs: Box::new(substitute_impl(rhs, subst)),
        },
        ExprNode::UnOp { op, arg } => ExprNode::UnOp {
            op: *op,
            arg: Box::new(substitute_impl(arg, subst)),
        },
        ExprNode::App { head, args } => ExprNode::App {
            head: Box::new(substitute_impl(head, subst)),
            args: args.iter().map(|a| substitute_impl(a, subst)).collect(),
        },
        ExprNode::Let { name, value, body } => {
            let new_value = substitute_impl(value, subst);
            let inner_subst = subst_without(subst, name);
            check_capture_lazy(&[name], &inner_subst, body, "let");
            ExprNode::Let {
                name: name.clone(),
                value: Box::new(new_value),
                body: Box::new(substitute_impl(body, &inner_subst)),
            }
        }
        ExprNode::Lambda { binders, body } => {
            let inner_subst = subst_remove_binders(subst, binders);
            let binder_names: Vec<&str> = binders.iter()
                .filter_map(|b| b.name.as_deref())
                .collect();
            check_capture_lazy(&binder_names, &inner_subst, body, "lambda");
            ExprNode::Lambda {
                binders: binders.clone(),
                body: Box::new(substitute_impl(body, &inner_subst)),
            }
        }
        ExprNode::Forall { binders, body } => {
            let inner_subst = subst_remove_binders(subst, binders);
            let binder_names: Vec<&str> = binders.iter()
                .filter_map(|b| b.name.as_deref())
                .collect();
            check_capture_lazy(&binder_names, &inner_subst, body, "forall");
            ExprNode::Forall {
                binders: binders.clone(),
                body: Box::new(substitute_impl(body, &inner_subst)),
            }
        }
        ExprNode::Exists { binders, body } => {
            let inner_subst = subst_remove_binders(subst, binders);
            let binder_names: Vec<&str> = binders.iter()
                .filter_map(|b| b.name.as_deref())
                .collect();
            check_capture_lazy(&binder_names, &inner_subst, body, "exists");
            ExprNode::Exists {
                binders: binders.clone(),
                body: Box::new(substitute_impl(body, &inner_subst)),
            }
        }
        ExprNode::If { cond, then_, else_ } => ExprNode::If {
            cond: Box::new(substitute_impl(cond, subst)),
            then_: Box::new(substitute_impl(then_, subst)),
            else_: else_.as_ref().map(|e| Box::new(substitute_impl(e, subst))),
        },
        ExprNode::Match { scrutinee, arms } => ExprNode::Match {
            scrutinee: Box::new(substitute_impl(scrutinee, subst)),
            arms: arms.iter().map(|a| {
                // Pattern variables are locally bound; remove them from subst
                // for the arm body.
                let bound = pattern_bound_names(&a.pattern);
                let mut inner = subst.clone();
                for n in &bound { inner.remove(n); }
                let bound_refs: Vec<&str> = bound.iter().map(String::as_str).collect();
                check_capture_lazy(&bound_refs, &inner, &a.body, "match pattern");
                MatchArm {
                    pattern: a.pattern.clone(),
                    body: substitute_impl(&a.body, &inner),
                }
            }).collect(),
        },
        ExprNode::TypeAnnot { expr, ty } => ExprNode::TypeAnnot {
            expr: Box::new(substitute_impl(expr, subst)),
            // Type expressions can also reference vars; substitute too.
            ty: Box::new(substitute_impl(ty, subst)),
        },
        ExprNode::FieldProj { expr, field } => ExprNode::FieldProj {
            expr: Box::new(substitute_impl(expr, subst)),
            field: field.clone(),
        },
        ExprNode::StructUpdate { base, updates } => ExprNode::StructUpdate {
            base: Box::new(substitute_impl(base, subst)),
            updates: updates.iter().map(|(f, e)| (f.clone(), substitute_impl(e, subst))).collect(),
        },
        ExprNode::ArrayLit(es) => ExprNode::ArrayLit(
            es.iter().map(|e| substitute_impl(e, subst)).collect()
        ),
        ExprNode::Index { base, idx } => ExprNode::Index {
            base: Box::new(substitute_impl(base, subst)),
            idx: Box::new(substitute_impl(idx, subst)),
        },
        ExprNode::Anon(es) => ExprNode::Anon(
            es.iter().map(|e| substitute_impl(e, subst)).collect()
        ),
        ExprNode::SpanMark { rust_loc, inner } => ExprNode::SpanMark {
            rust_loc: rust_loc.clone(),
            inner: Box::new(substitute_impl(inner, subst)),
        },
    };
    Expr::new(node)
}

/// Per-scope capture check. Precise enough to avoid false positives:
/// only panics when substitution would actually happen inside this
/// binder AND the substituted value's free vars would be captured.
///
/// Walks `body` to see which `inner_subst` keys actually occur free
/// there — if none, no substitution happens inside so no capture is
/// possible (early exit). Otherwise checks only the values for the
/// live keys against the binder names. Cost is two extra traversals
/// per binder hit (body and live-value free-var collection), both
/// bounded by expression size.
fn check_capture_lazy(
    binder_names: &[&str],
    inner_subst: &std::collections::HashMap<String, Expr>,
    body: &Expr,
    binder_kind: &str,
) {
    if inner_subst.is_empty() { return; }
    let body_free = {
        let mut out = std::collections::HashSet::new();
        collect_free_vars(body, &std::collections::HashSet::new(), &mut out);
        out
    };
    // Only keys that actually occur free in the body would trigger
    // substitution inside this binder's scope.
    let live_keys: Vec<&str> = inner_subst.keys()
        .filter(|k| body_free.contains(k.as_str()))
        .map(String::as_str)
        .collect();
    if live_keys.is_empty() { return; }

    let mut free_in_live_values = std::collections::HashSet::new();
    for k in &live_keys {
        collect_free_vars(&inner_subst[*k], &std::collections::HashSet::new(), &mut free_in_live_values);
    }
    for name in binder_names {
        if free_in_live_values.contains(*name) {
            panic!(
                "Lean-AST substitute: binder `{}` (kind: {}) would capture a free \
                 variable of the same name in a substitution value — alpha-\
                 renaming not yet implemented. See `substitute` in lean_ast.rs.",
                name, binder_kind,
            );
        }
    }
}

fn subst_without(
    subst: &std::collections::HashMap<String, Expr>,
    name: &str,
) -> std::collections::HashMap<String, Expr> {
    let mut out = subst.clone();
    out.remove(name);
    out
}

fn subst_remove_binders(
    subst: &std::collections::HashMap<String, Expr>,
    binders: &[Binder],
) -> std::collections::HashMap<String, Expr> {
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
    match &expr.node {
        ExprNode::Var(n) => {
            if !bound.contains(n) { out.insert(n.clone()); }
        }
        ExprNode::Lit(_) | ExprNode::LitBool(_) | ExprNode::LitStr(_)
        | ExprNode::LitChar(_) | ExprNode::Raw(_) => {}
        ExprNode::BinOp { lhs, rhs, .. } => {
            collect_free_vars(lhs, bound, out);
            collect_free_vars(rhs, bound, out);
        }
        ExprNode::UnOp { arg, .. } => collect_free_vars(arg, bound, out),
        ExprNode::App { head, args } => {
            collect_free_vars(head, bound, out);
            for a in args { collect_free_vars(a, bound, out); }
        }
        ExprNode::Let { name, value, body } => {
            collect_free_vars(value, bound, out);
            let mut inner = bound.clone();
            inner.insert(name.clone());
            collect_free_vars(body, &inner, out);
        }
        ExprNode::Lambda { binders, body }
        | ExprNode::Forall { binders, body }
        | ExprNode::Exists { binders, body } => {
            let mut inner = bound.clone();
            for b in binders {
                if let Some(n) = &b.name { inner.insert(n.clone()); }
            }
            collect_free_vars(body, &inner, out);
        }
        ExprNode::If { cond, then_, else_ } => {
            collect_free_vars(cond, bound, out);
            collect_free_vars(then_, bound, out);
            if let Some(e) = else_ { collect_free_vars(e, bound, out); }
        }
        ExprNode::Match { scrutinee, arms } => {
            collect_free_vars(scrutinee, bound, out);
            for arm in arms {
                let mut inner = bound.clone();
                for n in pattern_bound_names(&arm.pattern) { inner.insert(n); }
                collect_free_vars(&arm.body, &inner, out);
            }
        }
        ExprNode::TypeAnnot { expr, ty } => {
            collect_free_vars(expr, bound, out);
            collect_free_vars(ty, bound, out);
        }
        ExprNode::FieldProj { expr, .. } => collect_free_vars(expr, bound, out),
        ExprNode::StructUpdate { base, updates } => {
            collect_free_vars(base, bound, out);
            for (_, e) in updates { collect_free_vars(e, bound, out); }
        }
        ExprNode::ArrayLit(es) | ExprNode::Anon(es) => {
            for e in es { collect_free_vars(e, bound, out); }
        }
        ExprNode::Index { base, idx } => {
            collect_free_vars(base, bound, out);
            collect_free_vars(idx, bound, out);
        }
        ExprNode::SpanMark { inner, .. } => collect_free_vars(inner, bound, out),
    }
}

fn pattern_bound_names(pat: &Pattern) -> Vec<String> {
    let mut out = Vec::new();
    pattern_bound_names_impl(pat, &mut out);
    out
}

fn pattern_bound_names_impl(pat: &Pattern, out: &mut Vec<String>) {
    match pat {
        Pattern::Var(n) => out.push(n.clone()),
        Pattern::Wildcard | Pattern::Lit(_) => {}
        Pattern::Ctor { args, .. } => {
            for a in args { pattern_bound_names_impl(a, out); }
        }
        Pattern::Or(l, r) => {
            pattern_bound_names_impl(l, out);
            pattern_bound_names_impl(r, out);
        }
        Pattern::Binding { name, sub } => {
            out.push(name.clone());
            pattern_bound_names_impl(sub, out);
        }
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

    fn var(n: &str) -> Expr { Expr::new(ExprNode::Var(n.to_string())) }
    fn lit(n: i64) -> Expr { Expr::new(ExprNode::Lit(n.to_string())) }
    fn add(l: Expr, r: Expr) -> Expr {
        Expr::new(ExprNode::BinOp { op: BinOp::Add, lhs: Box::new(l), rhs: Box::new(r) })
    }
    fn let_bind(name: &str, val: Expr, body: Expr) -> Expr {
        Expr::new(ExprNode::Let {
            name: name.to_string(), value: Box::new(val), body: Box::new(body),
        })
    }
    fn forall(binder_name: &str, body: Expr) -> Expr {
        Expr::new(ExprNode::Forall {
            binders: vec![Binder {
                name: Some(binder_name.to_string()),
                ty: var("Int"),
                kind: BinderKind::Explicit,
            }],
            body: Box::new(body),
        })
    }
    fn exists(binder_name: &str, body: Expr) -> Expr {
        Expr::new(ExprNode::Exists {
            binders: vec![Binder {
                name: Some(binder_name.to_string()),
                ty: var("Int"),
                kind: BinderKind::Explicit,
            }],
            body: Box::new(body),
        })
    }
    fn lambda(binder_name: &str, body: Expr) -> Expr {
        Expr::new(ExprNode::Lambda {
            binders: vec![Binder {
                name: Some(binder_name.to_string()),
                ty: var("Int"),
                kind: BinderKind::Explicit,
            }],
            body: Box::new(body),
        })
    }
    fn subst_of(pairs: &[(&str, Expr)]) -> HashMap<String, Expr> {
        pairs.iter().map(|(k, v)| (k.to_string(), v.clone())).collect()
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
    #[should_panic(expected = "would capture a free variable")]
    fn capture_panics() {
        // ∀ y. x + y  with {x: y}
        // x is free inside ∀ y.; substituting x→y would capture the
        // substituted `y` inside the ∀. Panic.
        let e = forall("y", add(var("x"), var("y")));
        let s = subst_of(&[("x", var("y"))]);
        let _ = substitute(&e, &s);
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
                        args: vec![Pattern::Var("x".to_string())],
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
        });
        let s = subst_of(&[("base", var("arr")), ("i", lit(0))]);
        let expected = Expr::new(ExprNode::Index {
            base: Box::new(var("arr")),
            idx: Box::new(lit(0)),
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
                    name: Some("x".to_string()),
                    ty: var("Int"),
                    kind: BinderKind::Explicit,
                },
                Binder {
                    name: Some("y".to_string()),
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
                    name: Some("x".to_string()),
                    ty: var("Int"),
                    kind: BinderKind::Explicit,
                },
                Binder {
                    name: Some("y".to_string()),
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
    #[should_panic(expected = "would capture a free variable")]
    fn multi_binder_real_capture_does_panic() {
        // ∀ x y. z + y   with {z: x}
        //   z occurs free in the body and subst z→x; binder `x` would
        //   capture the substituted x. Real capture → panic.
        let e = Expr::new(ExprNode::Forall {
            binders: vec![
                Binder {
                    name: Some("x".to_string()),
                    ty: var("Int"),
                    kind: BinderKind::Explicit,
                },
                Binder {
                    name: Some("y".to_string()),
                    ty: var("Int"),
                    kind: BinderKind::Explicit,
                },
            ],
            body: Box::new(add(var("z"), var("y"))),
        });
        let s = subst_of(&[("z", var("x"))]);
        let _ = substitute(&e, &s);
    }
}
