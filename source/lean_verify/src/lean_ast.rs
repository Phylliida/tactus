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
    /// Axiom declaration: `axiom <name> [binders] : <type>`.
    /// Used for spec fns with `body = None` (Verus's
    /// `pub uninterp spec fn`, external_body fns, closed-body
    /// cross-crate spec fns whose body was stripped at
    /// `export_crate` time). Lean's kernel trusts axioms; safe
    /// here because the Verus side already treats these as
    /// axiomatized.
    Axiom(Axiom),
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
    /// When true (and `termination_by` has exactly one measure), render
    /// `termination_by structural <measure>` — Lean's structural
    /// (subterm) recursion, which kernel-reduces, vs. the WF default,
    /// which is kernel-inert. `decreasing_by` must be `None` (structural
    /// recursion has no decreasing goals). See vir
    /// `FunctionAttrs::tactus_structural_decreases`.
    pub termination_structural: bool,
    /// Optional `decreasing_by <tactic>` clause emitted after
    /// `termination_by`. Used when Lean's default `decreasing_tactic`
    /// can't close the obligation — e.g., height fns for recursive
    /// datatypes whose recursive field is wrapper-typed
    /// (`Box<Self>` etc.), where the size inequality has a
    /// `.deref` projection the default tactic doesn't peel.
    pub decreasing_by: Option<String>,
}

/// Axiom: declares a constant whose value is unspecified.
/// `[@[attr₁] @[attr₂]] axiom <name> [binders] : <ret_ty>`.
///
/// Used for body-less spec fns (Verus's `pub uninterp spec fn`,
/// external_body spec fns, cross-crate spec fns whose body was
/// stripped at export time). The binder set mirrors the spec fn's
/// params + return type via `fn_binders_without_bound_hyps`, so an
/// uninterp `spec fn f(x: int) -> int` becomes
/// `axiom f : Int → Int` (the binder + ret_ty currying).
///
/// `attrs` carries Lean attribute markers (e.g., `"instance"`) — used
/// for external_body datatype Inhabited stipulations:
/// `@[instance] axiom T.instInhabited : Inhabited T`.
#[derive(Debug, Clone)]
pub struct Axiom {
    pub name: String,
    pub binders: Vec<Binder>,
    pub ret_ty: Expr,
    pub attrs: Vec<String>,
    /// Emitted as a `-- …` line above the axiom. Transparency device:
    /// when the pipeline axiomatizes something it would normally
    /// define (e.g. a spec fn whose body contains un-renderable
    /// `call_ensures`), the artifact must SAY so — the reader of the
    /// generated Lean should never have to guess why a def became an
    /// axiom.
    pub comment: Option<String>,
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
    /// Preamble fragments this theorem needs to elaborate. Aggregated
    /// across all of an exec fn's theorems by `generate.rs`'s
    /// `krate_preamble`, then deduped and emitted once at the top of
    /// the generated file.
    ///
    /// Empty for proof fns and for exec-fn theorems that need only the
    /// default Tactus preamble. Populated by walker arms that emit
    /// goals requiring extra Lean infrastructure — currently just
    /// `Wp::AssertBitVector` (#130), which needs `Mathlib.Data.BitVec`
    /// + `Lean.Elab.Tactic.BVDecide` imports plus the
    /// `HXor`/`HAnd`/`HOr`/`HShiftLeft`/`HShiftRight Int Int Int`
    /// instances.
    ///
    /// Replaces the prior 4-site bool-flag plumbing
    /// (`ObligationEmitter::needs_bitvec_instances` →
    /// `ExecFnTheorems::needs_bitvec_instances` →
    /// `PreambleConfig::ExecFn { needs_bitvec }` →
    /// `krate_preamble`'s `bitvec_mode` branch). The
    /// theorem-as-source-of-truth shape generalizes: future "this fn
    /// needs Mathlib.Tactic.X" requirements just add a
    /// `PreambleFragment` constructor + a walker-arm push, without
    /// threading another bool through the pipeline.
    pub requires_preamble: Vec<PreambleFragment>,
    /// Optional per-theorem `maxHeartbeats` override. Populated from
    /// the fn's `#[verifier::heartbeats(N)]` attribute. When `Some(N)`,
    /// the pretty-printer emits `set_option maxHeartbeats N in\n`
    /// before the `theorem` keyword. When `None`, the prelude's
    /// global `set_option maxHeartbeats 800000` applies.
    ///
    /// Lean's `maxHeartbeats` is the deterministic-timeout knob —
    /// the equivalent of Verus's Z3 `rlimit` annotation, but
    /// reproducible (heartbeats count kernel reduction steps, not
    /// wall-clock). All theorems emitted from a single fn share the
    /// fn's attribute value.
    pub heartbeats: Option<u32>,
    /// Termination measure for recursive theorems. Mirrors `Def.termination_by`:
    /// empty for non-recursive (most theorems); single-element for plain
    /// `decreases n`; multi-element for lexicographic `decreases a, b, ...`.
    /// Populated from the proof fn's `f.decrease` clause; the pretty-printer
    /// emits `termination_by <expr>` (or `(e1, e2, ...)` for lex) after the
    /// tactic body.
    ///
    /// Lean often auto-infers termination for simple structural recursion
    /// (`(n - 1) as nat` on a `Nat`), but cases like Collatz-shaped recursion,
    /// recursion on computed values, or lex measures require the explicit
    /// clause. Verus has already certified termination via its `decreases`
    /// check, so passing it to Lean is a faithful translation, not new work.
    ///
    /// Currently always empty for exec-fn-emitted theorems (the per-obligation
    /// theorems are flat in shape; the recursion happens at the obligation-level
    /// `CheckDecreaseHeight` rather than in the theorem itself).
    pub termination_by: Vec<Expr>,
    /// Optional `decreasing_by <tactic>` clause emitted after `termination_by`,
    /// mirroring `Def.decreasing_by`. `Some` only when `termination_by` is
    /// non-empty (a bare `decreasing_by` on a non-recursive theorem is a Lean
    /// error). Lets a recursive proof fn with a measure Lean's default
    /// `decreasing_tactic` can't discharge — notably the modular `a % b < b` —
    /// still verify. Populated by `proof_fn_to_ast` from the same
    /// `DECREASING_BY_TACTIC` the spec-fn path uses.
    pub decreasing_by: Option<String>,
}

/// N3b goal-provenance capture (DESIGN-N3-serializer.md §5). The Wp
/// walker records the STRUCTURED spine of each exec-fn obligation
/// statement here — at the single `OblCtx::wrap` site, before the frames
/// are folded into the flat `Theorem.goal` — so the serializer prints the
/// production goal as a `tactus_core.GoalData` literal without re-parsing
/// the flattened statement (which is ambiguous at the spine tail: a
/// hypothesis can itself be `a → b` or `∀`).
///
/// This IS the "provenance" of §5. Rather than marking nodes in the
/// shared [`Expr`] type (which would touch every exhaustive match and the
/// pretty-printer), the walker keeps its own construction record. It is
/// non-circular exactly as §5 requires: the spine only records where the
/// production CLAIMS structure; refWp (W2) recomputes structure
/// independently from the SST literal, and the `decide` equality is what
/// validates the claim. A mismark surfaces as a bridge failure, never a
/// silent pass.
///
/// Populated only for WP-obligation theorems. `None` (in the
/// index-aligned `goal_shapes` vector) marks a documented stage-A
/// exclusion — `bit_vector`/`query` obligations, which use `wrap_no_hyps`
/// and get no `GoalData`.
///
/// Faithfulness invariant (worth pinning in a test): folding a `GoalShape`
/// back to an `Expr` — `All→forall`, `Imp→implies`, `Let→let_bind`,
/// `leaf` at the core — must equal the `Theorem.goal` the pp emits.
#[derive(Debug, Clone)]
pub struct GoalShape {
    /// Spine constructors, OUTERMOST first (matching `OblCtx::wrap`'s
    /// fold: theorem binders wrap the frame stack wraps the leaf).
    pub spine: Vec<GoalSpine>,
    /// The obligation predicate at the core of the spine.
    pub leaf: Expr,
}

/// One structural node of a [`GoalShape`] spine. Mirrors
/// `tactus_core.GoalData`'s `All`/`Imp`/`Let` constructors; the `Leaf`
/// constructor corresponds to [`GoalShape::leaf`].
#[derive(Debug, Clone)]
pub enum GoalSpine {
    /// `∀ (x : T),` — a theorem-level binder or a walker `Binder` frame.
    All(Binder),
    /// `h →` — a hypothesis (an assumption, a branch condition, or a
    /// discharged assertion carried forward). Carries its provenance
    /// for the Link-discharge generator.
    Imp(Expr, HypProvenance),
    /// `let x := v;` — a let-binding frame.
    Let(crate::lean_name::LeanName, Expr),
}

/// Provenance of a hypothesis frame in a [`GoalSpine`] — recorded for
/// the Link-discharge generator (DESIGN-link-discharge.md §3.1). The
/// discharge term must supply a proof for every `Imp` it applies
/// through, and the recipe depends on where the hypothesis came from.
/// Documentation-plus-data only: never affects the rendered theorem.
#[derive(Debug, Clone, PartialEq)]
pub enum HypProvenance {
    /// A callee-ensures fact woven by a proof-body call: discharged by
    /// the callee's closed theorem instantiated at `args` (or by the
    /// synthesized fix's own recursive call when `is_self`).
    CallFact(CallFactInfo),
    /// A branch / discriminator condition (if-cond, lowered-match
    /// `isX` chain, loop cond): discharged by `(by simp)` on a
    /// constructor-refined arm.
    Branch,
    /// The woven height-decrease fact of a recursive call (a passed
    /// Termination assert carried forward): discharged by the emitted
    /// termination VC theorem.
    HeightFact,
    /// Anything else (assumes, invariants, passed plain asserts…) —
    /// not dischargeable mechanically; census-tagged by the generator.
    Other,
}

/// Instantiation record for one woven callee fact.
#[derive(Debug, Clone, PartialEq)]
pub struct CallFactInfo {
    /// Callee's stable dotted Lean name (e.g. `lib.u_gapp_cons`).
    pub callee: String,
    /// The call is a self-recursion (an IH premise for the fix).
    pub is_self: bool,
    /// Rendered instantiation, in callee param order.
    pub args: Vec<SpineArg>,
}

/// One rendered call argument plus the bound-discharge recipe hint.
#[derive(Debug, Clone, PartialEq)]
pub struct SpineArg {
    /// Rendered Lean text of the argument.
    pub text: String,
    /// Recipe hint for discharging the callee's `h_*_bound` binder (if
    /// any) at this arg position.
    pub tag: SpineArgTag,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SpineArgTag {
    /// The arg is exactly a caller signature param — the caller's own
    /// `h_<name>_bound` binder discharges the callee's bound hyp.
    CallerParam(String),
    /// A literal numeral — bounds discharge by `decide`.
    Literal,
    /// Anything else — needs L2's wf machinery (or a census tag).
    Expr,
}

/// A piece of preamble that some theorem needs in its elaboration
/// context. `krate_preamble` collects these from all emitted
/// theorems, dedups, and emits at file top.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PreambleFragment {
    /// `import <module>` line. Order among multiple imports doesn't
    /// matter to Lean; dedup is by exact string.
    Import(String),
    /// Raw Lean text emitted between the prelude and the namespace
    /// open. Used for typeclass instance blocks (#130's `HXor Int Int
    /// Int` etc.) where structured AST representation isn't worth the
    /// complexity for static text. Dedup is by exact string.
    PreludeAddendum(String),
}

#[derive(Debug, Clone)]
pub struct Datatype {
    pub name: String,
    /// The name SELF-references inside the declaration render as — the
    /// relative (non-root-anchored) form. `IndexedInductive` constructor
    /// result types (`| Plain : ∀ {A}, A → Mut A`) must use it: during
    /// elaboration the inductive is not yet a global constant, so the
    /// root-anchored `name` is `Unknown identifier` there (verified
    /// empirically; the render-time relative-name machinery this rule
    /// once shared is retired — Option B full names resolve mid-decl).
    pub self_name: String,
    pub typ_params: Vec<String>,
    pub kind: DatatypeKind,
    /// `deriving` clause class names (e.g., `"Inhabited"`). Emitted
    /// as `deriving <cls1>, <cls2>` after the variants/fields.
    /// `datatype_to_cmds` unconditionally adds `Inhabited` (post-#108)
    /// so that auto-generated accessors' `default` fallback
    /// resolves — particularly for self-referential types where
    /// the accessor's return type is the datatype itself. For
    /// generic datatypes, Lean auto-derives the conditional
    /// `[Inhabited A] → Inhabited (T A)` instance, so the bound
    /// flows through callers that supply `[Inhabited A]`.
    pub derives: Vec<String>,
}

#[derive(Debug, Clone)]
pub enum DatatypeKind {
    /// Single-variant datatype → Lean `structure`.
    Structure { fields: Vec<Field> },
    /// Multi-variant datatype → Lean `inductive` in parameter style:
    /// `inductive T (A : Type) where | Variant (...) | ...`.
    /// Used for the common case of uniform recursion (or no recursion).
    /// `deriving Inhabited` works on this shape.
    Inductive { variants: Vec<Variant> },
    /// Multi-variant datatype → Lean `inductive` in indexed style:
    /// `inductive T : Type → Type 1 where | Variant : ∀ {A}, ... → T A | ...`.
    /// Used when the datatype has **non-uniform recursive instantiation** —
    /// i.e., a variant's recursive field uses a different type-arg from the
    /// parent's parameter (e.g., `enum Mut<A> { Recurse(Mut<u8>) }`).
    /// Lean's parameter-style strict-positivity check rejects that shape;
    /// indexed style allows it.
    ///
    /// `deriving Inhabited` does NOT work for indexed-style; the caller
    /// (`datatype_to_cmds` / `datatype_group_to_cmds`) emits a manual
    /// `Command::Instance` for `Inhabited (T A)` alongside the indexed
    /// inductive.
    IndexedInductive { variants: Vec<Variant> },
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
    /// own AND transitively-inherited outParam-marked associated types
    /// (via `BinderKind::OutParam`).
    pub typ_params: Vec<Binder>,
    /// Superclass parents, emitted as Lean's native `extends P₁, P₂, …`.
    /// Each is the fully-applied parent class (`Super Self`, `FnOnce Self
    /// Args Output`). `extends` — rather than `[Super Self]` instance
    /// binders — handles superclass transitivity and inherited outParams
    /// natively (a child's bound provides only the parent it directly names;
    /// Lean threads the grandparents). Empty for traits with no superclass.
    pub extends_parents: Vec<Expr>,
    pub methods: Vec<ClassMethod>,
}

#[derive(Debug, Clone)]
pub struct ClassMethod {
    pub name: String,
    pub ty: Expr,
    /// Optional default body for this method, rendered as
    /// `name : ty := default`. When present, instances may omit
    /// the method and Lean uses this default. Populated from a
    /// trait method's body when the trait declaration provides one
    /// (Verus's `fn method(&self) ensures P { body }` shape — the
    /// default body is `body`).
    ///
    /// For trait methods without a default body (Verus's
    /// `fn method(&self) ensures P;` — abstract decl), this is `None`
    /// and the rendering is just `name : ty` (impls must override).
    pub default: Option<Expr>,
    /// Termination clause(s) for recursive default bodies — rendered
    /// as `termination_by d₁` or `termination_by (d₁, d₂, …)` after
    /// the `:= default`. Populated from the trait method's
    /// `decrease` field. Empty when the default is non-recursive
    /// or when there's no default.
    pub termination_by: Vec<Expr>,
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

impl Binder {
    /// `(name : ty)`
    pub fn explicit(name: crate::lean_name::LeanName, ty: Expr) -> Self {
        Binder { name: Some(name), ty, kind: BinderKind::Explicit }
    }

    /// `{name : ty}`
    pub fn implicit(name: crate::lean_name::LeanName, ty: Expr) -> Self {
        Binder { name: Some(name), ty, kind: BinderKind::Implicit }
    }

    /// Anonymous instance bracket: `[ty]`
    pub fn instance(ty: Expr) -> Self {
        Binder { name: None, ty, kind: BinderKind::Instance }
    }

    /// A type-parameter binder `name : Type` with the given bracket
    /// kind — `{T : Type}` (Implicit) or `(T : Type)` (Explicit). The
    /// name goes through `LeanName::typ_param` (the sanitization
    /// chokepoint for `impl%N` / `Self%` forms).
    pub fn typ_param(name: &str, kind: BinderKind) -> Self {
        Binder {
            name: Some(crate::lean_name::LeanName::typ_param(name)),
            ty: Expr::var_lit("Type"),
            kind,
        }
    }
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

    /// Visit every direct child expression (one level, no recursion —
    /// callers recurse themselves so they can stop early or track
    /// scope). Binder TYPES count as children; `Raw`/`ByBlock` text
    /// does not (it's opaque to the AST). Exhaustive on purpose: a new
    /// variant must decide its children here rather than silently
    /// having none.
    pub fn for_each_child<'a>(&'a self, mut f: impl FnMut(&'a Expr)) {
        match &self.node {
            ExprNode::Var(_)
            | ExprNode::Lit(_)
            | ExprNode::LitBool(_)
            | ExprNode::LitStr(_)
            | ExprNode::LitChar(_)
            | ExprNode::Raw(_)
            | ExprNode::ByBlock { .. } => {}
            ExprNode::BinOp { lhs, rhs, .. } => {
                f(lhs);
                f(rhs);
            }
            ExprNode::UnOp { arg, .. } => f(arg),
            ExprNode::App { head, args } => {
                f(head);
                args.iter().for_each(f);
            }
            ExprNode::Let { value, body, .. } => {
                f(value);
                f(body);
            }
            ExprNode::Lambda { binders, body }
            | ExprNode::Forall { binders, body }
            | ExprNode::Exists { binders, body } => {
                binders.iter().for_each(|b| f(&b.ty));
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
                arms.iter().for_each(|a| f(&a.body));
            }
            ExprNode::TypeAnnot { expr, ty } => {
                f(expr);
                f(ty);
            }
            ExprNode::FieldProj { expr, .. } => f(expr),
            ExprNode::StructUpdate { base, updates } => {
                f(base);
                updates.iter().for_each(|(_, e)| f(e));
            }
            ExprNode::ArrayLit(es)
            | ExprNode::VectorLit(es)
            | ExprNode::Tuple(es)
            | ExprNode::Anon(es) => es.iter().for_each(f),
            ExprNode::Index { base, idx, .. } => {
                f(base);
                f(idx);
            }
            ExprNode::Subtype { ty, pred, .. } => {
                f(ty);
                f(pred);
            }
            ExprNode::SpanMark { inner, .. } => f(inner),
        }
    }

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
    /// A reference to a VIR **type parameter** by name. Routes through the
    /// single sanitizing `LeanName::typ_param` constructor so synthetic
    /// names (`impl%1`, `T%0`, `Self%`) render legally and *identically* to
    /// the binders that introduce them. Use this — never `var_lit` — for any
    /// type-param reference.
    pub fn var_tp(name: &str) -> Self {
        Expr::new(ExprNode::Var(crate::lean_name::LeanName::typ_param(name)))
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
    pub fn tuple(elems: Vec<Expr>) -> Self { Expr::new(ExprNode::Tuple(elems)) }

    /// Wrap `inner` with a source-location marker carrying the
    /// obligation's semantic kind. Transparent at the Lean level;
    /// pp emits a `/- @rust:LOC -/` block before `inner` and
    /// records `(line, loc, rust_span, kind)` in landmarks for
    /// `#51` error formatting.
    ///
    /// `rust_span` carries the obligation's source `Span` so the
    /// verifier can attach errors directly at the obligation site
    /// (rustc-style `-->` line pointing at the failing assert /
    /// invariant / call, rather than at the enclosing fn
    /// signature). `None` is acceptable for synthetic /
    /// test-fixture sites that don't have a real source location.
    pub fn span_mark(
        rust_loc: impl Into<String>,
        rust_span: Option<vir::messages::Span>,
        kind: AssertKind,
        inner: Expr,
    ) -> Self {
        Expr::new(ExprNode::SpanMark {
            rust_loc: rust_loc.into(),
            rust_span,
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

    /// `by <tactic>` proof term.
    pub fn by_block(tactic: impl Into<String>) -> Self {
        Expr::new(ExprNode::ByBlock { tactic: tactic.into() })
    }

    pub fn match_expr(scrutinee: Expr, arms: Vec<MatchArm>) -> Self {
        Expr::new(ExprNode::Match { scrutinee: Box::new(scrutinee), arms })
    }

    /// `{ name : ty // pred }` refinement subtype.
    pub fn subtype(name: crate::lean_name::LeanName, ty: Expr, pred: Expr) -> Self {
        Expr::new(ExprNode::Subtype { name, ty: Box::new(ty), pred: Box::new(pred) })
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

    /// `#v[a, b, c]` Lean core Vector literal. Verus `[T; N]` maps to
    /// `Vector T N` (to_lean_type), so array literals in Array-typed
    /// position must render as Vector literals — a bare `[a, b, c]` is
    /// a `List` and mistypes (the `{ deref := [a, b, c] }` family; F3,
    /// DESIGN-lean-all-proofs-followons.md). Slice-typed literals keep
    /// `ArrayLit`. Dispatch: `expr_shared::array_literal_node`.
    VectorLit(Vec<Expr>),

    /// `(a, b, c)` Lean tuple syntax — sugar for nested `Prod.mk a (Prod.mk b c)`.
    /// Distinct from `Anon` (`⟨a, b, c⟩`) because Lean's anon-ctor
    /// notation requires a known expected type ("expected type of this
    /// term could not be determined" elaboration error otherwise),
    /// while `(a, b, c)` infers `Prod` from the operands and works
    /// without context. Used by `ctor_node` for `Dt::Tuple`
    /// constructors (which appear in let-bindings without a target
    /// type) and by `&mut t.<i>` rebind (#145) for the same reason.
    Tuple(Vec<Expr>),

    /// `base[idx]` or `base[idx]!` — array/slice indexing as a dedicated form
    /// so pp can parenthesize the base against application precedence.
    /// `bang: true` emits Lean's panic-on-out-of-bounds variant
    /// (`getElem!`, requires `Inhabited`); `false` emits plain `[idx]`
    /// which Lean elaborates with an inferred bounds proof.
    Index { base: Box<Expr>, idx: Box<Expr>, bang: bool },

    /// `⟨a, b, c⟩` — Lean's anonymous constructor. Used for tuples and for
    /// inferred data constructors where the target type is unambiguous.
    Anon(Vec<Expr>),

    /// `{ name : ty // pred }` — Lean's subtype (refinement) type.
    /// `name` is bound in `pred`. Used to render proof-fn trait method
    /// types with non-unit returns: `∀ (params...), { r : RetTy //
    /// <ensures> }`. The instance method body provides a value of
    /// this type as `⟨witness, proof⟩` (via the `Anon` constructor).
    ///
    /// `name` is the bound variable's name; the subtype introduces a
    /// single binder scope. Sanity check treats this as a Forall-like
    /// scope (the predicate is checked with the bound name in scope).
    Subtype {
        name: crate::lean_name::LeanName,
        ty: Box<Expr>,
        pred: Box<Expr>,
    },

    /// Escape hatch: verbatim Lean text. Reserved for VIR forms that have
    /// no direct Lean analogue (effectless markers, exotic shapes). The
    /// goal is to keep this set small; prefer adding a real node.
    Raw(String),

    /// `by <tactic_body>` — a tactic proof in term position. Used for
    /// proof-fn trait method bodies in class defaults and instance
    /// methods (where the term must produce a proof of the Prop-valued
    /// class field type). The pp re-indents `tactic` based on the
    /// current line's indentation, so the body lines are unambiguously
    /// past the surrounding context's indent — Lean's tactic parser
    /// requires the body to be indented strictly past the `by`-block
    /// start, and inline-Raw emission would put the body at column 0
    /// which conflicts with sibling field declarations.
    ///
    /// `tactic` is the verbatim text from the user's source (read via
    /// `read_tactic_from_source`, already dedented to column 0). Pp
    /// adds the right indent for the emission context.
    ByBlock { tactic: String },

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
    /// wrapping site in `walk_obligations` / `walk_loop` /
    /// `walk_call` / `WpCtx::new` (for fn-ensures Postcondition).
    SpanMark {
        rust_loc: String,
        /// Original Verus `Span` for the obligation (clone of the
        /// SST/VIR-AST node's span). Used by the rust_verify error
        /// reporter to emit a diagnostic whose primary span points
        /// at the obligation site rather than the enclosing fn.
        /// `None` only when the SpanMark was built from a synthetic
        /// site without a real source location (test fixtures,
        /// degenerate `ensures` fallbacks); production codegen paths
        /// always carry a span.
        rust_span: Option<vir::messages::Span>,
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
        use vir::tactus_messages::*;
        match self {
            AssertKind::Obligation(o) => match o {
                ObligationKind::Plain => "",
                ObligationKind::Postcondition => ASSERT_LABEL_POSTCONDITION,
                ObligationKind::LoopInvariant => ASSERT_LABEL_LOOP_INVARIANT,
                ObligationKind::LoopDecrease => ASSERT_LABEL_LOOP_DECREASE,
                ObligationKind::CallPrecondition => ASSERT_LABEL_CALL_PRECONDITION,
                ObligationKind::Termination => ASSERT_LABEL_TERMINATION,
            },
            AssertKind::Hypothesis(h) => match h {
                HypothesisKind::LoopCondition => ASSERT_LABEL_LOOP_CONDITION,
                HypothesisKind::BranchCondition => ASSERT_LABEL_BRANCH_CONDITION,
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
    /// Lean anonymous-constructor tuple pattern `(p1, p2, …)` — the
    /// pattern-side render of `Dt::Tuple` (the expr side is
    /// `ExprNode::Tuple`). `Tuple(1)` never reaches here: the type
    /// renderer flattens 1-tuples to their element, so
    /// `pattern_to_ast` flattens the pattern too.
    Tuple(Vec<Pattern>),
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
    /// `ExprNode::Subtype { name, ty, pred }` — single-name binder
    /// over a refinement predicate. `ty` is in outer scope; `pred`
    /// is in scope extended by `name`. Semantically Forall-like
    /// (one binder, body is `pred`), but rebuilds to a distinct
    /// ExprNode constructor — so it has its own ScopeKind variant
    /// rather than being smuggled through `Quantified`.
    Subtype {
        name: &'a crate::lean_name::LeanName,
        ty: &'a Expr,
        pred: &'a Expr,
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
            ExprNode::Subtype { name, ty, pred } => ScopeKind::Subtype {
                name,
                ty,
                pred,
            },
            // Non-binder compounds + leaves other than Var.
            // Listed explicitly (no `_ =>`) so a new variant
            // compile-errors here, forcing categorization.
            ExprNode::Lit(_)
            | ExprNode::LitBool(_)
            | ExprNode::LitStr(_)
            | ExprNode::LitChar(_)
            | ExprNode::Raw(_)
            | ExprNode::ByBlock { .. }
            | ExprNode::BinOp { .. }
            | ExprNode::UnOp { .. }
            | ExprNode::App { .. }
            | ExprNode::If { .. }
            | ExprNode::TypeAnnot { .. }
            | ExprNode::FieldProj { .. }
            | ExprNode::StructUpdate { .. }
            | ExprNode::ArrayLit(_)
            | ExprNode::VectorLit(_)
            | ExprNode::Index { .. }
            | ExprNode::Anon(_)
            | ExprNode::Tuple(_)
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
        | ExprNode::Raw(_)
        | ExprNode::ByBlock { .. } => {}
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
        ExprNode::Subtype { ty, pred, .. } => {
            f(ty);
            f(pred);
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
        ExprNode::ArrayLit(es) | ExprNode::VectorLit(es)
        | ExprNode::Anon(es) | ExprNode::Tuple(es) => {
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
///
/// `pub(crate)` so `to_lean_fn::strip_class_qualifier` can use the same
/// exhaustive-walker pattern (every new ExprNode variant must be added
/// to map_children, which means consumer transforms can't accidentally
/// miss a new variant — surfaces as a compile error in this file).
pub(crate) fn map_children<F>(node: &ExprNode, mut f: F) -> ExprNode
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
        ExprNode::ByBlock { tactic } => ExprNode::ByBlock { tactic: tactic.clone() },
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
        ExprNode::Subtype { name, ty, pred } => {
            let ty = Box::new(f(ty));
            let pred = Box::new(f(pred));
            ExprNode::Subtype { name: name.clone(), ty, pred }
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
        ExprNode::VectorLit(es) => {
            ExprNode::VectorLit(es.iter().map(|e| f(e)).collect())
        }
        ExprNode::Index { base, idx, bang } => {
            let base = Box::new(f(base));
            let idx = Box::new(f(idx));
            ExprNode::Index { base, idx, bang: *bang }
        }
        ExprNode::Anon(es) => ExprNode::Anon(es.iter().map(|e| f(e)).collect()),
        ExprNode::Tuple(es) => ExprNode::Tuple(es.iter().map(|e| f(e)).collect()),
        ExprNode::SpanMark { rust_loc, rust_span, kind, inner } => ExprNode::SpanMark {
            rust_loc: rust_loc.clone(),
            rust_span: rust_span.clone(),
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
        Pattern::Tuple(args) => {
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
        Pattern::Tuple(args) => Pattern::Tuple(args.iter().map(|a| f(a)).collect()),
        Pattern::Or(l, r) => Pattern::Or(Box::new(f(l)), Box::new(f(r))),
        Pattern::Binding { name, sub } => Pattern::Binding {
            name: name.clone(),
            sub: Box::new(f(sub)),
        },
    }
}

/// Recursively strip `ExprNode::SpanMark` wrappers from an
/// expression tree, returning a structurally-equivalent tree
/// with all source-mapping metadata removed. Used by tests
/// (`pp_eq`) to compare semantic-equivalent expressions where
/// one side carries `SpanMark` wrappers from the WP walker
/// (`walk_obligations` and friends) and the other doesn't.
/// Strips are reasonable here because `SpanMark` is transparent
/// at the Lean level — the wrapping affects only the pp output
/// (a leading `/- @rust:LOC -/` comment) and the landmark
/// side-channel, never semantics.
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
        // Subtype `{ name : ty // pred }` — single binder over `pred`.
        // Same alpha-rename + body subst pattern as Let, just with the
        // body field renamed (`pred` vs `body`). `ty` is in OUTER
        // scope (not affected by the binder).
        ScopeKind::Subtype { name, ty, pred } => {
            let new_ty = substitute_impl(ty, subst);
            let inner_subst = subst_without(subst, name);
            let renames = compute_alpha_renames(&[name], &inner_subst, pred);
            let (final_name, pred_for_subst) = if let Some(fresh) = renames.get(name) {
                let rename_subst = rename_map_to_subst(&renames);
                let renamed_pred = substitute_impl(pred, &rename_subst);
                (fresh.clone(), renamed_pred)
            } else {
                (name.clone(), pred.clone())
            };
            ExprNode::Subtype {
                name: final_name,
                ty: Box::new(new_ty),
                pred: Box::new(substitute_impl(&pred_for_subst, &inner_subst)),
            }
        }
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
        ScopeKind::Subtype { name, .. } => {
            out.insert(name.as_str().to_string());
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

/// The `Var` names `expr` references with no outer binders in scope.
/// Used by instance emission (`trait_impl_to_ast`) to find which binder
/// type-params the instance head actually determines (#122 B3).
pub(crate) fn free_var_names(expr: &Expr) -> std::collections::HashSet<String> {
    let mut out = std::collections::HashSet::new();
    collect_free_vars(expr, &std::collections::HashSet::new(), &mut out);
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
        // Subtype: ty is in outer scope; pred is in scope extended
        // with `name`. Mirror of Let, with `pred` playing the role
        // of body.
        ScopeKind::Subtype { name, ty, pred } => {
            collect_free_vars(ty, bound, out);
            let mut inner = bound.clone();
            inner.insert(name.as_str().to_string());
            collect_free_vars(pred, &inner, out);
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
/// e.g., `push_ret_frames`' Approach-A dest-rename guard (#128)
/// keeps the gensym when the dest name is free in the substituted
/// ensures, because a `∀ x` binder would capture the caller arg.
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
#[path = "tests/lean_ast.rs"]
mod substitute_tests;
