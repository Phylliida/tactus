//! Helpers shared between the VIR-AST renderer (`to_lean_expr.rs`) and
//! the SST renderer (`to_lean_sst_expr.rs`).
//!
//! ## Why two renderers, and why shared helpers instead of full unification
//!
//! VIR-AST and SST are genuinely different trees at different pipeline
//! stages. VIR-AST renders spec fn bodies, proof fn requires/ensures/
//! goals, and decreases clauses. SST renders exec fn bodies and the
//! `CheckDecreaseHeight` termination obligation. Many variants don't
//! cross: VIR-AST has `Block` / `Match` / `Ctor` / `Place`; SST has
//! `CheckDecreaseHeight` / `CallFun::InternalFun` / a flattened
//! statement sequence.
//!
//! A full trait-based unification (`trait ExprLike`) was investigated
//! and rejected — half the variants are asymmetric, so a shared trait
//! would still require per-impl case-splits for the asymmetric half,
//! netting boilerplate without eliminating it. Routing callee-spec
//! inlining through SST (so `to_lean_expr.rs` is purely for spec/proof
//! fns) was also rejected — `FuncCheckSst` is built per-fn during
//! verification rather than prebuilt in the krate, so accessing a
//! callee's SST would require invasive changes to Verus's compilation
//! pipeline. See DESIGN.md § "Two parallel expression renderers" for
//! the full reasoning.
//!
//! What remains: each helper here corresponds to a rule that BOTH
//! renderers must apply identically. The exec-fn WP path inlines
//! callee require/ensure via the VIR renderer while the callee's own
//! theorem renders via the SST renderer; divergence between the two
//! would produce a silent mismatch between the spec Tactus checks and
//! the spec the callee actually proved. Centralising each rule here
//! makes divergence a compile error rather than a runtime
//! disagreement.

use std::collections::HashMap;

use vir::ast::{
    ArithOp, BinaryOp, BitwiseOp, Constant, Dt, FieldOpr, Fun, FunctionX, Ident,
    InequalityOp, RealArithOp, Typ, TypDecoration, TypX,
};

use crate::lean_ast::{BinOp as L, Expr as LExpr, ExprNode};
use crate::to_lean_type::{lean_name, sanitize, short_name};

// ── RenderCtx ────────────────────────────────────────────────────────
//
// Context passed to expression renderers (VIR-AST and SST). Carries
// information that comes from OUTSIDE the local expression structure
// — currently the fn_map for trait-method param-typ lookups, but
// designed to grow as more typing-from-outside needs surface.
//
// The motivation: rendering a class-method-call site needs to know
// the class signature's expected param typs (so args can be coerced
// to wrapper-typed receivers for `&self` / `&mut self` methods).
// Without a context, the renderer only knows the arg's local typ
// and falls back to TypeAnnot-with-wrong-typ, which is what caused
// the test_old_view_trait_dispatch_probe failure pre-RenderCtx.
//
// Pattern: similar to the existing `BinderCtx` for VIR-AST (which
// tracks per-binder typs from fn params), `RenderCtx` carries
// codegen-time-known info that the renderer otherwise lacks.

/// Function lookup borrowed by `RenderCtx`. Same shape as
/// `sst_to_lean::FnMap` — declared here too so `expr_shared` doesn't
/// depend on `sst_to_lean`.
pub type RenderFnMap<'a> = HashMap<&'a Fun, &'a FunctionX>;

/// Render context: typing info available to expression renderers.
///
/// Currently holds an optional `fn_map` for class-method-call lookup.
/// Construct with `RenderCtx::empty()` for tests or rendering paths
/// without fn_map (e.g., test fixtures, sanity check probes). Use
/// `RenderCtx::with_fn_map(&fn_map)` for production rendering at
/// codegen entry points.
#[derive(Clone, Copy)]
pub struct RenderCtx<'a> {
    pub fn_map: Option<&'a RenderFnMap<'a>>,
}

impl<'a> RenderCtx<'a> {
    /// Empty context — class-method-call rendering falls back to
    /// no-coerce. Safe for any rendering path; ideal for tests.
    pub fn empty() -> Self {
        Self { fn_map: None }
    }

    /// Context with fn_map for class-method-call rendering.
    pub fn with_fn_map(fn_map: &'a RenderFnMap<'a>) -> Self {
        Self { fn_map: Some(fn_map) }
    }

    /// Look up a class-method decl's declared param typs. Returns
    /// `None` when the Fun isn't in fn_map (cross-crate, or no fn_map
    /// in this RenderCtx). Caller falls back to no-coerce rendering
    /// when `None` — gracefully degrades for the cross-crate case
    /// rather than panicking.
    ///
    /// The lookup goes to the trait method DECL's params (which is
    /// what `CallFun::Fun(fun, Some(_))` references in SST and what
    /// `CallTarget::Fun(DynamicResolved, fun, ...)` references in
    /// VIR-AST). Trait dispatch happens at the decl's typing; the
    /// resolved impl might have textually-different param names but
    /// positionally-aligned typs — the decl's typs are what the class
    /// signature uses.
    pub fn class_method_param_typs(&self, fun: &Fun) -> Option<Vec<Typ>> {
        let fn_map = self.fn_map?;
        let func = fn_map.get(fun)?;
        Some(func.params.iter().map(|p| p.x.typ.clone()).collect())
    }
}

/// Map a VIR/SST binary op to its structural Lean `BinOp` representation.
///
/// Returns `None` for ops that don't correspond to a Lean structural
/// binary operator — the caller emits those via
/// `App(non_binop_head(op), …)`. SST's exec-fn path rejects everything
/// except `Xor` before reaching the `None` branch; the VIR-AST path
/// accepts all variants for spec/proof fn rendering.
pub(crate) fn binop_to_ast(op: &BinaryOp) -> Option<L> {
    Some(match op {
        BinaryOp::And => L::And,
        BinaryOp::Or => L::Or,
        BinaryOp::Implies => L::Implies,
        BinaryOp::Eq(_) => L::Eq,
        BinaryOp::Ne => L::Ne,
        BinaryOp::Inequality(InequalityOp::Le) => L::Le,
        BinaryOp::Inequality(InequalityOp::Lt) => L::Lt,
        BinaryOp::Inequality(InequalityOp::Ge) => L::Ge,
        BinaryOp::Inequality(InequalityOp::Gt) => L::Gt,
        BinaryOp::Arith(ArithOp::Add(_)) => L::Add,
        BinaryOp::Arith(ArithOp::Sub(_)) => L::Sub,
        BinaryOp::Arith(ArithOp::Mul(_)) => L::Mul,
        BinaryOp::Arith(ArithOp::EuclideanDiv(_)) => L::Div,
        BinaryOp::Arith(ArithOp::EuclideanMod(_)) => L::Mod,
        BinaryOp::RealArith(RealArithOp::Add) => L::Add,
        BinaryOp::RealArith(RealArithOp::Sub) => L::Sub,
        BinaryOp::RealArith(RealArithOp::Mul) => L::Mul,
        BinaryOp::RealArith(RealArithOp::Div) => L::Div,
        BinaryOp::Bitwise(BitwiseOp::BitAnd, _) => L::BitAnd,
        BinaryOp::Bitwise(BitwiseOp::BitOr, _) => L::BitOr,
        BinaryOp::Bitwise(BitwiseOp::BitXor, _) => L::BitXor,
        BinaryOp::Bitwise(BitwiseOp::Shr(_), _) => L::Shr,
        BinaryOp::Bitwise(BitwiseOp::Shl(_, _), _) => L::Shl,
        BinaryOp::Xor
        | BinaryOp::HeightCompare { .. }
        | BinaryOp::StrGetChar
        | BinaryOp::Index(_, _)
        | BinaryOp::IeeeFloat(_) => return None,
    })
}

/// Head identifier used when a VIR/SST binop is expressed as a 2-arg
/// function call rather than a structural `BinOp` — i.e., the `None`
/// return from [`binop_to_ast`]. These render as stand-ins; the exec-fn
/// SST path reaches `Xor` and `StrGetChar`. The spec/proof VIR path
/// reaches all cases.
pub(crate) fn non_binop_head(op: &BinaryOp) -> &'static str {
    match op {
        // Lean's `Bool.xor` — dotted so it bypasses the sanity allowlist
        // and resolves natively. Verus's `BinaryOp::Xor` is logical xor on
        // bools (bitwise xor on ints goes through `BitwiseOp::BitXor`,
        // which already has a structural `BinOp::BitXor`).
        BinaryOp::Xor => "Bool.xor",
        BinaryOp::HeightCompare { .. } => "Tactus.heightLt",
        // Verus's `verus_builtin::strslice_get_char(s, i)` — codepoint-
        // indexed string lookup. Lean's `String.get` is byte-indexed and
        // returns Lean's `Char`, while Verus's surface returns `char` →
        // Tactus's `Nat`. The prelude provides `Tactus.strGetChar` as
        // the right adapter (see TactusPrelude.lean for semantics).
        BinaryOp::StrGetChar => "Tactus.strGetChar",
        BinaryOp::Index(_, _) => "Tactus.index",
        BinaryOp::IeeeFloat(_) => "Tactus.floatOp",
        _ => "?",
    }
}

/// Render the non-float arms of a `Constant`.
///
/// Returns `None` for `Real` / `Float32` / `Float64` so each caller
/// decides: the VIR-AST path emits a type-annotated literal (Verus
/// accepts floats in spec code); the SST path rejects them as
/// unsupported in exec-fn bodies.
pub(crate) fn const_to_node_common(c: &Constant) -> Option<ExprNode> {
    Some(match c {
        Constant::Bool(b) => ExprNode::LitBool(*b),
        Constant::Int(n) => ExprNode::Lit(n.to_string()),
        Constant::StrSlice(s) => ExprNode::LitStr(s.to_string()),
        Constant::Char(c) => ExprNode::LitChar(*c),
        Constant::Real(_) | Constant::Float32(_) | Constant::Float64(_) => return None,
    })
}

/// Resolve a `Clip` coercion to its Lean wrapper name, given whether
/// the source and destination types render as Lean `Int` (per
/// `to_lean_sst_expr::renders_as_lean_int`).
///
///   * `(Int, Nat)` → `Some("Int.toNat")`
///   * `(Nat, Int)` → `Some("Int.ofNat")`
///   * same-side    → `None` (passthrough)
///
/// Both renderers' Clip arms consult this table so the coercion rule
/// lives in one place. Dropping a coercion in the mixed case (the old
/// SST behaviour) caused a soundness hole: `x as int - y as int` for
/// `x, y : u8` rendered as `x - y` on `Nat`, which truncates negatives
/// to zero. Forcing subtraction to happen over `Int` — via
/// `Int.ofNat` — makes the lower-bound refinement check actually fire.
pub(crate) fn clip_coercion_head(src_int: bool, dst_int: bool) -> Option<&'static str> {
    match (src_int, dst_int) {
        (true, false) => Some("Int.toNat"),
        (false, true) => Some("Int.ofNat"),
        _ => None,
    }
}

/// Apply a clip coercion wrapper to an already-rendered `LExpr`, using
/// [`clip_coercion_head`] to pick the wrapper name. Passthrough
/// (same-side) returns the expression unchanged.
pub(crate) fn apply_clip_coercion(src_int: bool, dst_int: bool, inner: LExpr) -> LExpr {
    match clip_coercion_head(src_int, dst_int) {
        Some(head) => LExpr::app1(LExpr::var_lit(head), inner),
        None => inner,
    }
}

/// Build a Lean constructor expression from an already-rendered
/// `Vec<LExpr>` of field values.
///
/// * `Dt::Path(path)` + variant → named ctor `TypeName.variant arg₁ arg₂ …`,
///   with the special case that a struct's sole variant (whose name
///   equals the type's short name) renders as `TypeName.mk` —
///   matching Lean's auto-generated `.mk` for single-field-group
///   inductives.
/// * `Dt::Tuple(_)` → Lean tuple syntax `(a, b, c)` (sugar for
///   `Prod.mk a (Prod.mk b c)`). Distinct from anon-ctor `⟨a, b, c⟩`
///   because the bare anon-ctor needs a known expected type — which
///   isn't available at let-bindings (`let t := ⟨x, 0⟩` fails to
///   elaborate). Tuple syntax infers `Prod` from the operands and
///   works without context.
///
/// Both expression renderers (VIR-AST and SST) use this so the ctor
/// naming convention can't drift between the proof-fn / spec-fn path
/// and the exec-fn WP path. Caller is responsible for rendering the
/// fields via their respective per-tree walker.
pub(crate) fn ctor_node(
    dt: &Dt,
    variant: &Ident,
    rendered_fields: Vec<LExpr>,
) -> ExprNode {
    match dt {
        Dt::Path(path) => {
            let type_name = lean_name(path);
            let variant_seg = if variant.as_str() == short_name(path) {
                "mk".to_string()
            } else {
                sanitize(variant)
            };
            let head = format!("{}.{}", type_name, variant_seg);
            // Constructor heads are dotted Lean names like `MyType.Variant`.
            // They're path-derived (not VarIdent), but the path has already
            // been sanitized via `lean_name`. `synthetic` wraps verbatim.
            let head_name = crate::lean_name::LeanName::synthetic(head);
            if rendered_fields.is_empty() {
                ExprNode::Var(head_name)
            } else {
                ExprNode::App {
                    head: Box::new(LExpr::var(head_name)),
                    args: rendered_fields,
                }
            }
        }
        Dt::Tuple(_) => ExprNode::Tuple(rendered_fields),
    }
}

/// Render the `is_<variant>` discriminator for a `UnaryOpr::IsVariant`
/// applied to an already-rendered receiver expression. Lean's inductive
/// derivation provides these accessors automatically: `x.isSome` for
/// `Option.Some`, `x.isOk` for `Result.Ok`, etc. Both renderers call
/// this so the naming convention stays consistent.
pub(crate) fn is_variant_node(variant: &Ident, inner: LExpr) -> ExprNode {
    LExpr::field_proj(inner, format!("is{}", variant)).node
}

// ── Reserved identifier conventions ────────────────────────────────────
//
// Tactus codegen produces several kinds of synthetic Lean identifiers.
// The conventions below describe what each prefix/suffix means and
// when to use which. A new contributor adding a gensym site or a
// prelude def should pick the matching convention rather than invent
// a new one.
//
// **Convention 1: `_tactus_<role>_<id>` prefix** — codegen-internal
// gensyms and theorem names. Reserved by virtue of leading underscore
// + `tactus_` prefix; Rust source can't produce these as identifiers.
// Examples:
//   * `_tactus_d_old_<loop_id>` — pre-body decrease snapshot per loop
//     (`build_wp_loop`).
//   * `_tactus_ret_<id>` — post-call ∀-bound return value
//     (`build_call_substitutions`).
//   * `_tactus_mut_post_<id>` — post-call existential for a `&mut`
//     arg (`build_call_substitutions`).
//   * (`_tactus_field_<idx>` was previously used for accessor-fn body's
//     field-extract local. Now both accessor-fn bodies and height-fn
//     pattern binders use the field's declared name directly via
//     `to_lean_fn::field_name` — same name the inductive's variant
//     ctor uses — so the synthetic convention is no longer needed.)
//   * `_tactus_<kind>_<fn>_at_<loc>_<id>` — per-obligation theorem
//     names (`build_theorem_name`).
//   * `_tactus_assoc_<X>_<N>` — fresh implicit type binder lifted
//     from a `<X as T>::N` projection in a blanket impl signature
//     (`impl_subst::ImplSubst::build`, Bug B step 2). One per
//     unique (X, T, N) triple discovered in the impl's signature
//     typs. Mapped to a synthesised `TypEquality` bound so existing
//     `trait_bounds_to_ast` machinery augments the trait bracket
//     (`[View A _tactus_assoc_A_V]`) from the same source.
//
// **Convention 2: `<x>_at_pre_tactus` SUFFIX** — pre-state references
// for `&mut` params in callee-spec inlining. The ONLY suffix-style
// reserved name; every other convention is a prefix. Justification:
// the suffix preserves the original param name `x` at the start of
// the identifier, which keeps Lean error messages readable
// (`x_at_pre_tactus = 5` is more legible than
// `_tactus_at_pre_x = 5`). See `varat_pre_name`.
//
// **Convention 3: `tactus_<name>` (no underscore prefix)** — user-
// visible Lean tactics defined in `TactusPrelude.lean`. Users may
// reference these in `proof { … }` blocks or via the
// `#[verifier::tactus_tactic("…")]` attribute. Examples:
//   `tactus_auto`, `tactus_peel`, `tactus_first`,
//   `tactus_case_split`, `tactus_usize_bound`.
// No leading underscore because they're meant to be human-typed.
//
// **Convention 4: Bare names in `TactusPrelude.lean`** — axioms /
// defs that are user-visible but read-only. Examples:
//   `arch_word_bits`, `arch_word_bits_valid`, `usize_hi`, `isize_hi`.
// These look unprotected but actually can't collide with user code:
// Tactus generates user definitions inside `namespace
// crate.module`, while these live at top-level in TactusPrelude.
// Lean's namespace resolution prevents the collision. Listed in
// `sanity::name_resolves`'s allowlist so the post-codegen check
// doesn't flag them as unresolved.
//
// **Convention 5: `<base>_α<N>` suffix** — alpha-rename freshness
// suffix produced by `lean_ast::fresh_name` (#116). When
// `substitute` detects that a binder would capture a free variable
// from the substitution, it generates a fresh name by appending
// `_α<N>` (smallest N ≥ 1 not in the forbidden set) and rewrites
// the binder + body in lockstep before applying the main
// substitution. The Greek letter α makes the alpha-renaming origin
// obvious in error messages and generated Lean. This is the only
// convention that uses Unicode — every other reserved name is
// ASCII. User code can technically produce identifiers containing
// Unicode α (Lean accepts them), but `<base>_α<N>` specifically is
// reserved for this purpose; if a user happened to define `x_α1`
// themselves, our forbidden-set check would skip it and pick `_α2`
// instead. See `lean_ast::fresh_name`.
//
// **Gensym mechanism choice**: when generating a `_tactus_<role>_<id>`
// name:
//   * Use Verus's stable identifier (e.g., `StmX::Loop::id`, a
//     `u64` per loop instance) when one is available — gives
//     deterministic output that's stable across runs.
//   * Fall back to `ObligationEmitter::next_id()` (per-fn
//     monotonic counter) when no stable upstream ID exists.
//     Theorem names are namespaced by `fn_name` so per-fn
//     uniqueness is sufficient.
//
// **`sanity::name_resolves` is the canonical allowlist** for names
// that resolve via the prelude rather than via emitted definitions.
// Adding a new prelude def means updating the allowlist.

/// Render a `VarAt(x, Pre)` reference (the post-`old(x)` form Verus
/// uses for pre-state references in `&mut` ensures clauses) as a
/// distinct Lean identifier.
///
/// Why distinct from `Var(x)`: in a callee with `fn bump(x: &mut u8)
/// requires *old(x) < 100 ensures *x == *old(x) + 1`, the VIR-AST
/// ensures contains both `Var(x)` (post-call value) and `VarAt(x,
/// Pre)` (pre-call value). If both rendered to the same Lean name,
/// the ensures would collapse to `x == x + 1` — vacuously false for
/// finite arithmetic, silent translation bug. Rendering `VarAt(x,
/// Pre)` to a syntactically distinct name lets the call-site
/// substitution map send it to the caller's pre-call value while
/// `Var(x)` goes to a fresh existential for the post-call value.
///
/// The `_at_pre_tactus` suffix is reserved (combined with the
/// already-documented `_tactus_` prefix convention, won't collide
/// with user identifiers — Rust source can't produce trailing
/// `_tactus`).
///
/// Shared between the VIR-AST and SST renderers so the rendering
/// rule lives in one place. Divergence would make the
/// substitution-key in `walk_call` (built against VIR-AST shape)
/// fail to match the SST renderer's output for the same VarAt.
pub(crate) fn varat_pre_name(name: &str) -> String {
    format!("{}_at_pre_tactus", name)
}

/// True when a parameter (or local) is an `&mut`-like reference whose
/// Lean binder type should be the `Tactus.MutRef` wrapper.
///
/// Covers three Verus shapes that all denote the same semantic thing
/// (a mutable reference to T):
/// * **Legacy mode**: `is_mut: true` with `typ` = plain `T`. Verus's
///   default mode produces this for `fn f(x: &mut T)`.
/// * **New-mut-ref mode after migration**: `is_mut: false` with
///   `typ` = `TypX::MutRef(T)`. Produced under `-V new-mut-ref` plus
///   `deprecated_postcondition_mut_ref_style(true)`.
/// * **Decorated**: `typ` = `Decorate(MutRef, _, T)`. The decoration-
///   level shape that appears at some VIR sites.
///
/// All three render uniformly as `(x : Tactus.MutRef T)` at the Lean
/// binder via [`crate::to_lean_type::param_binder_typ`]. The shared
/// predicate keeps every site that asks "is this an &mut?" in
/// lockstep — a future Verus-side change to how `&mut` is represented
/// updates one place rather than several. Used by:
/// * `to_lean_fn::wrap_body_with_param_derefs` (decides which params
///   need a body-deref shadow)
/// * `sst_to_lean::build_param_binders` (decides which binders get
///   wrapper-typed)
/// * `sst_to_lean::exec_fn_theorems_to_ast` (decides which params
///   populate `mut_param_names` for the SST rewrite + the pre-state
///   capture frames)
/// * `sst_to_lean::add_param_subst_entries` (decides which callee
///   params need pre/post substitution split)
pub(crate) fn is_mut_ref_typ(typ: &Typ, is_mut: bool) -> bool {
    if is_mut {
        return true;
    }
    match &**typ {
        TypX::MutRef(_) => true,
        TypX::Decorate(TypDecoration::MutRef, _, _) => true,
        _ => false,
    }
}

/// Wrapper name (e.g., `"Tactus.Ref"`) for a reference-like decoration,
/// or `None` for transparent ones (Ghost / Tracked / Never / ConstPtr).
/// Single source of truth — `to_lean_type::typ_to_node` and
/// `to_lean_expr`'s coercion machinery agree on this mapping. Adding
/// a new reference-like decoration is one edit.
pub(crate) fn decoration_wrapper(deco: TypDecoration) -> Option<&'static str> {
    match deco {
        TypDecoration::Ref => Some("Tactus.Ref"),
        TypDecoration::MutRef => Some("Tactus.MutRef"),
        TypDecoration::Box => Some("Tactus.Box"),
        TypDecoration::Rc => Some("Tactus.Rc"),
        TypDecoration::Arc => Some("Tactus.Arc"),
        TypDecoration::Ghost | TypDecoration::Tracked
        | TypDecoration::Never | TypDecoration::ConstPtr => None,
    }
}

/// Count the number of reference-decoration layers in a typ. Peels
/// `Boxed` transparently (Verus's poly encoding, not user-visible).
/// `TypX::MutRef` counts as one layer (new-mut-ref-mode's
/// non-Decorate shape).
///
/// Used by both `to_lean_expr::apply_ref_coercion_if_needed`
/// (wrapping with `.mk` for under-decorated rendered exprs) and
/// `apply_deref_chain` (unwrapping with `.deref` to reach inner T
/// for height-fn args and exec-fn body shadows).
pub(crate) fn count_ref_decorations(typ: &TypX) -> usize {
    let mut n = 0;
    let mut cur = typ;
    loop {
        match cur {
            TypX::Decorate(deco, _, inner) => {
                if decoration_wrapper(*deco).is_some() {
                    n += 1;
                }
                cur = &**inner;
            }
            TypX::Boxed(inner) => cur = &**inner,
            TypX::MutRef(_) => {
                n += 1;
                break;
            }
            _ => break,
        }
    }
    n
}

/// Apply N `.deref` field-projections to `base`, peeling N wrapper
/// layers to reach the inner value. Used wherever the rendered Lean
/// type has more `Tactus.X` wrappers than the call site expects:
///
/// * **Exec-fn body shadow**: a fn param `(s : Tactus.Ref Stack)`
///   needs `let s := s.deref` so body code sees `s : Stack`.
/// * **Height-fn recursive arg**: a field of type `Box<Stack>` has
///   binder type `Tactus.Box Stack`, but `Stack.height` expects
///   `Stack` — pass `<field_binder>.deref` instead of `<field_binder>`.
///
/// `n = 0` returns `base` unchanged.
pub(crate) fn apply_deref_chain(base: LExpr, n: usize) -> LExpr {
    let mut out = base;
    for _ in 0..n {
        out = LExpr::field_proj(out, "deref");
    }
    out
}

/// Collect the reference-decoration wrapper names from `typ`,
/// outermost-first. `Boxed` is transparent (Verus's poly encoding,
/// not user-visible); peeled silently. `MutRef` counts as one
/// (terminal — stops the walk).
///
/// Companion to [`count_ref_decorations`] — the count tells you "how
/// many", this tells you "which", in outermost-first order.
pub(crate) fn collect_ref_wraps(typ: &TypX) -> Vec<&'static str> {
    let mut out = Vec::new();
    let mut cur = typ;
    loop {
        match cur {
            TypX::Decorate(deco, _, inner) => {
                if let Some(w) = decoration_wrapper(*deco) {
                    out.push(w);
                }
                cur = &**inner;
            }
            TypX::Boxed(inner) => cur = &**inner,
            TypX::MutRef(_) => {
                out.push("Tactus.MutRef");
                break;
            }
            _ => break,
        }
    }
    out
}

/// Wrap `base` with N `.mk` constructors. `wraps[0]` is OUTERMOST
/// (last applied); `wraps[last]` is INNERMOST (first applied). So
/// `apply_wrap_chain(x, &["Tactus.Ref", "Tactus.Box"])` produces
/// `Tactus.Ref.mk (Tactus.Box.mk x)` — Box innermost, Ref outermost.
///
/// Dual of [`apply_deref_chain`]: deref peels wrappers off, wrap
/// puts them on. Both compose to identity when `wraps` matches the
/// peel order.
pub(crate) fn apply_wrap_chain(base: LExpr, wraps: &[&'static str]) -> LExpr {
    let mut out = base;
    for w in wraps.iter().rev() {
        out = LExpr::app1(LExpr::var_lit(&format!("{}.mk", w)), out);
    }
    out
}

/// Bidirectional wrapper-kind-and-depth coercion. Bridge `value`
/// (currently at `from_typ`) to `to_typ` by inserting `.deref` chain
/// and/or `.mk` chain to match wrapper sequences.
///
/// Compares wrapper sequences (outermost-first) from both types:
///
/// * Sequences equal → no coercion.
/// * Sequences share a common inner suffix → peel only the
///   non-matching outer wraps of `from`, then wrap with the
///   non-matching outer wraps of `to`. Examples:
///   - `from=[Ref]`, `to=[]` → `value.deref` (depth shrink).
///   - `from=[]`, `to=[Ref]` → `Tactus.Ref.mk value` (depth grow).
///   - `from=[Box, Ref]`, `to=[Ref, Ref]` → `Tactus.Ref.mk value.deref`
///     (common suffix `[Ref]`; rewrap outer Box → Ref).
///   - `from=[MutRef]`, `to=[Ref]` → `Tactus.Ref.mk value.deref`
///     (kind mismatch at equal depth — peel one, wrap one).
///
/// This is the shared bidirectional helper that
/// `to_lean_expr::apply_ref_coercion_if_needed` and the SST-side
/// typed-composition machinery both delegate to. Centralising it
/// here means callers across the VIR-AST renderer, SST renderer,
/// substitution sites, and TypedExpr smart constructors all bridge
/// wrapper mismatches identically.
///
/// Coercion is wrapper-only: we don't model the inner type's
/// structure. If `from_typ` and `to_typ` have matching wrapper
/// sequences but different inner types (e.g., `Box<Int>` vs
/// `Box<Bool>`), this returns `value` unchanged — type-level
/// mismatches at the inner level are Lean's problem, not ours.
pub(crate) fn coerce_lexpr(value: LExpr, from_typ: &Typ, to_typ: &Typ) -> LExpr {
    let from_wraps = collect_ref_wraps(&**from_typ);
    let to_wraps = collect_ref_wraps(&**to_typ);
    if from_wraps == to_wraps {
        return value;
    }
    // Find longest common SUFFIX of the two wrap sequences. The
    // suffix corresponds to inner wraps that already match — we
    // leave those untouched. Only the non-matching outer wraps need
    // peel + rewrap.
    let suffix_len = from_wraps
        .iter()
        .rev()
        .zip(to_wraps.iter().rev())
        .take_while(|(a, b)| a == b)
        .count();
    let peel_n = from_wraps.len() - suffix_len;
    let wrap_slice = &to_wraps[..to_wraps.len() - suffix_len];
    let peeled = apply_deref_chain(value, peel_n);
    apply_wrap_chain(peeled, wrap_slice)
}

/// Lean accessor string for the `n`th element of an `arity`-tuple.
///
/// Lean 4 represents N-tuples as right-nested `Prod`:
/// `(a, b, c) : Int × Int × Int = Int × (Int × Int)`. The
/// auto-derived accessors are `.fst` (= `.1`) and `.snd` (= `.2`)
/// on each level — for an N-tuple, the j-th element (0-indexed)
/// requires `.2` (j times) followed by `.1`, except the last
/// element which is just `.2` repeated (arity-1) times. Examples:
///
/// | arity | n | result   | meaning                  |
/// |-------|---|----------|--------------------------|
/// | 2     | 0 | `1`      | `.1` (first of pair)     |
/// | 2     | 1 | `2`      | `.2` (second of pair)    |
/// | 3     | 0 | `1`      | first element            |
/// | 3     | 1 | `2.1`    | inner pair's first       |
/// | 3     | 2 | `2.2`    | inner pair's second      |
/// | 4     | 0 | `1`      |                          |
/// | 4     | 1 | `2.1`    |                          |
/// | 4     | 2 | `2.2.1`  |                          |
/// | 4     | 3 | `2.2.2`  |                          |
///
/// The result is intended to be appended to a base via
/// `<base>.<result>` — Lean parses `e.2.1` as `((e).2).1`, which
/// matches the desired projection.
///
/// Requires `arity >= 2`. Verus doesn't produce 0-tuples (unit type
/// lowers to no field access) or 1-tuples (degenerate case with
/// other lowerings); the assert guards against shape drift if a
/// future Verus rebase changes that.
pub(crate) fn tuple_field_accessor(arity: usize, n: usize) -> String {
    // Verus shouldn't produce 0- or 1-tuples here (unit type lowers
    // to no field access; 1-tuples have other lowerings). If one
    // arrives, the prior fallback `(n + 1).to_string()` would emit a
    // probably-wrong Lean accessor; surface it as shape drift instead.
    assert!(
        arity >= 2,
        "tuple_field_accessor: arity {} < 2 — 0-tuple (unit) and 1-tuple \
         shouldn't reach field accessor synthesis. n={n}. If this fires, \
         please open an issue (probable Verus rebase shape drift).",
        arity,
    );
    if n + 1 >= arity {
        // Last position: `.2` repeated (arity - 1) times.
        // Arity-2 i=1 → "2"; arity-3 i=2 → "2.2"; etc.
        std::iter::repeat("2")
            .take(arity - 1)
            .collect::<Vec<_>>()
            .join(".")
    } else {
        // Non-last position: `.2` repeated n times, then `.1`.
        // Arity-3 i=0 → "1"; arity-3 i=1 → "2.1"; arity-4 i=2 → "2.2.1".
        let twos: Vec<&str> = std::iter::repeat("2").take(n).collect();
        if twos.is_empty() {
            "1".to_string()
        } else {
            format!("{}.1", twos.join("."))
        }
    }
}

/// Map a VIR field access to the Lean side's field name.
///
/// * Anonymous tuple (`Dt::Tuple`) uses 0-indexed numeric fields like
///   `"0"` / `"1"`; Lean's `Prod`-derived accessor is 1-indexed
///   (`.1`, `.2`), so `"0"` → `"1"`, `"1"` → `"2"`, etc.
/// * Single-variant struct (`Dt::Path` where the variant name equals
///   the type's short name) uses the structure-auto-derived accessor
///   names: numeric `"0"` → `"val0"`, named fields pass through
///   (after sanitization). Lean's `structure` auto-derives these.
/// * Multi-variant enum (`Dt::Path` where the variant name differs
///   from the type's short name) routes through the per-variant
///   accessor fns emitted by `datatype_to_cmds` — numeric field
///   becomes `"<Variant>_val<n>"`, named field becomes
///   `"<Variant>_<field>"`. Lean's `inductive` doesn't auto-derive
///   field accessors, so we synthesise `def Kind.Foo_val0 : Kind → …`
///   alongside the inductive declaration.
///
/// Shared between the VIR-AST and SST renderers so the naming rule
/// lives in one place. Divergence would make match-arm desugaring
/// (exec path) reference a field name that the accessor-fn emission
/// (preamble path) doesn't define — silent Lean "invalid field"
/// failure.
pub(crate) fn field_access_name(field_opr: &FieldOpr) -> String {
    let raw = field_opr.field.as_str();
    let numeric = raw.parse::<usize>().ok();
    match (&field_opr.datatype, numeric) {
        (Dt::Tuple(arity), Some(n)) => tuple_field_accessor(*arity, n),
        (Dt::Path(path), _) => {
            let type_short = short_name(path);
            let variant = field_opr.variant.as_str();
            let is_single_variant = variant == type_short;
            let field_seg = match numeric {
                Some(n) => format!("val{}", n),
                None => sanitize(raw),
            };
            if is_single_variant {
                field_seg
            } else {
                format!("{}_{}", sanitize(variant), field_seg)
            }
        }
        // Tuple with non-numeric field name — Verus shouldn't produce
        // this (tuple fields are positional, named "0", "1", ...). If
        // it ever does, the previous defensive fallback (`sanitize(raw)`)
        // would silently produce a wrong field name. Surface it as a
        // shape-drift signal instead.
        (Dt::Tuple(_), None) => unreachable!(
            "field_access_name: tuple with non-numeric field `{}` — Verus's mode \
             check should reject this upstream. If this fires, please open an \
             issue (probable Verus rebase shape drift).",
            raw,
        ),
    }
}
