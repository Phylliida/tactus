//! Translate SST expressions (`vir::sst::Exp`) to `lean_ast::Expr`.
//!
//! Mirrors `to_lean_expr` but operates on SST's `Exp` / `ExpX` instead of
//! VIR-AST's `Expr` / `ExprX`. SST is a cleaned-up AST used as the input
//! to WP generation for exec fns (`sst_to_lean`).
//!
//! ## Validation and rendering — unified case analysis
//!
//!   * [`sst_exp_to_ast_checked`] is the primary recursive impl — it
//!     validates every SST shape as it renders, returning `Err(…)` for
//!     forms we don't support. Use this at the boundary where unchecked
//!     SST enters the pipeline (walk, req/ens validation).
//!   * [`Validated`] + [`lower`] is the typed pipeline used by the WP
//!     walker (`sst_to_lean`): construct a `Validated<'a>` witness via
//!     `Validated::check`, then `lower` is infallible by type. This
//!     replaces an earlier `sst_exp_to_ast` panic-shim (removed in
//!     #115) — sites that need a non-fallible render now use
//!     `sst_exp_to_ast_checked(e).expect("<contract>")` with a
//!     site-specific message naming why validation should hold.
//!
//! This unification replaces an earlier split where `check_exp` (in
//! `sst_to_lean`) and a panic-shim `sst_exp_to_ast` each had parallel
//! case analyses that had to stay in sync by hand.

use vir::ast::*;
use vir::sst::{BndX, CallFun, Exp, ExpX, InternalFun};
use crate::expr_shared::{
    apply_deref_chain, binop_to_ast, const_to_node_common, count_ref_decorations,
    ctor_node, field_proj_opr, is_variant_node, non_binop_head,
};
use crate::lean_ast::{substitute, Expr as LExpr, ExprNode};
use crate::to_lean_expr::vir_var_binders_to_ast;
use crate::to_lean_type::{lean_name, typ_to_expr};

/// Build a `lean_ast::Expr` from an SST expression, validating as we
/// go. Returns `Err(reason)` for any SST form we don't know how to
/// emit. This is the primary entry point — use it anywhere unchecked
/// SST enters (walk, req/ens validation).
///
/// Uses an empty [`RenderCtx`], so class-method-call rendering falls
/// back to no-coerce (the pre-RenderCtx behavior). Use
/// [`sst_exp_to_ast_checked_with_ctx`] when a ctx is available to
/// enable per-call-site wrapper-arch coercion.
pub fn sst_exp_to_ast_checked(e: &Exp) -> Result<LExpr, String> {
    sst_exp_to_ast_checked_with_ctx(e, &crate::expr_shared::RenderCtx::empty())
}

/// Variant of [`sst_exp_to_ast_checked`] that takes a [`RenderCtx`]
/// for typing info that comes from outside the local expression
/// structure (currently: class method param typs for `&self` /
/// `&mut self` arg coercion).
pub fn sst_exp_to_ast_checked_with_ctx(
    e: &Exp,
    ctx: &crate::expr_shared::RenderCtx,
) -> Result<LExpr, String> {
    // Typed spine boundary (P1, DESIGN-typed-renderer.md): internal
    // rendering carries ACTUAL typs; the public contract is "rendered
    // == claimed", restored here by bridging to `e.typ`. Passthrough
    // when actual == claimed (the unmigrated default), so this is
    // bit-for-bit the old behavior for unmigrated arms.
    Ok(exp_to_typed(e, ctx)?.into_slot(&e.typ))
}

/// A reference to an SST expression that has been validated (via
/// [`sst_exp_to_ast_checked`]) and is therefore safe to lower to
/// `LExpr` without panic risk.
///
/// The newtype is constructable only via [`Validated::check`]; the
/// only way to consume it is [`lower`], which is infallible by
/// construction. This replaces the older `sst_exp_to_ast` panic
/// site — the panic case ("caller should have validated") was a
/// runtime-checked contract; now it's a type-system-enforced one.
///
/// Walkers (`walk_obligations` / `walk_loop` / `walk_call` / etc.)
/// receive `Wp<'a>` whose Exp slots are already `Validated<'a>`,
/// so the inside of the walker never has to think about
/// validation — the type guarantees it.
///
/// **Borrow over ownership.** `Validated` is a borrow into the
/// input SST, not an owning wrapper. Synthesized hypotheses (not
/// derived from an SST Exp — e.g., a negated cond from #114's
/// cond_setup transform) go through [`Wp::Hyp`] instead, which
/// carries an already-rendered `LExpr` directly. Avoiding the
/// `Arc<Exp>` clone in `Validated` keeps the validation contract
/// scoped to genuinely-borrowed SST cases.
///
/// See `lean_name::LeanName` for the same architectural pattern
/// applied to identifiers; see DESIGN.md "Type-system-enforced
/// invariants" for the rationale.
#[derive(Clone, Copy)]
pub struct Validated<'a> {
    inner: &'a Exp,
}

impl<'a> Validated<'a> {
    /// Run validation by attempting `sst_exp_to_ast_checked`. Returns
    /// a witness on success, or the validation error on failure.
    pub fn check(e: &'a Exp) -> Result<Self, String> {
        sst_exp_to_ast_checked(e)?;
        Ok(Validated { inner: e })
    }

    /// The underlying `Exp` reference. Use sparingly — most consumers
    /// should go through [`lower`] which preserves the validated
    /// invariant. Useful for routing the same Exp through a
    /// different lowering path (e.g., looking at its `.typ` field
    /// or matching on its `ExpX` shape).
    pub fn raw(&self) -> &'a Exp { self.inner }
}

/// Lower a validated Exp to `LExpr`. Cannot panic — the type system
/// guarantees the input was already validated by `Validated::check`.
/// Takes `&Validated` so callers don't have to deref-copy at call
/// sites (Validated is Copy, but `*v` is more noise than necessary
/// when callers usually have a borrow already).
///
/// Uses an empty [`RenderCtx`], so class-method-call rendering falls
/// back to no-coerce. Use [`lower_with_ctx`] when a ctx is available
/// to enable wrapper-arch coercion at trait dispatch sites.
pub fn lower(v: &Validated<'_>) -> LExpr {
    lower_with_ctx(v, &crate::expr_shared::RenderCtx::empty())
}

/// Variant of [`lower`] that takes a [`RenderCtx`] for typing info
/// (currently: class method param typs for `&self` / `&mut self` arg
/// coercion). Use at codegen entry points where the fn_map is
/// available.
pub fn lower_with_ctx(v: &Validated<'_>, ctx: &crate::expr_shared::RenderCtx) -> LExpr {
    sst_exp_to_ast_checked_with_ctx(v.inner, ctx).unwrap_or_else(|reason| panic!(
        // Reachable only if `Validated::check` has a bug where it
        // accepted an Exp that fails validation on the second pass.
        // sst_exp_to_ast_checked is deterministic, so this is
        // structurally unreachable — but keep the message useful for
        // the impossible case.
        "Validated::lower: invariant violated — {}",
        reason
    ))
}

// The pre-#100 `sst_exp_to_ast` shim was removed by #115. Sites that
// previously used it now go through one of two typed paths:
//
//   * Fallible contexts (return Result) use
//     `lower(Validated::check(e)?)` — the typed pipeline that
//     guarantees lower's input was validated.
//   * Walker / non-fallible contexts use
//     `sst_exp_to_ast_checked(e).expect("<contract>")` with a
//     site-specific message naming why validation should hold (e.g.,
//     "validated upstream by Wp::Let.value", "sub of validated Exp
//     tree"). The runtime behavior is identical to the old shim
//     (single deterministic validation pass + panic on Err); the
//     architectural improvement is that each panic message documents
//     its specific contract rather than a generic "shim hit."

/// `2^n` rendered as a decimal string. Supports 0 ≤ n ≤ 128 — VIR's
/// `U(n)` / `I(n)` only reach that range in practice (u8/u16/u32/u64/u128).
/// We compute it in `u128`; `n = 128` is the boundary, so we fall back to
/// a precomputed constant for that single case.
fn two_pow_str(n: u32) -> String {
    if n < 128 {
        (1u128 << n).to_string()
    } else if n == 128 {
        "340282366920938463463374607431768211456".to_string()
    } else {
        panic!("two_pow_str: bit width {} exceeds the u128 ceiling", n)
    }
}

fn two_pow_lit(n: u32) -> LExpr { LExpr::lit_int(two_pow_str(n)) }

/// If `e` is a constant non-negative integer that fits in `u32`, return
/// its value. Used to read the bit-width argument of `IntegerTypeBound`
/// from an SST `Exp`.
fn const_u32_from_sst(e: &Exp) -> Option<u32> {
    match &e.x {
        ExpX::Const(Constant::Int(n)) => n.to_string().parse().ok(),
        _ => None,
    }
}

/// VIR-AST counterpart of `const_u32_from_sst`.
fn const_u32_from_vir(e: &Expr) -> Option<u32> {
    match &e.x {
        ExprX::Const(Constant::Int(n)) => n.to_string().parse().ok(),
        _ => None,
    }
}

/// Shared helper: lower `IntegerTypeBound(kind, _) applied to <bit width>`.
/// Both the SST and VIR-AST paths end up here once they've extracted
/// `bits`. `ArchWordBits` is handled specially — it's a reference to
/// the prelude axiom rather than a computed literal.
pub fn integer_type_bound_node(kind: &IntegerTypeBoundKind, bits: u32) -> ExprNode {
    match kind {
        IntegerTypeBoundKind::ArchWordBits => {
            // `arch_word_bits : Nat` from TactusPrelude — an opaque axiom
            // whose value comes from the build target. Downstream tactics
            // only know `arch_word_bits = 32 ∨ arch_word_bits = 64`; that
            // disjunction is available as the `arch_word_bits_valid`
            // axiom if a proof needs to case-split.
            LExpr::var_lit("arch_word_bits").node
        }
        _ => integer_type_bound_lit(kind.clone(), bits).node,
    }
}

/// Entry point for the VIR-AST rendering path (`to_lean_expr.rs`).
pub fn integer_type_bound_from_vir(
    kind: &IntegerTypeBoundKind,
    inner: &Expr,
) -> LExpr {
    if matches!(kind, IntegerTypeBoundKind::ArchWordBits) {
        // Fall through to the shared helper's panic so the message
        // matches regardless of which pipeline tripped it.
        return LExpr::new(integer_type_bound_node(kind, 0));
    }
    let bits = const_u32_from_vir(inner).unwrap_or_else(|| panic!(
        "IntegerTypeBound({:?}): non-constant bit width is not supported \
         (VIR-AST inner = {:?})",
        kind, inner.x,
    ));
    LExpr::new(integer_type_bound_node(kind, bits))
}

/// The literal value of `IntegerTypeBound(kind, _)` at the given bit width.
///
/// Mirrors the AIR encoding in `sst_to_air::exp_to_expr`:
///   * `UnsignedMax` → `2^bits - 1`
///   * `SignedMin`   → `-2^(bits-1)`
///   * `SignedMax`   → `2^(bits-1) - 1`
///
/// `ArchWordBits` is handled by the caller (it needs prelude plumbing).
fn integer_type_bound_lit(kind: IntegerTypeBoundKind, bits: u32) -> LExpr {
    let s = match kind {
        IntegerTypeBoundKind::UnsignedMax => {
            // 2^bits - 1. At bits == 128 we hit u128::MAX; shift-by-128
            // is UB so branch around it.
            if bits == 128 {
                "340282366920938463463374607431768211455".to_string()
            } else if bits == 0 {
                "0".to_string()
            } else {
                ((1u128 << bits) - 1).to_string()
            }
        }
        IntegerTypeBoundKind::SignedMin => {
            assert!(bits >= 1, "SignedMin on 0-bit int");
            format!("-{}", two_pow_str(bits - 1))
        }
        IntegerTypeBoundKind::SignedMax => {
            assert!(bits >= 1, "SignedMax on 0-bit int");
            ((1u128 << (bits - 1)) - 1).to_string()
        }
        IntegerTypeBoundKind::ArchWordBits => unreachable!(
            "integer_type_bound_lit: ArchWordBits should be handled at the call site"
        ),
    };
    LExpr::lit_int(s)
}

thread_local! {
    /// Per-render map of single-variant struct datatypes → their fields'
    /// `(lean accessor, typ)`. Lets `type_bound_predicate` recurse into a
    /// datatype param's fixed-width fields and materialize their bounds
    /// (`0 ≤ h.v < 256`) — the same `0 ≤ x < 256` a `u8` *param* already
    /// gets, but for a `u8` *field* of a struct param. Built once from the
    /// krate (`generate::install_datatype_field_bounds`), where the
    /// `DatatypeX` field list is in scope. Enums (multi-variant) are
    /// omitted — their field bounds are variant-conditional, deferred.
    static DATATYPE_FIELDS: std::cell::RefCell<std::collections::HashMap<vir::ast::Path, Vec<(String, Typ)>>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
}

/// Install the datatype-field-bounds table (see `DATATYPE_FIELDS`).
pub(crate) fn set_datatype_fields(map: std::collections::HashMap<vir::ast::Path, Vec<(String, Typ)>>) {
    DATATYPE_FIELDS.with(|m| *m.borrow_mut() = map);
}

/// Build the Lean predicate expressing the type invariant on `e : ty`
/// (i.e., the refinement bounds Verus treats as `HasType(e, ty)`).
///
/// Returns `None` when the target type carries no additional constraint:
///   * `Nat`, `Int` — unbounded
///   * non-integer types — structural, no refinement
///
/// Returns `Some(pred)` otherwise.
///
/// For `U(n)` (rendered as `Int`): `0 ≤ e ∧ e < 2^n`. Rendering u-types
/// as `Int` rather than `Nat` is what makes subtraction underflow
/// catchable — Lean's `Nat` silently truncates negatives, but `Int`
/// gives the true mathematical value so this refinement check can fire.
///
/// For `I(n)` (rendered as `Int`): `-2^(n-1) ≤ e ∧ e < 2^(n-1)`.
///
/// For `USize` (rendered as `Int`): `0 ≤ e ∧ e < usize_hi`, where
/// `usize_hi = 2^arch_word_bits` is a prelude-defined constant. For
/// `ISize`: `-isize_hi ≤ e ∧ e < isize_hi`, same idea. `tactus_auto`
/// generally can't discharge these symbolically (omega doesn't reason
/// about `2^n` for unknown `n`) — proofs often need an explicit
/// `cases arch_word_bits_valid` step. Emitting them anyway is the
/// soundness-preserving choice.
///
/// For `Char` (rendered as `Nat`): `e < 0x110000`. The `0 ≤` half comes
/// for free from `Nat`.
///
/// For a single-variant **struct** datatype (or a tuple): recurse into the
/// fields, conjoining each fixed-width field's bound — so a `Holder { v: u8
/// }` param carries `0 ≤ h.v < 256`. Multi-variant enums and self-recursive
/// fields contribute nothing (see `type_bound_predicate_rec`).
pub fn type_bound_predicate(e: &LExpr, ty: &Typ) -> Option<LExpr> {
    type_bound_predicate_rec(e, ty, &mut std::collections::HashSet::new())
}

/// Inner recursion for `type_bound_predicate`. `visited` guards against
/// infinite recursion on recursive datatypes (`List { next: Box<List> }`):
/// a self-referential field simply contributes no bound rather than looping.
fn type_bound_predicate_rec(
    e: &LExpr,
    ty: &Typ,
    visited: &mut std::collections::HashSet<vir::ast::Path>,
) -> Option<LExpr> {
    // Transparent: unbox before examining.
    if let TypX::Boxed(inner) = &**ty {
        return type_bound_predicate_rec(e, inner, visited);
    }
    // `&mut T` params (in new-mut-ref mode after migration) carry
    // `TypX::MutRef(T)`; the binder type renders as `T` (see
    // `to_lean_type::typ_to_node`'s `MutRef` arm) and `build_param_binders`
    // already deref'd `e` to the inner value, so the bound is for `T`. (#95)
    if let TypX::MutRef(inner) = &**ty {
        return type_bound_predicate_rec(e, inner, visited);
    }
    // Datatype params: recurse into fields so a struct's fixed-width fields
    // carry their bounds (`0 ≤ h.v < 256`), just like numeric params do.
    if let TypX::Datatype(dt, typ_args, _) = &**ty {
        return match dt {
            // Tuple: field typs are the typ_args; project via `.N` accessor.
            vir::ast::Dt::Tuple(n) => (0..*n)
                .filter_map(|i| {
                    let elem = LExpr::field_proj(
                        e.clone(), crate::expr_shared::tuple_field_accessor(*n, i));
                    type_bound_predicate_rec(&elem, typ_args.get(i)?, visited)
                })
                .reduce(|a, b| LExpr::and(a, b)),
            // Single-variant struct: look the fields up in the table.
            vir::ast::Dt::Path(path) => {
                if visited.contains(path) { return None; }
                let fields = DATATYPE_FIELDS.with(|m| m.borrow().get(path).cloned())?;
                visited.insert(path.clone());
                let result = fields.iter()
                    .filter_map(|(accessor, ftyp)| {
                        let fe = LExpr::field_proj(e.clone(), accessor.clone());
                        type_bound_predicate_rec(&fe, ftyp, visited)
                    })
                    .reduce(|a, b| LExpr::and(a, b));
                visited.remove(path);
                result
            }
        };
    }
    let range = match &**ty {
        TypX::Int(r) => r,
        _ => return None,
    };
    // Two shapes, parameterized only by the upper bound `hi`:
    // unsigned `0 ≤ e < hi` (U/USize) and signed `-hi ≤ e < hi` (I/ISize).
    let unsigned = |hi: LExpr| {
        Some(LExpr::and(
            LExpr::le(LExpr::lit_int("0"), e.clone()),
            LExpr::lt(e.clone(), hi),
        ))
    };
    let signed = |hi: LExpr| {
        Some(LExpr::and(
            LExpr::le(LExpr::neg(hi.clone()), e.clone()),
            LExpr::lt(e.clone(), hi),
        ))
    };
    match range {
        IntRange::U(n) => unsigned(two_pow_lit(*n)),
        IntRange::USize => unsigned(LExpr::var_lit("usize_hi")),
        IntRange::I(n) => signed(two_pow_lit(*n - 1)),
        IntRange::ISize => signed(LExpr::var_lit("isize_hi")),
        // Unicode scalar range: 0 ≤ c ≤ U+10FFFF. `c < 0x110000` covers
        // the upper half; `0 ≤` is free from `Nat`. (Surrogates
        // U+D800..U+DFFF are technically excluded from Unicode scalar
        // values, but Verus and Rust's `char` don't track that, and
        // omega's simpler with a single upper-bound literal.)
        IntRange::Char => Some(LExpr::lt(e.clone(), LExpr::lit_int("0x110000"))),
        IntRange::Nat | IntRange::Int => None,
    }
}

// `renders_as_lean_int` moved to `expr_shared` (P0,
// DESIGN-typed-renderer.md § D1) — it now also feeds `coerce_lexpr`'s
// numeric-sort reconciliation, so the shared-rules file is its home.
// `clip_to_node_checked` retired (P1): the Clip arm of `exp_to_typed`
// is exactly "coerce the value to the clipped range" via the unified
// `coerce_lexpr` — same Int.toNat/Int.ofNat table (which guards the
// `x as int - y as int` underflow soundness hole; see coerce_lexpr's
// doc), but keyed on the value's ACTUAL typ instead of the claimed
// `inner.typ`.

/// Render a `CheckDecreaseHeight` arg with Verus's param-substitution
/// `Bind(Let)` wrapper zeta-reduced.
///
/// ## Shape assumption (Verus invariant)
///
/// `vir::recursion::check_decrease_call` encodes parameter
/// substitution as a `Bind(Let(params → args, decrease_expr))`
/// wrapping the decrease. Additionally, `poly::coerce_exp_to_poly`
/// may wrap the whole thing in `UnaryOpr::Box` / `UnaryOpr::Unbox`,
/// and upstream mode-coercion / trigger markers may wrap it in
/// `Unary::CoerceMode` / `Unary::Trigger`. We peel those via
/// [`crate::sst_to_lean::peel_transparent`] to reach the Bind(Let),
/// then substitute at the Lean AST level via `lean_ast::substitute`.
///
/// **Why substitute instead of letting the default `Bind(Let)`
/// renderer emit `let name := value; body`?** On self-recursion the
/// callee's param names match the caller's, so the emitted let would
/// shadow — `let n := n - 1; ...; n < old_n` — and omega can't
/// zeta-reduce through the shadow. Direct substitution removes the
/// shadow entirely and leaves omega-friendly arithmetic.
///
/// If Verus ever changes `check_decrease_call` to encode
/// substitution differently (e.g., not via Bind(Let)), this peel
/// falls through to `sst_exp_to_ast_checked` which renders the let
/// as-is — producing the shadowed form and breaking recursive
/// `tactus_auto` goals. That would be a caught regression (the
/// `test_exec_call_recursive_*` suite exercises this path).
fn render_checked_decrease_arg(e: &Exp, ctx: &crate::expr_shared::RenderCtx) -> Result<LExpr, String> {
    use crate::sst_to_lean::peel_transparent;
    let peeled = peel_transparent(e);
    match &peeled.x {
        ExpX::Bind(bnd, body) => match &bnd.x {
            BndX::Let(binders) => {
                let mut subst: std::collections::HashMap<crate::lean_name::LeanName, LExpr> =
                    std::collections::HashMap::new();
                for b in binders.iter() {
                    subst.insert(
                        crate::lean_name::LeanName::from_var_ident(&b.name),
                        sst_exp_to_ast_checked_with_ctx(&b.a, ctx)?,
                    );
                }
                let body_rendered = render_checked_decrease_arg(body, ctx)?;
                Ok(substitute(&body_rendered, &subst))
            }
            _ => sst_exp_to_ast_checked_with_ctx(e, ctx),
        },
        _ => sst_exp_to_ast_checked_with_ctx(e, ctx),
    }
}

/// Lean-level wrapper depth (`Tactus.Ref`/`Box`/`Rc`/`Arc`/`MutRef`
/// count) of `inner` at a projection site, used to decide how many
/// `.deref`s precede a Field / IsVariant access. Binder-aware analog of
/// the Exp path's `lean_level_wrap_count`: when `inner` is a fn-param
/// Var, the depth comes from the param's **declared Lean typ**
/// (`ctx.binder_typs`, seeded from `WpCtx::caller_param_typs`), which
/// preserves the `&self` → `&Bar` wrapper that Verus strips from the SST
/// expression's spanned typ. For non-var bases — or when no binder map
/// is in scope (requires rendering, which unwraps via `let x := x.deref`
/// shadows instead) — it falls back to the spanned typ, identical to the
/// prior behaviour.
/// Extra `.deref`s a TUPLE-slot projection needs to land at its CLAIMED
/// typ. Tuple typ args keep their ref decorations (`(&Sym, &Sym)` =
/// `Tuple[Ref(Sym), Ref(Sym)]`) while the SST strips them from the
/// projection's claimed result typ — see the `Field` arm's comment
/// (cluster bug 5). Returns `slot_depth − claimed_depth`, saturating
/// (a claimed typ DEEPER than its slot has not been observed; it would
/// need a `.mk` wrap, not a deref — if it ever appears, the sanity
/// check / Lean elaboration fails loud, not silent). Returns 0 for
/// non-tuple datatypes and any unexpected shape.
/// The typ of tuple slot `field_opr.field` in `base_typ`'s tuple typ
/// args, peeling boxing/decorations to reach the tuple datatype. `None`
/// for non-tuple bases/fields.
///
/// P1 successor of `tuple_slot_extra_derefs` (cluster bug 5): tuple
/// slots KEEP their ref decorations in the tuple's typ args
/// (`(&Sym, &Sym)` is `Tuple[Ref(Sym), Ref(Sym)]`) while the SST
/// STRIPS them from the projection's claimed result typ. Instead of
/// computing a repair deref count against the claimed typ, the typed
/// spine reports the SLOT typ as the projection's ACTUAL typ and lets
/// the composition boundary bridge.
fn tuple_slot_typ(base_typ: &Typ, field_opr: &FieldOpr) -> Option<Typ> {
    if !matches!(field_opr.datatype, Dt::Tuple(_)) {
        return None;
    }
    let idx = field_opr.field.as_str().parse::<usize>().ok()?;
    let mut t = &**base_typ;
    loop {
        match t {
            TypX::Decorate(_, _, inner) | TypX::Boxed(inner) => t = &**inner,
            _ => break,
        }
    }
    let TypX::Datatype(Dt::Tuple(_), args, _) = t else { return None };
    args.get(idx).cloned()
}

/// Will `exp_to_typed(e)`'s actual typ come from a TRUSTED source —
/// one that describes the rendered Lean value definitionally — rather
/// than from the claimed-typ default? Trusted sources: a binder lookup
/// (the Lean binder's declared type IS the value's type), a render-time
/// substitution (bridged to claimed by construction), the tuple-slot
/// rule (the projection's Lean type is the slot's type), and Clip (the
/// arm coerces to its range definitionally). Claimed typs at arbitrary
/// nodes are NOT trusted — VIR's poly-boxing lies at some Var uses
/// (see the Box/Unbox arm of `exp_to_typed`). Mirrors `exp_to_typed`'s
/// arm structure; keep the two in sync.
fn actual_is_trusted(e: &Exp, ctx: &crate::expr_shared::RenderCtx) -> bool {
    match &e.x {
        ExpX::Var(v) | ExpX::VarLoc(v) | ExpX::VarAt(v, _) => {
            ctx.binder_typs.is_some_and(|b| b.contains_key(v))
                || ctx
                    .lookup_subst(&crate::lean_name::LeanName::from_var_ident(v), &e.typ)
                    .is_some()
        }
        ExpX::Unary(UnaryOp::CoerceMode { .. }, inner)
        | ExpX::Unary(UnaryOp::Trigger(_), inner)
        | ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner)
        | ExpX::WithTriggers(_, inner)
        | ExpX::Loc(inner) => actual_is_trusted(inner, ctx),
        // Tuple projections report the slot typ (truthful); non-tuple
        // Field actuals are the claimed typ (not trusted, but the
        // reset is an identity there anyway).
        ExpX::UnaryOpr(UnaryOpr::Field(fo), _) => matches!(fo.datatype, Dt::Tuple(_)),
        ExpX::Unary(UnaryOp::Clip { .. }, _) => true,
        _ => false,
    }
}

/// Typed rendering spine (P1, DESIGN-typed-renderer.md). Returns the
/// rendered expression TOGETHER with its actual Lean-level typ — which
/// for migrated arms may legitimately differ from the node's claimed
/// SST typ (`e.typ`). The public entry bridges back to the claimed typ
/// at the boundary via `into_slot`, so external consumers keep the
/// "rendered == claimed" contract while internal composition uses
/// actual typs. Unmigrated arms render through `exp_to_node_checked`
/// at the claimed typ — bit-for-bit today's behavior (the boundary
/// bridge is passthrough when actual == claimed).
///
/// Migrated so far (each replaced a per-site repair helper):
/// * Var family — actual typ is the BINDER's declared typ where
///   binder-backed; replaces `sst_lean_wrap_count`'s re-derivation
///   through transparent wrappers (the typed value carries its truth
///   through them).
/// * Transparent wrappers (CoerceMode/Trigger/WithTriggers/Loc) —
///   actual typ flows through. Box/Unbox flow the child's actual only
///   when binder-backed (see the arm — VIR poly-boxing claims lie at
///   some Var uses).
/// * Clip — exactly "coerce the value to the clipped range" via the
///   unified `coerce_lexpr`; replaces `clip_to_node_checked`.
/// * Field/IsVariant — deref count from the base's ACTUAL typ; tuple
///   projections report the slot typ as actual (replaces
///   `tuple_slot_extra_derefs`).
fn exp_to_typed(
    e: &Exp,
    ctx: &crate::expr_shared::RenderCtx,
) -> Result<crate::typed_expr::TypedExpr, String> {
    use crate::typed_expr::TypedExpr;
    Ok(match &e.x {
        ExpX::Var(ident) | ExpX::VarLoc(ident) | ExpX::VarAt(ident, _) => {
            // Render-time substitution: if ctx has a value_subst map
            // and `ident` is in it, `lookup_subst` returns the value
            // already bridged to `e.typ` (the slot's claimed typ) —
            // actual == claimed by construction.
            let lean_name = crate::lean_name::LeanName::from_var_ident(ident);
            if let Some(bridged) = ctx.lookup_subst(&lean_name, &e.typ) {
                return Ok(TypedExpr::from_untyped(bridged, e.typ.clone()));
            }
            // Plain var: the rendered Lean value is the binder itself,
            // so the actual typ is the binder's DECLARED typ (the SST
            // may wrap the read in transparent Unbox/CoerceMode that
            // shift the claimed typ; the render doesn't).
            let actual = ctx
                .binder_typs
                .and_then(|b| b.get(ident))
                .cloned()
                .unwrap_or_else(|| e.typ.clone());
            TypedExpr::var(lean_name, actual)
        }
        // Transparent wrappers that DON'T shift the typ (mode/trigger
        // markers): no Lean code — the value's actual typ flows
        // through unchanged.
        ExpX::Unary(UnaryOp::CoerceMode { .. }, inner)
        | ExpX::Unary(UnaryOp::Trigger(_), inner)
        | ExpX::WithTriggers(_, inner)
        | ExpX::Loc(inner) => exp_to_typed(inner, ctx)?,
        // Box/Unbox: transparent in Lean but typ-SHIFTING in VIR — and
        // VIR's poly-boxing can claim wrapper-decorated typs at Var
        // uses whose bound value is actually bare (Box::new's ctor
        // lowering produces `Unbox(tmp : Box<u8>) : u8` where the WP
        // bound `tmp` to the bare inner value — the
        // wrapper-instantiation probe). The old renderer's claimed-typ
        // contract silently canceled that lie; propagating the child's
        // actual typ would ACT on it (spurious `.deref`). Rule
        // (matching `sst_lean_wrap_count`'s old semantics exactly):
        // propagate the child's actual only when it's BINDER-backed
        // (params — trustworthy); otherwise reset to the claimed
        // contract. A trustworthy let-binder typ environment (P2)
        // lifts this.
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner) => {
            let child = exp_to_typed(inner, ctx)?;
            if actual_is_trusted(inner, ctx) {
                child
            } else {
                TypedExpr::from_untyped(child.into_untyped(), e.typ.clone())
            }
        }
        // Clip is exactly "coerce the value to the clipped range":
        // wrapper peel + Int.toNat/Int.ofNat sort bridge, both via the
        // unified coerce_lexpr. Verus's Clip is value-preserving *if*
        // the source fits in dst — overflow is guarded by a
        // neighbouring HasType assertion, so our job is just keeping
        // Lean's types aligned.
        ExpX::Unary(UnaryOp::Clip { range, .. }, inner) => {
            let dst: Typ = std::sync::Arc::new(TypX::Int(*range));
            exp_to_typed(inner, ctx)?.coerce_to(&dst)
        }
        // Field projection: `x.name` / `x.0` / `x.val0`. Shared
        // `field_access_name` with the VIR-AST path. The field belongs
        // to the inner inductive — peel ALL rendered wrappers of the
        // base's ACTUAL typ (β refactor Piece 2, now actual-typ-driven).
        ExpX::UnaryOpr(UnaryOpr::Field(field_opr), inner) => {
            let base = exp_to_typed(inner, ctx)?;
            let n = count_ref_decorations(base.typ());
            let actual =
                tuple_slot_typ(base.typ(), field_opr).unwrap_or_else(|| e.typ.clone());
            let projected =
                field_proj_opr(apply_deref_chain(base.into_untyped(), n), field_opr);
            TypedExpr::from_untyped(projected, actual)
        }
        // `IsVariant` from match-desugared patterns. A tuple has
        // exactly one "variant" — its test is vacuously true (the
        // general path would emit `.istuple%2`, a field that exists on
        // no Lean type — cluster bug 6).
        ExpX::UnaryOpr(UnaryOpr::IsVariant { datatype, variant }, inner) => {
            if matches!(datatype, Dt::Tuple(_)) {
                return Ok(TypedExpr::from_untyped(
                    LExpr::new(ExprNode::LitBool(true)),
                    e.typ.clone(),
                ));
            }
            let base = exp_to_typed(inner, ctx)?;
            let n = count_ref_decorations(base.typ());
            let node = is_variant_node(variant, apply_deref_chain(base.into_untyped(), n));
            TypedExpr::from_untyped(LExpr::new(node), e.typ.clone())
        }
        // Default: unmigrated arms render at the claimed typ.
        _ => TypedExpr::from_untyped(LExpr::new(exp_to_node_checked(e, ctx)?), e.typ.clone()),
    })
}

/// Render a trait/class-method call as `Trait.method (arg : Self_typ)` so
/// Lean infers the instance from the typed value arg — NOT by passing the
/// `Self` type as a positional argument (the class projection's `Self` is
/// implicit, so `Foo.predicate Bar self` mis-elaborates: `Bar` lands in
/// the `Tactus.Ref Self` slot).
///
/// Shared by the resolved arm (`Fun(_, Some(_))` = DynamicResolved) and
/// the unresolved arm (`Fun(_, None)` / `Recursive`) when the callee is a
/// trait method. The latter is the abstract `<Self as Tr>::m` reference
/// Verus emits in an *inherited* trait ensures, where `Self` is a
/// type-param instantiated at the call site; before this was shared, that
/// path passed `typs` positionally and produced the malformed
/// `Foo.predicate Bar self`. Routing both through here renders
/// `Foo.predicate (self : Tactus.Ref Bar)` uniformly.
fn render_class_method_call(
    fun: &vir::ast::Fun,
    typs: &[Typ],
    args: &[Exp],
    e_typ: &Typ,
    ctx: &crate::expr_shared::RenderCtx,
) -> Result<ExprNode, String> {
    let head = LExpr::var(crate::lean_name::LeanName::from_path(&fun.path));
    // Look up the trait method decl's declared param typs (instantiated by
    // the call's typ_args) so each arg coerces to the wrapper-typed
    // receiver the class signature expects.
    let expected_typs = ctx.fn_param_typs(fun, typs);
    let app_args: Result<Vec<LExpr>, String> = args.iter().enumerate().map(|(i, a)| {
        // Typed spine (P1): bridge from the arg's ACTUAL rendered typ
        // to the declared param typ, not from the claimed `a.typ`.
        let arg_typed = exp_to_typed(a, ctx)?;
        let arg_coerced = match &expected_typs {
            Some(ts) if i < ts.len() => arg_typed.into_slot(&ts[i]),
            _ => arg_typed.into_slot(&a.typ),
        };
        // TypeAnnot serves Self / type-param inference at the elaborator.
        // Annotate with the expected param typ (the wrapper-typed form),
        // unless it still mentions a type-param (then the annotation would
        // be circular — leave it for unification).
        let annot_typ = match &expected_typs {
            Some(ts) if i < ts.len() => ts[i].clone(),
            _ => a.typ.clone(),
        };
        if crate::to_lean_expr::typ_contains_param(&annot_typ) {
            Ok(arg_coerced)
        } else {
            Ok(LExpr::type_annot(arg_coerced, typ_to_expr(&annot_typ)))
        }
    }).collect();
    let app = if args.is_empty() { head } else { LExpr::app(head, app_args?) };
    if crate::to_lean_expr::typ_contains_param(e_typ) {
        Ok(app.node)
    } else {
        Ok(ExprNode::TypeAnnot { expr: Box::new(app), ty: Box::new(typ_to_expr(e_typ)) })
    }
}

/// Is `fun` a trait method (decl or impl)? Consulted by the unresolved
/// call arm to route abstract `<Self as Tr>::m` references through class
/// dispatch instead of positional type-args. Looks the fn up in the
/// RenderCtx's fn_map; returns false for cross-crate callees absent from
/// the map (they fall back to the prior rendering — unchanged behaviour).
fn fun_is_trait_method(fun: &vir::ast::Fun, ctx: &crate::expr_shared::RenderCtx) -> bool {
    ctx.fn_map
        .and_then(|m| m.get(fun))
        .map(|f| matches!(
            &f.kind,
            vir::ast::FunctionKind::TraitMethodDecl { .. }
                | vir::ast::FunctionKind::TraitMethodImpl { .. }
        ))
        .unwrap_or(false)
}

fn exp_to_node_checked(e: &Exp, ctx: &crate::expr_shared::RenderCtx) -> Result<ExprNode, String> {
    Ok(match &e.x {
        ExpX::Const(c) => const_to_node_checked(c)?,
        // Migrated to the typed spine (P1) — delegation keeps this
        // match total and direct callers safe; `exp_to_typed` handles
        // these patterns specifically (no bounce-back cycle).
        ExpX::Var(..) | ExpX::VarLoc(..) | ExpX::VarAt(..) => {
            return Ok(exp_to_typed(e, ctx)?.into_slot(&e.typ).node);
        }
        ExpX::StaticVar(fun) | ExpX::ExecFnByName(fun) => {
            ExprNode::Var(crate::lean_name::LeanName::from_path(&fun.path))
        }

        ExpX::Unary(UnaryOp::Not, inner) => LExpr::not(sst_exp_to_ast_checked_with_ctx(inner, ctx)?).node,
        // Migrated to the typed spine (P1).
        ExpX::Unary(UnaryOp::Clip { .. }, _)
        | ExpX::Unary(UnaryOp::CoerceMode { .. }, _)
        | ExpX::Unary(UnaryOp::Trigger(_), _) => {
            return Ok(exp_to_typed(e, ctx)?.into_slot(&e.typ).node);
        }
        ExpX::Unary(op, _) => {
            // The exec-fn SST path is conservative — we accept Not /
            // Clip / CoerceMode / Trigger directly above, and reject
            // the rest. Common surface forms reaching here:
            // * `BitNot(_)` — `!x` on int types (`!0u8`, `!x` for
            //   signed types). The proof-fn / spec-fn path handles
            //   it; lifting to exec-fn requires extending
            //   `to_lean_sst_expr` to mirror `to_lean_expr`.
            // * `IntToReal` / `RealToInt` / `FloatToBits` /
            //   `IeeeFloat` — float ops; Verus rejects floats
            //   upstream so these are only reachable in spec.
            // * `MutRefCurrent` / `MutRefFuture` — new-mut-ref mode
            //   (#95 follow-up to #55).
            return Err(format!(
                "unsupported unary op `{:?}` in exec-fn body — the SST renderer \
                 accepts only Not / Clip / CoerceMode / Trigger today. See \
                 DESIGN.md \"Expression-level forms rejected by \
                 sst_exp_to_ast_checked\" for the catalogue.",
                op
            ));
        }

        // Box/Unbox, Field, IsVariant: migrated to the typed spine (P1)
        // — the base's deref count comes from its ACTUAL typ, and tuple
        // projections report the slot typ as actual (cluster bugs 5/6
        // rules live in `exp_to_typed`).
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), _)
        | ExpX::UnaryOpr(UnaryOpr::Field(_), _)
        | ExpX::UnaryOpr(UnaryOpr::IsVariant { .. }, _) => {
            return Ok(exp_to_typed(e, ctx)?.into_slot(&e.typ).node);
        }
        // `HasType(e, t)` — the refinement constraint for `e` to inhabit
        // `t`. For fixed-width ints (u8, i32, …) this is the bounds check
        // Verus emits at every arithmetic site. For unbounded types (Nat,
        // Int, structs) it's vacuous; we emit `True` and let Lean simplify.
        ExpX::UnaryOpr(UnaryOpr::HasType(t), inner) => {
            let e_ast = sst_exp_to_ast_checked_with_ctx(inner, ctx)?;
            match type_bound_predicate(&e_ast, t) {
                Some(pred) => pred.node,
                None => ExprNode::LitBool(true),
            }
        }
        // `IntegerTypeBound(kind, _)` returns the numeric bound of a
        // fixed-width int type. The inner expression is the bit width
        // (a literal like 8, 32, …) — we evaluate at codegen time and
        // emit the decimal literal directly.
        ExpX::UnaryOpr(UnaryOpr::IntegerTypeBound(kind, _), inner) => {
            if matches!(kind, IntegerTypeBoundKind::ArchWordBits) {
                return Ok(integer_type_bound_node(kind, 0));
            }
            let bits = const_u32_from_sst(inner).ok_or_else(|| format!(
                "IntegerTypeBound({:?}): non-constant bit width is not supported \
                 (SST inner = {:?})",
                kind, inner.x,
            ))?;
            integer_type_bound_node(kind, bits)
        }
        ExpX::UnaryOpr(_, inner) => exp_to_node_checked(inner, ctx)?,

        ExpX::Binary(op, lhs, rhs) => {
            // HeightCompare: `is_smaller_than(lhs, rhs)` for decreases-
            // related ordering. `strictly_lt` distinguishes `<` from
            // `==`. Lower based on operand height type:
            //   * Int height (lhs.typ peels to TypX::Int) → emit
            //     direct `lhs < rhs` / `lhs = rhs`. The "height" of an
            //     int IS the int (per `vir::recursion::height_is_int`).
            //   * Same datatype on both sides → emit `T.height lhs <
            //     T.height rhs` (or `=`). The companion `T.height` fn
            //     is emitted by `to_lean_fn::height_fn_for_datatype`.
            //   * Otherwise → reject (mixed types, generics, etc.).
            if let BinaryOp::HeightCompare { strictly_lt, .. } = op {
                let l_int = is_int_height(&lhs.typ);
                let r_int = is_int_height(&rhs.typ);
                let l_dt = decrease_height_datatype(&lhs.typ);
                let r_dt = decrease_height_datatype(&rhs.typ);
                let (l, r) = (sst_exp_to_ast_checked_with_ctx(lhs, ctx)?, sst_exp_to_ast_checked_with_ctx(rhs, ctx)?);
                let (l_h, r_h) = if l_int && r_int {
                    (l, r)
                } else if let (Some(lp), Some(rp)) = (l_dt, r_dt) {
                    if lp != rp {
                        return Err(format!(
                            "HeightCompare across different datatypes ({:?} vs {:?}) \
                             not supported",
                            lp, rp,
                        ));
                    }
                    let head = format!("{}.height", lean_name(lp));
                    let lh = LExpr::app(LExpr::var_synthetic(head.clone()), vec![l]);
                    let rh = LExpr::app(LExpr::var_synthetic(head), vec![r]);
                    (lh, rh)
                } else {
                    return Err(format!(
                        "HeightCompare on non-int / non-concrete-datatype types \
                         (lhs: {:?}, rhs: {:?}) is not yet supported",
                        lhs.typ, rhs.typ,
                    ));
                };
                let cmp = if *strictly_lt {
                    LExpr::lt(l_h, r_h)
                } else {
                    LExpr::eq(l_h, r_h)
                };
                return Ok(cmp.node);
            }
            match op {
                BinaryOp::Index(_kind, _bounds) => {
                    // `a[i]` in exec fns. The SST guarantees
                    // `BoundsCheck::Allow` (the bounds obligation is
                    // discharged separately by Verus's mode pass), so we
                    // don't emit a precondition theorem here — we just
                    // render the indexing operation.
                    //
                    // Lean's `xs[i]!` notation handles both `Array α`
                    // (Verus arrays — `[T; N]`) and `List α` (Verus
                    // slices — `&[T]`) via the `GetElem` typeclass with
                    // `getElem!` — total in the type system, panics
                    // out-of-bounds. The panic is observationally fine:
                    // Tactus only verifies the goal, never executes the
                    // generated Lean. Out-of-bounds is unspecified, which
                    // matches Verus's "spec is total but unspecified
                    // out-of-bounds" model. Requires `[Inhabited α]`,
                    // which holds for primitives and for non-generic
                    // user datatypes (we already emit `deriving Inhabited`
                    // — see DESIGN.md "Non-int decreases").
                    //
                    // The index in `array_index(a, i)` is Verus's `int`
                    // (lowers to Lean `Int`), but `getElem!` wants `Nat`.
                    // Coerce via `Int.toNat`. For an `Int` index that's
                    // already non-negative (always true under
                    // `BoundsCheck::Allow`), `Int.toNat` is identity.
                    let (l, r) = (sst_exp_to_ast_checked_with_ctx(lhs, ctx)?, sst_exp_to_ast_checked_with_ctx(rhs, ctx)?);
                    let r_nat = LExpr::app(LExpr::var_lit("Int.toNat"), vec![r]);
                    return Ok(ExprNode::Index {
                        base: Box::new(l),
                        idx: Box::new(r_nat),
                        bang: true,
                    });
                }
                BinaryOp::IeeeFloat(_) => {
                    return Err(
                        "IEEE float comparison not yet supported (Verus rejects \
                         f32/f64 upstream; this path exists for completeness)".to_string()
                    );
                }
                _ => {}
            }
            // Fold `e ∧ true` / `true ∧ e` → `e`. `ast_simplify`'s
            // match desugaring (`pattern_to_exprs_rec` on Wildcard)
            // emits `Const(Bool(true))` as the per-arm "always true"
            // base case and chains it with pattern tests via
            // `BinaryOp::And`. The raw form produces `x.isFoo ∧ True`
            // in the generated Lean — which type-checks but also
            // requires `[Decidable …]` synthesis on the combined
            // proposition for the surrounding `if`. Folding at the
            // emission layer sidesteps both: we emit just `x.isFoo`,
            // which is directly decidable.
            if matches!(op, BinaryOp::And) {
                if let ExpX::Const(Constant::Bool(true)) = &rhs.x {
                    return exp_to_node_checked(lhs, ctx);
                }
                if let ExpX::Const(Constant::Bool(true)) = &lhs.x {
                    return exp_to_node_checked(rhs, ctx);
                }
            }
            let (l, r) = (sst_exp_to_ast_checked_with_ctx(lhs, ctx)?, sst_exp_to_ast_checked_with_ctx(rhs, ctx)?);
            match binop_to_ast(op) {
                // Structural binops (==, +, *, ≤, ...) — reconcile the
                // two operands to a common wrapper depth before applying
                // the op. Verus keeps `*p` (for a `&T` param) at the
                // reference typ `&T` with the deref implicit, so the SST
                // can hand us mismatched depths — e.g. `p : &u8` (depth
                // 1) `≤` `100 : u8` (depth 0). Without reconciliation
                // that renders `p ≤ 100`, comparing `Tactus.Ref Int` to
                // `Int` (a Lean type error).
                //
                // Peel the DEEPER operand(s) down to the shallower
                // (min-depth): equal-depth operands — the common case,
                // e.g. `s1 == s2` for two `&T` params, or `r == b` after
                // a `let r := b` — are untouched (min == both depths →
                // zero peels), so this is a strict refinement of the
                // previous "never peel structural operands" rule
                // (commit `d9476e6`). The asymmetry that `d9476e6`
                // worried about — body renders `let r := b` uncoerced
                // while ensures peels — is closed by the paired
                // return-expr coercion in `build_wp`'s `StmX::Return`
                // arm (both sides now meet at the declared ret typ).
                // Pinned by test_exec_nested_wrapper_probe (still green)
                // and test_exec_call_site_ref_to_bare_probe (flips green);
                // soundness pinned by _ref_to_bare_wrong_post (a false
                // postcondition still fails after reconcile).
                //
                // Depth-only (`apply_deref_chain`), not kind-aware: two
                // operands at the SAME depth but DIFFERENT wrapper kinds
                // (`Ref u8 ≤ Box u8`) wouldn't reconcile (min == both → no
                // peel). That shape doesn't arise from real Rust —
                // structural binops compare like-typed values — so the
                // depth-only form is sufficient; `coerce_lexpr` (kind-aware)
                // would be the generalization if it ever surfaces.
                Some(l_op) => {
                    let dl = count_ref_decorations(&*lhs.typ);
                    let dr = count_ref_decorations(&*rhs.typ);
                    let m = dl.min(dr);
                    let l = apply_deref_chain(l, dl - m);
                    let r = apply_deref_chain(r, dr - m);
                    LExpr::binop(l_op, l, r).node
                }
                // Non-structural: emit as `head lhs rhs` via App.
                // Reachable cases in the exec-fn path:
                // * `Xor` (logical xor on Bool)
                // * `StrGetChar` (Verus's `strslice_get_char`, lowering
                //   to `Tactus.strGetChar` from the prelude)
                // Other non-structural ops (`HeightCompare`, `IeeeFloat`,
                // `Index`) are rejected upstream in this arm or via
                // earlier match guards.
                // Routed through the shared `non_binop_head` table so
                // the head string stays in sync with the VIR-AST
                // renderer.
                //
                // β refactor Piece 3: peel wrapper decorations from each
                // operand for these non-structural binops. The head
                // fns (`Tactus.strGetChar`, `Bool.xor`, etc.) take
                // inner-typed args; an SST operand with wrapper typ
                // needs `.deref` to bridge. Restricted to the
                // non-structural path because structural binops don't
                // have this constraint.
                None => {
                    let l = apply_deref_chain(l, count_ref_decorations(&*lhs.typ));
                    let r = apply_deref_chain(r, count_ref_decorations(&*rhs.typ));
                    LExpr::app(LExpr::var_lit(non_binop_head(op)), vec![l, r]).node
                }
            }
        }
        ExpX::BinaryOpr(BinaryOpr::ExtEq(_, _), lhs, rhs) => {
            LExpr::eq(sst_exp_to_ast_checked_with_ctx(lhs, ctx)?, sst_exp_to_ast_checked_with_ctx(rhs, ctx)?).node
        }

        ExpX::If(cond, then_e, else_e) => ExprNode::If {
            cond: Box::new(sst_exp_to_ast_checked_with_ctx(cond, ctx)?),
            then_: Box::new(sst_exp_to_ast_checked_with_ctx(then_e, ctx)?),
            else_: Some(Box::new(sst_exp_to_ast_checked_with_ctx(else_e, ctx)?)),
        },

        // `CallFun::Fun(decl_fun, Some(_))` is precisely the
        // `DynamicResolved` (trait-method-resolved) case — the
        // `Option<(Fun, Typs)>` second component is set iff the VIR
        // `CallTargetKind` was `DynamicResolved` (see
        // `CallTargetKind::resolved` in `ast_util.rs`). Render these
        // through Lean's class-method dispatch — `Trait.method (arg
        // : Self_typ)` — so Lean infers the instance from the
        // typed value arg, exactly as the proof-fn renderer
        // (`to_lean_expr::expr_to_node`'s `is_class_method` branch)
        // does. The previous pass-through of `typs` as positional
        // arguments produced `View.view Holder z`, which Lean parses
        // as `(View.view Holder) z` and rejects (`View.view Holder
        // : Int`, not a function). Bug D-remaining pin: vstd's
        // `old(vec)@` shape and any trait-method spec ref inside
        // a `&mut` callee's pre/post.
        // Trait-method-resolved call (`Some(_)` = DynamicResolved). Render
        // via class dispatch — see `render_class_method_call`.
        ExpX::Call(CallFun::Fun(fun, Some(_)), typs, args) => {
            render_class_method_call(fun, &typs[..], args, &e.typ, ctx)?
        }
        // Trait method called abstractly (`<Self as Tr>::m` in an inherited
        // ensures) routes here as `Fun(_, None)` with `Self` a type-param;
        // render it through class dispatch too, NOT positional type-args.
        ExpX::Call(CallFun::Fun(fun, None), typs, args) if fun_is_trait_method(fun, ctx) => {
            render_class_method_call(fun, &typs[..], args, &e.typ, ctx)?
        }
        ExpX::Call(CallFun::Fun(fun, None), typs, args)
        | ExpX::Call(CallFun::Recursive(fun), typs, args) => {
            let head = LExpr::app(
                LExpr::var(crate::lean_name::LeanName::from_path(&fun.path)),
                typs.iter().map(|t| typ_to_expr(t)).collect(),
            );
            // Bridge each arg to the callee's expected param typ — the
            // auto-borrow analog. For inherent-method calls and regular
            // fn calls, the receiver / args may arrive at a different
            // wrapper depth than the callee declares (e.g., `self.view()`
            // passes a bare local where `view(&self)` expects
            // `Tactus.Ref T`). `coerce_lexpr` inserts `.mk` wraps or
            // `.deref` peels structurally. When fn_param_typs returns
            // None (cross-crate callee not in fn_map), falls back to
            // no-coerce.
            let expected_typs = ctx.fn_param_typs(fun, &typs[..]);
            let rendered_args: Result<Vec<LExpr>, String> = args.iter().enumerate().map(|(i, a)| {
                // Typed spine (P1): bridge from the arg's ACTUAL
                // rendered typ, not the claimed `a.typ`.
                let arg_typed = exp_to_typed(a, ctx)?;
                Ok(match &expected_typs {
                    Some(typs) if i < typs.len() => arg_typed.into_slot(&typs[i]),
                    _ => arg_typed.into_slot(&a.typ),
                })
            }).collect();
            LExpr::app(head, rendered_args?).node
        }
        // `CheckDecreaseHeight(cur, prev, otherwise)` is the
        // termination obligation Verus inserts before each recursive
        // call (including mutual recursion across an SCC; see
        // `vir::recursion::check_decrease_call`). Per the prelude
        // axiom (`vir/src/prelude.rs:1019-1028`), its semantics is:
        //
        //   height_lt(height(cur), height(prev))
        //     ∨ (height(cur) = height(prev) ∧ otherwise)
        //
        // For int-typed decreases (`TypX::Int`), `height` is the
        // identity (modulo poly box/unbox), and the prelude also
        // axiomatises `height_lt(height(c), height(p)) ↔ 0 ≤ c ∧ c <
        // p` (`vir/src/prelude.rs:1030-1037`). So we can inline the
        // whole thing directly at the Lean level — no `height`
        // function needed, no axioms, completely transparent.
        //
        // For non-int (datatype) decreases, the `height` function is
        // non-trivial (encodes structural recursion on the datatype).
        // We don't support that yet; reject here if the decrease type
        // isn't int-like.
        ExpX::Call(CallFun::InternalFun(InternalFun::CheckDecreaseHeight), _, args) => {
            if args.len() != 3 {
                return Err(format!(
                    "CheckDecreaseHeight expects 3 args (cur, prev, otherwise), got {}",
                    args.len()
                ));
            }
            // `cur` is shaped as `let params = args in decrease_expr`
            // (see `recursion::check_decrease_call`), i.e., Verus
            // encodes parameter substitution via a BndX::Let. Render
            // it with the let zeta-reduced so omega can see the
            // substituted expression directly.
            let cur = render_checked_decrease_arg(&args[0], ctx)?;
            let prev = render_checked_decrease_arg(&args[1], ctx)?;
            let otherwise = sst_exp_to_ast_checked_with_ctx(&args[2], ctx)?;
            if is_int_height(&args[0].typ) {
                // Int fast-path. Prelude axiom at prelude.rs:1030-1037
                // gives `height_lt(height(c), height(p)) ↔ 0 ≤ c ∧ c
                // < p`, so we inline arithmetic directly — no
                // `height` fn, no axioms, transparent to omega.
                // (0 ≤ cur ∧ cur < prev) ∨ (cur = prev ∧ otherwise)
                let lt_branch = LExpr::and(
                    LExpr::le(LExpr::lit_int("0"), cur.clone()),
                    LExpr::lt(cur.clone(), prev.clone()),
                );
                let eq_branch = LExpr::and(LExpr::eq(cur, prev), otherwise);
                LExpr::or(lt_branch, eq_branch).node
            } else if let (Some(cur_path), Some(prev_path)) = (
                decrease_height_datatype(&args[0].typ),
                decrease_height_datatype(&args[1].typ),
            ) {
                // Datatype path. `to_lean_fn::height_fn_for_datatype`
                // emits a companion `<path>.height : T → Nat` def
                // via structural match. Obligation:
                //   <cur_T>.height cur < <prev_T>.height prev
                //     ∨ (<cur_T>.height cur = <prev_T>.height prev ∧ otherwise)
                //
                // For mutual-fn-SCC where cur and prev have DIFFERENT
                // types in the same datatype SCC (#109 stretch), each
                // side uses its own type's height fn. The comparison
                // `<cur_T>.height cur < <prev_T>.height prev` typechecks
                // because both height fns return `Nat`. Semantic
                // soundness comes from the height fns themselves
                // (mutual block ensures cross-type recursive calls
                // resolve, so each height correctly counts the
                // structural depth of its argument).
                //
                // For the common single-type case (cur and prev have
                // the same type), `cur_path == prev_path` and the
                // emitted shape matches the pre-#109 single-type
                // pattern.
                let cur_height = format!("{}.height", lean_name(cur_path));
                let prev_height = format!("{}.height", lean_name(prev_path));
                // Peel wrapper layers via `.deref` so the height fn
                // call typechecks. For an arg of type `Box<Stack>` the
                // rendered LExpr has Lean type `Tactus.Box Stack` but
                // `Stack.height` expects `Stack` — wrap with `.deref`
                // once per wrapper layer (matches the body-shadow's
                // unwrapping convention).
                let cur_n = count_ref_decorations(&*args[0].typ);
                let prev_n = count_ref_decorations(&*args[1].typ);
                let cur_h = LExpr::app1(LExpr::var_synthetic(cur_height), apply_deref_chain(cur, cur_n));
                let prev_h = LExpr::app1(LExpr::var_synthetic(prev_height), apply_deref_chain(prev, prev_n));
                let lt_branch = LExpr::lt(cur_h.clone(), prev_h.clone());
                let eq_branch = LExpr::and(LExpr::eq(cur_h, prev_h), otherwise);
                LExpr::or(lt_branch, eq_branch).node
            } else {
                // Types we can't anchor a height fn on: generic
                // datatype instantiations, tuples, spec fns, etc.
                // Tracked as task #54 deferrals — see DESIGN.md
                // "Non-int decreases".
                return Err(format!(
                    "recursive call termination check with non-int decrease \
                     (type {:?}) — only int and concrete (non-generic) user \
                     datatypes are supported today. See DESIGN.md 'Non-int \
                     decreases' for deferrals (generics, SCCs, lexicographic).",
                    args[0].typ
                ));
            }
        }
        ExpX::Call(CallFun::InternalFun(internal_fun), _, _) => {
            return Err(format!(
                "calls to Verus's internal `{:?}` builtin not yet supported in \
                 exec fns (only `CheckDecreaseHeight` is lowered today). See \
                 DESIGN.md \"Expression-level forms rejected\" for the list.",
                internal_fun
            ));
        }

        ExpX::Bind(bnd, body) => match &bnd.x {
            BndX::Let(binders) => {
                // Validate + render binder values first. The closure
                // returns `Result<(String, LExpr), String>`; `collect`
                // flips it into `Result<Vec<_>, String>` which `?`
                // unwraps to a plain Vec for the fold.
                let rendered_binders = binders.iter()
                    .map(|b| sst_exp_to_ast_checked_with_ctx(&b.a, ctx)
                        .map(|val| (crate::lean_name::LeanName::from_var_ident(&b.name), val)))
                    .collect::<Result<Vec<_>, _>>()?;
                let body_rendered = sst_exp_to_ast_checked_with_ctx(body, ctx)?;
                // Nest single-variable lets right-to-left so each binder is
                // in scope for the remainder.
                let out = rendered_binders.into_iter().rev().fold(body_rendered, |acc, (name, val)| {
                    LExpr::let_bind(name, val, acc)
                });
                out.node
            }
            BndX::Quant(quant, binders, _, _) => {
                let l_binders = vir_var_binders_to_ast(binders);
                let body = Box::new(sst_exp_to_ast_checked_with_ctx(body, ctx)?);
                match quant.quant {
                    air::ast::Quant::Forall => ExprNode::Forall { binders: l_binders, body },
                    air::ast::Quant::Exists => ExprNode::Exists { binders: l_binders, body },
                }
            }
            BndX::Lambda(binders, _) => ExprNode::Lambda {
                binders: vir_var_binders_to_ast(binders),
                body: Box::new(sst_exp_to_ast_checked_with_ctx(body, ctx)?),
            },
            BndX::Choose(binders, _, cond) => {
                // `Classical.epsilon (fun (x : T) => cond ∧ body)`
                let cond_ast = sst_exp_to_ast_checked_with_ctx(cond, ctx)?;
                let body_ast = sst_exp_to_ast_checked_with_ctx(body, ctx)?;
                let lambda = LExpr::lambda(
                    vir_var_binders_to_ast(binders),
                    LExpr::and(cond_ast, body_ast),
                );
                LExpr::app1(LExpr::var_lit("Classical.epsilon"), lambda).node
            }
        },

        // Migrated to the typed spine (P1) — transparent passthrough.
        ExpX::WithTriggers(..) | ExpX::Loc(_) => {
            return Ok(exp_to_typed(e, ctx)?.into_slot(&e.typ).node);
        }

        ExpX::NullaryOpr(_) => ExprNode::LitBool(true),

        // Datatype constructors: render via the shared `ctor_node`
        // so naming (named ctor with `.mk` fallback, anon tuple) agrees
        // with the VIR-AST path. Exec fn bodies reach this arm when
        // constructing structs/enums, e.g. `let p = Point { x: 1, y: 2 };`
        // or `return Some(x);`. The required datatype declarations are
        // brought into the Lean preamble by `dep_order::walk_expr`'s
        // `ExprX::Ctor` case.
        ExpX::Ctor(dt, variant, fields) => {
            let rendered = fields.iter()
                .map(|f| sst_exp_to_ast_checked_with_ctx(&f.a, ctx))
                .collect::<Result<Vec<_>, _>>()?;
            ctor_node(dt, variant, rendered)
        }

        // Spec-closure call (`f(args)` where `f: spec_fn(_) -> _`).
        // Lean's function types are first-class — `spec_fn(int) -> int`
        // renders as `Int → Int` via `typ_to_expr`'s `Lambda` arm — so
        // calling a closure is just an `App` with the closure value as
        // head. This mirrors the proof-fn path's `CallTarget::FnSpec`
        // handling in `to_lean_expr::call_to_node`. Closure construction
        // (`StmX::ClosureInner`) and exec-mode `FnOnce`/`Fn`/`FnMut`
        // calls remain deferred — see #93.
        ExpX::CallLambda(f, args) => {
            let f_rendered = sst_exp_to_ast_checked_with_ctx(f, ctx)?;
            if args.is_empty() {
                return Ok(f_rendered.node);
            }
            let args_rendered = args.iter()
                .map(|a| sst_exp_to_ast_checked_with_ctx(a, ctx))
                .collect::<Result<Vec<_>, _>>()?;
            ExprNode::App {
                head: Box::new(f_rendered),
                args: args_rendered,
            }
        }
        ExpX::ArrayLiteral(_) => return Err(
            "array literal `[a, b, c]` not yet supported in exec fns (Verus \
             rejects these upstream when slice indexing is unwired, so this is \
             usually unreachable)".to_string()
        ),
        // Internal-bug rejection (see ExpX::Old's `Snapshot reference for
        // generating AIR Old expressions; only used during sst_to_air`
        // docstring in `vir/sst.rs`). User-syntax `old(x)` lowers to
        // `ExpX::VarAt(x, Pre)` at AST→SST time, which Tactus handles
        // directly. Hitting this means Verus's pipeline changed; please
        // open an issue.
        ExpX::Old(..) => return Err(
            "ExpX::Old leaked from Verus's sst_to_air pipeline into Tactus's \
             SST input — internal bug, please open an issue.".to_string()
        ),
        ExpX::Interp(_) => return Err(
            "Interp nodes should never escape the interpreter — internal bug, \
             please open an issue.".to_string()
        ),
        // Internal-bug rejection. `ExpX::FuelConst(i)` is produced
        // exclusively by `vir::recursion::rewrite_rec_call_with_fuel_const`,
        // which is only called from `vir::expand_errors` — Verus's Z3
        // SMT-error-expansion pipeline. Tactus doesn't traverse that
        // pipeline (we go VIR → SST → Lean directly, never through
        // AIR / Z3 / expand_errors), so `FuelConst` should never reach
        // this rendering path.
        //
        // Hitting this arm would mean Verus's pipeline changed —
        // either `expand_errors` started running for Tactus fns, or
        // a new producer of `FuelConst` was added. Please open an issue.
        //
        // Note for users: `reveal_with_fuel(f, n)` itself is a separate
        // VIR construct (`StmX::Fuel(..)`, handled transparently in
        // `build_wp`) and is unrelated to `FuelConst`. In tactus_auto
        // fns, the user-facing way to expose a spec fn body is Lean's
        // `proof { unfold f }`, since the Verus fuel concept (Z3
        // recursion-unrolling depth) has no analog in Lean's
        // deterministic kernel. See DESIGN.md "reveal_with_fuel and
        // unfold in Tactus".
        ExpX::FuelConst(_) => return Err(
            "ExpX::FuelConst leaked from Verus's expand_errors / \
             Z3 pipeline into Tactus's SST input — internal bug, \
             please open an issue.".to_string()
        ),
    })
}

/// Does this type bottom out at `TypX::Int(_)` once transparent
/// wrappers (`Boxed`, `Decorate`) are peeled? Mirrors
/// `vir::recursion::height_is_int`.
fn is_int_height(typ: &Typ) -> bool {
    matches!(&**crate::to_lean_type::peel_typ_wrappers(typ), TypX::Int(_))
}

/// Extract the datatype Path when a decrease measure is a user
/// datatype (not int). Peels `Boxed` and `Decorate` wrappers via
/// `peel_typ_wrappers`. Returns None for tuples and anything else
/// that can't anchor a `T.height` fn. `height_fn_for_datatype`
/// in `to_lean_fn.rs` emits the matching definition.
///
/// Generic datatype instantiations (`Tree<A>` etc.) are accepted
/// (#108). The height fn is parameterized by implicit type args
/// at the Lean level, so callers just write `Tree.height cur` —
/// Lean infers `A` from `cur`'s type.
pub(crate) fn decrease_height_datatype(typ: &Typ) -> Option<&Path> {
    match &**crate::to_lean_type::peel_typ_wrappers(typ) {
        TypX::Datatype(Dt::Path(path), _args, _) => Some(path),
        _ => None,
    }
}

fn const_to_node_checked(c: &Constant) -> Result<ExprNode, String> {
    const_to_node_common(c).ok_or_else(||
        format!("unsupported constant: {:?}", c)
    )
}

// ── BitVec-mode rendering for assert by(bit_vector) (#111 / #130) ─────────
//
// `assert(P) by(bit_vector)` goals get a different lowering: each
// fixed-width-int `Var(x : U(n))` renders as `BitVec.ofInt n x`
// instead of just `x`. The resulting LExpr's bitwise ops resolve to
// BitVec instances (via Lean's HXor/HAnd/HOr/HShiftLeft/etc.
// typeclasses), and Lean tactics like `decide` and `simp [BitVec.*]`
// can reason about the BitVec semantics.
//
// Outside `by(bit_vector)` contexts, u-types stay rendered as `Int`
// (preserving omega-friendly linear-arithmetic semantics for the
// usual exec-fn proofs). Two encodings switched contextually —
// matches what Verus does for its bit-vector queries.
//
// Scope of this first cut (#130): rendering only. The "real"
// soundness story for parameterized `BitVec.ofInt n x` terms — where
// `bv_decide` would prefer free `BitVec n` vars — is left for a
// follow-up. For now `simp` + `decide` close commutativity / identity
// laws / concrete cases; richer reasoning needs the bound-hypothesis
// bridge work (introduce `x_bv : BitVec n` with a tie-back hyp).

/// Render an SST `Exp` in bit-vector mode: variables of fixed-width
/// unsigned-int types become `BitVec.ofInt n x` wrappings, constants
/// stay as numeric literals (Lean's `OfNat` instance coerces them to
/// the surrounding BitVec type), and bitwise/arithmetic operators
/// route to BitVec instances naturally.
///
/// Limited to the shapes a typical `assert by(bit_vector)` uses:
/// Var, Const, BinaryOp (Eq/Ne, And/Or/Implies, bitwise ops, arith),
/// UnaryOp (Not). More complex shapes (Calls, structs, lambdas) are
/// rejected with a clear error — those don't usually appear inside
/// bit-vector assertions, and routing them through BitVec encoding
/// has its own design questions.
pub fn sst_exp_to_bit_vector_ast(e: &Exp) -> Result<LExpr, String> {
    bv_exp_to_node(e).map(LExpr::new)
}

fn bv_exp_to_node(e: &Exp) -> Result<ExprNode, String> {
    use crate::expr_shared::binop_to_ast;
    use crate::lean_ast::UnOp as LUnOp;
    match &e.x {
        ExpX::Var(v) => {
            let name = crate::lean_name::LeanName::from_var_ident(v);
            // U(n) → wrap as BitVec.ofInt n x. Other types pass
            // through (Bool stays Bool, Int stays Int — only the
            // u-typed vars get the coercion).
            match &**crate::to_lean_type::peel_typ_wrappers(&e.typ) {
                TypX::Int(IntRange::U(n)) => {
                    Ok(ExprNode::App {
                        head: Box::new(LExpr::var_lit("BitVec.ofInt")),
                        args: vec![
                            LExpr::lit_int(n.to_string()),
                            LExpr::var(name),
                        ],
                    })
                }
                _ => Ok(ExprNode::Var(name)),
            }
        }
        ExpX::Const(c) => const_to_node_checked(c),
        ExpX::Binary(op, lhs, rhs) => {
            let l = bv_exp_to_node(lhs)?;
            let r = bv_exp_to_node(rhs)?;
            if let Some(bop) = binop_to_ast(op) {
                Ok(ExprNode::BinOp {
                    op: bop,
                    lhs: Box::new(LExpr::new(l)),
                    rhs: Box::new(LExpr::new(r)),
                })
            } else {
                Err(format!(
                    "binary op {:?} not supported in bit_vector assert — \
                     fall back to `assert(P) by {{ ... }}` with a custom \
                     Lean tactic for non-bitwise/non-arithmetic operators",
                    op
                ))
            }
        }
        ExpX::Unary(UnaryOp::Not, inner) => {
            let i = bv_exp_to_node(inner)?;
            Ok(ExprNode::UnOp {
                op: LUnOp::Not,
                arg: Box::new(LExpr::new(i)),
            })
        }
        // Inside bit_vector assertions we don't see complex SST
        // shapes (calls, ctors, lambdas) — Verus typically rejects
        // those upstream. If one shows up, return a clear error
        // naming the variant so the user can identify which shape
        // they wrote.
        other => Err(format!(
            "expression shape `{}` not yet supported inside `by(bit_vector)` — \
             use `assert(P) by {{ ... }}` with a custom Lean tactic for \
             non-trivial shapes (#130)",
            bv_unsupported_shape_name(other)
        )),
    }
}

/// Human-readable variant name for `ExpX` shapes that
/// `bv_exp_to_node` rejects. `std::mem::discriminant` produces a
/// numeric ID; this gives the user the name they can search for.
fn bv_unsupported_shape_name(x: &ExpX) -> &'static str {
    match x {
        ExpX::Call(..) => "ExpX::Call",
        ExpX::CallLambda(..) => "ExpX::CallLambda",
        ExpX::Ctor(..) => "ExpX::Ctor",
        ExpX::Bind(..) => "ExpX::Bind",
        ExpX::If(..) => "ExpX::If",
        ExpX::Loc(..) => "ExpX::Loc",
        ExpX::ArrayLiteral(..) => "ExpX::ArrayLiteral",
        ExpX::VarAt(..) => "ExpX::VarAt",
        ExpX::VarLoc(..) => "ExpX::VarLoc",
        ExpX::StaticVar(..) => "ExpX::StaticVar",
        ExpX::Old(..) => "ExpX::Old",
        ExpX::ExecFnByName(..) => "ExpX::ExecFnByName",
        ExpX::WithTriggers(..) => "ExpX::WithTriggers",
        ExpX::FuelConst(..) => "ExpX::FuelConst",
        ExpX::Interp(..) => "ExpX::Interp",
        ExpX::NullaryOpr(..) => "ExpX::NullaryOpr",
        ExpX::UnaryOpr(..) => "ExpX::UnaryOpr",
        // Note: Var, Const, Binary, Unary handled in the main match;
        // their arms produce LExpr directly, never reach this helper.
        _ => "<unknown ExpX variant>",
    }
}
