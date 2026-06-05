//! Mut-ref normalization — the unified rewrite pass that maps every
//! mut-ref shape Verus emits (legacy `is_mut: true` and new-mut-ref
//! `MutRef<T>` modes) to a canonical destination shape before rendering.
//!
//! Entry points (`pub(crate)`): `rewrite_mut_ref_in_exp` /
//! `rewrite_mut_ref_in_stm` (SST body/ensures), `rewrite_varat_for_mut_params`
//! (VIR-AST callee-spec inlining), and `rewrite_return_final_ref`
//! (returned-mut-ref prophecy). See `RewritePhase` for the body/ensures/reqs
//! scope distinction.

use std::collections::HashSet;
use std::sync::Arc;

use vir::ast::{Expr, ExprX, SpannedTyped, Typ, UnaryOp, UnaryOpr, VarAt, VarIdent};
use vir::ast_visitor::map_expr_visitor;
use vir::sst::{Exp, ExpX, Stm};

use crate::expr_shared::varat_pre_name;
use crate::to_lean_type::sanitize;

/// Rewrite `VarAt(p, Pre)` references for the given `&mut` param
/// names to a synthetic `Var(<p>_at_pre_tactus)` so the call-site
/// renderer-then-substitution can target pre-state independently
/// of post-state (`Var(p)` stays as-is for post-state references).
///
/// This pre-rewrite happens at the VIR-AST level — *before*
/// `vir_expr_to_ast` collapses `VarAt(_, _)` into `Var(_)`. We
/// don't change the renderer because `VarAt` is also used outside
/// `&mut` (loop ensures' at-entry references, where the natural
/// collapse to `Var` is correct), and changing the global
/// rendering would unbind the `_at_pre_tactus` names in those
/// contexts. Doing the rewrite here, scoped by the &mut param
/// name set, keeps the change local to `&mut` callee-spec
/// inlining.
///
/// `mut_param_names` is the set of `sanitize`d param-name strings
/// for `&mut` parameters of the callee. Other vars (callee-local
/// loop vars referenced via `VarAt`, non-mut params, etc.) are
/// left alone — their natural `VarAt → Var` collapse is what we
/// want.
pub(crate) fn rewrite_varat_for_mut_params(
    expr: &Expr,
    mut_param_names: &std::collections::HashSet<String>,
) -> Expr {
    // Short-circuit: callees without &mut params (the common case)
    // don't need any rewriting. `map_expr_visitor` would otherwise
    // walk + clone the whole tree for nothing.
    if mut_param_names.is_empty() {
        return expr.clone();
    }
    // Helper: extract inner Var from an MutRef* op's argument,
    // peeling transparent decorations the way `peel_to_var` does
    // for SST. Returns the inner VarIdent if it's a Var/VarLoc of a
    // mut param, else None.
    //
    // Verus emits several semantically-equivalent shapes for "value
    // of mut-ref local h":
    //   * `Var(h)` / `VarLoc(h)` — direct (legacy mode)
    //   * `ReadPlace(Local(h), _)` — new-mut-ref encoding, treats the
    //     local-read as a place-read with some read kind
    // plus the transparent Box/Unbox/Trigger/CoerceMode wrappers
    // that Verus's poly encoding may insert around any of these.
    //
    // All these forms are normalized here to the inner `VarIdent`,
    // and `rewrite_varat_for_mut_params` then maps the whole shape
    // to canonical `Var(h)` (post-state) or `Var(h_at_pre_tactus)`
    // (pre-state). Peeling ReadPlace ensures `MutRefCurrent(
    // ReadPlace(Local(h)))` gets normalized — previously this fell
    // through the rewrite and aliased pre-state with post-state.
    let extract_mut_var = |inner: &Expr| -> Option<VarIdent> {
        let mut cursor = inner;
        loop {
            match &cursor.x {
                ExprX::Unary(
                    vir::ast::UnaryOp::CoerceMode { .. }
                    | vir::ast::UnaryOp::Trigger(_),
                    inner,
                ) => cursor = inner,
                ExprX::UnaryOpr(
                    vir::ast::UnaryOpr::Box(_) | vir::ast::UnaryOpr::Unbox(_),
                    inner,
                ) => cursor = inner,
                ExprX::Var(ident) | ExprX::VarLoc(ident) => {
                    if mut_param_names.contains(&sanitize(&ident.0)) {
                        return Some(ident.clone());
                    }
                    return None;
                }
                ExprX::ReadPlace(place, _) => match &place.x {
                    vir::ast::PlaceX::Local(ident) => {
                        if mut_param_names.contains(&sanitize(&ident.0)) {
                            return Some(ident.clone());
                        }
                        return None;
                    }
                    _ => return None,
                },
                _ => return None,
            }
        }
    };
    map_expr_visitor(expr, &|e: &Expr| {
        // Legacy mode: `*old(x)` → `VarAt(x, Pre)` for &mut params.
        if let ExprX::VarAt(ident, VarAt::Pre) = &e.x {
            let raw_name = sanitize(&ident.0);
            if mut_param_names.contains(&raw_name) {
                // Use `raw_name` (already sanitized) so the synthetic
                // string matches what `subst`'s key — `varat_pre_name(
                // sanitize(p.name))` — produces. `sanitize` is
                // idempotent on the resulting `<name>_at_pre_tactus`
                // shape (no special chars introduced).
                let new_str: vir::ast::Ident = Arc::new(varat_pre_name(&raw_name));
                let new_ident = VarIdent(new_str, ident.1.clone());
                return Ok(SpannedTyped::new(
                    &e.span,
                    &e.typ,
                    ExprX::Var(new_ident),
                ));
            }
        }
        // New-mut-ref mode: `MutRefCurrent(x)` = pre-state, rewrite
        // to `Var(<x>_at_pre_tactus)` so caller-side substitution
        // (in `add_param_subst_entries`) maps it to the caller's
        // pre-state arg. `MutRefFuture` / `MutRefFinal` are post-
        // state — they collapse to `Var(x)` which the substitution
        // map sends to the fresh `_tactus_mut_post_N` existential.
        // Without this distinction, the bare-pass-through of
        // `Unary(_, inner)` in `vir_expr_to_ast` aliases both
        // pre- and post-state to `Var(x)`, mapping them both to
        // the post-state fresh and producing the substitution bug
        // observed in `test_exec_call_mut_arg_vec_index_probe`.
        if let ExprX::Unary(op, inner) = &e.x {
            match op {
                vir::ast::UnaryOp::MutRefCurrent => {
                    if let Some(ident) = extract_mut_var(inner) {
                        let raw_name = sanitize(&ident.0);
                        let new_str: vir::ast::Ident =
                            Arc::new(varat_pre_name(&raw_name));
                        let new_ident = VarIdent(new_str, ident.1.clone());
                        return Ok(SpannedTyped::new(
                            &e.span, &e.typ, ExprX::Var(new_ident),
                        ));
                    }
                }
                vir::ast::UnaryOp::MutRefFuture(_)
                | vir::ast::UnaryOp::MutRefFinal(_) => {
                    if let Some(ident) = extract_mut_var(inner) {
                        return Ok(SpannedTyped::new(
                            &e.span, &e.typ, ExprX::Var(ident),
                        ));
                    }
                }
                _ => {}
            }
        }
        Ok(e.clone())
    })
    // The closure only constructs valid Var nodes from existing
    // VarAt/MutRef nodes; it cannot fail.
    .expect("rewrite_varat_for_mut_params is structural and shouldn't error")
}

/// Returned-mut-ref prophecy: in a callee's inlined ensures, rewrite the
/// RETURN ref's `*final` — `MutRefFuture`/`MutRefFinal` of the named
/// return — to a distinct synthetic `Var(final_var)`, which
/// `push_post_call_frames` then substitutes to the prophecy var `P`.
///
/// Mirrors `rewrite_varat_for_mut_params`, but for the callee's RETURN
/// rather than its `&mut` params. Only `MutRefFuture`/`MutRefFinal` are
/// rewritten; `MutRefCurrent(ret)` is left to collapse to `Var(ret)` →
/// `fresh_ret` (the just-returned/current value, handled by the #128 ret
/// path). Without this split, both current AND final collapse to
/// `Var(ret)`, so a `final(vec)@ == update(old@, i, *final(ret))` ensures
/// (vstd's `vec_index_mut`) inserts the *current* element instead of the
/// prophesied final — the `&mut v[i]` bug.
///
/// General over any callee with a `MutRef`-typed return; not specific to
/// `vec_index_mut`. Matches the return by sanitized base name.
pub(crate) fn rewrite_return_final_ref(expr: &Expr, ret_name: &VarIdent, final_var: &VarIdent) -> Expr {
    let ret_san = sanitize(&ret_name.0);
    // Peel transparent wrappers + ReadPlace to the inner ident; true iff
    // it names the return. Mirrors `extract_mut_var`'s peel set.
    fn inner_names(e: &Expr, ret_san: &str) -> bool {
        let mut cursor = e;
        loop {
            match &cursor.x {
                ExprX::Unary(
                    vir::ast::UnaryOp::CoerceMode { .. }
                    | vir::ast::UnaryOp::Trigger(_),
                    inner,
                ) => cursor = inner,
                ExprX::UnaryOpr(
                    vir::ast::UnaryOpr::Box(_) | vir::ast::UnaryOpr::Unbox(_),
                    inner,
                ) => cursor = inner,
                ExprX::Var(id) | ExprX::VarLoc(id) | ExprX::VarAt(id, _) => {
                    return sanitize(&id.0) == ret_san;
                }
                ExprX::ReadPlace(place, _) => match &place.x {
                    vir::ast::PlaceX::Local(id) => return sanitize(&id.0) == ret_san,
                    _ => return false,
                },
                _ => return false,
            }
        }
    }
    map_expr_visitor(expr, &|e: &Expr| {
        if let ExprX::Unary(
            vir::ast::UnaryOp::MutRefFuture(_) | vir::ast::UnaryOp::MutRefFinal(_),
            inner,
        ) = &e.x
        {
            if inner_names(inner, &ret_san) {
                return Ok(SpannedTyped::new(
                    &e.span, &e.typ, ExprX::Var(final_var.clone()),
                ));
            }
        }
        Ok(e.clone())
    })
    .expect("rewrite_return_final_ref is structural and shouldn't error")
}

// ── Unified mut-ref rewrite pass ───────────────────────────────────────
//
// Single pass that maps every mut-ref shape Verus emits — across both
// legacy mode (`is_mut: true`, plain typ) and new-mut-ref mode
// (`is_mut: false`, `MutRef<T>` typ) — to a canonical destination
// shape. Replaces the prior two-pass pipeline (`normalize_mut_ref_*`
// then `rewrite_varat_for_mut_params_*`) that converted new-mode
// shapes to legacy form and then applied the legacy rewrite.
//
// **Rewrite table** (for `x` in `mut_param_names`):
//
// | Phase   | Source                            | Destination                  |
// |---------|-----------------------------------|------------------------------|
// | body    | `VarAt(x, Pre)`                   | `Var(<x>_at_pre_tactus)`     |
// | body    | `MutRefCurrent(Var(x))`           | `Var(x)`                     |
// | body    | `MutRefCurrent(VarLoc(x))`        | `VarLoc(x)`                  |
// | body    | `MutRefCurrent(VarAt(x, Pre))`    | `Var(<x>_at_pre_tactus)`     |
// | ensures | `VarAt(x, Pre)`                   | `Var(<x>_at_pre_tactus)`     |
// | ensures | `MutRefCurrent(Var(x))`           | `Var(<x>_at_pre_tactus)`     |
// | ensures | `MutRefCurrent(VarAt(x, Pre))`    | `Var(<x>_at_pre_tactus)`     |
// | both    | `MutRefFuture(_, Var(x))`         | `Var(x)`                     |
// | both    | `MutRefFinal(_, Var(x))`          | `Var(x)`                     |
//
// In the body phase, `Var(x)` is the OblCtx-shadowed inner T (set by
// the `let x := x.deref` frame in `exec_fn_theorems_to_ast`). In the
// ensures phase, `Var(x)` is the post-state inner T (after all body
// let-shadows). `Var(<x>_at_pre_tactus)` is the captured pre-state
// inner T from the OblCtx `let <x>_at_pre_tactus := x.deref` frame.
//
// `MutRefCurrent(VarLoc(x))` (LHS of `*x = e` in body) becomes
// `VarLoc(x)`, which after the outer `Loc(_)` wrapper gives the
// assignment shape `Loc(VarLoc(x))` that `walk_assign` handles.
//
// Other shapes — e.g., `MutRefCurrent(Field(...))` for `*x.field`,
// or `MutRefCurrent` wrapping non-`Var`/`VarLoc` — are left alone
// and will hit the renderer's "unsupported unary op" arm. Those map
// to deferred follow-ups (`&mut v[i]`, etc.).

/// Phase-of-rendering context for [`rewrite_mut_ref_in_exp`]. The
/// canonical destination for `VarAt(x, Pre)` and `MutRefCurrent(Var(x))`
/// depends on what's in scope at the rendering site:
/// * **Body**: OblCtx has `let <x>_at_pre_tactus := x.deref` and
///   `let x := x.deref` in scope. `*x` (current) → `Var(x)` (resolves
///   to body-shadowed inner T); `*old(x)` (pre-state) →
///   `Var(<x>_at_pre_tactus)` (resolves to captured pre-state).
/// * **Ensures**: same OblCtx scope as Body. `*x` (post-state via
///   let-shadow chain) → `Var(x)`; `*old(x)` (pre-state) →
///   `Var(<x>_at_pre_tactus)`. The difference from Body is that
///   `MutRefCurrent(Var(x))` reads pre-state in new-mut-ref mode's
///   ensures convention (Verus pairs `MutRefCurrent` with pre-state
///   semantics in ensures).
/// * **Reqs**: theorem-binder scope — `<x>_at_pre_tactus` is NOT in
///   scope; only the per-req `let x := x.deref` wrap applies. At fn
///   entry pre-state IS current state, so `VarAt(x, Pre)` and
///   `MutRefCurrent(Var(x))` both → `Var(x)` (resolves to inner T
///   via the per-req shadow).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum RewritePhase {
    Body,
    Ensures,
    Reqs,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum InnerKind {
    Var,
    VarLoc,
    VarAtPre,
}

/// Peel transparent wrappers (Box/Unbox/MustBeFinalized/CoerceMode/
/// Trigger) to find an inner `Var` / `VarLoc` / `VarAt(_, Pre)`.
/// Returns `(ident, kind)` indicating which it is.
///
/// `VarAt(x, Pre)` appears as the inner of `MutRefFuture`/`MutRefFinal`
/// ops in new-mut-ref postconditions because Verus pairs the
/// post-state `MutRefFuture` wrapper with a pre-state `VarAt`
/// reference (the post-state of x's entry value).
fn peel_to_var(e: &Exp) -> Option<(&VarIdent, InnerKind)> {
    match &e.x {
        ExpX::Var(id) => Some((id, InnerKind::Var)),
        ExpX::VarLoc(id) => Some((id, InnerKind::VarLoc)),
        ExpX::VarAt(id, vir::ast::VarAt::Pre) => Some((id, InnerKind::VarAtPre)),
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner)
        | ExpX::Unary(UnaryOp::MustBeFinalized | UnaryOp::CoerceMode { .. } | UnaryOp::Trigger(_), inner) => {
            peel_to_var(inner)
        }
        _ => None,
    }
}

/// Construct the SST node that maps a mut-ref param name `id` to its
/// pre-state synthetic `Var(<id>_at_pre_tactus)`. The same synthetic
/// name is bound by the OblCtx frame `let <x>_at_pre_tactus :=
/// x.deref` at fn entry, so `Var(<x>_at_pre_tactus)` resolves to the
/// captured inner-T pre-state value.
///
/// `varat_pre_name` (in `expr_shared`) is the single source of truth
/// for the synthetic name format — shared between this rewrite and
/// the OblCtx Let-frame construction so divergence is a compile
/// error rather than a runtime mismatch.
fn mk_pre_state_var(span: &vir::messages::Span, typ: &Typ, id: &VarIdent) -> Exp {
    let raw_name = sanitize(&id.0);
    let new_str: vir::ast::Ident = Arc::new(varat_pre_name(&raw_name));
    // Reuse the original disambiguator. The `<x>_at_pre_tactus`
    // suffix contains no special chars, so `LeanName::from_var_ident`
    // won't add another disambiguator.
    let new_ident = VarIdent(new_str, id.1.clone());
    SpannedTyped::new(span, typ, ExpX::Var(new_ident))
}

// The rewrite happens in two ordered sub-passes. The split is forced
// by Verus's `sst_visitor`, which walks children-then-parent (post-
// order). Doing both transformations in one closure would race: for
// `MutRefFuture(_, VarAt(x, Pre))` (Verus's post-state-of-entry-value
// pattern), the inner `VarAt(x, Pre)` would be rewritten to
// `Var(<x>_at_pre_tactus)` before the outer `MutRefFuture` closure
// fires, and the outer would no longer recognize it as a mut-param ref.
//
// Splitting into two ordered passes side-steps the ordering issue
// while keeping each pass simple enough that the bottom-up visitor
// gives the right answer for it in isolation:
//
//   Sub-pass A (`unwrap_mut_ref_ops`): strip MutRefCurrent /
//     MutRefFuture / MutRefFinal wrappers, leaving inner Var / VarLoc /
//     VarAt(_, Pre) untouched. This is a structural one-step rewrite —
//     bottom-up is fine because the inner ident is preserved literally.
//
//   Sub-pass B (`rename_varat_pre`): rename any remaining standalone
//     VarAt(x, Pre) → Var(<x>_at_pre_tactus). After sub-pass A the
//     only VarAt(_, Pre) sites are the legacy `*old(x)` references,
//     which need the synthetic-name rewrite uniformly.
//
// `rewrite_mut_ref_in_exp` chains them — one external call, two
// internal passes — so the call sites see a single "make this Exp
// reference mut-ref state correctly" operation.

/// Sub-pass A: unwrap MutRefCurrent / MutRefFuture / MutRefFinal ops
/// around mut-param references. Phase determines what each becomes:
///
/// | Phase   | Op                                | Result                          |
/// |---------|-----------------------------------|---------------------------------|
/// | Body    | `MutRefCurrent(Var(x))`           | `Var(x)`                        |
/// | Body    | `MutRefCurrent(VarLoc(x))`        | `VarLoc(x)`                     |
/// | Body    | `MutRefCurrent(VarAt(x, Pre))`    | `VarAt(x, Pre)` (sub-pass B handles)|
/// | Ensures | `MutRefCurrent(Var(x))`           | `VarAt(x, Pre)` (sub-pass B handles)|
/// | Ensures | `MutRefCurrent(VarAt(x, Pre))`    | `VarAt(x, Pre)` (sub-pass B handles)|
/// | Reqs    | `MutRefCurrent(Var(x))`           | `Var(x)`                        |
/// | Reqs    | `MutRefCurrent(VarAt(x, Pre))`    | `Var(x)` (collapsed by per-req shadow)|
/// | both    | `MutRefFuture(_, Var(x))`         | `Var(x)`                        |
/// | both    | `MutRefFuture(_, VarLoc(x))`      | `VarLoc(x)`                     |
/// | both    | `MutRefFuture(_, VarAt(x, Pre))`  | `Var(x)` (post-state collapse)  |
/// | both    | `MutRefFinal(_, ...)`             | same as MutRefFuture            |
///
/// In ensures phase, `MutRefCurrent` semantically reads pre-state;
/// rather than producing the synthetic `<x>_at_pre_tactus` here, we
/// produce `VarAt(x, Pre)` and let sub-pass B handle the rename
/// uniformly. Same for body's `MutRefCurrent(VarAt(x, Pre))` (rare
/// shape but Verus's lowering can produce it).
fn unwrap_one_mut_ref_op(
    e: &Exp,
    mut_param_names: &HashSet<String>,
    phase: RewritePhase,
) -> Exp {
    let (inner, is_future_or_final) = match &e.x {
        ExpX::Unary(UnaryOp::MutRefCurrent, inner) => (inner, false),
        ExpX::Unary(UnaryOp::MutRefFuture(_) | UnaryOp::MutRefFinal(_), inner) => (inner, true),
        _ => return e.clone(),
    };
    let Some((id, kind)) = peel_to_var(inner) else { return e.clone() };
    if !mut_param_names.contains(&sanitize(&id.0)) {
        return e.clone();
    }
    let new_x = if is_future_or_final {
        // Future/Final = post-state of the wrapper. Body's let-shadow
        // chain rebinds `x` to inner T; that's the post-state. VarLoc
        // stays VarLoc (assign LHS); VarAt-inner collapses to Var
        // (post-state == final-state, no pre-state semantics here).
        match kind {
            InnerKind::VarLoc => ExpX::VarLoc(id.clone()),
            InnerKind::Var | InnerKind::VarAtPre => ExpX::Var(id.clone()),
        }
    } else {
        // MutRefCurrent — phase-dependent.
        match (phase, kind) {
            (RewritePhase::Body, InnerKind::Var) => ExpX::Var(id.clone()),
            (RewritePhase::Body, InnerKind::VarLoc) => ExpX::VarLoc(id.clone()),
            (RewritePhase::Body, InnerKind::VarAtPre) => {
                // Leave as VarAt(x, Pre) for sub-pass B to rename to
                // `<x>_at_pre_tactus`.
                ExpX::VarAt(id.clone(), vir::ast::VarAt::Pre)
            }
            (RewritePhase::Ensures, InnerKind::VarLoc) => {
                panic!("VarLoc shouldn't appear in ensures position");
            }
            (RewritePhase::Ensures, InnerKind::Var | InnerKind::VarAtPre) => {
                // Ensures MutRefCurrent reads pre-state — leave as
                // VarAt(x, Pre) for sub-pass B to rename.
                ExpX::VarAt(id.clone(), vir::ast::VarAt::Pre)
            }
            (RewritePhase::Reqs, InnerKind::Var | InnerKind::VarAtPre) => {
                // Reqs: at fn entry pre = current, both forms → Var(x).
                ExpX::Var(id.clone())
            }
            (RewritePhase::Reqs, InnerKind::VarLoc) => ExpX::VarLoc(id.clone()),
        }
    };
    SpannedTyped::new(&e.span, &e.typ, new_x)
}

/// Sub-pass B: standalone `VarAt(x, Pre)` (any source — legacy
/// `*old(x)` or sub-pass A's collapsed `MutRefCurrent`/`MutRefFuture`
/// output) becomes the synthetic pre-state binder in Body/Ensures
/// scope, or stays as `Var(x)` in Reqs scope (where `<x>_at_pre_tactus`
/// isn't in scope and pre-state IS current state at fn entry).
fn rename_varat_pre_in_exp(
    exp: &Exp,
    mut_param_names: &HashSet<String>,
    phase: RewritePhase,
) -> Exp {
    if mut_param_names.is_empty() {
        return exp.clone();
    }
    vir::sst_visitor::map_exp_visitor(exp, &mut |e: &Exp| {
        let ExpX::VarAt(id, vir::ast::VarAt::Pre) = &e.x else { return e.clone() };
        if !mut_param_names.contains(&sanitize(&id.0)) {
            return e.clone();
        }
        match phase {
            RewritePhase::Body | RewritePhase::Ensures => {
                mk_pre_state_var(&e.span, &e.typ, id)
            }
            RewritePhase::Reqs => {
                SpannedTyped::new(&e.span, &e.typ, ExpX::Var(id.clone()))
            }
        }
    })
}

fn unwrap_mut_ref_ops_in_exp(
    exp: &Exp,
    mut_param_names: &HashSet<String>,
    phase: RewritePhase,
) -> Exp {
    if mut_param_names.is_empty() {
        return exp.clone();
    }
    vir::sst_visitor::map_exp_visitor(exp, &mut |e: &Exp| {
        unwrap_one_mut_ref_op(e, mut_param_names, phase)
    })
}

/// External entry point: chains sub-pass A (unwrap MutRef* ops) then
/// sub-pass B (rename standalone VarAt(x, Pre)). One call site → one
/// canonical destination shape, regardless of which Verus mode produced
/// the input.
pub(crate) fn rewrite_mut_ref_in_exp(
    exp: &Exp,
    mut_param_names: &HashSet<String>,
    phase: RewritePhase,
) -> Exp {
    if mut_param_names.is_empty() {
        return exp.clone();
    }
    let unwrapped = unwrap_mut_ref_ops_in_exp(exp, mut_param_names, phase);
    rename_varat_pre_in_exp(&unwrapped, mut_param_names, phase)
}

pub(crate) fn rewrite_mut_ref_in_stm(
    stm: &Stm,
    mut_param_names: &HashSet<String>,
) -> Stm {
    if mut_param_names.is_empty() {
        return stm.clone();
    }
    // Body phase only — ensures expressions reach the rewrite via
    // `rewrite_mut_ref_in_exp` in `WpCtx::new`.
    let unwrapped = vir::sst_visitor::map_exps_in_stm_visitor(stm, &mut |e: &Exp| {
        unwrap_one_mut_ref_op(e, mut_param_names, RewritePhase::Body)
    });
    vir::sst_visitor::map_exps_in_stm_visitor(&unwrapped, &mut |e: &Exp| {
        rename_varat_pre_in_exp(e, mut_param_names, RewritePhase::Body)
    })
}
