//! Unit tests for `to_lean_expr` — extracted to `src/tests/` (a `#[path]`'d
//! `mod tests` child of `to_lean_expr`, so `use super::*` reaches private items).

use super::*;
use crate::expr_shared::count_ref_decorations;
use crate::test_fixtures::typ_int;
use std::sync::Arc;
use vir::ast::{Mode, ParamX, TypDecoration};
use vir::def::Spanned;
use vir::messages::Span;

fn typ_ref(inner: Typ) -> Typ {
    Arc::new(TypX::Decorate(TypDecoration::Ref, None, inner))
}

fn typ_box(inner: Typ) -> Typ {
    Arc::new(TypX::Decorate(TypDecoration::Box, None, inner))
}

fn typ_boxed(inner: Typ) -> Typ {
    Arc::new(TypX::Boxed(inner))
}

fn typ_mut_ref(inner: Typ) -> Typ {
    Arc::new(TypX::MutRef(inner))
}

fn mk_var_ident(name: &str) -> VarIdent {
    VarIdent(Arc::new(name.to_string()), vir::ast::VarIdentDisambiguate::NoBodyParam)
}

fn mk_param(name: &str, typ: Typ, is_mut: bool) -> Param {
    Spanned::new(Span::dummy(), ParamX {
        name: mk_var_ident(name),
        typ,
        mode: Mode::Spec,
        user_mut: false,
        is_mut,
        unwrapped_info: None,
    })
}

// ── strip_one_ref_decoration ─────────────────────────────────────────

#[test]
fn strip_one_ref_decoration_strips_ref() {
    let int = typ_int();
    let r = typ_ref(int.clone());
    let stripped = strip_one_ref_decoration(&r);
    // Stripping `&Int` should give `Int` — count drops by 1.
    assert_eq!(count_ref_decorations(&stripped), 0);
}

#[test]
fn strip_one_ref_decoration_strips_mut_ref() {
    // TypX::MutRef (new mode) is treated like a ref decoration
    // — strip the outer layer.
    let int = typ_int();
    let m = typ_mut_ref(int.clone());
    let stripped = strip_one_ref_decoration(&m);
    assert_eq!(count_ref_decorations(&stripped), 0);
}

#[test]
fn strip_one_ref_decoration_strips_only_one_layer() {
    // `&Box<Int>` (count 2) → strip outermost ref → `Box<Int>` (count 1).
    // Only ONE decoration peeled per call, mirroring the shadow's
    // single `.deref` step.
    let int = typ_int();
    let bx = typ_box(int);
    let r_bx = typ_ref(bx);
    assert_eq!(count_ref_decorations(&r_bx), 2);
    let stripped = strip_one_ref_decoration(&r_bx);
    assert_eq!(count_ref_decorations(&stripped), 1);
}

#[test]
fn strip_one_ref_decoration_passes_through_bare() {
    // No ref decoration → no change.
    let int = typ_int();
    let stripped = strip_one_ref_decoration(&int);
    assert_eq!(count_ref_decorations(&stripped), 0);
}

#[test]
fn strip_one_ref_decoration_does_not_peel_boxed() {
    // `TypX::Boxed` is Verus's poly-encoding "transparent" marker
    // (NOT the `Box<T>` decoration). It's Lean-transparent and not
    // a wrapper. `strip_one_ref_decoration` only peels reference
    // decorations and MutRef.
    let int = typ_int();
    let boxed = typ_boxed(int);
    let stripped = strip_one_ref_decoration(&boxed);
    // `Boxed(Int)` returned as-is.
    assert!(matches!(&*stripped, TypX::Boxed(_)));
}

// ── binder_ctx_from_params ───────────────────────────────────────────

#[test]
fn binder_ctx_empty_params_empty_ctx() {
    let params: Params = Arc::new(vec![]);
    let ctx = binder_ctx_from_params(&params);
    assert!(ctx.is_empty());
}

#[test]
fn binder_ctx_ref_only_param_keeps_wrapper() {
    // `&Int` param (`Decorate(Ref, _, Int)`, is_mut: false) is
    // NOT shadowed post-U2 — BinderCtx records the wrapper-
    // decorated typ as-declared.
    let int = typ_int();
    let r = typ_ref(int);
    let params: Params = Arc::new(vec![mk_param("p", r.clone(), false)]);
    let ctx = binder_ctx_from_params(&params);
    let recorded = ctx.get(&mk_var_ident("p")).expect("p should be in ctx");
    assert_eq!(count_ref_decorations(recorded), 1);
}

#[test]
fn binder_ctx_legacy_mut_param_strips() {
    // Legacy `&mut x: Int` is `is_mut: true` with bare typ.
    // Lean renders the binder as `Tactus.MutRef Int` (via
    // param_binder_typ wrapping based on is_mut), and the body
    // shadow strips back to `Int`. BinderCtx records the
    // post-shadow `Int` (count 0).
    let int = typ_int();
    let params: Params = Arc::new(vec![mk_param("p", int, true)]);
    let ctx = binder_ctx_from_params(&params);
    let recorded = ctx.get(&mk_var_ident("p")).expect("p should be in ctx");
    assert_eq!(count_ref_decorations(recorded), 0);
}

#[test]
fn binder_ctx_new_mode_mut_ref_param_strips_one() {
    // New-mode `&mut x: Int` arrives as `TypX::MutRef(Int)`,
    // `is_mut: false`. Lean renders as `Tactus.MutRef Int`;
    // shadow strips one layer → BinderCtx records `Int` (count 0).
    let int = typ_int();
    let m = typ_mut_ref(int);
    assert_eq!(count_ref_decorations(&m), 1);
    let params: Params = Arc::new(vec![mk_param("p", m, false)]);
    let ctx = binder_ctx_from_params(&params);
    let recorded = ctx.get(&mk_var_ident("p")).expect("p should be in ctx");
    assert_eq!(count_ref_decorations(recorded), 0);
}

#[test]
fn binder_ctx_mixed_params_strips_only_mut() {
    // Three params: `&Int` (not shadowed), legacy `&mut Int`
    // (shadowed, bare typ → still bare), new-mode `MutRef<Int>`
    // (shadowed, MutRef → bare). Verify each is recorded
    // correctly.
    let int = typ_int();
    let r = typ_ref(int.clone());
    let m_new = typ_mut_ref(int.clone());
    let params: Params = Arc::new(vec![
        mk_param("a", r, false),                  // &-only
        mk_param("b", int.clone(), true),         // legacy &mut
        mk_param("c", m_new, false),              // new-mode MutRef
    ]);
    let ctx = binder_ctx_from_params(&params);
    assert_eq!(count_ref_decorations(ctx.get(&mk_var_ident("a")).unwrap()), 1);
    assert_eq!(count_ref_decorations(ctx.get(&mk_var_ident("b")).unwrap()), 0);
    assert_eq!(count_ref_decorations(ctx.get(&mk_var_ident("c")).unwrap()), 0);
}
