//! Unit tests for `to_lean_fn` — extracted to `src/tests/` (a `#[path]`'d
//! `mod tests` child of `to_lean_fn`, so `use super::*` reaches private items).

use super::*;
use crate::test_fixtures::{mk_path, typ_datatype};
use std::collections::HashSet;
use std::sync::Arc;

fn trait_bound(trait_name: &str, arg: &str) -> GenericBound {
    Arc::new(GenericBoundX::Trait(
        TraitId::Path(mk_path(trait_name)),
        Arc::new(vec![typ_datatype(arg)]),
    ))
}

// R-1 (#122): the shared bound→binder chokepoint
// (`trait_bounds_to_ast_with`) drops bounds that reference an
// un-emittable (shell) trait. Centralizing the filter here means
// EVERY bound site — class superclass bounds, instance binders, AND
// fn-level generic bounds (spec/proof fns via `fn_binders`) — is
// covered uniformly. This pins the chokepoint behaviour directly so
// a future caller of the renderer can't silently regress the
// fn-level path (the site the call-site pre-filter missed).
#[test]
fn trait_bounds_to_ast_drops_shell_trait_bounds() {
    let bounds: GenericBounds = Arc::new(vec![
        trait_bound("Clone", "T"),      // shell — should be dropped
        trait_bound("Emittable", "T"),  // ordinary — should survive
    ]);

    // With Clone marked un-emittable: only the Emittable bound survives.
    let mut unemittable: HashSet<Path> = HashSet::new();
    unemittable.insert(mk_path("Clone"));
    let binders = trait_bounds_to_ast(&bounds, &unemittable);
    assert_eq!(binders.len(), 1,
        "the shell-trait bound (Clone) must be dropped at the chokepoint");

    // Empty un-emittable set: nothing dropped (both bounds render).
    let none: HashSet<Path> = HashSet::new();
    let binders = trait_bounds_to_ast(&bounds, &none);
    assert_eq!(binders.len(), 2,
        "no shell traits → no bounds dropped");
}

// ── Statement defs (emit-module Stmts layer, DESIGN-emit-module.md) ────

/// The full binder-kind spread in one statement: implicit type param,
/// anonymous instance bracket, explicit value param, hypothesis binder.
/// Pins the exact `@[reducible] noncomputable def … : Prop := ∀ …`
/// shape the M0 probe validated (finding F2: reducibility is what
/// makes intro/application/link-unification work without `unfold`).
#[test]
fn stmt_cmd_renders_reducible_forall_prop() {
    let binders = vec![
        LBinder::typ_param("A", BinderKind::Implicit),
        LBinder::instance(LExpr::app(
            LExpr::var_lit("Nonempty"),
            vec![LExpr::var_lit("A")],
        )),
        LBinder::explicit(
            crate::lean_name::LeanName::synthetic("x".to_string()),
            LExpr::var_lit("Int"),
        ),
        LBinder::explicit(
            crate::lean_name::LeanName::synthetic("h0".to_string()),
            LExpr::var_lit("True"),
        ),
    ];
    let cmd = stmt_cmd("lemma_a_stmt".to_string(), binders, LExpr::var_lit("True"));
    let out = crate::lean_pp::pp_command(&cmd);
    assert_eq!(
        out,
        "@[reducible] noncomputable def lemma_a_stmt : Prop :=\n  \
         ∀ {A : Type} [Nonempty A] (x : Int) (h0 : True), True\n",
        "statement def shape drifted; got:\n{out}"
    );
}

/// Zero binders: a nullary lemma's statement is the bare ensures —
/// no vacuous `∀ ,` wrapper.
#[test]
fn stmt_cmd_zero_binders_is_bare_goal() {
    let cmd = stmt_cmd("nullary_stmt".to_string(), vec![], LExpr::var_lit("True"));
    let out = crate::lean_pp::pp_command(&cmd);
    assert_eq!(
        out,
        "@[reducible] noncomputable def nullary_stmt : Prop :=\n  True\n",
        "nullary statement shape drifted; got:\n{out}"
    );
}

/// `stmt_name` is the single chokepoint for the `_stmt` naming
/// convention shared by the Stmts renderer, consumer hypothesis
/// binders (M2), and the Link module (M3).
#[test]
fn stmt_name_appends_suffix_to_lean_name() {
    assert_eq!(stmt_name(&mk_path("lemma_a")), "lemma_a_stmt");
}
