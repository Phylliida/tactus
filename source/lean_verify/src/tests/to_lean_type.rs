//! Unit tests for `to_lean_type` — extracted to `src/tests/` (a `#[path]`'d
//! `mod tests` child of `to_lean_type`, so `use super::*` reaches private items).

use super::*;
use crate::lean_pp::pp_expr;
use std::sync::Arc;

fn render(t: &TypX) -> String { pp_expr(&typ_to_expr(t)) }

#[test]
fn test_basic_types() {
    assert_eq!(render(&TypX::Bool), "Prop");
    assert_eq!(render(&TypX::Int(IntRange::Int)), "Int");
    assert_eq!(render(&TypX::Int(IntRange::Nat)), "Nat");
    assert_eq!(render(&TypX::Int(IntRange::U(32))), "Int");
    assert_eq!(render(&TypX::Int(IntRange::I(64))), "Int");
}

#[test]
fn test_type_param() {
    assert_eq!(render(&TypX::TypParam(Arc::new("T".into()))), "T");
}

#[test]
fn test_boxed_transparent() {
    assert_eq!(render(&TypX::Boxed(Arc::new(TypX::Int(IntRange::Nat)))), "Nat");
}

// ── is_unit_typ shape-drift guards ─────────────────────────────

/// After `ast_simplify`, Verus represents the unit type `()` as
/// `TypX::Datatype(Dt::Tuple(0), [], _)`. `is_unit_typ` is used in
/// two places (proof_fn_method_type emission dispatch, dep_order
/// pre-seeding) — both rely on this exact shape. If Verus ever
/// changes how the post-simplify unit type is represented, this
/// test fails with a clear pointer to `is_unit_typ` as the fix
/// site.
#[test]
fn is_unit_typ_recognizes_post_simplify_unit() {
    let unit = TypX::Datatype(
        Dt::Tuple(0),
        Arc::new(vec![]),
        Arc::new(vec![]),
    );
    assert!(is_unit_typ(&unit),
        "Verus's post-simplify unit shape changed; update is_unit_typ");
}

#[test]
fn is_unit_typ_rejects_non_unit_types() {
    assert!(!is_unit_typ(&TypX::Bool));
    assert!(!is_unit_typ(&TypX::Int(IntRange::Int)));
    // Non-zero tuple: NOT unit.
    let pair = TypX::Datatype(
        Dt::Tuple(2),
        Arc::new(vec![Arc::new(TypX::Bool), Arc::new(TypX::Bool)]),
        Arc::new(vec![]),
    );
    assert!(!is_unit_typ(&pair));
}

#[test]
fn test_spec_fn_type() {
    let t = TypX::SpecFn(
        Arc::new(vec![Arc::new(TypX::Int(IntRange::Nat))]),
        Arc::new(TypX::Int(IntRange::Nat)),
    );
    assert_eq!(render(&t), "Nat → Nat");
}
