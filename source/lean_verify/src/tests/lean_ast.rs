//! Unit tests for `lean_ast` — extracted to `src/tests/` (a `#[path]`'d
//! `mod substitute_tests` child of `lean_ast`, so `use super::*` reaches private items).

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
            rust_span: None,
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
        rust_span: None,
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

// ── ScopeKind / scope_kind() coverage (#98 follow-up) ────────────

/// Direct test of `ExprNode::scope_kind()` — locks in the
/// categorization of every variant. If a future contributor
/// accidentally puts a binder into `ScopeKind::Other` (the one
/// way the structural lock could still be circumvented — by
/// positively lying about scope semantics), this test catches
/// it for the existing variants. New variants compile-error in
/// scope_kind() until categorized; this test then guards their
/// stated category against later edits.
#[test]
fn scope_kind_categorizes_each_variant() {
    // Var → ScopeKind::Var
    assert!(matches!(
        var("x").node.scope_kind(),
        ScopeKind::Var(_)
    ), "Var should be ScopeKind::Var");

        // Let → ScopeKind::Let
        assert!(matches!(
            let_bind("x", lit(1), var("x")).node.scope_kind(),
        ScopeKind::Let { .. }
    ), "Let should be ScopeKind::Let");

    // Lambda → ScopeKind::Quantified { kind: Lambda }
    match lambda("x", var("x")).node.scope_kind() {
        ScopeKind::Quantified { kind: QuantifierKind::Lambda, .. } => {}
        other => panic!("Lambda should be Quantified Lambda; got {:?}",
            std::mem::discriminant(&other)),
    }

    // Forall → ScopeKind::Quantified { kind: Forall }
    match forall("x", var("x")).node.scope_kind() {
        ScopeKind::Quantified { kind: QuantifierKind::Forall, .. } => {}
        other => panic!("Forall should be Quantified Forall; got {:?}",
            std::mem::discriminant(&other)),
    }

    // Exists → ScopeKind::Quantified { kind: Exists }
    match exists("x", var("x")).node.scope_kind() {
        ScopeKind::Quantified { kind: QuantifierKind::Exists, .. } => {}
        other => panic!("Exists should be Quantified Exists; got {:?}",
            std::mem::discriminant(&other)),
    }

    // Match → ScopeKind::Match
    let match_e = Expr::new(ExprNode::Match {
        scrutinee: Box::new(var("x")),
        arms: vec![],
    });
    assert!(matches!(
        match_e.node.scope_kind(),
        ScopeKind::Match { .. }
    ), "Match should be ScopeKind::Match");

    // All non-binder variants → ScopeKind::Other
    let non_binders: Vec<Expr> = vec![
        lit(1),
        Expr::new(ExprNode::LitBool(true)),
        Expr::new(ExprNode::LitStr("s".into())),
        Expr::new(ExprNode::LitChar('a')),
        Expr::new(ExprNode::Raw("r".into())),
            add(var("a"), var("b")),
        Expr::new(ExprNode::UnOp { op: UnOp::Not, arg: Box::new(var("p")) }),
        Expr::new(ExprNode::App {
            head: Box::new(var("f")),
            args: vec![var("x")],
        }),
        Expr::new(ExprNode::If {
            cond: Box::new(var("c")),
            then_: Box::new(lit(1)),
            else_: None,
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
            updates: vec![],
        }),
        Expr::new(ExprNode::ArrayLit(vec![])),
        Expr::new(ExprNode::Index {
            base: Box::new(var("a")),
            idx: Box::new(lit(0)),
            bang: false,
        }),
        Expr::new(ExprNode::Anon(vec![])),
        Expr::new(ExprNode::SpanMark {
            rust_loc: "loc".into(),
            rust_span: None,
            kind: AssertKind::Hypothesis(HypothesisKind::BranchCondition),
            inner: Box::new(var("x")),
        }),
    ];
    for e in &non_binders {
        assert!(matches!(e.node.scope_kind(), ScopeKind::Other),
            "expected ScopeKind::Other for {:?}", e.node);
    }
}

/// `QuantifierKind::build` rebuilds the right `ExprNode` constructor.
/// Indirectly tested via substitute on Lambda/Forall/Exists, but a
/// direct test pins the dispatch contract.
#[test]
fn quantifier_kind_build_dispatches_correctly() {
    let binder = vec![Binder {
        name: Some(LeanName::lit("x")),
        ty: var("Int"),
        kind: BinderKind::Explicit,
    }];
    let body = Box::new(var("x"));

    let lam = QuantifierKind::Lambda.build(binder.clone(), body.clone());
    assert!(matches!(lam, ExprNode::Lambda { .. }));
    let fa = QuantifierKind::Forall.build(binder.clone(), body.clone());
    assert!(matches!(fa, ExprNode::Forall { .. }));
    let ex = QuantifierKind::Exists.build(binder, body);
    assert!(matches!(ex, ExprNode::Exists { .. }));
}

// ── Pattern::Binding behavior coverage ───────────────────────────

/// `Pattern::Binding { name, sub }` introduces a name that scopes
/// over the arm body. `match_arm_pattern_shadows` covers
/// `Pattern::Var` and `Pattern::Ctor`; this test pins
/// `Pattern::Binding` shadowing in substitute.
#[test]
fn match_arm_binding_pattern_shadows() {
    // match scrut with | b @ Some(x) => b
    //   with {b: lit(99), x: lit(42)}
    //   Both b and x are pattern-bound, so substitution should
    //   leave the body's `b` alone.
    let e = Expr::new(ExprNode::Match {
        scrutinee: Box::new(var("scrut")),
        arms: vec![MatchArm {
            pattern: Pattern::Binding {
                name: LeanName::lit("b"),
                sub: Box::new(Pattern::Ctor {
                    name: "Some".into(),
                    args: vec![Pattern::Var(LeanName::lit("x"))],
                }),
            },
            body: var("b"),
        }],
    });
    let s = subst_of(&[("b", lit(99)), ("x", lit(42))]);
    let out = substitute(&e, &s);
    let printed = crate::lean_pp::pp_expr(&out);
    // `b` is pattern-bound by Pattern::Binding, so the body's `b`
    // should NOT be substituted to 99.
    assert!(!printed.contains("=> 99"),
        "b should NOT be substituted (Pattern::Binding shadows): {}", printed);
    assert!(printed.contains("=> b"),
        "body should still read `b`: {}", printed);
}

/// `Pattern::Binding`'s name should rename when it would capture
/// a free var of the substitution. Pinned to lock alpha-rename
/// behavior on Pattern::Binding (rename_in_pattern's Binding arm
/// + pattern_bound_names treating the name as bound).
#[test]
fn capture_alpha_renames_match_binding_pattern() {
    // match scrut with | b @ _ => b + y
    //   with {y: var("b")}  — the substitution would capture
    //   the pattern-bound `b`, so the binding gets alpha-renamed.
    let e = Expr::new(ExprNode::Match {
        scrutinee: Box::new(var("scrut")),
        arms: vec![MatchArm {
            pattern: Pattern::Binding {
                name: LeanName::lit("b"),
                sub: Box::new(Pattern::Wildcard),
            },
            body: add(var("b"), var("y")),
        }],
    });
    let s = subst_of(&[("y", var("b"))]);
    let result = substitute(&e, &s);
    let printed = crate::lean_pp::pp_expr(&result);
    // The `b` binding renames; substituted-y becomes free `b`.
    assert!(printed.contains("b_α"),
        "Pattern::Binding `b` should alpha-rename: {}", printed);
    // The substituted free `b` (from y → b) survives unrenamed.
    assert!(mentions_free_var(&result, "b"),
        "free b (substituted from y) should remain: {}", printed);
}

// ── SpanMark preservation through substitute ─────────────────────

/// Substitute on a `SpanMark` should preserve `rust_loc` and
/// `kind` while substituting through `inner`. After the #98
/// refactor, SpanMark falls into the `ScopeKind::Other` →
/// `map_children` arm; this test pins that the metadata
/// survives the round-trip.
#[test]
fn substitute_preserves_span_mark_metadata() {
    let inner = var("x");
    let span_mark = Expr::new(ExprNode::SpanMark {
        rust_loc: "test.rs:42:7".into(),
        rust_span: None,
        kind: AssertKind::Obligation(ObligationKind::Plain),
        inner: Box::new(inner),
    });
    let s = subst_of(&[("x", lit(99))]);
    let out = substitute(&span_mark, &s);

    match &out.node {
        ExprNode::SpanMark { rust_loc, rust_span: _, kind, inner } => {
            assert_eq!(rust_loc, "test.rs:42:7", "rust_loc preserved");
            assert!(matches!(kind, AssertKind::Obligation(ObligationKind::Plain)),
                "kind preserved");
            // Inner should now be 99 (substituted from x).
            assert!(matches!(&inner.node, ExprNode::Lit(s) if s == "99"),
                "inner substituted: {:?}", inner.node);
        }
        other => panic!("expected SpanMark, got {:?}", other),
    }
}
