//! Unit tests for the deterministic-floor classifier (S1).

use super::*;
use crate::lean_ast::BinderKind;
use crate::lean_name::LeanName;

fn var(s: &str) -> Expr {
    Expr::new(ExprNode::Var(LeanName::lit(s)))
}
fn lit(n: &str) -> Expr {
    Expr::new(ExprNode::Lit(n.to_string()))
}
fn bin(op: BinOp, l: Expr, r: Expr) -> Expr {
    Expr::new(ExprNode::BinOp { op, lhs: Box::new(l), rhs: Box::new(r) })
}
fn binder(name: &str, ty: Expr) -> Binder {
    Binder { name: Some(LeanName::lit(name)), ty, kind: BinderKind::Explicit }
}

#[test]
fn bare_arith_selects_omega() {
    // (i : Nat) (h : i < 10) ⊢ i + 1 ≤ 10
    let goal = bin(BinOp::Le, bin(BinOp::Add, var("i"), lit("1")), lit("10"));
    let binders = vec![
        binder("i", var("Nat")),
        binder("h", bin(BinOp::Lt, var("i"), lit("10"))),
    ];
    assert_eq!(select_deterministic(&goal, &binders), Some(Selection::Omega));
}

#[test]
fn implication_spine_selects_peel_omega() {
    // ⊢ x ≤ 100 → x < 256  (wrapped hypothesis: peel intros, omega closes)
    let goal = bin(
        BinOp::Implies,
        bin(BinOp::Le, var("x"), lit("100")),
        bin(BinOp::Lt, var("x"), lit("256")),
    );
    let binders = vec![binder("x", var("Int"))];
    assert_eq!(select_deterministic(&goal, &binders), Some(Selection::PeelOmega));
}

#[test]
fn forall_and_let_spine_select_peel_omega() {
    // ⊢ ∀ (j : Nat), let k := j + 1; k > j
    let inner = bin(BinOp::Gt, var("k"), var("j"));
    let let_e = Expr::new(ExprNode::Let {
        name: LeanName::lit("k"),
        value: Box::new(bin(BinOp::Add, var("j"), lit("1"))),
        body: Box::new(inner),
    });
    let goal = Expr::new(ExprNode::Forall {
        binders: vec![binder("j", var("Nat"))],
        body: Box::new(let_e),
    });
    assert_eq!(select_deterministic(&goal, &[]), Some(Selection::PeelOmega));
}

#[test]
fn spec_fn_application_rejected() {
    // ⊢ 0 < lib.seq.Seq.len s  — opaque head: not in fragment
    let goal = bin(
        BinOp::Lt,
        lit("0"),
        Expr::new(ExprNode::App {
            head: Box::new(var("lib.seq.Seq.len")),
            args: vec![var("s")],
        }),
    );
    assert_eq!(select_deterministic(&goal, &[]), None);
}

#[test]
fn used_opaque_binder_rejected_unused_ok() {
    // (r : Tactus.Ref T) used in the goal → reject.
    let goal = bin(BinOp::Eq, var("r"), var("r"));
    let binders = vec![binder("r", var("Tactus.Ref"))];
    assert_eq!(select_deterministic(&goal, &binders), None);
    // Same binder present but goal never mentions it → fine.
    let goal2 = bin(BinOp::Lt, var("i"), lit("5"));
    let binders2 = vec![
        binder("r", var("Tactus.Ref")),
        binder("i", var("Nat")),
    ];
    assert_eq!(select_deterministic(&goal2, &binders2), Some(Selection::Omega));
}

#[test]
fn nonlinear_mul_rejected_linear_ok() {
    let xy = bin(BinOp::Mul, var("x"), var("y"));
    let goal = bin(BinOp::Ge, xy, lit("0"));
    let bs = vec![binder("x", var("Int")), binder("y", var("Int"))];
    assert_eq!(select_deterministic(&goal, &bs), None);
    let x2 = bin(BinOp::Mul, var("x"), lit("2"));
    let goal2 = bin(BinOp::Ge, x2, var("x"));
    assert_eq!(
        select_deterministic(&goal2, &bs[..1].to_vec()),
        Some(Selection::Omega)
    );
}

#[test]
fn bool_and_ite_rejected() {
    let goal = bin(BinOp::Eq, var("b"), Expr::new(ExprNode::LitBool(true)));
    assert_eq!(select_deterministic(&goal, &[binder("b", var("Bool"))]), None);
    let ite = Expr::new(ExprNode::If {
        cond: Box::new(bin(BinOp::Lt, var("x"), lit("0"))),
        then_: Box::new(lit("0")),
        else_: Some(Box::new(var("x"))),
    });
    let goal2 = bin(BinOp::Ge, ite, lit("0"));
    assert_eq!(select_deterministic(&goal2, &[binder("x", var("Int"))]), None);
}

#[test]
fn spanmark_transparent_tonat_atom_ok() {
    let inner = bin(
        BinOp::Lt,
        Expr::new(ExprNode::FieldProj {
            expr: Box::new(var("x")),
            field: "toNat".to_string(),
        }),
        lit("10"),
    );
    let goal = LExprSpanMark(inner);
    let bs = vec![binder("x", var("Int"))];
    assert_eq!(select_deterministic(&goal, &bs), Some(Selection::Omega));
}

fn LExprSpanMark(inner: Expr) -> Expr {
    Expr::new(ExprNode::SpanMark {
        rust_loc: "test.rs:1:1".to_string(),
        rust_span: None,
        kind: crate::lean_ast::AssertKind::Obligation(
            crate::lean_ast::ObligationKind::Plain,
        ),
        inner: Box::new(inner),
    })
}

#[test]
fn nested_forall_off_spine_rejected() {
    // ⊢ (∀ j, j ≥ 0) ∧ x > 0 — the ∀ is under ∧, not on the spine:
    // peel can't reach it and omega rejects it.
    let inner_forall = Expr::new(ExprNode::Forall {
        binders: vec![binder("j", var("Nat"))],
        body: Box::new(bin(BinOp::Ge, var("j"), lit("0"))),
    });
    let goal = bin(BinOp::And, inner_forall, bin(BinOp::Gt, var("x"), lit("0")));
    assert_eq!(select_deterministic(&goal, &[binder("x", var("Int"))]), None);
}

#[test]
fn prop_equality_rejected_regression() {
    // let r := x > 0; r = (x > 0) — propositional equality: omega
    // rejects it (rfl closes it). The v1 single-layer walk admitted
    // this (test_exec_loop_cond_with_setup regression).
    let cmp = || bin(BinOp::Gt, var("x"), lit("0"));
    let goal = Expr::new(ExprNode::Let {
        name: LeanName::lit("r"),
        value: Box::new(cmp()),
        body: Box::new(bin(BinOp::Eq, var("r"), cmp())),
    });
    assert_eq!(select_deterministic(&goal, &[binder("x", var("Int"))]), None);
}

#[test]
fn prop_bound_let_var_as_conjunct_ok() {
    // let r := x > 0; r ∧ x < 256 — the bare prop atom is fine (peel
    // substitutes it back), only Eq-operand use is out.
    let goal = Expr::new(ExprNode::Let {
        name: LeanName::lit("r"),
        value: Box::new(bin(BinOp::Gt, var("x"), lit("0"))),
        body: Box::new(bin(
            BinOp::And,
            var("r"),
            bin(BinOp::Lt, var("x"), lit("256")),
        )),
    });
    assert_eq!(
        select_deterministic(&goal, &[binder("x", var("Int"))]),
        Some(Selection::PeelOmega)
    );
}

#[test]
fn term_bound_let_var_in_eq_ok() {
    // let r := x + 1; r = x + 1 — term-layer equality: omega domain.
    let goal = Expr::new(ExprNode::Let {
        name: LeanName::lit("r"),
        value: Box::new(bin(BinOp::Add, var("x"), lit("1"))),
        body: Box::new(bin(BinOp::Eq, var("r"), bin(BinOp::Add, var("x"), lit("1")))),
    });
    assert_eq!(
        select_deterministic(&goal, &[binder("x", var("Int"))]),
        Some(Selection::PeelOmega)
    );
}
