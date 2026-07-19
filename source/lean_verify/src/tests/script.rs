//! Unit tests for the N3-M2 script author (script.rs).

use super::*;
use crate::lean_ast::{BinOp, GoalShape, GoalSpine};
use crate::lean_name::LeanName;

fn var(s: &str) -> Expr {
    Expr::new(ExprNode::Var(LeanName::lit(s)))
}
fn app(f: &str, args: Vec<Expr>) -> Expr {
    Expr::new(ExprNode::App { head: Box::new(var(f)), args })
}
fn bin(op: BinOp, l: Expr, r: Expr) -> Expr {
    Expr::new(ExprNode::BinOp { op, lhs: Box::new(l), rhs: Box::new(r) })
}
fn binder(name: &str, ty: Expr) -> Binder {
    Binder { name: Some(LeanName::lit(name)), ty, kind: crate::lean_ast::BinderKind::Explicit }
}
fn all(b: Binder, prov: Option<HypProvenance>) -> GoalSpine {
    GoalSpine::All(b, prov)
}

fn pmul_inventory() -> DtDefInventory {
    DtDefInventory {
        spec_fns: ["lib.poly.coeff".to_string()].into_iter().collect(),
        recursive_spec_fns: ["lib.poly.pmul".to_string()].into_iter().collect(),
        ..Default::default()
    }
}

#[test]
fn form_b_script_for_recursive_lhs_head() {
    // ⊢ pmul p q = rhs, with a CallFact hyp visible — the author must
    // emit the one-step rw, the named guard simp, and the Defeq-first
    // close; census script:formB.
    let goal = bin(
        BinOp::Eq,
        app("lib.poly.pmul", vec![var("p"), var("q")]),
        app("lib.poly.padd", vec![var("s"), var("h")]),
    );
    let shape = GoalShape {
        spine: vec![
            all(binder("T", var("Type")), None),
            all(
                binder("_h_hoist_1", var("some_fact_prop")),
                Some(HypProvenance::AssertFact),
            ),
        ],
        leaf: goal.clone(),
    };
    let (moves, form) = author_v1(&goal, &shape, &pmul_inventory(), &[]).expect("form B applies");
    assert_eq!(form, ScriptForm::B);
    let text = render_script(&moves);
    assert!(text.contains("rw [lib.poly.pmul]"), "{text}");
    assert!(text.contains("_h_hoist_1"), "{text}");
    assert!(text.contains("first | (rfl) |"), "{text}");
    assert_eq!(form.census().as_str(), "script:formB");
}

#[test]
fn form_a_script_with_call_fact_and_hoists() {
    // ⊢ eqv (coeff empty i) zero — the probe's shape: a hoist-eq and a
    // CallFact hyp; the author emits subst + unfold + split.
    let zero = "lib.traits.additive_commutative_monoid.AdditiveCommutativeMonoid.zero";
    let goal = app(
        "lib.traits.equivalence.Equivalence.eqv",
        vec![app("lib.poly.coeff", vec![var("e"), var("i")]), var(zero)],
    );
    let hoist_prop = bin(BinOp::Eq, var("tmp__1"), var(zero));
    let shape = GoalShape {
        spine: vec![
            all(binder("T", var("Type")), None),
            all(
                binder("_h_tmp__1_hoist1", hoist_prop),
                Some(HypProvenance::HoistEq { binder: LeanName::lit("tmp__1") }),
            ),
            all(
                binder("_h_hoist_3", var("call_fact_prop")),
                Some(HypProvenance::CallFact(crate::lean_ast::CallFactInfo {
                    callee: "lib.some_axiom".to_string(),
                    is_self: false,
                    args: vec![],
                    ensures_summary: vec![],
                })),
            ),
        ],
        leaf: goal.clone(),
    };
    let (moves, form) = author_v1(&goal, &shape, &pmul_inventory(), &[]).expect("form A applies");
    assert_eq!(form, ScriptForm::A);
    let text = render_script(&moves);
    assert!(text.contains("subst _h_tmp__1_hoist1"), "{text}");
    assert!(text.contains("simp only [lib.poly.coeff]"), "{text}");
    assert!(text.contains("split <;> (first |"), "{text}");
    assert_eq!(form.census().as_str(), "script:formA");
}

#[test]
fn exact_hyp_when_texts_match_after_substs() {
    // The hyp `_h_hoist_3 : eqv tmp__1 tmp__1` with `tmp__1 := zero`
    // — after substs its text equals the goal `eqv zero zero`: the
    // author adds ExactHyp to the legs.
    let zero = "z.zero";
    let goal = app("z.eqv", vec![var(zero), var(zero)]);
    let hoist_prop = bin(BinOp::Eq, var("tmp__1"), var(zero));
    let fact_prop = app("z.eqv", vec![var("tmp__1"), var("tmp__1")]);
    let shape = GoalShape {
        spine: vec![
            all(
                binder("_h_tmp__1_hoist1", hoist_prop),
                Some(HypProvenance::HoistEq { binder: LeanName::lit("tmp__1") }),
            ),
            all(binder("_h_hoist_3", fact_prop), Some(HypProvenance::AssertFact)),
        ],
        leaf: goal.clone(),
    };
    let dts = DtDefInventory {
        spec_fns: ["z.eqv".to_string()].into_iter().collect(),
        ..Default::default()
    };
    let (moves, form) = author_v1(&goal, &shape, &dts, &[]).expect("form A applies");
    assert_eq!(form, ScriptForm::A);
    let text = render_script(&moves);
    assert!(text.contains("exact _h_hoist_3"), "{text}");
}

#[test]
fn no_script_without_unfolds_or_facts() {
    // A bare equation: no spec fns, no facts — the author declines,
    // the caller falls to the derived chain.
    let goal = bin(BinOp::Eq, var("x"), var("y"));
    let shape = GoalShape { spine: vec![], leaf: goal.clone() };
    assert!(author_v1(&goal, &shape, &pmul_inventory(), &[]).is_none());
}

#[test]
fn render_is_valid_lean_shapes() {
    // Empty GuardSimp / StructuralTail render without dangling commas.
    let moves = vec![
        Move::GuardSimp(vec![]),
        Move::StructuralTail(vec![], vec!["-_tactus_bc_8".to_string()]),
        Move::FirstOf(vec![Move::Defeq, Move::LeafClose]),
        Move::SplitIf(vec![Move::LeafClose, Move::ExactHyp("h1".to_string())]),
    ];
    let text = render_script(&moves);
    assert!(text.contains("simp only [if_true"), "{text}");
    assert!(!text.contains(", ]"), "{text}");
    assert!(!text.contains("[, "), "{text}");
    assert!(text.contains("first | (rfl) | (first | assumption | omega | with_reducible rfl)"), "{text}");
    assert!(text.contains("split <;> (first | (first | assumption | omega | with_reducible rfl) | (exact h1))"), "{text}");
}
