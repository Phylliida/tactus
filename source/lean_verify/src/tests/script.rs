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
    assert!(text.contains("simp only [lib.poly.coeff] at ⊢"), "{text}");
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
    let (moves, form) = author_v1(&goal, &shape, &dts, &[]).expect("a script applies");
    // The exact-hyp match fires as form C (the better classification).
    assert_eq!(form, ScriptForm::C);
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

#[test]
fn form_c_exact_hyp_from_antecedent_chain() {
    // The 159:13 shape: ∀ ret, peqv tmp15 tmp17 → peqv (pmul (push p c) q) (padd ...)
    // with lets binding tmp15/tmp17 to exactly those polynomials. The
    // script: intro, intro+subst, exact the last antecedent.
    let lhs = app("lib.poly.pmul", vec![var("T"), app("lib.seq.Seq.push", vec![var("T"), var("p"), var("c")]), var("q")]);
    let rhs = app("lib.poly.padd", vec![var("T"), var("x"), var("y")]);
    let eq_goal = app("lib.poly.peqv", vec![var("T"), lhs.clone(), rhs.clone()]);
    // Goal: (let tmp15 := lhs; let tmp17 := rhs; peqv tmp15 tmp17 → eq_goal)
    let fact = app("lib.poly.peqv", vec![var("T"), var("tmp15"), var("tmp17")]);
    let goal = Expr::new(ExprNode::Let {
        name: LeanName::lit("tmp15"),
        value: Box::new(lhs),
        body: Box::new(Expr::new(ExprNode::Let {
            name: LeanName::lit("tmp17"),
            value: Box::new(rhs),
            body: Box::new(bin(BinOp::Implies, fact, eq_goal)),
        })),
    });
    let shape = GoalShape { spine: vec![], leaf: goal.clone() };
    let dts = DtDefInventory {
        spec_fns: ["lib.poly.peqv".to_string()].into_iter().collect(),
        recursive_spec_fns: ["lib.poly.pmul".to_string()].into_iter().collect(),
        ..Default::default()
    };
    let (moves, form) = author_v1(&goal, &shape, &dts, &[]).expect("form C applies");
    assert_eq!(form, ScriptForm::C);
    let text = render_script(&moves);
    assert!(text.contains("exact h_scr_0"), "{text}");
    assert!(text.contains("subst tmp15"), "{text}");
    assert_eq!(form.census().as_str(), "script:formC");
}

#[test]
fn form_c_refine_exact_for_conjunction() {
    // The 853:9 shape (N1 path): goal `peqv tmp9 tmp10 ∧ peqv tmp10 tmp11`
    // with hoist-eq binders and matching CallFact hyps in the shape.
    let conj = bin(
        BinOp::And,
        app("lib.poly.peqv", vec![var("T"), var("tmp9"), var("tmp10")]),
        app("lib.poly.peqv", vec![var("T"), var("tmp10"), var("tmp11")]),
    );
    let p9 = app("lib.poly.pmul", vec![var("T"), var("q"), var("p")]);
    let p10 = app("lib.poly.padd", vec![var("T"), var("a"), var("b")]);
    let fact1 = app("lib.poly.peqv", vec![var("T"), p9.clone(), p10.clone()]);
    let fact2 = app("lib.poly.peqv", vec![var("T"), p10.clone(), var("c")]);
    let hoist = |n: &str, v: Expr| all(
        binder(&format!("_h_{}_hoist1", n), bin(BinOp::Eq, var(n), v)),
        Some(HypProvenance::HoistEq { binder: LeanName::lit(n) }),
    );
    let call = |p: Expr, n: &str| all(
        binder(n, p),
        Some(HypProvenance::CallFact(crate::lean_ast::CallFactInfo {
            callee: "lib.lemma".to_string(),
            is_self: false,
            args: vec![],
            ensures_summary: vec![],
        })),
    );
    // goal conjuncts: peqv tmp9 tmp10, peqv tmp10 c — after substs
    // (tmp9 := pmul q p, tmp10 := padd a b) they equal fact1, fact2.
    let goal = bin(
        BinOp::And,
        app("lib.poly.peqv", vec![var("T"), var("tmp9"), var("tmp10")]),
        app("lib.poly.peqv", vec![var("T"), var("tmp10"), var("c")]),
    );
    let shape = GoalShape {
        spine: vec![
            hoist("tmp9", p9),
            hoist("tmp10", p10),
            call(fact1, "_h_hoist_1"),
            call(fact2, "_h_hoist_2"),
        ],
        leaf: goal.clone(),
    };
    let dts = DtDefInventory {
        spec_fns: ["lib.poly.peqv".to_string()].into_iter().collect(),
        ..Default::default()
    };
    let (moves, form) = author_v1(&goal, &shape, &dts, &[]).expect("form C applies");
    assert_eq!(form, ScriptForm::C);
    let text = render_script(&moves);
    assert!(text.contains("refine ⟨_h_hoist_1, _h_hoist_2⟩"), "{text}");
    assert!(text.contains("subst _h_tmp9_hoist1"), "{text}");
    let _ = conj;
}
