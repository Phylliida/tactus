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
fn nullary_spec_fn_bare_var_rejected_regression() {
    // `test_crate.pair = test_crate.pair` — a nullary spec fn renders
    // as a BARE Var (not an App). It is NOT a local integer, so the
    // equality must fall out of the fragment (the goal wants rfl, not
    // omega). Regression exposed by the bootstrap package-check path,
    // which emits this obligation as `theorem := by <closer>` that S1
    // classifies (the islands path emitted a Prop def selection never
    // saw). Pre-fix, frag_term admitted any bare Var as an int atom.
    let goal = bin(BinOp::Eq, var("test_crate.pair"), var("test_crate.pair"));
    // Even with an unrelated Int binder in scope (the real failing
    // case was `noop(v: u8)`), the global must not be admitted.
    assert_eq!(select_deterministic(&goal, &[binder("v", var("Int"))]), None);
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

#[test]
fn derived_closer_is_search_free_and_census_exact() {
    // S2c's derived default closer (§3.4) + B4's explicit peel (§4):
    // no search tactic named, kernel rungs + generated intro/refine
    // prefix + fixed CORE set + omega tail.
    let goal = bin(BinOp::Eq, var("x"), var("y"));
    let derived = derived_closer(&goal, &Default::default(), &[], false, &[], 0, None);
    assert!(!derived.contains("tactus_auto"));
    assert!(!derived.contains("case_split"));
    assert!(!derived.contains("tactus_first"));
    assert!(!derived.contains("tactus_peel"));
    // Equation-core goal → bare rfl kernel (defeq closes one-step
    // unfold lemmas); non-equation core → with_reducible rfl (full
    // delta on arith goals with stuck matches hits uncatchable
    // maxRecDepth). Shape-derived, see goal_core_is_equation.
    assert!(derived.starts_with("first | rfl | decide | omega | ("));
    // No goal-mentioned spec fns here, so no form E arm: the chain
    // ends with the structural rung (no eliminators registered).
    assert!(derived.ends_with("] <;> omega)"));
    // A flat goal has no structure to peel: the kernel branch is just
    // the leaf ladder.
    assert!(derived.contains("first | rfl | decide | omega"));
    let goal_le = bin(BinOp::Le, var("x"), var("y"));
    let derived_le = derived_closer(&goal_le, &Default::default(), &[], false, &[], 0, None);
    assert!(derived_le.starts_with("first | with_reducible rfl | decide | omega | ("));
    // The CORE set is the census union + extensions: 51 lemmas (50 separators).
    assert_eq!(CORE_LEMMAS.matches(", ").count(), 50);
    // Mathlib-context name hygiene: bare `not_imp` is ambiguous with
    // `_root_.not_imp`; the qualified form is mandatory.
    assert!(CORE_LEMMAS.contains("Classical.not_imp"));
    assert!(!CORE_LEMMAS.contains(", not_imp,"));
}

#[test]
fn unfold_once_arm_for_recursive_lhs_head() {
    // N3 form B (probe pmul_conv.lean): ⊢ pmul p q = rhs — the LHS
    // head is a RECURSIVE spec fn, so the derived closer gains the
    // one-step `rw [pmul]` arm (recursive fns never ride simp sets).
    let app = |f: &str, args: Vec<Expr>| Expr::new(ExprNode::App {
        head: Box::new(var(f)),
        args,
    });
    let goal = bin(
        BinOp::Eq,
        app("lib.poly.pmul", vec![var("p"), var("q")]),
        app("lib.poly.padd", vec![var("s"), var("t")]),
    );
    let dts = DtDefInventory {
        recursive_spec_fns: ["lib.poly.pmul".to_string()].into_iter().collect(),
        ..Default::default()
    };
    let derived = derived_closer(&goal, &dts, &[], false, &[], 0, None);
    assert!(derived.contains("rw [lib.poly.pmul]"), "{derived}");
    assert!(derived.contains("simp_all only [if_true, if_false, reduceIte, reduceCtorEq, Nat.succ_ne_zero"), "{derived}");
    // The arm is one measured step followed by kernel/ladder closes.
    assert!(derived.contains("; first | rfl | ("), "{derived}");
}

#[test]
fn no_unfold_once_arm_for_nonrecursive_or_rhs_heads() {
    let app = |f: &str, args: Vec<Expr>| Expr::new(ExprNode::App {
        head: Box::new(var(f)),
        args,
    });
    let dts = DtDefInventory {
        recursive_spec_fns: ["lib.poly.pmul".to_string()].into_iter().collect(),
        ..Default::default()
    };
    // Non-recursive LHS head: no rw arm.
    let goal_coeff = bin(
        BinOp::Eq,
        app("lib.poly.coeff", vec![var("p"), var("i")]),
        var("z"),
    );
    let derived = derived_closer(&goal_coeff, &dts, &[], false, &[], 0, None);
    assert!(!derived.contains("rw ["), "{derived}");
    // Recursive fn present but only on the RHS: no rw arm (first-match
    // discipline keeps the rewrite to exactly the LHS head).
    let goal_rhs = bin(
        BinOp::Eq,
        var("z"),
        app("lib.poly.pmul", vec![var("p"), var("q")]),
    );
    let derived = derived_closer(&goal_rhs, &dts, &[], false, &[], 0, None);
    assert!(!derived.contains("rw ["), "{derived}");
}

#[test]
fn unfold_once_arm_looks_through_n1_let_wrapper() {
    // N1 shape (probe pmul_conv.lean): ⊢ let t := s; (let tmp := (pmul t e = rhs); tmp)
    // — the Eq core hides behind the trailing wrapper. The wrapper is
    // NOT intro'd (rw searches through the goal-position let), but the
    // outer let is.
    let app = |f: &str, args: Vec<Expr>| Expr::new(ExprNode::App {
        head: Box::new(var(f)),
        args,
    });
    let eq = bin(
        BinOp::Eq,
        app("lib.poly.pmul", vec![var("t"), var("e")]),
        app("lib.poly.padd", vec![var("s"), var("h")]),
    );
    // The wrapper's body var arrives SpanMark-wrapped on real
    // (rust-annotated) goals — the detection must look through it.
    let spanned_tmp = Expr::new(ExprNode::SpanMark {
        rust_loc: "poly_ring.rs:1:1".to_string(),
        rust_span: None,
        kind: crate::lean_ast::AssertKind::Obligation(crate::lean_ast::ObligationKind::Plain),
        inner: Box::new(var("tmp")),
    });
    let wrapper = Expr::new(ExprNode::Let {
        name: LeanName::lit("tmp"),
        value: Box::new(eq),
        body: Box::new(spanned_tmp),
    });
    let goal = Expr::new(ExprNode::Let {
        name: LeanName::lit("t"),
        value: Box::new(var("s")),
        body: Box::new(wrapper),
    });
    let dts = DtDefInventory {
        recursive_spec_fns: ["lib.poly.pmul".to_string()].into_iter().collect(),
        ..Default::default()
    };
    let derived = derived_closer(&goal, &dts, &[], false, &[], 2, None);
    assert!(derived.contains("intro t; subst t; rw [lib.poly.pmul]"), "{derived}");
    // The wrapper is never intro'd BEFORE the rw in the UnfoldOnce arm
    // (the structural rung's own `intro t tmp` is its own business —
    // it closes by simp, not by rewriting through the wrapper).
    assert!(!derived.contains("intro t tmp; rw ["), "{derived}");
    // The guard simp excludes every broadcast have (the ext axioms
    // would otherwise explode the goal's Seq equality) — and only
    // those; the goal's own hyps stay usable.
    assert!(derived.contains("-_tactus_bc_0"), "{derived}");
    assert!(derived.contains("-_tactus_bc_1"), "{derived}");
    assert!(!derived.contains("-_tactus_bc_2"), "{derived}");
}

#[test]
fn form_e_arm_is_two_phase() {
    // Form E (probe zpoly_generic.lean): a targeted unfold of the
    // goal-mentioned fns as phase 1 (NO CORE — it leaves residuals the
    // split can't close), then the guarded split. The two phases are
    // ONE arm: as a bare chain arm `split` never sees the ite guards
    // hidden inside unfolded spec fns.
    let app = |f: &str, args: Vec<Expr>| Expr::new(ExprNode::App {
        head: Box::new(var(f)),
        args,
    });
    let goal = bin(
        BinOp::Eq,
        app("lib.poly.coeff", vec![var("p"), var("i")]),
        var("z"),
    );
    let dts = DtDefInventory {
        spec_fns: ["lib.poly.coeff".to_string()].into_iter().collect(),
        ..Default::default()
    };
    let derived = derived_closer(&goal, &dts, &[], false, &[], 0, None);
    let expected = format!(
        " | (simp_all only [lib.poly.coeff]; first | omega | (split <;> simp_all only [{}] <;> omega) | (split <;> simp_all only [{}]))",
        crate::tactic_select::LEG_SIMP_LEMMAS,
        crate::tactic_select::LEG_SIMP_LEMMAS,
    );
    assert!(derived.contains(&expected), "{derived}");
    // No goal-mentioned unfolds → no form E arm at all.
    let bare = derived_closer(&bin(BinOp::Eq, var("x"), var("y")), &Default::default(), &[], false, &[], 0, None);
    assert!(!bare.contains("split"), "{bare}");
}

#[test]
fn peel_flat_goal_is_leaf() {
    // No structure: the peel is exactly the leaf tactic.
    let goal = bin(BinOp::Eq, var("x"), var("y"));
    assert_eq!(render_peel(&goal, "LEAF"), "LEAF");
}

#[test]
fn peel_forall_and_implies_intros() {
    // ⊢ ∀ (j : Nat), P j → Q j  ⇒  intro _; intro _; LEAF
    let inner = bin(
        BinOp::Implies,
        bin(BinOp::Le, var("j"), lit("3")),
        bin(BinOp::Le, var("j"), lit("5")),
    );
    let goal = Expr::new(ExprNode::Forall {
        binders: vec![binder("j", var("Nat"))],
        body: Box::new(inner),
    });
    assert_eq!(render_peel(&goal, "LEAF"), "intro _; intro _; LEAF");
}

#[test]
fn peel_destructures_conjunction_hypotheses() {
    // ⊢ (P ∧ Q) → R  ⇒  intro ⟨_, _⟩; LEAF
    let goal = bin(
        BinOp::Implies,
        bin(BinOp::And, var("P"), var("Q")),
        var("R"),
    );
    assert_eq!(render_peel(&goal, "LEAF"), "intro ⟨_, _⟩; LEAF");
}

#[test]
fn peel_conjunction_refine_mirrors_tree() {
    // ⊢ (A ∧ B) ∧ C  ⇒  refine ⟨⟨by LEAF, by LEAF⟩, by LEAF⟩
    // (explicit nesting — flattening picks the right-nested reading)
    let goal = bin(
        BinOp::And,
        bin(BinOp::And, var("A"), var("B")),
        var("C"),
    );
    assert_eq!(
        render_peel(&goal, "LEAF"),
        "refine ⟨⟨by LEAF, by LEAF⟩, by LEAF⟩"
    );
}

#[test]
fn peel_right_nested_conjunction() {
    // ⊢ A ∧ (B ∧ C)  ⇒  refine ⟨by LEAF, ⟨by LEAF, by LEAF⟩⟩
    let goal = bin(
        BinOp::And,
        var("A"),
        bin(BinOp::And, var("B"), var("C")),
    );
    assert_eq!(
        render_peel(&goal, "LEAF"),
        "refine ⟨by LEAF, ⟨by LEAF, by LEAF⟩⟩"
    );
}

#[test]
fn peel_mixed_wrappers() {
    // ⊢ ∀ (x : Int), (P ∧ Q) → (A ∧ B)  ⇒
    //   intro _; intro ⟨_, _⟩; refine ⟨by LEAF, by LEAF⟩
    let goal = Expr::new(ExprNode::Forall {
        binders: vec![binder("x", var("Int"))],
        body: Box::new(bin(
            BinOp::Implies,
            bin(BinOp::And, var("P"), var("Q")),
            bin(BinOp::And, var("A"), var("B")),
        )),
    });
    assert_eq!(
        render_peel(&goal, "LEAF"),
        "intro _; intro ⟨_, _⟩; refine ⟨by LEAF, by LEAF⟩"
    );
}


#[test]
fn census_marks_which_arms_fired() {
    // N3-M0 census (DESIGN-N3 §8): derived_closer records which M1
    // arms it attached, via the out-param.
    let app = |f: &str, args: Vec<Expr>| Expr::new(ExprNode::App {
        head: Box::new(var(f)),
        args,
    });
    let dts = DtDefInventory {
        spec_fns: ["lib.poly.coeff".to_string()].into_iter().collect(),
        recursive_spec_fns: ["lib.poly.pmul".to_string()].into_iter().collect(),
        ..Default::default()
    };
    // Recursive-LHS head + a goal-mentioned spec fn → both arms.
    let goal = bin(
        BinOp::Eq,
        app("lib.poly.pmul", vec![var("p"), var("q")]),
        app("lib.poly.coeff", vec![var("s"), var("i")]),
    );
    let mut c = crate::lean_ast::CloserCensus::RungOnly;
    derived_closer(&goal, &dts, &[], false, &[], 0, Some(&mut c));
    assert_eq!(c, crate::lean_ast::CloserCensus::RungFormBE);
    // No recursive head → form E only.
    let goal2 = bin(BinOp::Eq, app("lib.poly.coeff", vec![var("p"), var("i")]), var("z"));
    let mut c = crate::lean_ast::CloserCensus::RungOnly;
    derived_closer(&goal2, &dts, &[], false, &[], 0, Some(&mut c));
    assert_eq!(c, crate::lean_ast::CloserCensus::RungFormE);
    // Bare goal → plain rung.
    let mut c = crate::lean_ast::CloserCensus::RungFormB;
    derived_closer(&bin(BinOp::Eq, var("x"), var("y")), &dts, &[], false, &[], 0, Some(&mut c));
    assert_eq!(c, crate::lean_ast::CloserCensus::RungOnly);
    // The artifact comment spellings are the fixed N4 format.
    assert_eq!(crate::lean_ast::CloserCensus::RungFormBE.as_str(), "rung:formB+formE");
    assert_eq!(crate::lean_ast::CloserCensus::S1Omega.as_str(), "s1-omega");
}
