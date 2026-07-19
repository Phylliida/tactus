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

/// Package-mode hypothesis binder (M2): named by the SHORT name (what
/// raw tactic text references — binder shadowing keeps the body
/// unchanged), typed by the statement def (lean_name-based, matching
/// the Stmts module declaration).
#[test]
fn helper_hyp_binder_uses_short_name_and_stmt_type() {
    let b = helper_hyp_binder(&mk_path("lemma_a"));
    assert_eq!(b.name.as_ref().map(|n| n.as_str().to_string()),
        Some("lemma_a".to_string()));
    assert_eq!(crate::lean_pp::pp_expr(&b.ty), "lemma_a_stmt");
    assert!(matches!(b.kind, BinderKind::Explicit));

    // Multi-segment path: binder name stays SHORT (tactic text says
    // `helper`), stmt type is the dotted lean_name form (declared that
    // way in the Stmts module, resolvable under the same namespace).
    let p = Arc::new(vir::ast::PathX {
        krate: None,
        segments: Arc::new(vec![
            Arc::new("word".to_string()),
            Arc::new("helper".to_string()),
        ]),
    });
    let b = helper_hyp_binder(&p);
    assert_eq!(b.name.as_ref().map(|n| n.as_str().to_string()),
        Some("helper".to_string()));
    assert_eq!(crate::lean_pp::pp_expr(&b.ty), "word.helper_stmt");
}

// ── mainline-10: per-measure decreasing dispatch ─────────────────────

fn dec_var(s: &str) -> LExpr {
    LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit(s)))
}
fn dec_app(head: LExpr, args: Vec<LExpr>) -> LExpr {
    LExpr::new(ExprNode::App { head: Box::new(head), args })
}
fn dec_bin(op: BinOp, l: LExpr, r: LExpr) -> LExpr {
    LExpr::new(ExprNode::BinOp { op, lhs: Box::new(l), rhs: Box::new(r) })
}

/// The recursive fn `test_crate.f` calling itself with `n - 1` is a
/// LINEAR measure → omega.
#[test]
fn dec_classifies_linear_measure() {
    let body = dec_app(dec_var("test_crate.f"), vec![dec_bin(BinOp::Sub, dec_var("n"), dec_var("1"))]);
    assert_eq!(decreasing_kind(&dec_var("n"), "test_crate.f", &body, false), DecreasingKind::Linear);
}

/// `gcd a (b % a)` in the self-call → the mod rung.
#[test]
fn dec_classifies_modular_measure() {
    let body = dec_app(
        dec_var("test_crate.gcd"),
        vec![dec_var("a"), dec_bin(BinOp::Mod, dec_var("b"), dec_var("a"))],
    );
    assert_eq!(decreasing_kind(&dec_var("b"), "test_crate.gcd", &body, false), DecreasingKind::Modular);
}

/// `f (a / 2)` in the self-call → the div rung.
#[test]
fn dec_classifies_div_measure() {
    let body = dec_app(dec_var("test_crate.f"), vec![dec_bin(BinOp::Div, dec_var("a"), dec_var("2"))]);
    assert_eq!(decreasing_kind(&dec_var("a"), "test_crate.f", &body, false), DecreasingKind::Div);
}

/// `f (Seq.subrange w 1 (Seq.len w))` → the subrange companion rung.
#[test]
fn dec_classifies_subrange_measure() {
    let body = dec_app(
        dec_var("test_crate.f"),
        vec![dec_app(dec_var("lib.seq.Seq.subrange"), vec![dec_var("w"), dec_var("1"), dec_var("n")])],
    );
    assert_eq!(decreasing_kind(&dec_var("w"), "test_crate.f", &body, false), DecreasingKind::SeqSubrange);
}

/// `f (Seq.len (drop_base_run (Seq.drop_first W)))` with monos → chaining.
#[test]
fn dec_classifies_nested_suffix_chaining() {
    let body = dec_app(
        dec_var("test_crate.f"),
        vec![dec_app(
            dec_var("lib.seq.Seq.len"),
            vec![dec_var("T"),
                 dec_app(dec_var("lib.m.drop_base_run"),
                         vec![dec_var("T"),
                              dec_app(dec_var("lib.seq.Seq.drop_first"), vec![dec_var("T"), dec_var("W")])])],
        )],
    );
    assert_eq!(decreasing_kind(&dec_var("W"), "test_crate.f", &body, true), DecreasingKind::Chaining);
    // …but without registered monos the same shape degrades to drop_first.
    assert_eq!(decreasing_kind(&dec_var("W"), "test_crate.f", &body, false), DecreasingKind::SeqDropFirst);
}

/// Constructor-shaped self-call arg → structural (Lean's default).
#[test]
fn dec_classifies_structural_measure() {
    let body = dec_app(
        dec_var("test_crate.f"),
        vec![dec_app(dec_var("lib.symbol.Symbol.Gen"), vec![dec_var("i")])],
    );
    assert_eq!(decreasing_kind(&dec_var("s"), "test_crate.f", &body, false), DecreasingKind::Structural);
}

/// An If in the measure (Int-abs shape) → the split rung.
#[test]
fn dec_classifies_int_if_measure() {
    let measure = LExpr::new(ExprNode::If {
        cond: Box::new(dec_bin(BinOp::Le, dec_var("0"), dec_var("t"))),
        then_: Box::new(dec_var("t")),
        else_: Some(Box::new(LExpr::new(ExprNode::UnOp { op: crate::lean_ast::UnOp::Neg, arg: Box::new(dec_var("t")) }))),
    });
    let body = dec_app(dec_var("test_crate.f"), vec![dec_bin(BinOp::Sub, dec_var("t"), dec_var("1"))]);
    assert_eq!(decreasing_kind(&measure, "test_crate.f", &body, false), DecreasingKind::Split);
}

/// The dispatch emits ONE rung, never a `first`-chain.
#[test]
fn dec_emitted_text_has_no_outer_first() {
    let body = dec_app(dec_var("test_crate.f"), vec![dec_bin(BinOp::Mod, dec_var("b"), dec_var("a"))]);
    let text = decreasing_by_tactic(&dec_var("b"), "test_crate.f", &body);
    assert!(!text.starts_with("all_goals (first"));
    assert!(text.contains("Nat.mod_lt"));
}

/// Let-bound self-call args carry their value's signals:
/// `let rest := drop_first w; f data rest …` is a drop_first measure
/// (britton_via_tower.translate_word_at regression).
#[test]
fn dec_classifies_let_bound_drop_first() {
    // let rest := Seq.drop_first T w; test_crate.f data rest (base + 1)
    let body = LExpr::new(ExprNode::Let {
        name: crate::lean_name::LeanName::lit("rest"),
        value: Box::new(dec_app(dec_var("lib.seq.Seq.drop_first"), vec![dec_var("T"), dec_var("w")])),
        body: Box::new(dec_app(
            dec_var("test_crate.f"),
            vec![dec_var("data"), dec_var("rest"), dec_bin(BinOp::Add, dec_var("base"), dec_var("1"))],
        )),
    });
    assert_eq!(decreasing_kind(
        &dec_app(dec_var("lib.seq.Seq.len"), vec![dec_var("T"), dec_var("w")]),
        "test_crate.f",
        &body,
        false
    ), DecreasingKind::SeqDropFirst);
}

/// Self-calls inside let VALUES are seen:
/// `let rc := f (drop_first w) n` is a drop_first measure
/// (britton.stable_letter_count regression).
#[test]
fn dec_classifies_self_call_in_let_value() {
    // if len w = 0 then 0 else let rc := test_crate.f (Seq.drop_first T w) n; rc
    let body = LExpr::new(ExprNode::If {
        cond: Box::new(dec_bin(BinOp::Eq, dec_var("lenw"), dec_var("0"))),
        then_: Box::new(dec_var("0")),
        else_: Some(Box::new(LExpr::new(ExprNode::Let {
            name: crate::lean_name::LeanName::lit("rc"),
            value: Box::new(dec_app(
                dec_var("test_crate.f"),
                vec![dec_app(dec_var("lib.seq.Seq.drop_first"), vec![dec_var("T"), dec_var("w")]), dec_var("n")],
            )),
            body: Box::new(dec_var("rc")),
        }))),
    });
    assert_eq!(decreasing_kind(&dec_var("w"), "test_crate.f", &body, false), DecreasingKind::SeqDropFirst);
}

/// Nested suffix behind a let-var: `let after := drop_first W;
/// split_q (drop_base_run after)` → Chaining (m3_blinker.split_q).
#[test]
fn dec_classifies_nested_suffix_behind_let() {
    let body = LExpr::new(ExprNode::Let {
        name: crate::lean_name::LeanName::lit("after"),
        value: Box::new(dec_app(dec_var("lib.seq.Seq.drop_first"), vec![dec_var("T"), dec_var("W")])),
        body: Box::new(dec_app(
            dec_var("test_crate.split_q"),
            vec![dec_app(dec_var("test_crate.drop_base_run"), vec![dec_var("after")])],
        )),
    });
    assert_eq!(decreasing_kind(&dec_var("W"), "test_crate.split_q", &body, true), DecreasingKind::Chaining);
}
