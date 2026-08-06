//! Unit tests for `sanity` — extracted to `src/tests/` (a `#[path]`'d
//! `mod tests` child of `sanity`, so `use super::*` reaches private items).

use super::*;

fn var(s: &str) -> Expr { Expr::new(ExprNode::Var(crate::lean_name::LeanName::lit(s))) }

#[test]
fn known_builtins_pass() {
    let thm = Theorem {
        name: "t".into(),
        binders: vec![],
        goal: Expr::new(ExprNode::BinOp {
            op: BinOp::Eq,
            lhs: Box::new(var("Nat")),
            rhs: Box::new(var("Nat")),
        }),
        closer_census: None,
        tactic: Tactic::Named("rfl".into()),
        requires_preamble: Vec::new(),
        heartbeats: None,
        termination_by: Vec::new(),
        decreasing_by: None,
    };
    assert!(check_references(&[Command::Theorem(thm)]).is_empty());
}

#[test]
fn undefined_reference_flagged() {
    // Theorem references `missing_fn`, which is never defined.
    let thm = Theorem {
        name: "t".into(),
        binders: vec![],
        goal: Expr::new(ExprNode::App {
            head: Box::new(var("missing_fn")),
            args: vec![var("x")],
        }),
        closer_census: None,
        tactic: Tactic::Named("sorry".into()),
        requires_preamble: Vec::new(),
        heartbeats: None,
        termination_by: Vec::new(),
        decreasing_by: None,
    };
    let v = check_references(&[Command::Theorem(thm)]);
    assert_eq!(v.len(), 2); // missing_fn + x
    assert!(v.iter().any(|vi| vi.name == "missing_fn"));
}

/// Regression for the dependent-binder fix (2026-05-15 review pass).
/// Pre-fix, `check_expr`'s Forall/Lambda/Exists arm checked all
/// binder types under the OUTER scope, then added binder names —
/// so `∀ (self : Self) (h : P self), ...` flagged `self` in the
/// second binder's type as unresolved. Post-fix: binders are
/// checked left-to-right, adding each to scope before the next.
/// Surfaced via `test_proof_fn_trait_method_with_requires` e2e —
/// this is a focused unit test pinning the same property at the
/// sanity-check layer.
#[test]
fn forall_dependent_binder_resolves() {
    // ∀ (a : Nat) (h : a = a), Nat
    // Second binder type `a = a` references `a` from first via the
    // structural BinOp::Eq node — pre-fix the sanity check flagged
    // `a` as unresolved because it checked all binder types under
    // the outer scope. Post-fix: left-to-right, adding each binder
    // name before checking the next binder's type.
    let inner_eq = Expr::new(ExprNode::BinOp {
        op: BinOp::Eq,
        lhs: Box::new(var("a")),
        rhs: Box::new(var("a")),
    });
    let goal = Expr::new(ExprNode::Forall {
        binders: vec![
            Binder {
                name: Some(crate::lean_name::LeanName::lit("a")),
                ty: var("Nat"),
                kind: BinderKind::Explicit,
            },
            Binder {
                name: Some(crate::lean_name::LeanName::lit("h")),
                ty: inner_eq,
                kind: BinderKind::Explicit,
            },
        ],
        body: Box::new(var("Nat")),
    });
    let thm = Theorem {
        name: "t".into(),
        binders: vec![],
        goal,
        closer_census: None,
        tactic: Tactic::Named("sorry".into()),
        requires_preamble: Vec::new(),
        heartbeats: None,
        termination_by: Vec::new(),
        decreasing_by: None,
    };
    let v = check_references(&[Command::Theorem(thm)]);
    assert!(v.is_empty(),
        "expected dependent binder type to resolve, got violations: {:?}", v);
}

#[test]
fn earlier_def_is_resolved() {
    // Def `f` first, then Theorem references `f`.
    let d = Def {
        attrs: vec![],
        name: "f".into(),
        binders: vec![Binder {
            name: Some(crate::lean_name::LeanName::lit("x")), ty: var("Nat"), kind: BinderKind::Explicit,
        }],
        ret_ty: var("Nat"),
        body: var("x"),
        termination_by: vec![],
        termination_structural: false,
        decreasing_by: None,
    };
    let t = Theorem {
        name: "t".into(),
        binders: vec![Binder {
            name: Some(crate::lean_name::LeanName::lit("n")), ty: var("Nat"), kind: BinderKind::Explicit,
        }],
        goal: Expr::new(ExprNode::App {
            head: Box::new(var("f")),
            args: vec![var("n")],
        }),
        closer_census: None,
        tactic: Tactic::Named("rfl".into()),
        requires_preamble: Vec::new(),
        heartbeats: None,
        termination_by: Vec::new(),
        decreasing_by: None,
    };
    let violations = check_references(&[Command::Def(d), Command::Theorem(t)]);
    assert!(violations.is_empty(), "expected no violations, got {:?}", violations);
}

#[test]
fn let_binder_shadows_reference() {
    // `let x := 5; x + x` — `x` is bound, should resolve.
    let body = Expr::new(ExprNode::Let {
        name: crate::lean_name::LeanName::lit("x"),
        value: Box::new(Expr::new(ExprNode::Lit("5".into()))),
        body: Box::new(Expr::new(ExprNode::BinOp {
            op: BinOp::Add,
            lhs: Box::new(var("x")),
            rhs: Box::new(var("x")),
        })),
    });
    let d = Def {
        termination_structural: false,
        attrs: vec![], name: "ten".into(), binders: vec![],
        ret_ty: var("Nat"), body, termination_by: vec![],
        decreasing_by: None,
    };
    assert!(check_references(&[Command::Def(d)]).is_empty());
}

#[test]
fn forall_binder_scopes_body() {
    let goal = Expr::new(ExprNode::Forall {
        binders: vec![Binder {
            name: Some(crate::lean_name::LeanName::lit("k")), ty: var("Nat"), kind: BinderKind::Explicit,
        }],
        body: Box::new(Expr::new(ExprNode::BinOp {
            op: BinOp::Eq,
            lhs: Box::new(var("k")),
            rhs: Box::new(var("k")),
        })),
    });
    let t = Theorem {
        name: "t".into(), binders: vec![], goal,
        closer_census: None,
        tactic: Tactic::Named("rfl".into()),
        requires_preamble: Vec::new(),
        heartbeats: None,
        termination_by: Vec::new(),
        decreasing_by: None,
    };
    assert!(check_references(&[Command::Theorem(t)]).is_empty());
}

#[test]
fn mutual_group_resolves_cross_references() {
    // `mutual def f := g   def g := f end` — would fail without
    // predefining names across the group.
    let d1 = Def {
        termination_structural: false,
        attrs: vec![], name: "f".into(), binders: vec![], ret_ty: var("Nat"),
        body: var("g"), termination_by: vec![], decreasing_by: None,
    };
    let d2 = Def {
        termination_structural: false,
        attrs: vec![], name: "g".into(), binders: vec![], ret_ty: var("Nat"),
        body: var("f"), termination_by: vec![], decreasing_by: None,
    };
    let m = Command::Mutual(vec![Command::Def(d1), Command::Def(d2)]);
    assert!(check_references(&[m]).is_empty());
}

#[test]
fn dotted_names_pass_through() {
    // `Classical.arbitrary` should be accepted without explicit definition.
    let t = Theorem {
        name: "t".into(), binders: vec![],
        goal: var("Classical.arbitrary"),
        closer_census: None,
        tactic: Tactic::Named("sorry".into()),
        requires_preamble: Vec::new(),
        heartbeats: None,
        termination_by: Vec::new(),
        decreasing_by: None,
    };
    assert!(check_references(&[Command::Theorem(t)]).is_empty());
}

/// Pin the prelude-name extractor against the actual `TactusPrelude.lean`.
///
/// If a contributor adds a new top-level def/axiom/macro/syntax/elab
/// to TactusPrelude.lean, this test confirms it lands in the allowlist
/// without a corresponding `sanity.rs` edit. If a contributor introduces
/// a new prelude-form syntax our parser doesn't recognise (e.g.,
/// multi-line `def NAME\n  : Ty := …`), this test is the most natural
/// place to fail loudly.
#[test]
fn extract_prelude_names_recognises_current_prelude() {
    let mut names = extract_prelude_names(crate::prelude::TACTUS_DEFS);
    names.extend(extract_prelude_names(crate::prelude::TACTUS_SEARCH));
    // Axioms.
    assert!(names.contains("arch_word_bits"),
        "expected `arch_word_bits` in extracted prelude names; got {:?}", names);
    assert!(names.contains("arch_word_bits_valid"));
    // noncomputable defs.
    assert!(names.contains("usize_hi"));
    assert!(names.contains("isize_hi"));
    // syntax-introduced tactic names.
    assert!(names.contains("tactus_first"));
    // Dotted declarations (`opaque Tactus.hasResolved …`,
    // `noncomputable def Tactus.index …`) contribute their HEAD segment
    // (the extractor truncates at `.`) — pin it so a prelude-form change
    // that drops the Tactus.* declarations fails loudly here.
    assert!(names.contains("Tactus"),
        "expected `Tactus` (head of the Tactus.* declarations) in extracted \
         prelude names; got {:?}", names);
    // macro-introduced tactic names.
    assert!(names.contains("tactus_auto"));
    assert!(names.contains("tactus_usize_bound"));
    // elab-introduced tactic names.
    assert!(names.contains("tactus_case_split"));
}

#[test]
fn extract_prelude_names_skips_non_definition_lines() {
    // `import`, `set_option`, `attribute`, `open`, comments, blank
    // lines — none introduces a top-level name we should allowlist.
    let synthetic = r#"
            import Lean
            set_option maxHeartbeats 800000
            -- This is a comment
            -- axiom not_a_real_axiom : Nat
            open Classical in
            attribute [instance] Classical.propDecidable
            macro_rules
              | `(tactic| tactus_first $[| $ts:tacticSeq]*) => `(tactic| skip)
        "#;
    let names = extract_prelude_names(synthetic);
    assert!(names.is_empty(),
        "non-definition lines shouldn't introduce names; got {:?}", names);
}

#[test]
fn extract_prelude_names_handles_each_form() {
    let synthetic = r#"
            axiom my_axiom : Nat
            def my_def : Int := 0
            noncomputable def my_ncdef : Int := 1
            opaque my_opaque : Prop
            syntax "my_syntax" : tactic
            macro "my_macro" : tactic => `(tactic| skip)
            elab "my_elab" : tactic => do return
        "#;
    let names = extract_prelude_names(synthetic);
    for expected in &["my_axiom", "my_def", "my_ncdef", "my_opaque",
                      "my_syntax", "my_macro", "my_elab"] {
        assert!(names.contains(*expected),
            "expected `{}` in {:?}", expected, names);
    }
}

/// Pin which multi-line def shapes the parser handles, and which it
/// misses. DESIGN.md catalogue flagged the line-based parser as a
/// concern for "future prelude growth"; this test makes the actual
/// failure surface concrete:
///
/// * `def name\n  : Type := body` — works (name is on the same
///   line as `def`, so line-1 extraction succeeds).
/// * `def name {A : Type}\n  [Inhabited A] : T A := body` — works
///   (same reason; the implicit-binder section on line 1 doesn't
///   matter because take_while on `name {A : ...` stops at `{`).
/// * `def name :=\n  body` — works (name on line 1, body wraps).
/// * `noncomputable\ndef name : T := body` — MISSES (line 1 is
///   bare `noncomputable` with no name; line 2 has `def name` but
///   the parser handles `noncomputable def NAME` as a single-line
///   prefix only; on line 2 alone, `def name` does match the bare
///   `def NAME` form, so this case ACTUALLY works through that
///   fallback).
/// * `def\n  name : T := body` — MISSES (line 1 is bare `def`, no
///   space-after-def matches; line 2 doesn't match any prefix).
///
/// The single failure mode is bare `def\n` separated from the
/// name. That's unidiomatic Lean (no one writes it that way), but
/// pinning it makes the actual failure surface concrete instead of
/// the DESIGN.md guess.
#[test]
fn extract_prelude_names_multi_line_def_shapes() {
    // Cases that should work:
    let works_a = "def my_a\n  : Int := 0";
    let works_b = "def my_b {A : Type}\n  [Inhabited A] : Int := 0";
    let works_c = "def my_c :=\n  0";
    let works_d = "noncomputable\ndef my_d : Int := 0";
    for (label, src) in &[("a", works_a), ("b", works_b),
                          ("c", works_c), ("d", works_d)] {
        let names = extract_prelude_names(src);
        let expected = format!("my_{}", label);
        assert!(names.contains(&expected),
            "case {}: expected `{}` in {:?}", label, expected, names);
    }

    // The single failure mode: bare `def\n` separated from name.
    let fails = "def\n  my_e : Int := 0";
    let names = extract_prelude_names(fails);
    assert!(!names.contains("my_e"),
        "bare `def\\n` followed by name on next line is not handled \
         by the line-based parser; if this case starts working, \
         update extract_prelude_names docs");
}

/// Regression guard: every name the old hardcoded allowlist had
/// should still be accepted via the auto-derived path. Catches any
/// future TactusPrelude.lean refactor that removes one of these
/// without realising the sanity-check depended on it.
#[test]
fn cached_prelude_names_includes_legacy_allowlist() {
    let cached = cached_prelude_names();
    for legacy in &["arch_word_bits", "arch_word_bits_valid",
                    "usize_hi", "isize_hi",
                    "tactus_usize_bound"] {
        assert!(cached.contains(*legacy),
            "legacy allowlist name `{}` missing from auto-derived set; \
             did TactusPrelude.lean change?", legacy);
    }
}

/// Pin that `name_resolves` accepts a prelude-defined name. Catches
/// regressions where the wiring between `cached_prelude_names`
/// and `name_resolves` breaks (e.g., someone re-introducing the
/// hardcoded `matches!` arm without removing the cache lookup, or
/// vice versa).
#[test]
fn name_resolves_accepts_prelude_name() {
    let defined = HashSet::new();
    let scope = HashSet::new();
    assert!(name_resolves("arch_word_bits", &defined, &scope));
    assert!(name_resolves("usize_hi", &defined, &scope));
    // Sanity: a made-up name is still rejected.
    assert!(!name_resolves("not_a_prelude_name_xyz", &defined, &scope));
}

// ── Anchored-self-reference rule (preventive check, ──
// ── DESIGN-lean-all-proofs-followons.md "Preventive check") ──

/// A datatype whose field references the datatype ITSELF root-anchored
/// must be flagged: during elaboration the inductive is not yet a
/// global, so `_root_.ns.Stack` inside `inductive _root_.ns.Stack` is
/// `Unknown identifier` at lake time — the 2026-07-10 regression class,
/// now caught at codegen time.
#[test]
fn anchored_self_ref_in_datatype_field_flagged() {
    let dt = Datatype {
        name: "_root_.test.Stack".into(),
        self_name: "Stack".into(),
        typ_params: vec![],
        kind: DatatypeKind::Inductive {
            variants: vec![Variant {
                name: "Push".into(),
                fields: vec![Field {
                    name: "val0".into(),
                    // The bug shape: root-anchored self-reference.
                    ty: var("_root_.test.Stack"),
                }],
            }],
        },
        derives: vec![],
    };
    let v = check_references(&[Command::Datatype(dt)]);
    assert!(
        v.iter().any(|x| x.name.contains("root-anchored self-reference")),
        "expected anchored-self-ref violation, got {:?}", v,
    );
}

/// The RELATIVE self-reference (what `with_self_decls` produces) is the
/// correct form and must NOT be flagged.
#[test]
fn relative_self_ref_in_datatype_field_ok() {
    let dt = Datatype {
        name: "_root_.test.Stack".into(),
        self_name: "Stack".into(),
        typ_params: vec![],
        kind: DatatypeKind::Inductive {
            variants: vec![Variant {
                name: "Push".into(),
                fields: vec![Field { name: "val0".into(), ty: var("Stack") }],
            }],
        },
        derives: vec![],
    };
    assert!(check_references(&[Command::Datatype(dt)]).is_empty());
}

/// A class method TYPE referencing a sibling via the anchored
/// `_root_.ns.Class.method` form must be flagged (the trait
/// sibling-ref regression); a DIFFERENT decl's anchored name (already
/// declared above) must not.
#[test]
fn anchored_class_sibling_ref_flagged() {
    let c = Class {
        name: "_root_.test.HasZero".into(),
        typ_params: vec![],
        extends_parents: vec![],
        methods: vec![
            ClassMethod {
                name: "val".into(),
                ty: var("Int"),
                default: None,
                termination_by: vec![],
            },
            ClassMethod {
                name: "val_is_zero".into(),
                ty: Expr::new(ExprNode::App {
                    head: Box::new(var("_root_.test.HasZero.val")),
                    args: vec![var("Int")],
                }),
                default: None,
                termination_by: vec![],
            },
        ],
    };
    let v = check_references(&[Command::Class(c)]);
    assert!(
        v.iter().any(|x| x.name.contains("root-anchored self-reference")),
        "expected anchored sibling-ref violation, got {:?}", v,
    );
}

/// The reserved-name rule (Option B's ONE reserved name): a binder equal
/// to the crate namespace would capture the leading segment of every
/// crate-internal reference. Runs in ALL build profiles.
#[test]
fn reserved_crate_ns_binder_flagged() {
    crate::to_lean_type::install_crate_ns("resv_test_ns");
    let t = Theorem {
        name: "t".into(),
        binders: vec![Binder {
            name: Some(crate::lean_name::LeanName::lit("resv_test_ns")),
            ty: var("Nat"),
            kind: BinderKind::Explicit,
        }],
        goal: var("True"),
        closer_census: None,
        tactic: Tactic::Named("trivial".into()),
        requires_preamble: Vec::new(),
        heartbeats: None,
        termination_by: Vec::new(),
        decreasing_by: None,
    };
    let v = check_references(&[Command::Theorem(t)]);
    assert!(
        v.iter().any(|x| x.name.contains("shadows the crate namespace")),
        "expected reserved-binder violation, got {:?}", v,
    );
    // A ∀-bound occurrence is flagged too (check_expr arm wiring).
    let t2 = Theorem {
        name: "t2".into(),
        binders: vec![],
        goal: Expr::new(ExprNode::Forall {
            binders: vec![Binder {
                name: Some(crate::lean_name::LeanName::lit("resv_test_ns")),
                ty: var("Nat"),
                kind: BinderKind::Explicit,
            }],
            body: Box::new(var("True")),
        }),
        closer_census: None,
        tactic: Tactic::Named("trivial".into()),
        requires_preamble: Vec::new(),
        heartbeats: None,
        termination_by: Vec::new(),
        decreasing_by: None,
    };
    let v2 = check_references(&[Command::Theorem(t2)]);
    assert!(
        v2.iter().any(|x| x.name.contains("shadows the crate namespace")),
        "expected forall-binder violation, got {:?}", v2,
    );
}
