//! Unit tests for `lean_pp` — extracted to `src/tests/` (a `#[path]`'d
//! `mod tests` child of `lean_pp`, so `use super::*` reaches private items).

use super::*;

fn var(s: &str) -> Expr { Expr::new(ExprNode::Var(crate::lean_name::LeanName::lit(s))) }
fn lit(n: i64) -> Expr { Expr::new(ExprNode::Lit(n.to_string())) }
fn bin(op: BinOp, l: Expr, r: Expr) -> Expr {
    Expr::new(ExprNode::BinOp { op, lhs: Box::new(l), rhs: Box::new(r) })
}

// ── current_line_indent (helper used by ExprNode::ByBlock pp) ────

#[test]
fn current_line_indent_empty_string() {
    assert_eq!(current_line_indent(""), 0);
}

#[test]
fn current_line_indent_no_indent() {
    assert_eq!(current_line_indent("foo := bar"), 0);
    }

    #[test]
    fn current_line_indent_two_spaces() {
        assert_eq!(current_line_indent("  foo := bar"), 2);
}

#[test]
fn current_line_indent_string_ending_with_newline() {
    // Last line is empty — indent of empty line is 0.
    assert_eq!(current_line_indent("foo\n"), 0);
}

#[test]
fn current_line_indent_multi_line_uses_last_line() {
    // Previous lines' indents don't matter — only the current
    // (last, unterminated) line's indent counts.
    assert_eq!(current_line_indent("    early\n  current"), 2);
}

#[test]
fn current_line_indent_tabs_not_counted() {
    // Tabs aren't used in Tactus's output; only space-prefix counts.
    // A line starting with a tab is treated as zero-indent.
    assert_eq!(current_line_indent("\tfoo"), 0);
}

#[test]
fn current_line_indent_only_spaces() {
    // A "line" that's all spaces — count them all.
    assert_eq!(current_line_indent("    "), 4);
}

#[test]
fn mul_binds_tighter_than_add() {
    // a + b * c → "a + b * c" (no parens; mul is inside)
    let e = bin(BinOp::Add, var("a"), bin(BinOp::Mul, var("b"), var("c")));
    assert_eq!(pp_expr(&e), "a + b * c");
}

#[test]
fn add_inside_mul_parenthesizes() {
    // (a + b) * c → "(a + b) * c"
    let e = bin(BinOp::Mul, bin(BinOp::Add, var("a"), var("b")), var("c"));
    assert_eq!(pp_expr(&e), "(a + b) * c");
}

#[test]
fn sub_is_left_associative() {
    // a - b - c = (a - b) - c, no parens needed on left
    let e = bin(BinOp::Sub, bin(BinOp::Sub, var("a"), var("b")), var("c"));
    assert_eq!(pp_expr(&e), "a - b - c");
}

#[test]
fn sub_right_nested_needs_parens() {
    // a - (b - c) — subtraction is left-assoc, so right child at same prec parenthesizes
    let e = bin(BinOp::Sub, var("a"), bin(BinOp::Sub, var("b"), var("c")));
    assert_eq!(pp_expr(&e), "a - (b - c)");
}

#[test]
fn implies_is_right_associative() {
    // a → b → c = a → (b → c), no parens
    let e = bin(BinOp::Implies, var("a"), bin(BinOp::Implies, var("b"), var("c")));
    assert_eq!(pp_expr(&e), "a → b → c");
}

#[test]
fn implies_left_nested_needs_parens() {
    // (a → b) → c — left child at same prec on right-assoc op parenthesizes
    let e = bin(BinOp::Implies, bin(BinOp::Implies, var("a"), var("b")), var("c"));
    assert_eq!(pp_expr(&e), "(a → b) → c");
}

#[test]
fn and_binds_tighter_than_implies() {
    // a ∧ b → c = (a ∧ b) → c (∧ at 35 tighter than → at 25)
    let e = bin(BinOp::Implies, bin(BinOp::And, var("a"), var("b")), var("c"));
    assert_eq!(pp_expr(&e), "a ∧ b → c");
}

#[test]
fn implies_inside_and_needs_parens() {
    // a ∧ (b → c) — ∧ is tighter, so the implication child needs parens
    let e = bin(BinOp::And, var("a"), bin(BinOp::Implies, var("b"), var("c")));
    assert_eq!(pp_expr(&e), "a ∧ (b → c)");
}

#[test]
fn negative_literal_parenthesizes() {
    let e = Expr::new(ExprNode::Lit("-5".into()));
    assert_eq!(pp_expr(&e), "(-5)");
}

#[test]
fn app_binds_tightest() {
    // f x + 1 — application + literal at add prec, no parens
    let e = bin(
        BinOp::Add,
        Expr::new(ExprNode::App {
            head: Box::new(var("f")),
            args: vec![var("x")],
        }),
        lit(1),
    );
    assert_eq!(pp_expr(&e), "f x + 1");
}

#[test]
fn app_of_app_is_left_assoc() {
    // f g x — `App(App(f, [g]), [x])` emits the same as `App(f, [g, x])`.
    let nested = Expr::new(ExprNode::App {
        head: Box::new(var("f")),
        args: vec![var("g")],
    });
    let e = Expr::new(ExprNode::App {
        head: Box::new(nested),
        args: vec![var("x")],
    });
    assert_eq!(pp_expr(&e), "f g x");
}

#[test]
fn app_arg_is_app_parenthesizes() {
    // f (g x) — inner app as an arg needs parens
    let inner = Expr::new(ExprNode::App {
        head: Box::new(var("g")),
        args: vec![var("x")],
    });
    let e = Expr::new(ExprNode::App {
        head: Box::new(var("f")),
        args: vec![inner],
    });
    assert_eq!(pp_expr(&e), "f (g x)");
}

#[test]
fn simple_def_renders() {
    let d = Def {
        attrs: vec!["irreducible".into()],
        name: "double".into(),
        binders: vec![Binder {
            name: Some(crate::lean_name::LeanName::lit("x")),
            ty: var("Nat"),
            kind: BinderKind::Explicit,
        }],
        ret_ty: var("Nat"),
        body: bin(BinOp::Add, var("x"), var("x")),
        termination_by: vec![],
        decreasing_by: None,
    };
    let expected = "@[irreducible] noncomputable def double (x : Nat) : Nat :=\n  x + x\n";
    assert_eq!(pp_command(&Command::Def(d)), expected);
}

#[test]
fn theorem_with_heartbeats_emits_set_option() {
    let t = Theorem {
        name: "expensive".into(),
        binders: vec![],
        goal: bin(BinOp::Eq, lit(1), lit(1)),
        tactic: Tactic::Named("rfl".into()),
        requires_preamble: Vec::new(),
        heartbeats: Some(1600000),
        termination_by: Vec::new(),
        decreasing_by: None,
    };
    let out = pp_command(&Command::Theorem(t));
    assert!(out.starts_with("set_option maxHeartbeats 1600000 in\ntheorem expensive"),
        "expected heartbeats option before theorem, got:\n{}", out);
}

#[test]
fn theorem_without_heartbeats_no_set_option() {
    let t = Theorem {
        name: "cheap".into(),
        binders: vec![],
        goal: bin(BinOp::Eq, lit(1), lit(1)),
        tactic: Tactic::Named("rfl".into()),
        requires_preamble: Vec::new(),
        heartbeats: None,
        termination_by: Vec::new(),
        decreasing_by: None,
    };
    let out = pp_command(&Command::Theorem(t));
    assert!(!out.contains("set_option maxHeartbeats"),
        "expected no heartbeats option, got:\n{}", out);
    assert!(out.starts_with("theorem cheap"),
        "expected theorem to start the output, got:\n{}", out);
}

#[test]
fn theorem_with_named_tactic() {
    let t = Theorem {
        name: "foo".into(),
        binders: vec![Binder {
            name: Some(crate::lean_name::LeanName::lit("x")),
            ty: var("Nat"),
            kind: BinderKind::Explicit,
        }],
        goal: bin(BinOp::Eq, var("x"), var("x")),
        tactic: Tactic::Named("rfl".into()),
        requires_preamble: Vec::new(),
        heartbeats: None,
        termination_by: Vec::new(),
        decreasing_by: None,
    };
    let out = pp_command(&Command::Theorem(t));
    assert!(out.contains("theorem foo (x : Nat)"));
    assert!(out.contains("x = x := by"));
    assert!(out.contains("  rfl"));
}

#[test]
fn if_without_else() {
    let e = Expr::new(ExprNode::If {
        cond: Box::new(var("c")),
        then_: Box::new(var("t")),
        else_: None,
    });
    assert_eq!(pp_expr(&e), "if c then t");
}

#[test]
fn pp_records_raw_tactic_start() {
    // The tactic body is `omega`. The theorem emits four lines before
    // the body starts (`theorem …`, ` … goal`, ` … := by`, then the
    // indented tactic). Confirm `tactic_starts` points at the right line.
    let t = Theorem {
        name: "foo".into(),
        binders: vec![],
        goal: bin(BinOp::Eq, lit(1), lit(1)),
        tactic: Tactic::Raw("omega".into()),
        requires_preamble: Vec::new(),
        heartbeats: None,
        termination_by: Vec::new(),
        decreasing_by: None,
    };
    let out = pp_commands(&[Command::Theorem(t)]);
    assert_eq!(out.landmarks.tactic_starts.len(), 1);
    // Pull the recorded line and verify it contains the tactic text.
    let start = out.landmarks.tactic_starts[0];
    let line = out.text.lines().nth(start - 1).expect("tactic line in range");
    assert!(line.contains("omega"), "line {} was {:?}", start, line);
}

#[test]
fn pp_index_is_atomic() {
    // `base[idx]` shouldn't take outer parens when used as a call arg.
    let idx = Expr::new(ExprNode::Index {
        base: Box::new(var("xs")),
        idx: Box::new(lit(0)),
        bang: false,
    });
    let apply_f = Expr::new(ExprNode::App {
        head: Box::new(var("f")),
        args: vec![idx],
    });
    assert_eq!(pp_expr(&apply_f), "f xs[0]");
}

#[test]
fn anon_constructor_tuple() {
    let e = Expr::new(ExprNode::Anon(vec![var("a"), var("b"), var("c")]));
    assert_eq!(pp_expr(&e), "⟨a, b, c⟩");
}

#[test]
fn anon_is_atomic_in_application() {
    // `f ⟨a, b⟩` — ⟨⟩ doesn't need outer parens as an arg.
    let tup = Expr::new(ExprNode::Anon(vec![var("a"), var("b")]));
    let e = Expr::new(ExprNode::App {
        head: Box::new(var("f")),
        args: vec![tup],
    });
    assert_eq!(pp_expr(&e), "f ⟨a, b⟩");
}

#[test]
fn type_product_right_associative() {
    // T × U × V = T × (U × V); no parens on the right.
    let inner = bin(BinOp::Prod, var("U"), var("V"));
    let e = bin(BinOp::Prod, var("T"), inner);
    assert_eq!(pp_expr(&e), "T × U × V");
}

#[test]
fn type_product_left_nested_needs_parens() {
    // (T × U) × V — left child at same prec on right-assoc op parens.
    let inner = bin(BinOp::Prod, var("T"), var("U"));
    let e = bin(BinOp::Prod, inner, var("V"));
    assert_eq!(pp_expr(&e), "(T × U) × V");
}

#[test]
fn termination_by_tuple() {
    let d = Def {
        attrs: vec![],
        name: "f".into(),
        binders: vec![Binder {
            name: Some(crate::lean_name::LeanName::lit("n")), ty: var("Nat"), kind: BinderKind::Explicit,
        }],
        ret_ty: var("Nat"),
        body: var("n"),
        termination_by: vec![var("n"), var("m")],
        decreasing_by: None,
    };
    let out = pp_command(&Command::Def(d));
    assert!(out.contains("termination_by (n, m)"), "{out}");
}

/// Recursive proof fn translation — `Theorem.termination_by` is emitted
/// after the tactic body. Mirrors `Def.termination_by` rendering.
#[test]
fn theorem_with_termination_by_single() {
    let t = Theorem {
        name: "rec_lemma".into(),
        binders: vec![Binder {
            name: Some(crate::lean_name::LeanName::lit("n")),
            ty: var("Nat"),
            kind: BinderKind::Explicit,
        }],
        goal: bin(BinOp::Ge, var("n"), lit(0)),
        tactic: Tactic::Named("omega".into()),
        requires_preamble: Vec::new(),
        heartbeats: None,
        termination_by: vec![var("n")],
        decreasing_by: None,
    };
    let out = pp_command(&Command::Theorem(t));
    assert!(out.contains("termination_by n"),
        "expected single-measure termination_by, got:\n{}", out);
    // Must appear AFTER the tactic body, not before/inside it.
    let tactic_pos = out.find("omega").expect("tactic present");
    let term_pos = out.find("termination_by").expect("termination_by present");
    assert!(term_pos > tactic_pos,
        "termination_by must follow the tactic body; got:\n{}", out);
}

/// Lex decreases for recursive proof fns — tuple rendering.
#[test]
fn theorem_with_termination_by_lex() {
    let t = Theorem {
        name: "lex_lemma".into(),
        binders: vec![],
        goal: bin(BinOp::Eq, lit(1), lit(1)),
        tactic: Tactic::Named("rfl".into()),
        requires_preamble: Vec::new(),
        heartbeats: None,
        termination_by: vec![var("a"), var("b")],
        decreasing_by: None,
    };
    let out = pp_command(&Command::Theorem(t));
    assert!(out.contains("termination_by (a, b)"),
        "expected lex-tuple termination_by, got:\n{}", out);
}

/// `decreasing_by` renders after `termination_by` for a recursive proof fn
/// whose measure needs a non-default tactic (the proof-fn twin of the
/// spec-fn modular-decreases fix).
#[test]
fn theorem_with_decreasing_by() {
    let t = Theorem {
        name: "rec_mod".into(),
        binders: vec![],
        goal: bin(BinOp::Eq, lit(1), lit(1)),
        tactic: Tactic::Named("rfl".into()),
        requires_preamble: Vec::new(),
        heartbeats: None,
        termination_by: vec![var("b")],
        decreasing_by: Some("all_goals omega".into()),
    };
    let out = pp_command(&Command::Theorem(t));
    assert!(out.contains("termination_by b"), "{out}");
    assert!(out.contains("decreasing_by all_goals omega"), "{out}");
    // `decreasing_by` must follow `termination_by`.
    let term_pos = out.find("termination_by").expect("termination_by present");
    let dec_pos = out.find("decreasing_by").expect("decreasing_by present");
    assert!(dec_pos > term_pos,
        "decreasing_by must follow termination_by; got:\n{}", out);
}

/// Non-recursive theorems (the common case) — no termination_by emitted.
#[test]
fn theorem_without_termination_by_no_clause() {
    let t = Theorem {
        name: "trivial".into(),
        binders: vec![],
        goal: bin(BinOp::Eq, lit(1), lit(1)),
        tactic: Tactic::Named("rfl".into()),
        requires_preamble: Vec::new(),
        heartbeats: None,
        termination_by: Vec::new(),
        decreasing_by: None,
    };
    let out = pp_command(&Command::Theorem(t));
    assert!(!out.contains("termination_by"),
        "non-recursive theorem should not emit termination_by, got:\n{}", out);
}

/// Pins that SpanMark rendering passes the `rust_loc` string
/// through verbatim into both the `/- @rust:LOC -/` comment
/// and the recorded `SpanMarkLandmark.loc`. The pp used to
/// strip newlines from `rust_loc` defensively; we removed that
/// because `format_rust_loc` produces single-line output by
/// construction (`Span::start_loc` is `path:line:col` and the
/// `Span::as_string` fallback is `format!("{:?}", rustc_span)`,
/// also single-line). If a future change reintroduces multi-
/// line locs, this test fails — fix the producer rather than
/// re-adding pp-side sanitization.
#[test]
fn span_mark_render_preserves_loc_verbatim() {
    use crate::lean_ast::AssertKind;
    use crate::lean_ast::ObligationKind;
    let inner = lit(42);
    let loc = "src/main.rs:42:13".to_string();
    let marked = Expr::new(ExprNode::SpanMark {
        rust_loc: loc.clone(),
        rust_span: None,
        kind: AssertKind::Obligation(ObligationKind::Plain),
        inner: Box::new(inner),
    });
    let mut out = String::new();
    let mut lm = Landmarks { tactic_starts: Vec::new(), span_marks: Vec::new() };
    write_expr(&mut out, &marked, 0, &mut lm);
    assert!(
        out.contains(&format!("/- @rust:{} -/", loc)),
        "expected rust_loc verbatim in pp output, got: {out:?}",
    );
    assert_eq!(lm.span_marks.len(), 1, "expected one landmark recorded");
    assert_eq!(
        lm.span_marks[0].loc, loc,
        "landmark loc should be the rust_loc verbatim",
    );
}

/// Pins that representative span-loc shapes produced by
/// Tactus's path are single-line. If `Span::start_loc` ever
/// becomes multi-line for some input, this test fires and the
/// fix goes upstream (in `to_air_span` or wherever the loc is
/// constructed) rather than at pp time.
#[test]
fn span_mark_loc_shapes_have_no_newlines() {
    // path:line:col — `start_loc` shape from to_air_span.
    let shapes = [
        "src/main.rs:42:13",
        "/home/user/project/src/lib.rs:123:5",
        // as_string fallback shape from `format!("{:?}", rustc_span)`.
        "src/main.rs:42:13: 42:20 (#0)",
    ];
    for s in &shapes {
        assert!(
            !s.contains('\n') && !s.contains('\r'),
            "representative span-loc shape contained a newline: {s:?}",
        );
    }
}

// ── ExprNode::Let continuation column (F1, DESIGN-lean-all-proofs-followons.md) ──

/// A `let` starting at column 0: its body continues at column 0.
#[test]
fn let_body_aligns_at_column_zero() {
    let e = Expr::let_bind_synthetic("x", lit(1), var("x"));
    assert_eq!(pp_expr(&e), "let x := 1;\nx");
}

/// Chained lets stay flat: the inner let is the outer's body, printed
/// at the outer `let`'s column, so its own body aligns there too.
#[test]
fn let_chain_stays_flat() {
    let inner = Expr::let_bind_synthetic("y", lit(2), var("y"));
    let e = Expr::let_bind_synthetic("x", lit(1), inner);
    assert_eq!(pp_expr(&e), "let x := 1;\nlet y := 2;\ny");
}

/// The F1 bug shape: a `let` in an if-branch starts mid-line; its body
/// must align under the `let` keyword, NOT at the old fixed 4-space
/// indent (which dedented the body below enclosing column guards —
/// `unexpected token '('; expected 'else'`).
#[test]
fn let_body_aligns_under_midline_let() {
    let then_ = Expr::let_bind_synthetic("i", lit(1), var("i"));
    let e = Expr::new(ExprNode::If {
        cond: Box::new(var("c")),
        then_: Box::new(then_),
        else_: Some(Box::new(var("z"))),
    });
    // `if c then ` is 10 chars, so `let` sits at column 10 and the
    // body gets 10 spaces of continuation indent.
    assert_eq!(pp_expr(&e), "if c then let i := 1;\n          i else z");
}

/// Column counting is in codepoints, not bytes: a multibyte `∧` before
/// the `let` must not inflate the continuation indent.
#[test]
fn let_column_counts_chars_not_bytes() {
    let rhs = Expr::let_bind_synthetic("i", lit(1), var("i"));
    let e = bin(BinOp::And, var("p"), rhs);
    // The let parenthesizes under `∧`; `p ∧ (` is 5 chars (7 bytes),
    // so `let` sits at column 5 → 5 spaces. Byte-counting would have
    // yielded 7.
    assert_eq!(pp_expr(&e), "p ∧ (let i := 1;\n     i)");
}

// ── ExprNode::VectorLit (F3, DESIGN-lean-all-proofs-followons.md) ──

/// Vector literals print with Lean core's `#v[…]` syntax; List
/// literals keep plain `[…]`. The dispatch lives in
/// `expr_shared::array_literal_node`; here we pin the two print shapes.
#[test]
fn vector_lit_prints_hash_v() {
    let v = Expr::new(ExprNode::VectorLit(vec![lit(1), lit(2), lit(3)]));
    assert_eq!(pp_expr(&v), "#v[1, 2, 3]");
    let l = Expr::new(ExprNode::ArrayLit(vec![lit(1), lit(2)]));
    assert_eq!(pp_expr(&l), "[1, 2]");
}
