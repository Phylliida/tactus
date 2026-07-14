//! Unit + golden tests for the SST serializer ([`crate::sst_serialize`]).
//!
//! Split out of `sst_serialize.rs` so the trusted module stays under the
//! §7.6 audit budget (<1k lines: doc-comment + code a skeptic reads).
//! These tests are the serializer's checks, not part of the TCB — a child
//! `mod tests` still reaches the parent's private items via `super::*`.

use super::*;

#[test]
fn box_and_paren() {
    assert_eq!(paren("lib.StmData.Skip"), "lib.StmData.Skip");
    assert_eq!(paren("(lib.StmData.Seq a b)"), "(lib.StmData.Seq a b)");
    assert_eq!(paren("lib.LeafList.Cons 0 x"), "(lib.LeafList.Cons 0 x)");
    assert_eq!(box_("lib.LeafList.Nil"), "(Tactus.Box.mk lib.LeafList.Nil)");
}

#[test]
fn leaf_list_order() {
    let s = Serializer::default();
    // ids 1,2,3 → Cons 1 (Cons 2 (Cons 3 Nil))
    let t = s.leaf_list(&[1, 2, 3]);
    assert_eq!(
        t,
        "lib.LeafList.Cons 1 (Tactus.Box.mk (lib.LeafList.Cons 2 (Tactus.Box.mk (lib.LeafList.Cons 3 (Tactus.Box.mk lib.LeafList.Nil)))))"
    );
}

#[test]
fn stm_size_matches_core() {
    // Seq(Assert, If(Skip, Ret Nil)) — mirrors the in-crate
    // skeleton_kernel_computes example: size = 5. `Assert` carries the
    // finding-1 two-leaf form (annotated obligation, bare hyp); `stm_size`
    // counts the head, so the two ids don't change the size.
    let term = "(lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert 22 0)) (Tactus.Box.mk (lib.StmData.If 1 2 (Tactus.Box.mk lib.StmData.Skip) (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk lib.LeafList.Nil) lib.RetBind.RetNone)))))";
    assert_eq!(stm_size_of(term), 5);
}

/// Golden-file pin (N3c §7.5). This module is the TCB — its emitted
/// output shape is what a skeptic audits, so it must not drift
/// silently. `GOLDEN` is the verbatim cert file the rebuilt binary
/// emitted for the real fixture fn `add_capped` over
/// `bootstrap-fixture/lib.rs`, INCLUDING the N3b goal half; the test
/// re-renders and asserts byte-equality. Any change to the header text,
/// leaf-table format, `def` naming, term spacing, the `stm_size … := by
/// decide` probe (incl. `stm_size_of`), or the `production goals`
/// section (per-goal comments, `GoalList` def, `goal_count … := by
/// decide`) breaks this test — a *reviewed* diff, like the trusted code
/// it guards.
///
/// The `CertBody` inputs are recovered from the golden itself (leaf
/// texts from the `-- leaf N: ⟦…⟧` table; the ctx/sst/goals terms from
/// their three `def` bodies; goal names from the `-- goal N:` comments)
/// rather than hand-transcribed. This is a valid regression pin: the
/// golden bytes are fixed, while the recovered content is
/// format-independent, so a format change makes the re-render diverge
/// from the unchanged golden. (Bonus: no need to hand-copy the Unicode
/// leaves or the long fully-parenthesized terms, which would themselves
/// be a transcription-error surface.)
#[test]
fn golden_add_capped_cert() {
    const GOLDEN: &str = include_str!("testdata/add_capped.cert.lean");

    // vocab_hash() reads $TACTUS_CORE_VOCAB; the golden was emitted
    // with it unset ("unvendored"). Under a vendored env the header
    // hash differs by design — skip rather than spuriously fail.
    if vocab_hash() != "unvendored" {
        return;
    }

    let lines: Vec<&str> = GOLDEN.lines().collect();
    let mut leaf_texts: Vec<String> = Vec::new();
    let mut ctx_term = String::new();
    let mut stm_term = String::new();
    let mut goal_term = String::new();
    let mut goal_names: Vec<String> = Vec::new();
    for (i, line) in lines.iter().enumerate() {
        // A leaf-table row is `-- leaf N: ⟦text⟧` (N numeric). The
        // digit + ⟦ guard distinguishes it from the header prose line
        // `-- leaf rendering (stage B/W6)…`, which also begins
        // `-- leaf `.
        if let Some(rest) = line.strip_prefix("-- leaf ") {
            if rest.starts_with(|c: char| c.is_ascii_digit()) {
                let open = rest.find('⟦').expect("leaf row carries ⟦");
                let close = rest.rfind('⟧').expect("leaf row carries ⟧");
                leaf_texts.push(rest[open + '⟦'.len_utf8()..close].to_string());
            }
        } else if let Some(rest) = line.strip_prefix("-- goal ") {
            // N3b O4 pairing row: `-- goal N: <theorem name>`. Same
            // digit guard as the leaf rows so no header prose can
            // masquerade as a goal.
            if rest.starts_with(|c: char| c.is_ascii_digit()) {
                let colon = rest.find(": ").expect("goal row carries `: `");
                goal_names.push(rest[colon + 2..].to_string());
            }
        } else if line.contains("def cert_add_capped_ctx") {
            ctx_term = lines[i + 1].trim().to_string();
        } else if line.contains("def cert_add_capped_sst") {
            stm_term = lines[i + 1].trim().to_string();
        } else if line.contains("def cert_add_capped_goals") {
            goal_term = lines[i + 1].trim().to_string();
        }
    }
    assert_eq!(leaf_texts.len(), 24, "golden leaf-table size drifted");
    assert_eq!(goal_names.len(), 4, "golden goal count drifted");
    assert!(!ctx_term.is_empty(), "ctx term not recovered from golden");
    assert!(!stm_term.is_empty(), "sst term not recovered from golden");
    assert!(!goal_term.is_empty(), "goals term not recovered from golden");

    // N3b goal half is present in this golden (4 obligations: 3 asserts
    // + 1 postcondition), so render_cert emits the `production goals`
    // section; a from-golden recovery of both halves must re-render the
    // full byte stream.
    let body = CertBody {
        ctx_term,
        stm_term,
        goal_term,
        goal_names,
        leaf_texts,
    };
    let rendered = render_cert("lib", "add_capped", "add_capped", &body);
    assert_eq!(rendered, GOLDEN, "cert-file format drift vs golden");
}

/// N3b: a hand-built `GoalShape` serializes to the expected
/// `lib.GoalData` spine — pins the constructor mapping
/// (`All`/`Imp`/`Let`/`Leaf`), the outermost-first fold direction
/// (theorem binder ends up the outermost `All`), and that every spine
/// leaf lands in the shared table.
#[test]
fn goal_data_spine_shape() {
    use crate::lean_ast::{Binder, GoalShape, GoalSpine};
    use crate::lean_name::LeanName;

    // ∀ (nn : Ity), (hyp0) → let mm := vv; (goalpred)  [outermost-first].
    // Distinct identifiers throughout so no accidental leaf sharing
    // muddies the structural check.
    let shape = GoalShape {
        spine: vec![
            GoalSpine::All(Binder::explicit(
                LeanName::synthetic("nn"),
                LExpr::var(LeanName::synthetic("Ity")),
            )),
            GoalSpine::Imp(LExpr::var(LeanName::synthetic("hyp0"))),
            GoalSpine::Let(
                LeanName::synthetic("mm"),
                LExpr::var(LeanName::synthetic("vv")),
            ),
        ],
        leaf: LExpr::var(LeanName::synthetic("goalpred")),
    };
    let mut s = Serializer::default();
    let term = s.goal_data(&shape);
    // Leaf-out fold: Leaf wrapped by Let, then Imp, then All outermost.
    assert!(
        term.starts_with(&format!("({}.GoalData.All ", NS)),
        "outermost node should be the ∀ binder: {}", term,
    );
    assert!(term.contains(&format!("{}.GoalData.Imp ", NS)), "{}", term);
    assert!(term.contains(&format!("{}.GoalData.Let ", NS)), "{}", term);
    assert!(term.contains(&format!("{}.GoalData.Leaf ", NS)), "{}", term);
    // Each spine leaf reached the table: binder typ, binder name, hyp,
    // let name, let value, core predicate — all distinct here.
    for want in ["Ity", "nn", "hyp0", "mm", "vv", "goalpred"] {
        assert!(s.leaves.texts.iter().any(|t| t == want), "missing leaf {}: {:?}", want, s.leaves.texts);
    }
}

/// N3b: `goal_list` emits one `Cons` per obligation with a spine and
/// skips `None` (bit_vector/query) obligations, pairing each emitted
/// goal with its production theorem name.
#[test]
fn goal_list_skips_none_and_pairs_names() {
    use crate::lean_ast::{GoalShape, GoalSpine};
    use crate::lean_name::LeanName;

    let mk = |p: &str| GoalShape {
        spine: vec![GoalSpine::Imp(LExpr::var(LeanName::synthetic("h")))],
        leaf: LExpr::var(LeanName::synthetic(p)),
    };
    let thm = |n: &str| Theorem {
        name: n.to_string(),
        binders: Vec::new(),
        goal: LExpr::var(LeanName::synthetic("g")),
        tactic: crate::lean_ast::Tactic::Named("tactus_auto".to_string()),
        requires_preamble: Vec::new(),
        heartbeats: None,
        termination_by: Vec::new(),
        decreasing_by: None,
    };
    let theorems = vec![thm("obl_a"), thm("obl_bv"), thm("obl_c")];
    let shapes = vec![Some(mk("pa")), None, Some(mk("pc"))];

    let mut s = Serializer::default();
    let (term, names) = s.goal_list(&theorems, &shapes);
    assert_eq!(names, vec!["obl_a".to_string(), "obl_c".to_string()]);
    assert_eq!(term.matches(&format!("{}.GoalList.Cons", NS)).count(), 2, "{}", term);
}

// ── W6c: reference-side raw-expr transcription (ExpX → RawExp) ──────

/// `typ_data` maps the cast-class base types to their `lib.TypData` tags.
/// Nat → `TyNat`, every other integer range (uN/int/usize) → `TyInt`,
/// bool → `TyBool`. These are the only tags the `needs_nat_coercion`
/// decision reads, so pinning them pins the cast decision's inputs.
#[test]
fn typ_data_base_tags() {
    use std::sync::Arc;
    let mut s = Serializer::default();
    let nat: Typ = Arc::new(TypX::Int(IntRange::Nat));
    let u64t: Typ = Arc::new(TypX::Int(IntRange::U(64)));
    let intt: Typ = Arc::new(TypX::Int(IntRange::Int));
    let boolt: Typ = Arc::new(TypX::Bool);
    assert_eq!(s.typ_data(&nat).unwrap(), format!("{}.TypData.TyNat", NS));
    assert_eq!(s.typ_data(&u64t).unwrap(), format!("{}.TypData.TyInt", NS));
    assert_eq!(s.typ_data(&intt).unwrap(), format!("{}.TypData.TyInt", NS));
    assert_eq!(s.typ_data(&boolt).unwrap(), format!("{}.TypData.TyBool", NS));
}

/// `typ_data` peels the SMT-only `Boxed` wrapper (a uN inside a `Boxed`
/// still tags `TyInt`), so a boxed operand still drives the coercion.
#[test]
fn typ_data_peels_boxed() {
    use std::sync::Arc;
    let mut s = Serializer::default();
    let boxed_u64: Typ = Arc::new(TypX::Boxed(Arc::new(TypX::Int(IntRange::U(64)))));
    assert_eq!(s.typ_data(&boxed_u64).unwrap(), format!("{}.TypData.TyInt", NS));
}

/// `binop_opcode` is the canonical fixed opcode table shared by both W6c
/// transcriptions. Pin the cast-class ops used by the fixture (Eq for the
/// `sum_to` postcond, Mul for the derived-coercion Case B) and that an
/// out-of-class op fails loud with a sharp census tag.
#[test]
fn binop_opcode_canonical() {
    use vir::ast::{ArithOp, BinaryOp, Mode, OverflowBehavior};
    assert_eq!(binop_opcode(&BinaryOp::Eq(Mode::Spec)).unwrap(), 0);
    assert_eq!(
        binop_opcode(&BinaryOp::Arith(ArithOp::Mul(OverflowBehavior::Allow))).unwrap(),
        8
    );
    // A bitwise op is outside the cast class → sharp census tag.
    let bad = binop_opcode(&BinaryOp::StrGetChar);
    assert_eq!(bad.unwrap_err(), "raw-binop-strgetchar");
}

/// The two W6c opcode tables MUST agree: for every structural vir op, the
/// reference `binop_opcode(vir_op)` equals the production
/// `lean_binop_opcode(binop_to_ast(vir_op))`. Pinning the whole cast class +
/// the boolean ops THROUGH production's `binop_to_ast` lowering makes a future
/// edit to one table without the other a caught test failure — the invariant
/// that keeps `expr_eq(prod, render_exp(ref))` from a FALSE opcode divergence.
#[test]
fn binop_opcode_alignment() {
    use crate::expr_shared::binop_to_ast;
    use vir::ast::{
        ArithOp, BinaryOp, Div0Behavior, InequalityOp, Mode, OverflowBehavior,
    };
    let ob = OverflowBehavior::Allow;
    let d0 = Div0Behavior::Allow;
    let vir_ops = [
        BinaryOp::Eq(Mode::Spec),
        BinaryOp::Ne,
        BinaryOp::Inequality(InequalityOp::Lt),
        BinaryOp::Inequality(InequalityOp::Le),
        BinaryOp::Inequality(InequalityOp::Gt),
        BinaryOp::Inequality(InequalityOp::Ge),
        BinaryOp::Arith(ArithOp::Add(ob)),
        BinaryOp::Arith(ArithOp::Sub(ob)),
        BinaryOp::Arith(ArithOp::Mul(ob)),
        BinaryOp::Arith(ArithOp::EuclideanDiv(d0)),
        BinaryOp::Arith(ArithOp::EuclideanMod(d0)),
        BinaryOp::And,
        BinaryOp::Or,
        BinaryOp::Implies,
    ];
    for op in &vir_ops {
        let ref_code = binop_opcode(op).expect("cast-class op has a reference opcode");
        let lean = binop_to_ast(op).expect("cast-class op lowers to a lean_ast::BinOp");
        let prod_code = lean_binop_opcode(&lean).expect("lowered op has a production opcode");
        assert_eq!(ref_code, prod_code, "opcode mismatch for {op:?}");
    }
}

/// `lexpr_to_exprdata` transcribes the Case-A production leaf `Int.toNat r =
/// lib.tri (Int.toNat n)` verbatim into the `ExprData::BinOp(Eq, Cast(r),
/// App(tri, Cast(n)))` shape the W6b `expr_mirror_kernel_computes` proof pins.
/// Atom ids come from first-appearance interning order (r=0, lib.tri=1, n=2).
#[test]
fn lexpr_to_exprdata_case_a() {
    let mut s = Serializer::default();
    // Int.toNat r
    let lhs = LExpr::app1(LExpr::var_lit("Int.toNat"), LExpr::var_synthetic("r"));
    // lib.tri (Int.toNat n)
    let rhs = LExpr::app1(
        LExpr::var_synthetic("lib.tri"),
        LExpr::app1(LExpr::var_lit("Int.toNat"), LExpr::var_synthetic("n")),
    );
    let whole = LExpr::eq(lhs, rhs);
    assert_eq!(
        s.lexpr_to_exprdata(&whole).unwrap(),
        "(lib.ExprData.BinOp 0 \
           (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat \
             (Tactus.Box.mk (lib.ExprData.Atom 0)))) \
           (Tactus.Box.mk (lib.ExprData.App 1 \
             (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat \
               (Tactus.Box.mk (lib.ExprData.Atom 2)))))))"
    );
}

/// Case-C production side: `lib.tree_head (*t)` renders as an App over a
/// `.deref` FieldProj. The deref field id is the reference `deref_field()` (0),
/// so the prod ExprData matches `render_exp`'s `FieldProj(_, 0)`.
#[test]
fn lexpr_to_exprdata_deref_fieldproj() {
    let mut s = Serializer::default();
    let deref = LExpr::field_proj(LExpr::var_synthetic("t"), "deref");
    let call = LExpr::app1(LExpr::var_synthetic("lib.tree_head"), deref);
    // heads intern in order: lib.tree_head=0, t=1.
    assert_eq!(
        s.lexpr_to_exprdata(&call).unwrap(),
        "(lib.ExprData.App 0 \
           (Tactus.Box.mk (lib.ExprData.FieldProj \
             (Tactus.Box.mk (lib.ExprData.Atom 1)) 0)))"
    );
}

/// Out-of-class nodes and multi-arg apps fail loud with sharp `ed-<k>` census
/// tags — the same fail-loud discipline as the statement walk.
#[test]
fn lexpr_to_exprdata_census_rejects() {
    use crate::lean_ast::BinOp as L;
    let mut s = Serializer::default();
    // A boolean literal is outside the cast class.
    assert_eq!(
        s.lexpr_to_exprdata(&LExpr::lit_bool(true)).unwrap_err(),
        "ed-litbool"
    );
    // A 2-arg application (e.g. `lib.Point.mk a b`) is not the single-arg class.
    let two = LExpr::app(
        LExpr::var_synthetic("lib.Point.mk"),
        vec![LExpr::var_synthetic("a"), LExpr::var_synthetic("b")],
    );
    assert_eq!(s.lexpr_to_exprdata(&two).unwrap_err(), "ed-app-arity");
    // A bitwise binop is outside the cast class (both sides reject).
    let bitand = LExpr::binop(L::BitAnd, LExpr::var_synthetic("a"), LExpr::var_synthetic("b"));
    assert_eq!(s.lexpr_to_exprdata(&bitand).unwrap_err(), "ed-binop-bitand");
}
