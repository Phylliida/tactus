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
    // W6d.2a: Assert's obligation slot is a DEEP `RawExp` (opaque-atom
    // fallback here); Ret's obligation list is a `RawExpList`. Neither the
    // inline `RawExp.Var` nor the `RawExpList.Nil` adds a counted `Cons`, so
    // the size is still 5 (Seq+Assert+If+Skip+Ret heads).
    let term = "(lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert (lib.RawExp.Var 22 lib.TypData.TyBool) 0)) (Tactus.Box.mk (lib.StmData.If 1 2 (Tactus.Box.mk lib.StmData.Skip) (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk lib.RawExpList.Nil) lib.RetBind.RetNone)))))";
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
    assert_eq!(leaf_texts.len(), 39, "golden leaf-table size drifted");
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
/// (`All`/`Imp`/`Let`/`LeafE`), the outermost-first fold direction
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
            GoalSpine::All(
                Binder::explicit(
                    LeanName::synthetic("nn"),
                    LExpr::var(LeanName::synthetic("Ity")),
                ),
                None,
            ),
            GoalSpine::Imp(LExpr::var(LeanName::synthetic("hyp0")), crate::lean_ast::HypProvenance::Other),
            GoalSpine::Let(
                LeanName::synthetic("mm"),
                LExpr::var(LeanName::synthetic("vv")),
            ),
        ],
        leaf: LExpr::var(LeanName::synthetic("goalpred")),
    };
    let mut s = Serializer::default();
    let term = s.goal_data(&shape);
    // Leaf-out fold: LeafE wrapped by Let, then Imp, then All outermost.
    assert!(
        term.starts_with(&format!("({}.GoalData.All ", NS)),
        "outermost node should be the ∀ binder: {}", term,
    );
    assert!(term.contains(&format!("{}.GoalData.Imp ", NS)), "{}", term);
    assert!(term.contains(&format!("{}.GoalData.Let ", NS)), "{}", term);
    // W6d.2a: the core obligation leaf is now `LeafE(ExprData.Atom …)`.
    assert!(term.contains(&format!("{}.GoalData.LeafE ", NS)), "{}", term);
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
        spine: vec![GoalSpine::Imp(LExpr::var(LeanName::synthetic("h")), crate::lean_ast::HypProvenance::Other)],
        leaf: LExpr::var(LeanName::synthetic(p)),
    };
    let thm = |n: &str| Theorem {
        name: n.to_string(),
        binders: Vec::new(),
        goal: LExpr::var(LeanName::synthetic("g")),
        closer_census: None,
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

/// W7 (bootstrap-34): a fn-headed multi-arg app (`lib.Point.mk a b`) is
/// IN-class — it lowers to `ExprData.AppN fn (ExprList a b)`, the production
/// twin of the reference `RawExp::CallN` (`render_exp` lowers both to `AppN`,
/// keyed on the same interned fn id). Interning order: the head `lib.Point.mk`
/// interns first (id 0), then the AppN arm builds the cons-list by folding the
/// value args in REVERSE (`args.iter().rev()`) — so `b` interns to 1, `a` to 2,
/// and the resulting list reads `a(2) :: b(1) :: Nil` (source order preserved).
#[test]
fn lexpr_to_exprdata_appn_multiarg() {
    let mut s = Serializer::default();
    let two = LExpr::app(
        LExpr::var_synthetic("lib.Point.mk"),
        vec![LExpr::var_synthetic("a"), LExpr::var_synthetic("b")],
    );
    assert_eq!(
        s.lexpr_to_exprdata(&two).unwrap(),
        "(lib.ExprData.AppN 0 \
           (Tactus.Box.mk (lib.ExprList.Cons \
             (Tactus.Box.mk (lib.ExprData.Atom 2)) \
             (Tactus.Box.mk (lib.ExprList.Cons \
               (Tactus.Box.mk (lib.ExprData.Atom 1)) \
               (Tactus.Box.mk lib.ExprList.Nil))))))"
    );
}

/// Out-of-class nodes and multi-arg apps fail loud with sharp `ed-<k>` census
/// tags — the same fail-loud discipline as the statement walk.
#[test]
fn lexpr_to_exprdata_census_rejects() {
    use crate::lean_ast::BinOp as L;
    let mut s = Serializer::default();
    // A `-`-negated int (`UnOp::Neg`) is outside the class. (Bool literals are
    // in-class via G1; `¬` (`UnOp::Not`) and `let` are in-class via G4 — see
    // `lexpr_to_exprdata_g4_not_let` below.)
    assert_eq!(
        s.lexpr_to_exprdata(&LExpr::neg(LExpr::var_synthetic("p")))
            .unwrap_err(),
        "ed-unop"
    );
    // A multi-arg app with a NON-fn head (`(*t) a b` — the head is a field
    // projection, not a `Var`/`App{Var,..}` fn name) is still out of class: the
    // multi-arg AppN arm's `app_head_fn_name` returns `None` → `ed-app-head`.
    // (bootstrap-34 widened the App arm so a *fn-headed* multi-arg app is now
    // IN-class, lowering to `ExprData.AppN` — see the positive
    // `lexpr_to_exprdata_appn_multiarg` test. bootstrap-43 refocused this
    // rejection onto the non-fn-head case, which the census still enforces.)
    let bad_head = LExpr::app(
        LExpr::field_proj(LExpr::var_synthetic("t"), "deref"),
        vec![LExpr::var_synthetic("a"), LExpr::var_synthetic("b")],
    );
    assert_eq!(s.lexpr_to_exprdata(&bad_head).unwrap_err(), "ed-app-head");
    // A bitwise binop is outside the cast class (both sides reject).
    let bitand = LExpr::binop(L::BitAnd, LExpr::var_synthetic("a"), LExpr::var_synthetic("b"));
    assert_eq!(s.lexpr_to_exprdata(&bitand).unwrap_err(), "ed-binop-bitand");
}

/// G4 (W6e) — the value-if-lift goal leaves carry `¬` (`UnOp::Not`) and `let`
/// (`ExprNode::Let`) nodes production folds into each branch obligation. Both
/// transcribe structurally; the binder name interns its rendered text (the
/// SAME text the reference `RawExp::Let` interns), and `render_exp` passes both
/// straight through so the bridge `decide`s the sub-expressions.
#[test]
fn lexpr_to_exprdata_g4_not_let() {
    let mut s = Serializer::default();
    // `¬ p` → `ExprData.Not (Atom 0)` (p interns to 0).
    assert_eq!(
        s.lexpr_to_exprdata(&LExpr::not(LExpr::var_synthetic("p")))
            .unwrap(),
        "(lib.ExprData.Not (Tactus.Box.mk (lib.ExprData.Atom 0)))"
    );
    // `let m := y; m` → `ExprData.Let m (Atom y) (Atom m)`. Fresh serializer so
    // ids are deterministic: m=0 (binder), y=1 (value read), m=0 (body read).
    let mut s2 = Serializer::default();
    let letexpr = LExpr::let_bind_synthetic(
        "m",
        LExpr::var_synthetic("y"),
        LExpr::var_synthetic("m"),
    );
    assert_eq!(
        s2.lexpr_to_exprdata(&letexpr).unwrap(),
        "(lib.ExprData.Let 0 \
           (Tactus.Box.mk (lib.ExprData.Atom 1)) \
           (Tactus.Box.mk (lib.ExprData.Atom 0)))"
    );
}

// ── W6d.2b: raw_exp peel/alias arms (G0 Box/Unbox, G7 VarAt, G1 LitBool) ──
//
// The reference-side transcription (`ExpX → RawExp`) gained three arms this
// step (still `#[allow(dead_code)]` — wiring them into the emit path with the
// deep/atom fallback gate is a later W6d.2b sub-step). These pin the raw-SST
// shapes the W6d.0 dump found dominating the fixture's obligation leaves: every
// boxed value is `Box`/`Unbox`-wrapped (G0, the #1 unlock), ensures params read
// as `VarAt(_, Pre)` not `Var` (G7), and `ensures true` literals are
// `Const(Bool)` (G1).

/// A dummy-span SST `Exp` carrying the given node + type.
fn mk_exp(x: ExpX, typ: Typ) -> Exp {
    use vir::ast::SpannedTyped;
    std::sync::Arc::new(SpannedTyped { span: vir::messages::Span::dummy(), typ, x })
}

/// An `AirLocal` var ident — matches how production renders a binder, so the
/// reference `binder_id` and the production-side atom intern the same text.
fn tvar(name: &str) -> VarIdent {
    VarIdent(std::sync::Arc::new(name.to_string()), vir::ast::VarIdentDisambiguate::AirLocal)
}

/// The spec `int` type.
fn tint() -> Typ {
    std::sync::Arc::new(TypX::Int(IntRange::Int))
}

/// G0 — `Box(Unbox(Var x))` peels transparently to the SAME `RawExp` as the
/// bare `Var x`. The dump found these SMT coercion wrappers on every boxed
/// value; peeling them is the #1 unlock (without it even `tri (1)` fails).
#[test]
fn raw_exp_peels_box_unbox() {
    let mut s = Serializer::default();
    let x = mk_exp(ExpX::Var(tvar("x")), tint());
    let unboxed = mk_exp(ExpX::UnaryOpr(UnaryOpr::Unbox(tint()), x.clone()), tint());
    let boxed = mk_exp(ExpX::UnaryOpr(UnaryOpr::Box(tint()), unboxed), tint());
    let bare = s.raw_exp(&x).unwrap();
    assert_eq!(s.raw_exp(&boxed).unwrap(), bare);
    assert_eq!(bare, format!("({NS}.RawExp.Var 0 {NS}.TypData.TyInt)"));
}

/// G0 recurses through structure: a `Box`-wrapped operand inside a `+` peels,
/// leaving both operands bare `Var`s (the shape spec-fn/arith leaves take). Add
/// opcode = 6; result ty `TyInt`; operands intern a=0, b=1.
#[test]
fn raw_exp_peels_box_inside_binop() {
    use vir::ast::{ArithOp, OverflowBehavior};
    let mut s = Serializer::default();
    let a = mk_exp(ExpX::Var(tvar("a")), tint());
    let b = mk_exp(ExpX::Var(tvar("b")), tint());
    let boxed_a = mk_exp(ExpX::UnaryOpr(UnaryOpr::Box(tint()), a), tint());
    let sum = mk_exp(
        ExpX::Binary(BinaryOp::Arith(ArithOp::Add(OverflowBehavior::Allow)), boxed_a, b),
        tint(),
    );
    assert_eq!(
        s.raw_exp(&sum).unwrap(),
        format!(
            "({NS}.RawExp.BinOp 6 {NS}.TypData.TyInt \
               (Tactus.Box.mk ({NS}.RawExp.Var 0 {NS}.TypData.TyInt)) \
               (Tactus.Box.mk ({NS}.RawExp.Var 1 {NS}.TypData.TyInt)))"
        )
    );
}

/// G7 — a pre-state param read `VarAt(n, Pre)` mirrors identically to a plain
/// `Var n` (production collapses `VarAt` to a bare `Var`), interning the same
/// binder id (0). The `Var` of the same ident reuses that id.
#[test]
fn raw_exp_varat_reads_like_var() {
    use vir::ast::VarAt;
    let mut s = Serializer::default();
    let at = mk_exp(ExpX::VarAt(tvar("n"), VarAt::Pre), tint());
    assert_eq!(s.raw_exp(&at).unwrap(), format!("({NS}.RawExp.Var 0 {NS}.TypData.TyInt)"));
    let v = mk_exp(ExpX::Var(tvar("n")), tint());
    assert_eq!(s.raw_exp(&v).unwrap(), format!("({NS}.RawExp.Var 0 {NS}.TypData.TyInt)"));
}

/// G1 — a source bool literal maps to `RawExp.LitBool` with the 0/1 nat
/// encoding (no `bool` payload — a spec `bool` renders as `Prop` and sticks
/// `decide`; W6d.1a design deviation 1). `true → 1`, `false → 0`.
#[test]
fn raw_exp_bool_literal() {
    let mut s = Serializer::default();
    let boolt: Typ = std::sync::Arc::new(TypX::Bool);
    let t = mk_exp(ExpX::Const(Constant::Bool(true)), boolt.clone());
    let f = mk_exp(ExpX::Const(Constant::Bool(false)), boolt);
    assert_eq!(s.raw_exp(&t).unwrap(), format!("({NS}.RawExp.LitBool 1)"));
    assert_eq!(s.raw_exp(&f).unwrap(), format!("({NS}.RawExp.LitBool 0)"));
}

// ── W6d.2b-2: the remaining reference arms (G6 HasType, G3 Field) + the
// goal-side G1 arm. Still `#[allow(dead_code)]` on both transcriptions — the
// emit-path gate (wire into `oblig_leaf`/`goal_data` with the both-sides-agree
// fallback) is the next sub-step.

/// G1 goal side — a production `LitBool` leaf maps to `ExprData.LitBool` with
/// the SAME 0/1 nat encoding the reference `RawExp.LitBool` renders through, so
/// an `ensures true` bridges (both sides `LitBool 1`). This closes the
/// half-landed G1 gap (2b-1 added only the reference arm).
#[test]
fn lexpr_to_exprdata_bool_literal() {
    let mut s = Serializer::default();
    assert_eq!(
        s.lexpr_to_exprdata(&LExpr::lit_bool(true)).unwrap(),
        format!("({NS}.ExprData.LitBool 1)")
    );
    assert_eq!(
        s.lexpr_to_exprdata(&LExpr::lit_bool(false)).unwrap(),
        format!("({NS}.ExprData.LitBool 0)")
    );
}

/// G6 — an unsigned-overflow `HasType(U(64))(e)` refinement carries the width
/// 64 as a first-class `RawExp.HasType`; `render_exp` re-expands it to
/// `0 ≤ e ∧ e < 2^64`. The wrapped `e` renders/peels as usual (here a bare
/// `Var`, id 0). The HasType node's OWN type is irrelevant — the arm reads the
/// width off the `U(n)` range in the `UnaryOpr`, not off `e.typ`.
#[test]
fn raw_exp_hastype_carries_width() {
    let mut s = Serializer::default();
    let inner = mk_exp(ExpX::Var(tvar("s")), tint());
    let u64ty: Typ = std::sync::Arc::new(TypX::Int(IntRange::U(64)));
    let boolt: Typ = std::sync::Arc::new(TypX::Bool);
    let ht = mk_exp(ExpX::UnaryOpr(UnaryOpr::HasType(u64ty), inner), boolt);
    assert_eq!(
        s.raw_exp(&ht).unwrap(),
        format!(
            "({NS}.RawExp.HasType 64 (Tactus.Box.mk ({NS}.RawExp.Var 0 {NS}.TypData.TyInt)))"
        )
    );
}

/// G6 — a non-unsigned refinement (here a signed `I(64)`) is NOT carried; the
/// arm fails loud (`hastype-range`) so the census tracks it rather than
/// emitting a bound production never produces.
#[test]
fn raw_exp_hastype_rejects_signed() {
    let mut s = Serializer::default();
    let inner = mk_exp(ExpX::Var(tvar("s")), tint());
    let i64ty: Typ = std::sync::Arc::new(TypX::Int(IntRange::I(64)));
    let boolt: Typ = std::sync::Arc::new(TypX::Bool);
    let ht = mk_exp(ExpX::UnaryOpr(UnaryOpr::HasType(i64ty), inner), boolt);
    assert_eq!(s.raw_exp(&ht).unwrap_err(), "hastype-range");
}

/// G3 — a tuple field projection reuses production's `field_access_name`, so
/// the reference field id interns the SAME accessor production renders: a
/// `Dt::Tuple(2)` field `"1"` → `.2` (the 1-indexed shift), interning "2".
/// The base var `r` interns first (id 0), the accessor "2" second (id 1).
#[test]
fn raw_exp_field_tuple() {
    use vir::ast::{Dt, FieldOpr, VariantCheck};
    let mut s = Serializer::default();
    let r = mk_exp(ExpX::Var(tvar("r")), tint());
    let fop = FieldOpr {
        datatype: Dt::Tuple(2),
        variant: std::sync::Arc::new("tuple%2".to_string()),
        field: std::sync::Arc::new("1".to_string()),
        get_variant: false,
        check: VariantCheck::None,
    };
    let proj = mk_exp(ExpX::UnaryOpr(UnaryOpr::Field(fop), r), tint());
    assert_eq!(
        s.raw_exp(&proj).unwrap(),
        format!(
            "({NS}.RawExp.Field 1 {NS}.TypData.TyInt \
               (Tactus.Box.mk ({NS}.RawExp.Var 0 {NS}.TypData.TyInt)))"
        )
    );
}

// ── W7c (bootstrap-28): the def-body constructors (Ite first) ──────
//
// A spec-fn body uses more than the obligation-leaf vocabulary: first-class
// `if`, `match`, quantifiers, multi-arg apply. W7b landed the `tactus-core`
// mirrors (`RawExp::Ite` / `ExprData::Ite` …); these pin the two transcriber
// arms. Coercion lives on the reference `render_exp` side (already pinned
// in-crate by `defs_expr_vocab_kernel_computes`), so the production side is a
// verbatim structural transcription and the reference side just carries the
// branch result type.

/// W7c — a body `if c { t } else { e }` maps to `RawExp.Ite` carrying the
/// branch RESULT type (the If node's own `typ`) so `render_exp` can coerce per
/// branch. Cond/branches transcribe recursively; here all three are bare Int
/// vars (interned c=0, t=1, e=2 in walk order), result type `TyInt`.
#[test]
fn raw_exp_ite_body() {
    let mut s = Serializer::default();
    let c = mk_exp(ExpX::Var(tvar("c")), tint());
    let t = mk_exp(ExpX::Var(tvar("t")), tint());
    let e = mk_exp(ExpX::Var(tvar("e")), tint());
    let ite = mk_exp(ExpX::If(c, t, e), tint());
    assert_eq!(
        s.raw_exp(&ite).unwrap(),
        format!(
            "({NS}.RawExp.Ite {NS}.TypData.TyInt \
               (Tactus.Box.mk ({NS}.RawExp.Var 0 {NS}.TypData.TyInt)) \
               (Tactus.Box.mk ({NS}.RawExp.Var 1 {NS}.TypData.TyInt)) \
               (Tactus.Box.mk ({NS}.RawExp.Var 2 {NS}.TypData.TyInt)))"
        )
    );
}

// ── W7c-ref (bootstrap-29): the VIR-surface def-body transcriber ──────
// `raw_vir_exp` reads `vir::ast::Expr` (`ExprX`), where def bodies keep `If`/
// `Match` first-class (unlike SST, where `Match` is desugared). VIR `Expr` is
// the SAME `Arc<SpannedTyped<_>>` shape as SST `Exp`, so `mk_vexpr` mirrors
// `mk_exp`. The Match arm's REAL validation is the e2e `def_eq` bridge against
// the emitted fixture def `lib.tree_head` (W7d) — a hand-built ctor `Path`
// could render differently from the compiler's under `lean_name`, so a
// hand-built Match unit test would test the arm against itself, not against
// production. These tests pin the cheap, surface-specific control flow (Ite,
// the OPTIONAL-else fail-loud that diverges from SST's 3-branch If, leaf/peel
// parity).

/// A dummy-span VIR `Expr` carrying the given node + type (the `mk_exp` analog
/// for the `vir::ast::Expr` surface).
fn mk_vexpr(x: ExprX, typ: Typ) -> VirExpr {
    use vir::ast::SpannedTyped;
    std::sync::Arc::new(SpannedTyped { span: vir::messages::Span::dummy(), typ, x })
}

/// The def-body `Ite` arm (the `tri` shape). Cond is a bool var (never
/// coerced); branches are int vars. Interning order b=0, x=1, y=2; the leading
/// slot is the If node's RESULT type (`TyInt`), which `render_exp` reads for
/// per-branch coercion. Structurally identical to the SST `raw_exp_ite_body`,
/// confirming the surfaces converge on the same `RawExp::Ite`.
#[test]
fn raw_vir_exp_ite_var_leaves() {
    let mut s = Serializer::default();
    let boolt: Typ = std::sync::Arc::new(TypX::Bool);
    let cond = mk_vexpr(ExprX::Var(tvar("b")), boolt);
    let then_ = mk_vexpr(ExprX::Var(tvar("x")), tint());
    let else_ = mk_vexpr(ExprX::Var(tvar("y")), tint());
    let ite = mk_vexpr(ExprX::If(cond, then_, Some(else_)), tint());
    assert_eq!(
        s.raw_vir_exp(&ite).unwrap(),
        format!(
            "({NS}.RawExp.Ite {NS}.TypData.TyInt \
               (Tactus.Box.mk ({NS}.RawExp.Var 0 {NS}.TypData.TyBool)) \
               (Tactus.Box.mk ({NS}.RawExp.Var 1 {NS}.TypData.TyInt)) \
               (Tactus.Box.mk ({NS}.RawExp.Var 2 {NS}.TypData.TyInt)))"
        )
    );
}

/// VIR `If`'s else is OPTIONAL (unlike SST's 3-branch `If`); an else-less `if`
/// can't be a value-position def body → fail loud `if-noelse` (census-tracked,
/// never a silent pass). This is a genuine VIR-surface divergence from
/// `raw_exp`, so it gets its own pin.
#[test]
fn raw_vir_exp_if_noelse_fails() {
    let mut s = Serializer::default();
    let boolt: Typ = std::sync::Arc::new(TypX::Bool);
    let cond = mk_vexpr(ExprX::Var(tvar("b")), boolt);
    let then_ = mk_vexpr(ExprX::Var(tvar("x")), tint());
    let ite = mk_vexpr(ExprX::If(cond, then_, None), tint());
    assert_eq!(s.raw_vir_exp(&ite).unwrap_err(), "rawvir-if-noelse");
}

/// Leaf/peel parity with SST `raw_exp`: `Box(Unbox(Var x))` peels transparently
/// to the bare `Var x` (same binder id + typ) on the VIR surface too — the SMT
/// coercion wrappers carry no expression content.
#[test]
fn raw_vir_exp_peels_box_and_reads_var() {
    let mut s = Serializer::default();
    let x = mk_vexpr(ExprX::Var(tvar("x")), tint());
    let unboxed = mk_vexpr(ExprX::UnaryOpr(UnaryOpr::Unbox(tint()), x.clone()), tint());
    let boxed = mk_vexpr(ExprX::UnaryOpr(UnaryOpr::Box(tint()), unboxed), tint());
    let bare = s.raw_vir_exp(&x).unwrap();
    assert_eq!(s.raw_vir_exp(&boxed).unwrap(), bare);
    assert_eq!(bare, format!("({NS}.RawExp.Var 0 {NS}.TypData.TyInt)"));
}

/// A real spec-fn body arrives wrapped in the frontend's statement-less
/// block-expr `Block([], Some(tail))` — the shape the LIVE emit path feeds
/// (`tri`/`sq`/`tree_head`), which the bare-Ite unit pins missed and which hit
/// `rawvir-block` on the first live run (W7d, bootstrap-33). Production's
/// `block_to_node` peels an empty block straight to the lowered tail, so the
/// reference must too: the wrapped body serializes byte-identically to its bare
/// tail. (Fresh serializer per call so interning starts from 0 for both.)
#[test]
fn raw_vir_exp_peels_empty_block_to_tail() {
    let boolt: Typ = std::sync::Arc::new(TypX::Bool);
    let mk_ite = || {
        let cond = mk_vexpr(ExprX::Var(tvar("b")), boolt.clone());
        let then_ = mk_vexpr(ExprX::Var(tvar("x")), tint());
        let else_ = mk_vexpr(ExprX::Var(tvar("y")), tint());
        mk_vexpr(ExprX::If(cond, then_, Some(else_)), tint())
    };
    let bare = Serializer::default().raw_vir_exp(&mk_ite()).unwrap();
    let block = mk_vexpr(ExprX::Block(std::sync::Arc::new(vec![]), Some(mk_ite())), tint());
    assert_eq!(Serializer::default().raw_vir_exp(&block).unwrap(), bare);
}

/// A block WITH statements (a `let` in a spec fn) is outside the
/// fixture-reachable set — it lowers production-side to `let`/`match` nesting
/// the reference doesn't yet mirror, so it must stay fail-loud (`rawvir-block`)
/// rather than silently drop the statements.
#[test]
fn raw_vir_exp_block_with_stmts_fails() {
    use vir::ast::StmtX;
    let mut s = Serializer::default();
    let tail = mk_vexpr(ExprX::Var(tvar("x")), tint());
    let stmt = vir::def::Spanned::new(
        vir::messages::Span::dummy(),
        StmtX::Expr(mk_vexpr(ExprX::Var(tvar("x")), tint())),
    );
    let block = mk_vexpr(ExprX::Block(std::sync::Arc::new(vec![stmt]), Some(tail)), tint());
    assert_eq!(s.raw_vir_exp(&block).unwrap_err(), "rawvir-block");
}

/// W7c — the production side transcribes a body if VERBATIM (any branch
/// coercion is already an `Int.toNat` App the `Cast` arm handles), matching the
/// reference `render_exp`'s `Ite`. Cond/then/else are bare vars (c=0, t=1, e=2).
#[test]
fn lexpr_to_exprdata_ite_body() {
    let mut s = Serializer::default();
    let ite = LExpr::new(ExprNode::If {
        cond: Box::new(LExpr::var_synthetic("c")),
        then_: Box::new(LExpr::var_synthetic("t")),
        else_: Some(Box::new(LExpr::var_synthetic("e"))),
    });
    assert_eq!(
        s.lexpr_to_exprdata(&ite).unwrap(),
        format!(
            "({NS}.ExprData.Ite \
               (Tactus.Box.mk ({NS}.ExprData.Atom 0)) \
               (Tactus.Box.mk ({NS}.ExprData.Atom 1)) \
               (Tactus.Box.mk ({NS}.ExprData.Atom 2)))"
        )
    );
}

/// W7c — an else-less `if` is not a value-position body; the production arm
/// fails loud (`ed-if-noelse`) so the census tracks it rather than emitting a
/// shape the reference side has no counterpart for.
#[test]
fn lexpr_to_exprdata_ite_no_else_fails() {
    let mut s = Serializer::default();
    let ite = LExpr::new(ExprNode::If {
        cond: Box::new(LExpr::var_synthetic("c")),
        then_: Box::new(LExpr::var_synthetic("t")),
        else_: None,
    });
    assert_eq!(s.lexpr_to_exprdata(&ite).unwrap_err(), "ed-if-noelse");
}

/// W7c (bootstrap-28) — the production `match`-body transcription (the
/// `tree_head` exemplar: `match t { Tree.Leaf v => v, Tree.Node _l _r => 0 }`).
/// Interning follows the production walk order: scrutinee first (t=0), then arms
/// REVERSED (the fold builds the list right-to-left): the Node arm interns its
/// ctor `lib.Tree.Node`=1 and its field binders reversed (_r=2, _l=3), then the
/// Leaf arm interns `lib.Tree.Leaf`=4 and `v`=5 (the body reuses `v`=5). The
/// binder-id list preserves the pattern arg order (`_l`=3 then `_r`=2 in the
/// Node list). This pins the production shape; cross-side `def_eq` agreement
/// against the reference `MatchR` is the W7d e2e bridge's job.
#[test]
fn lexpr_to_exprdata_match_tree_head() {
    use crate::lean_ast::MatchArm;
    use crate::lean_name::LeanName;
    let mut s = Serializer::default();
    let leaf_arm = MatchArm {
        pattern: LPattern::Ctor {
            name: "lib.Tree.Leaf".to_string(),
            args: vec![LPattern::Var(LeanName::synthetic("v"))],
        },
        body: LExpr::var_synthetic("v"),
    };
    let node_arm = MatchArm {
        pattern: LPattern::Ctor {
            name: "lib.Tree.Node".to_string(),
            args: vec![
                LPattern::Var(LeanName::synthetic("_l")),
                LPattern::Var(LeanName::synthetic("_r")),
            ],
        },
        body: LExpr::lit_int("0"),
    };
    let m = LExpr::match_expr(LExpr::var_synthetic("t"), vec![leaf_arm, node_arm]);
    assert_eq!(
        s.lexpr_to_exprdata(&m).unwrap(),
        format!(
            "({NS}.ExprData.Match \
               (Tactus.Box.mk ({NS}.ExprData.Atom 0)) \
               (Tactus.Box.mk \
                 ({NS}.ArmList.Cons 4 \
                    ({NS}.BinderIdList.Cons 5 (Tactus.Box.mk {NS}.BinderIdList.Nil)) \
                    (Tactus.Box.mk ({NS}.ExprData.Atom 5)) \
                    (Tactus.Box.mk \
                      ({NS}.ArmList.Cons 1 \
                         ({NS}.BinderIdList.Cons 3 (Tactus.Box.mk \
                            ({NS}.BinderIdList.Cons 2 (Tactus.Box.mk {NS}.BinderIdList.Nil)))) \
                         (Tactus.Box.mk ({NS}.ExprData.Lit 0)) \
                         (Tactus.Box.mk {NS}.ArmList.Nil))))))"
        )
    );
}

/// W7c — a non-ctor arm pattern (a bare `_` at the arm head) has no `ArmList`
/// counterpart in a datatype match; the production arm fails loud (`ed-arm-pat`)
/// rather than emit a shape the reference `MatchR` side cannot produce. Mirrors
/// the reference twin's `rawvir-arm-pat`, so the two sides reject in lockstep.
#[test]
fn lexpr_to_exprdata_match_nonctor_arm_fails() {
    use crate::lean_ast::MatchArm;
    let mut s = Serializer::default();
    let arm = MatchArm {
        pattern: LPattern::Wildcard,
        body: LExpr::lit_int("0"),
    };
    let m = LExpr::match_expr(LExpr::var_synthetic("t"), vec![arm]);
    assert_eq!(s.lexpr_to_exprdata(&m).unwrap_err(), "ed-arm-pat");
}

// ── W7c (bootstrap-29): quantifier def-body constructors — Forall/Exists on
// BOTH transcriber sides. tgt-slice-only (no fixture body is quantified);
// verdict-neutral (the reference `raw_vir_exp` is dead code, and the production
// arm is unreachable on the emit path — a quantifier-cored obligation makes the
// SST `raw_exp` fail loud `raw-bind`, so it never enters `deep_ids`, so
// `goal_data` never calls `lexpr_to_exprdata` on a quantifier goal leaf).

/// Reference `raw_vir_exp` on `∀ (i j : int), p` — VIR carries BOTH binders in
/// one `Quant`; they nest right-to-left into single-binder `ForallR` (`∀ i j, p`
/// ⟶ `ForallR i (ForallR j p)`). Interning follows the walk: body `p` first
/// (bool var → id 0), then binders REVERSED (`j`=1, then `i`=2); binder types are
/// `TyInt`, the body's own type is `TyBool`.
#[test]
fn raw_vir_exp_forall_nests_binders() {
    use std::sync::Arc;
    let mut s = Serializer::default();
    let boolt: Typ = Arc::new(TypX::Bool);
    let binders: vir::ast::VarBinders<Typ> = Arc::new(vec![
        Arc::new(vir::ast::VarBinderX { name: tvar("i"), a: tint() }),
        Arc::new(vir::ast::VarBinderX { name: tvar("j"), a: tint() }),
    ]);
    let body = mk_vexpr(ExprX::Var(tvar("p")), boolt.clone());
    let q = mk_vexpr(
        ExprX::Quant(vir::ast::Quant { quant: air::ast::Quant::Forall }, binders, body),
        boolt,
    );
    assert_eq!(
        s.raw_vir_exp(&q).unwrap(),
        format!(
            "({NS}.RawExp.ForallR 2 {NS}.TypData.TyInt \
               (Tactus.Box.mk \
                 ({NS}.RawExp.ForallR 1 {NS}.TypData.TyInt \
                    (Tactus.Box.mk ({NS}.RawExp.Var 0 {NS}.TypData.TyBool)))))"
        )
    );
}

/// Reference `raw_vir_exp` on `∃ (i : int), p` — pins the `ExistsR` ctor (the
/// arm shares `lquant`-style folding with `ForallR`, differing only in the
/// ctor name off `quant.quant`).
#[test]
fn raw_vir_exp_exists_single_binder() {
    use std::sync::Arc;
    let mut s = Serializer::default();
    let boolt: Typ = Arc::new(TypX::Bool);
    let binders: vir::ast::VarBinders<Typ> =
        Arc::new(vec![Arc::new(vir::ast::VarBinderX { name: tvar("i"), a: tint() })]);
    let body = mk_vexpr(ExprX::Var(tvar("p")), boolt.clone());
    let q = mk_vexpr(
        ExprX::Quant(vir::ast::Quant { quant: air::ast::Quant::Exists }, binders, body),
        boolt,
    );
    assert_eq!(
        s.raw_vir_exp(&q).unwrap(),
        format!(
            "({NS}.RawExp.ExistsR 1 {NS}.TypData.TyInt \
               (Tactus.Box.mk ({NS}.RawExp.Var 0 {NS}.TypData.TyBool)))"
        )
    );
}

/// Production `lexpr_to_exprdata` on `∀ (i j : Int), p` — the production node
/// carries BOTH binders in one `Forall`; `lquant_to_exprdata` nests them
/// right-to-left into single-binder `ExprData::Forall`, the IDENTICAL nesting
/// the reference `raw_vir_exp` does over the same order (so `def_eq` agrees by
/// construction). Interning: body `p`=0, then binders reversed (`j`=1, `i`=2);
/// each `Int` binder type is recognized back to `TyInt` by `ltyp_to_typdata`.
#[test]
fn lexpr_to_exprdata_forall_nests_binders() {
    use crate::lean_ast::Binder;
    use crate::lean_name::LeanName;
    let mut s = Serializer::default();
    let q = LExpr::new(ExprNode::Forall {
        binders: vec![
            Binder::explicit(LeanName::synthetic("i"), LExpr::var_lit("Int")),
            Binder::explicit(LeanName::synthetic("j"), LExpr::var_lit("Int")),
        ],
        body: Box::new(LExpr::var_synthetic("p")),
    });
    assert_eq!(
        s.lexpr_to_exprdata(&q).unwrap(),
        format!(
            "({NS}.ExprData.Forall 2 {NS}.TypData.TyInt \
               (Tactus.Box.mk \
                 ({NS}.ExprData.Forall 1 {NS}.TypData.TyInt \
                    (Tactus.Box.mk ({NS}.ExprData.Atom 0)))))"
        )
    );
}

/// Production `ltyp_to_typdata` — the quantifier binder-type recognizer that
/// inverts `typ_to_expr` back to the `TypData` the reference `typ_data` emits.
/// Primitive heads map by name; a named datatype maps to `TyNamed(intern(pp))`;
/// a `Tactus.Ref` application to `TyRef(intern(pp(inner)))`; a non-type node
/// fails loud. NOTE the documented gap: `Nat` maps to `TyNat` (a `usize`/`char`
/// binder also renders `Var("Nat")` but the reference maps it to `TyInt`, so
/// such a binder spuriously fails the bridge — uncertifiable, never unsound).
#[test]
fn ltyp_to_typdata_recognizes_types() {
    let mut s = Serializer::default();
    assert_eq!(s.ltyp_to_typdata(&LExpr::var_lit("Prop")).unwrap(), format!("{NS}.TypData.TyBool"));
    assert_eq!(s.ltyp_to_typdata(&LExpr::var_lit("Nat")).unwrap(), format!("{NS}.TypData.TyNat"));
    assert_eq!(s.ltyp_to_typdata(&LExpr::var_lit("Int")).unwrap(), format!("{NS}.TypData.TyInt"));
    // Named datatype: id = intern(pp_expr(Var "lib.Tree")). Fresh serializer, so
    // this is the first interned leaf (id 0).
    assert_eq!(
        s.ltyp_to_typdata(&LExpr::var_lit("lib.Tree")).unwrap(),
        format!("({NS}.TypData.TyNamed 0)")
    );
    // `&T` binder → TyRef(intern(pp of the inner type-expr)) — agrees with the
    // reference `typ_data`'s `TyRef(typ_leaf(inner))` by construction.
    let refty = LExpr::app(LExpr::var_lit("Tactus.Ref"), vec![LExpr::var_lit("Int")]);
    assert_eq!(
        s.ltyp_to_typdata(&refty).unwrap(),
        format!("({NS}.TypData.TyRef 1)")
    );
    // A non-type node (a bool literal) is not a binder type → fail loud.
    assert_eq!(s.ltyp_to_typdata(&LExpr::lit_bool(true)).unwrap_err(), "ed-quant-bty");
}

// ── W7c (bootstrap-30): def-header transcription (RawDef / DefData) ──

/// The spec `nat` type.
fn tnat() -> Typ {
    std::sync::Arc::new(TypX::Int(IntRange::Nat))
}

/// A crate-local `Fun` with path `lib::<name>` (krate = None). `call_fun_id`
/// interns `LeanName::from_path` of this, = production's `def.name`.
fn mk_fun(name: &str) -> vir::ast::Fun {
    use vir::ast::{FunX, PathX};
    let path = std::sync::Arc::new(PathX {
        krate: None,
        segments: std::sync::Arc::new(vec![
            std::sync::Arc::new("lib".to_string()),
            std::sync::Arc::new(name.to_string()),
        ]),
    });
    std::sync::Arc::new(FunX { path })
}

/// `Params` from `(name, typ)` pairs — non-mut value params (spec-fn shape).
fn mk_params(items: Vec<(&str, Typ)>) -> vir::ast::Params {
    use vir::ast::ParamX;
    use vir::def::Spanned;
    use vir::messages::Span;
    std::sync::Arc::new(
        items
            .into_iter()
            .map(|(n, typ)| {
                Spanned::new(
                    Span::dummy(),
                    ParamX {
                        name: tvar(n),
                        typ,
                        mode: vir::ast::Mode::Spec,
                        user_mut: false,
                        is_mut: false,
                        unwrapped_info: None,
                    },
                )
            })
            .collect(),
    )
}

/// The reference def-header transcriber on a `tri`-shaped header: name
/// `lib::tri`, one `nat` value param `n`, `nat` ret, a trivial `Var n` body
/// (the header is under test; the Ite body is `raw_vir_exp`'s own pin). Forward
/// interning fixes name=0, n=1; the body reuses n=1. The single boxed
/// `ParamList` tail matches production's `ldef_to_defdata` by construction.
#[test]
fn raw_vir_def_tri_header() {
    let mut s = Serializer::default();
    let empty_tps: vir::ast::Idents = std::sync::Arc::new(vec![]);
    let params = mk_params(vec![("n", tnat())]);
    let body = mk_vexpr(ExprX::Var(tvar("n")), tnat());
    assert_eq!(
        s.raw_vir_def(&mk_fun("tri"), &empty_tps, &params, &tnat(), &body).unwrap(),
        format!(
            "({NS}.RawDef.mk 0 \
               ({NS}.ParamList.Cons 1 {NS}.TypData.TyNat (Tactus.Box.mk {NS}.ParamList.Nil)) \
               {NS}.TypData.TyNat \
               ({NS}.RawExp.Var 1 {NS}.TypData.TyNat))"
        )
    );
}

/// A polymorphic def (non-empty `typ_params`) fails loud — production's
/// `Def.binders` would prepend `{A : Type}` binders `TypData` can't mirror.
/// Deferred (tgt-slice), like AppN; the fixture defs are monomorphic.
#[test]
fn raw_vir_def_poly_fails() {
    let mut s = Serializer::default();
    let tps: vir::ast::Idents = std::sync::Arc::new(vec![std::sync::Arc::new("A".to_string())]);
    let params = mk_params(vec![]);
    let body = mk_vexpr(ExprX::Var(tvar("x")), tint());
    assert_eq!(
        s.raw_vir_def(&mk_fun("f"), &tps, &params, &tint(), &body).unwrap_err(),
        "rawvir-def-poly"
    );
}

/// The production def-header transcriber on the SAME `tri`-shaped header — a
/// `lean_ast::Def` with one explicit `n : Nat` binder + `Nat` ret + `Var n`
/// body. Emits the `DefData` twin of `raw_vir_def_tri_header`: name=0, param
/// (1 : TyNat), ret TyNat, body `Atom 1`. Id agreement with the reference is
/// by construction (shared `lean_name`/`from_var_ident`/`typ_to_expr`
/// interning); cross-side `def_eq` is the W7d bridge's job.
#[test]
fn ldef_to_defdata_tri_header() {
    use crate::lean_ast::{Binder, Def};
    use crate::lean_name::LeanName;
    let mut s = Serializer::default();
    let n = LeanName::from_var_ident(&tvar("n"));
    let def = Def {
        attrs: vec![],
        name: "lib.tri".to_string(),
        binders: vec![Binder::explicit(n.clone(), LExpr::var_lit("Nat"))],
        ret_ty: LExpr::var_lit("Nat"),
        body: LExpr::var(n),
        termination_by: vec![],
        termination_structural: false,
        decreasing_by: None,
    };
    assert_eq!(
        s.ldef_to_defdata(&def).unwrap(),
        format!(
            "({NS}.DefData.mk 0 \
               ({NS}.ParamList.Cons 1 {NS}.TypData.TyNat (Tactus.Box.mk {NS}.ParamList.Nil)) \
               {NS}.TypData.TyNat \
               ({NS}.ExprData.Atom 1))"
        )
    );
}

// ── W7c (bootstrap-31): datatype transcription (RawDt / DtData) ──
//
// The `Tree` fixture datatype (`enum Tree { Leaf(u64), Node(Box<Tree>,
// Box<Tree>) }`, emitted `inductive lib.Tree | Leaf (Int) | Node (Tactus.Box
// lib.Tree) (Tactus.Box lib.Tree)`). The load-bearing subtlety is the `Box`:
// a datatype FIELD keeps it (`TyBox`), unlike a value-position expr type where
// the cast layer peels it. Both sides map `Box<Tree>` → `TyBox(<lib.Tree id>)`,
// and since the datatype name interns `lib.Tree` first, the `TyBox` pointee
// reuses that id (0) — a nice cross-side coincidence the two independent
// Serializers both produce (real cross-side fidelity is the W7d e2e bridge).

/// A crate-local datatype `Path` `lib::<name>` (the `mk_fun` analog for a Dt);
/// `lean_name` of it is the interned datatype name.
fn mk_dt_path(name: &str) -> vir::ast::Path {
    use vir::ast::PathX;
    std::sync::Arc::new(PathX {
        krate: None,
        segments: std::sync::Arc::new(vec![
            std::sync::Arc::new("lib".to_string()),
            std::sync::Arc::new(name.to_string()),
        ]),
    })
}

/// A nullary `TypX::Datatype` at the given path — the self-reference a recursive
/// `Box<Tree>` field wraps. Its `typ_to_expr` renders to `lean_name(path)`, so
/// `typ_leaf` interns the SAME string as the datatype name.
fn tdatatype(path: &vir::ast::Path) -> Typ {
    std::sync::Arc::new(TypX::Datatype(
        Dt::Path(path.clone()),
        std::sync::Arc::new(vec![]),
        std::sync::Arc::new(vec![]),
    ))
}

/// A `Box<T>` decorated (datatype-field) type.
fn tbox(inner: Typ) -> Typ {
    std::sync::Arc::new(TypX::Decorate(TypDecoration::Box, None, inner))
}

/// A `u64` type — renders `TyInt` (the `Leaf(u64)` field's type).
fn tu64() -> Typ {
    std::sync::Arc::new(TypX::Int(IntRange::U(64)))
}

/// A VIR `Variant` from a name + positional field types (field names are
/// positional `"0"`, `"1"`, … — unread by the transcriber, which keeps only the
/// TYPES; W7a §7 Q4).
fn mk_variant(name: &str, fields: Vec<Typ>) -> vir::ast::Variant {
    use vir::ast::{CtorPrintStyle, Variant, Visibility};
    let flds: vir::ast::Fields = std::sync::Arc::new(
        fields
            .into_iter()
            .enumerate()
            .map(|(i, typ)| {
                std::sync::Arc::new(air::ast::BinderX {
                    name: std::sync::Arc::new(format!("{}", i)),
                    a: (typ, vir::ast::Mode::Spec, Visibility { restricted_to: None }),
                })
            })
            .collect(),
    );
    Variant { name: std::sync::Arc::new(name.to_string()), fields: flds, ctor_style: CtorPrintStyle::Parens }
}

/// The reference datatype transcriber on the `Tree` shape. Interning follows the
/// forward walk: name `lib.Tree`=0, then ctor `Leaf`=1, then ctor `Node`=2; the
/// `Box<Tree>` field's `TyBox` pointee reuses the `lib.Tree` id (0). The
/// `CtorList` and each `TypList` are folded reversed (boxed self-recursive
/// tails). The `Box` is KEPT (`TyBox 0`), NOT peeled to `TyNamed` — the W7a §7 Q4
/// subtlety this test exists to pin.
#[test]
fn raw_vir_dt_tree() {
    let mut s = Serializer::default();
    let path = mk_dt_path("Tree");
    let empty_tps: vir::ast::TypPositives = std::sync::Arc::new(vec![]);
    let variants: vir::ast::Variants = std::sync::Arc::new(vec![
        mk_variant("Leaf", vec![tu64()]),
        mk_variant("Node", vec![tbox(tdatatype(&path)), tbox(tdatatype(&path))]),
    ]);
    assert_eq!(
        s.raw_vir_dt(&Dt::Path(path), &empty_tps, &variants).unwrap(),
        format!(
            "({NS}.RawDt.mk 0 \
               ({NS}.CtorList.Cons 1 \
                  ({NS}.TypList.Cons {NS}.TypData.TyInt (Tactus.Box.mk {NS}.TypList.Nil)) \
                  (Tactus.Box.mk \
                     ({NS}.CtorList.Cons 2 \
                        ({NS}.TypList.Cons ({NS}.TypData.TyBox 0) \
                           (Tactus.Box.mk ({NS}.TypList.Cons ({NS}.TypData.TyBox 0) \
                              (Tactus.Box.mk {NS}.TypList.Nil)))) \
                        (Tactus.Box.mk {NS}.CtorList.Nil)))))"
        )
    );
}

/// A polymorphic datatype (non-empty `typ_params`) fails loud — like
/// `raw_vir_def`, production's `(A : Type)` params have no `TypData` mirror.
#[test]
fn raw_vir_dt_poly_fails() {
    let mut s = Serializer::default();
    let tps: vir::ast::TypPositives = std::sync::Arc::new(vec![(
        std::sync::Arc::new("A".to_string()),
        vir::ast::AcceptRecursiveType::RejectInGround,
    )]);
    let variants: vir::ast::Variants =
        std::sync::Arc::new(vec![mk_variant("Leaf", vec![tu64()])]);
    assert_eq!(
        s.raw_vir_dt(&Dt::Path(mk_dt_path("Poly")), &tps, &variants).unwrap_err(),
        "rawvir-dt-poly"
    );
}

/// A single-variant struct (variant name == the type short name) fails loud —
/// production emits a `structure` (ctor = type name, no variant list), a
/// different transcription. `Tree` (multi-variant) certifies; `Point` (a
/// one-variant struct) is gated here.
#[test]
fn raw_vir_dt_struct_fails() {
    let mut s = Serializer::default();
    let variants: vir::ast::Variants =
        std::sync::Arc::new(vec![mk_variant("Point", vec![tint(), tint()])]);
    let empty_tps: vir::ast::TypPositives = std::sync::Arc::new(vec![]);
    assert_eq!(
        s.raw_vir_dt(&Dt::Path(mk_dt_path("Point")), &empty_tps, &variants).unwrap_err(),
        "rawvir-dt-struct"
    );
}

/// The production datatype transcriber on the SAME `Tree` shape — a
/// `lean_ast::Datatype` (`Inductive`) with the already-rendered field types
/// (`Int`, `Tactus.Box lib.Tree`). Emits the `DtData` twin of `raw_vir_dt_tree`
/// (name=0, Leaf=1 [TyInt], Node=2 [TyBox 0, TyBox 0]); `ldt_field_typdata`
/// recognizes `Tactus.Box lib.Tree` back to `TyBox` with the same pointee id.
#[test]
fn ldt_to_dtdata_tree() {
    use crate::lean_ast::{Datatype, DatatypeKind, Field, Variant};
    let mut s = Serializer::default();
    let box_tree = LExpr::new(ExprNode::App {
        head: Box::new(LExpr::var_lit("Tactus.Box")),
        args: vec![LExpr::var_lit("lib.Tree")],
    });
    let dt = Datatype {
        name: "lib.Tree".to_string(),
        self_name: "Tree".to_string(),
        typ_params: vec![],
        kind: DatatypeKind::Inductive {
            variants: vec![
                Variant {
                    name: "Leaf".to_string(),
                    fields: vec![Field { name: "val0".to_string(), ty: LExpr::var_lit("Int") }],
                },
                Variant {
                    name: "Node".to_string(),
                    fields: vec![
                        Field { name: "val0".to_string(), ty: box_tree.clone() },
                        Field { name: "val1".to_string(), ty: box_tree.clone() },
                    ],
                },
            ],
        },
        derives: vec!["Inhabited".to_string()],
    };
    assert_eq!(
        s.ldt_to_dtdata(&dt).unwrap(),
        format!(
            "({NS}.DtData.mk 0 \
               ({NS}.CtorList.Cons 1 \
                  ({NS}.TypList.Cons {NS}.TypData.TyInt (Tactus.Box.mk {NS}.TypList.Nil)) \
                  (Tactus.Box.mk \
                     ({NS}.CtorList.Cons 2 \
                        ({NS}.TypList.Cons ({NS}.TypData.TyBox 0) \
                           (Tactus.Box.mk ({NS}.TypList.Cons ({NS}.TypData.TyBox 0) \
                              (Tactus.Box.mk {NS}.TypList.Nil)))) \
                        (Tactus.Box.mk {NS}.CtorList.Nil)))))"
        )
    );
}

/// A single-variant `Structure` fails loud (`ed-dt-struct`) — the reference gates
/// it symmetrically (`rawvir-dt-struct`).
#[test]
fn ldt_to_dtdata_structure_fails() {
    use crate::lean_ast::{Datatype, DatatypeKind, Field};
    let mut s = Serializer::default();
    let dt = Datatype {
        name: "lib.Point".to_string(),
        self_name: "Point".to_string(),
        typ_params: vec![],
        kind: DatatypeKind::Structure {
            fields: vec![Field { name: "x".to_string(), ty: LExpr::var_lit("Int") }],
        },
        derives: vec!["Inhabited".to_string()],
    };
    assert_eq!(s.ldt_to_dtdata(&dt).unwrap_err(), "ed-dt-struct");
}

// ── W7d (bootstrap-32): defs-layer certificate emission ──────────────────
//
// `serialize_def` / `serialize_dt` drive BOTH transcribers on one shared
// `Serializer`; the tests assert the returned `(raw, defdata)` / `(raw, dtdata)`
// pairs are BYTE-IDENTICAL to the two independent unit-test pins above — i.e.
// the shared serializer keeps the reference and production ids aligned, so it
// reproduces the EXACT pair `probe16_w7d_defbridge` proved closes `def_eq` /
// `dt_eq` under `decide`. The `render_*_cert` tests then pin that the assembler
// embeds those literals verbatim and emits the proven bridge `example` line.

/// `serialize_def` on the `tri` fixture: the shared serializer reproduces the
/// `raw_vir_def_tri_header` × `ldef_to_defdata_tri_header` pair (name 0, param
/// 1, body `Var 1` / `Atom 1`) — the probe16-proven `def_eq` inputs.
#[test]
fn serialize_def_tri_shared_serializer() {
    use crate::lean_ast::{Binder, Def};
    use crate::lean_name::LeanName;
    // Reference (VIR) side — the `raw_vir_def_tri_header` inputs.
    let empty_tps: vir::ast::Idents = std::sync::Arc::new(vec![]);
    let params = mk_params(vec![("n", tnat())]);
    let body = mk_vexpr(ExprX::Var(tvar("n")), tnat());
    // Production (`lean_ast`) side — the `ldef_to_defdata_tri_header` `Def`.
    let n = LeanName::from_var_ident(&tvar("n"));
    let def = Def {
        attrs: vec![],
        name: "lib.tri".to_string(),
        binders: vec![Binder::explicit(n.clone(), LExpr::var_lit("Nat"))],
        ret_ty: LExpr::var_lit("Nat"),
        body: LExpr::var(n),
        termination_by: vec![],
        termination_structural: false,
        decreasing_by: None,
    };
    let (raw, defdata) =
        serialize_def(&mk_fun("tri"), &empty_tps, &params, &tnat(), &body, &def).unwrap();
    assert_eq!(
        raw,
        format!(
            "({NS}.RawDef.mk 0 \
               ({NS}.ParamList.Cons 1 {NS}.TypData.TyNat (Tactus.Box.mk {NS}.ParamList.Nil)) \
               {NS}.TypData.TyNat \
               ({NS}.RawExp.Var 1 {NS}.TypData.TyNat))"
        )
    );
    assert_eq!(
        defdata,
        format!(
            "({NS}.DefData.mk 0 \
               ({NS}.ParamList.Cons 1 {NS}.TypData.TyNat (Tactus.Box.mk {NS}.ParamList.Nil)) \
               {NS}.TypData.TyNat \
               ({NS}.ExprData.Atom 1))"
        )
    );
}

/// A polymorphic def fails the REFERENCE gate FIRST (`?` short-circuits), so
/// `serialize_def` returns the reference's `rawvir-def-poly` tag and never runs
/// production — no half-cert is written.
#[test]
fn serialize_def_poly_gates_on_reference() {
    use crate::lean_ast::Def;
    let tps: vir::ast::Idents =
        std::sync::Arc::new(vec![std::sync::Arc::new("A".to_string())]);
    let params = mk_params(vec![]);
    let body = mk_vexpr(ExprX::Var(tvar("x")), tint());
    // The production `Def` is irrelevant — the reference gate fires first.
    let def = Def {
        attrs: vec![],
        name: "lib.f".to_string(),
        binders: vec![],
        ret_ty: LExpr::var_lit("Int"),
        body: LExpr::var_lit("x"),
        termination_by: vec![],
        termination_structural: false,
        decreasing_by: None,
    };
    assert_eq!(
        serialize_def(&mk_fun("f"), &tps, &params, &tint(), &body, &def).unwrap_err(),
        "rawvir-def-poly"
    );
}

/// `render_def_cert` embeds the `(raw, defdata)` literals verbatim and emits the
/// exact `def_eq (render_def …) … = 1 := by decide` bridge line probe16 pinned.
#[test]
fn render_def_cert_bridge_shape() {
    let text = render_def_cert("mycrate", "lib.tri", "lib__tri", "RAWLIT", "DEFDATALIT");
    assert!(text.contains(&format!("import {CERT_IMPORT}\n")));
    assert!(text.contains(&format!("def cert_lib__tri_raw : {NS}.RawDef :=\n  RAWLIT\n")));
    assert!(text.contains(&format!(
        "def cert_lib__tri_defdata : {NS}.DefData :=\n  DEFDATALIT\n"
    )));
    assert!(text.contains(&format!(
        "example : {NS}.def_eq ({NS}.render_def cert_lib__tri_raw) cert_lib__tri_defdata = 1 := by decide\n"
    )));
}

/// `serialize_dt` on the `Tree` fixture: the shared serializer reproduces the
/// `raw_vir_dt_tree` × `ldt_to_dtdata_tree` pair (name 0, Leaf=1 [TyInt],
/// Node=2 [TyBox 0, TyBox 0], Box KEPT) — the probe16-proven `dt_eq` inputs.
#[test]
fn serialize_dt_tree_shared_serializer() {
    use crate::lean_ast::{Datatype, DatatypeKind, Field, Variant as LVariant};
    // Reference (VIR) side.
    let path = mk_dt_path("Tree");
    let empty_tps: vir::ast::TypPositives = std::sync::Arc::new(vec![]);
    let variants: vir::ast::Variants = std::sync::Arc::new(vec![
        mk_variant("Leaf", vec![tu64()]),
        mk_variant("Node", vec![tbox(tdatatype(&path)), tbox(tdatatype(&path))]),
    ]);
    // Production (`lean_ast`) side.
    let box_tree = LExpr::new(ExprNode::App {
        head: Box::new(LExpr::var_lit("Tactus.Box")),
        args: vec![LExpr::var_lit("lib.Tree")],
    });
    let dt = Datatype {
        name: "lib.Tree".to_string(),
        self_name: "Tree".to_string(),
        typ_params: vec![],
        kind: DatatypeKind::Inductive {
            variants: vec![
                LVariant {
                    name: "Leaf".to_string(),
                    fields: vec![Field { name: "val0".to_string(), ty: LExpr::var_lit("Int") }],
                },
                LVariant {
                    name: "Node".to_string(),
                    fields: vec![
                        Field { name: "val0".to_string(), ty: box_tree.clone() },
                        Field { name: "val1".to_string(), ty: box_tree.clone() },
                    ],
                },
            ],
        },
        derives: vec!["Inhabited".to_string()],
    };
    let (raw, dtdata) =
        serialize_dt(&Dt::Path(path), &empty_tps, &variants, &dt).unwrap();
    let expected_ctors = format!(
        "({NS}.CtorList.Cons 1 \
           ({NS}.TypList.Cons {NS}.TypData.TyInt (Tactus.Box.mk {NS}.TypList.Nil)) \
           (Tactus.Box.mk \
              ({NS}.CtorList.Cons 2 \
                 ({NS}.TypList.Cons ({NS}.TypData.TyBox 0) \
                    (Tactus.Box.mk ({NS}.TypList.Cons ({NS}.TypData.TyBox 0) \
                       (Tactus.Box.mk {NS}.TypList.Nil)))) \
                 (Tactus.Box.mk {NS}.CtorList.Nil)))))"
    );
    assert_eq!(raw, format!("({NS}.RawDt.mk 0 {expected_ctors}"));
    assert_eq!(dtdata, format!("({NS}.DtData.mk 0 {expected_ctors}"));
}

/// `render_dt_cert` embeds the `(raw, dtdata)` literals and emits the exact
/// `dt_eq (render_dt …) … = 1 := by decide` bridge line.
#[test]
fn render_dt_cert_bridge_shape() {
    let text = render_dt_cert("mycrate", "lib.Tree", "lib__Tree", "RAWDT", "DTDATA");
    assert!(text.contains(&format!("def cert_lib__Tree_raw : {NS}.RawDt :=\n  RAWDT\n")));
    assert!(text.contains(&format!(
        "def cert_lib__Tree_dtdata : {NS}.DtData :=\n  DTDATA\n"
    )));
    assert!(text.contains(&format!(
        "example : {NS}.dt_eq ({NS}.render_dt cert_lib__Tree_raw) cert_lib__Tree_dtdata = 1 := by decide\n"
    )));
}

// ── W6d.2b-2: the emit-path gate (`oblig_slot` + `goal_data` deep/atom) ──
//
// The obligation (reference) side drives: `oblig_slot` deepens a coverable
// obligation into `RawExp.Span(loc, raw)` and records its leaf id in
// `deep_ids`; `goal_data` (run after the whole stm walk) deepens the matching
// goal leaf ONLY when that id is in `deep_ids` AND the goal transcription
// succeeds — else both fall back to the opaque `Atom(id)` by the same id. A
// forced-atom obligation (a shape `raw_exp` rejects) stays out of `deep_ids`,
// so its goal auto-stays atom (verdict-neutral, the W6d.2a behavior).

/// `oblig_slot` on a COVERABLE obligation (`true`): `raw_exp` succeeds, so the
/// slot is the deep `RawExp.Span(loc, LitBool 1)` (the `Span` wrapper added
/// here — the raw SST has no SpanMark node — matching production's outermost
/// span mark that the goal side transcribes) and the leaf id lands in
/// `deep_ids`. `loc` interns right after the span_mark'd leaf (id → id+1;
/// `raw_exp` interns nothing for a bool literal).
#[test]
fn oblig_slot_deep_wraps_span_and_records() {
    let mut s = Serializer::default();
    let boolt: Typ = std::sync::Arc::new(TypX::Bool);
    let e = mk_exp(ExpX::Const(Constant::Bool(true)), boolt);
    let (id, slot) = s.oblig_slot(&e).unwrap();
    assert!(s.deep_ids.contains(&id), "coverable obligation id recorded in deep_ids");
    assert_eq!(
        slot,
        format!("({NS}.RawExp.Span {} (Tactus.Box.mk ({NS}.RawExp.LitBool 1)))", id + 1)
    );
}

/// `oblig_slot` on a NON-coverable obligation (`¬true` — `raw_exp` has no `Not`
/// arm): the slot falls back to the opaque `atom_ob(id)` and the id is NOT
/// recorded, so the goal walk keeps the matching leaf atom too (the fn still
/// serializes; only this obligation stays shallow).
#[test]
fn oblig_slot_atom_fallback_when_not_coverable() {
    let mut s = Serializer::default();
    let boolt: Typ = std::sync::Arc::new(TypX::Bool);
    let inner = mk_exp(ExpX::Const(Constant::Bool(true)), boolt.clone());
    let e = mk_exp(ExpX::Unary(UnaryOp::Not, inner), boolt);
    let (id, slot) = s.oblig_slot(&e).unwrap();
    assert!(!s.deep_ids.contains(&id), "non-coverable obligation id NOT in deep_ids");
    assert_eq!(slot, format!("({NS}.RawExp.Var {} {NS}.TypData.TyBool)", id));
}

/// `goal_data` gate — the SAME goal leaf (`a = b`, which transcribes to a
/// visibly-distinct `BinOp`) deepens ONLY when its id is in `deep_ids`. Gate
/// off → opaque `Atom(whole-leaf-id)` (verdict-neutral); gate on → the
/// structural `BinOp(Eq, Atom a, Atom b)` the ref side's `render_exp` must
/// match for the bridge to `decide`.
#[test]
fn goal_data_gate_deep_only_when_in_deep_ids() {
    use crate::lean_ast::GoalShape;
    let shape = GoalShape {
        spine: vec![],
        leaf: LExpr::eq(LExpr::var_synthetic("a"), LExpr::var_synthetic("b")),
    };
    // Gate OFF: `deep_ids` empty → opaque atom fallback (whole leaf = id 0).
    let mut off = Serializer::default();
    assert_eq!(
        off.goal_data(&shape),
        "(lib.GoalData.LeafE (lib.ExprData.Atom 0))"
    );
    // Gate ON: the leaf id in `deep_ids` (ref side went deep) → the deep BinOp
    // (whole leaf = id 0, then atoms a=1, b=2).
    let mut on = Serializer::default();
    let id = on.lexpr_leaf(&shape.leaf);
    on.deep_ids.insert(id);
    assert_eq!(
        on.goal_data(&shape),
        "(lib.GoalData.LeafE (lib.ExprData.BinOp 0 \
           (Tactus.Box.mk (lib.ExprData.Atom 1)) \
           (Tactus.Box.mk (lib.ExprData.Atom 2))))"
    );
}

// ── b67 (W4b): cert write content-compare pin ───────────────────────

#[test]
fn write_if_changed_skips_byte_identical_rewrite() {
    let pid = std::process::id();
    let path = std::env::temp_dir().join(format!("tactus_b67_wic_{}.txt", pid));
    let _ = std::fs::remove_file(&path);
    // First call writes.
    assert_eq!(super::write_if_changed(&path, "aaa").unwrap(), true);
    let mtime1 = std::fs::metadata(&path).unwrap().modified().unwrap();
    // Identical content: no rewrite, mtime preserved.
    assert_eq!(super::write_if_changed(&path, "aaa").unwrap(), false);
    let mtime2 = std::fs::metadata(&path).unwrap().modified().unwrap();
    assert_eq!(mtime1, mtime2, "byte-identical rewrite must keep the mtime");
    // Changed content: rewritten.
    assert_eq!(super::write_if_changed(&path, "bbb").unwrap(), true);
    assert_eq!(std::fs::read_to_string(&path).unwrap(), "bbb");
    let _ = std::fs::remove_file(&path);
}
