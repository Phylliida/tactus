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
    // skeleton_kernel_computes example: size = 5.
    let term = "(lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert 0)) (Tactus.Box.mk (lib.StmData.If 1 2 (Tactus.Box.mk lib.StmData.Skip) (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk lib.LeafList.Nil))))))";
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
