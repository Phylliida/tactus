//! Unit tests for `lean_name` — extracted to `src/tests/` (a `#[path]`'d
//! `mod tests` child of `lean_name`, so `use super::*` reaches private items).

use super::*;
use std::sync::Arc;

fn vid(name: &str, d: VarIdentDisambiguate) -> VarIdent {
    VarIdent(Arc::new(name.to_string()), d)
}

#[test]
fn user_var_no_suffix() {
    // Plain user name `i` with VirRenumbered — no disambiguation needed
    // because the base name is unique by Verus's SSA.
    let n = LeanName::from_var_ident(&vid("i",
        VarIdentDisambiguate::VirRenumbered { is_stmt: true, does_shadow: false, id: 0 }));
    assert_eq!(n.as_str(), "i");
}

#[test]
fn synthetic_temp_disambiguated() {
    // `tmp%%` synthetic temp with id=1 — the chained-comparison case.
    // Must produce a distinct name from `tmp%%` with id=2.
    let n1 = LeanName::from_var_ident(&vid("tmp%%",
        VarIdentDisambiguate::VirRenumbered { is_stmt: true, does_shadow: false, id: 1 }));
    let n2 = LeanName::from_var_ident(&vid("tmp%%",
        VarIdentDisambiguate::VirRenumbered { is_stmt: true, does_shadow: false, id: 2 }));
    assert_eq!(n1.as_str(), "tmp___1");
    assert_eq!(n2.as_str(), "tmp___2");
    assert_ne!(n1, n2);
}

#[test]
fn lean_keyword_quoted() {
    let n = LeanName::from_var_ident(&vid("end", VarIdentDisambiguate::VirParam));
    assert_eq!(n.as_str(), "«end»");
}

#[test]
fn lit_unchanged() {
    // `lit` is the escape hatch for hardcoded Lean refs like `"Nat"`.
    let n = LeanName::lit("Int.toNat");
    assert_eq!(n.as_str(), "Int.toNat");
}

#[test]
fn reserved_tokens_sorted_and_deduped() {
    // `is_lean_keyword` binary-searches LEAN_RESERVED_TOKENS — the list
    // must stay strictly sorted (also catches duplicates).
    let toks = crate::to_lean_type::LEAN_RESERVED_TOKENS;
    for w in toks.windows(2) {
        assert!(w[0] < w[1], "LEAN_RESERVED_TOKENS out of order: {:?} >= {:?}", w[0], w[1]);
    }
}

#[test]
fn full_reserved_token_set_quoted() {
    // Real-corpus failure (tactus-group-theory): locals named `prefix`
    // emitted raw and hit Lean's reserved token — parse error. The old
    // ~30-word hand list missed it; the list is now generated from the
    // toolchain's token table (dump_reserved_tokens.lean).
    for kw in ["prefix", "calc", "matches", "suffices", "using", "lemma"] {
        let n = LeanName::from_var_ident(&vid(kw, VarIdentDisambiguate::VirParam));
        assert_eq!(n.as_str(), format!("«{}»", kw), "{} must be «»-quoted", kw);
    }
    // Empirically NOT reserved (verified against the toolchain,
    // 2026-07-09): tactic macro heads and `.`-scoped `rec`.
    for ok in ["tactus_auto", "rec", "this", "symbol"] {
        let n = LeanName::from_var_ident(&vid(ok, VarIdentDisambiguate::VirParam));
        assert_eq!(n.as_str(), ok, "{} must stay raw", ok);
    }
    // `_` is in Lean's token table but deliberately NOT quoted: a
    // generated wildcard binder must stay a wildcard.
    let n = LeanName::from_var_ident(&vid("_", VarIdentDisambiguate::VirParam));
    assert_eq!(n.as_str(), "_");
}
