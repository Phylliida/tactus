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
