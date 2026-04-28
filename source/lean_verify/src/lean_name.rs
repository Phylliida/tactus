//! `LeanName` — typed wrapper for identifiers that appear in generated Lean.
//!
//! ## Why a wrapper instead of `String`?
//!
//! Verus's `VarIdent = (Ident, VarIdentDisambiguate)` carries identity in
//! *both* halves: two VarIdents with the same `Ident` but different
//! disambiguators are *distinct variables*. Our previous renderer projected
//! to `String` via `sanitize(&v.0)`, which only sees the name half. The
//! collapse was *coincidentally* correct for user vars (Verus's SSA gives
//! them distinct strings) but **silently wrong** for synthetic temps where
//! the disambiguator alone distinguishes them.
//!
//! Concrete failure case: chained comparison `0 <= i <= 10` in a
//! `tactus_auto` fn invariant. `ast_simplify::temp_var` produces three
//! VarIdents `(tmp%%, VirRenumbered{id:N})` for N=1,2,3. Each is a distinct
//! variable in the IR, but `sanitize` collapses all three to `tmp__`. The
//! rendered Lean reads `let tmp__ := 0; let tmp__ := i; let tmp__ := 10;
//! tmp__ ≤ tmp__ ∧ tmp__ ≤ tmp__` which Lean's let-shadowing reduces to
//! `10 ≤ 10 ∧ 10 ≤ 10` = `True`. The proof obligation silently disappears.
//!
//! ## The fix: type-level enforcement
//!
//! `LeanName(String)` is a newtype with private inner field. The only way
//! to construct one is through an explicit constructor. The relevant ones:
//!
//! * [`LeanName::from_var_ident`] — the canonical entry point for any
//!   `VarIdent → Lean name` conversion. Includes the disambiguator's id
//!   when present, guaranteeing distinct VarIdents map to distinct names.
//! * [`LeanName::from_path`] — for fully-qualified module/fn paths
//!   (`crate.module.fn`). VIR `Path` doesn't carry a disambiguator.
//! * [`LeanName::lit`] — for hardcoded prelude/literal names (`"Nat"`,
//!   `"Int"`, `"omega"`, `"tactus_auto"`). The escape hatch.
//! * [`LeanName::synthetic`] — for codegen-generated names (gensym'd
//!   temps, theorem names like `_tactus_postcondition_*`).
//! * [`LeanName::from_field`] — for struct/enum field names. These come
//!   from Verus as `&str` (no disambiguator), so they need a separate
//!   constructor.
//!
//! `ExprNode::Var(LeanName)`, `ExprNode::Let { name: LeanName, .. }`, etc.
//! enforce at compile time that any name in the AST came from one of these
//! constructors. A new contributor can't accidentally write
//! `ExprNode::Var(sanitize(&v.0))` — there's no `From<String>` impl on
//! `LeanName`.
//!
//! ## What about `&str` field/path lookup?
//!
//! Some sites (struct field access, `dt.name` for a Path) only have `&str`.
//! Those use `from_field` / `from_path` / `lit` as appropriate. The naming
//! is intentional: at every call site, the constructor name documents
//! *what kind of source the name is from*, making misuse visible in code
//! review.

use vir::ast::{Path, VarIdent, VarIdentDisambiguate};

/// A Lean identifier, guaranteed to come from one of the explicit
/// constructors below. See module docs for the rationale.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LeanName(String);

impl LeanName {
    /// Canonical conversion for any `VarIdent`. Includes the disambiguator's
    /// id when present, so distinct VarIdents always map to distinct names.
    /// Names with `%`/`@`/`#` get the special chars squashed to `_` (matches
    /// the prior `sanitize` behavior); Lean keywords get `«…»`-quoted.
    pub fn from_var_ident(v: &VarIdent) -> Self {
        let base = sanitize_string(&v.0);
        let suffix: Option<String> = match &v.1 {
            VarIdentDisambiguate::VirRenumbered { id, .. } => Some(id.to_string()),
            VarIdentDisambiguate::VirTemp(n) => Some(n.to_string()),
            VarIdentDisambiguate::VirSubst(n) => Some(n.to_string()),
            VarIdentDisambiguate::RustcId(n) => Some(n.to_string()),
            VarIdentDisambiguate::ExpandErrorsDecl(n) => Some(n.to_string()),
            VarIdentDisambiguate::BitVectorToAirDecl(n) => Some(n.to_string()),
            VarIdentDisambiguate::UserDefinedTypeInvariantPass(n) => Some(n.to_string()),
            VarIdentDisambiguate::ResInfTemp(n) => Some(n.to_string()),
            VarIdentDisambiguate::VirParamRecursion(n) => Some(n.to_string()),
            // Variants with no id: pass-through (the base name alone is unique).
            VarIdentDisambiguate::AirLocal
            | VarIdentDisambiguate::NoBodyParam
            | VarIdentDisambiguate::TypParamBare
            | VarIdentDisambiguate::TypParamSuffixed
            | VarIdentDisambiguate::TypParamDecorated
            | VarIdentDisambiguate::Field
            | VarIdentDisambiguate::VirExprNoNumber
            | VarIdentDisambiguate::VirParam => None,
        };
        // Only append the suffix when the base name is sanitization-prone
        // (contained `%`/`@`/`#`). User-named locals like `i`, `count` keep
        // their natural names — Verus's SSA already gives distinct user
        // vars distinct base strings, so no collision risk there. This
        // narrows the user-visible noise: only synthetic temps look
        // disambiguated in the generated Lean.
        match suffix {
            Some(s) if needs_disambiguation(&v.0) => Self(format!("{}_{}", base, s)),
            _ => Self(base),
        }
    }

    /// Convert a VIR `Path` to a Lean dotted name, skipping the crate prefix
    /// and synthetic impl-block segments.
    /// `crate::module::name` → `module.name`.
    pub fn from_path(path: &Path) -> Self {
        // Filter out synthetic impl segments (e.g., "impl&%0") — these are
        // VIR-internal names for trait impl blocks, not user-visible names.
        let relevant: Vec<_> = path.segments.iter()
            .filter(|s| !(s.starts_with("impl") && s.bytes().any(|b| b == b'&' || b == b'%')))
            .collect();
        if relevant.len() == 1 && !needs_sanitization(&relevant[0]) {
            return Self(relevant[0].to_string());
        }
        Self(relevant.iter().map(|s| sanitize_string(s)).collect::<Vec<_>>().join("."))
    }

    /// Last segment of a VIR `Path`, sanitized. Used where we want just the
    /// short name (e.g., a datatype's variant name without the namespace).
    pub fn from_path_short(path: &Path) -> Self {
        let s = path.segments.last().map(|s| s.as_str()).unwrap_or("_");
        Self(sanitize_string(s))
    }

    /// For struct/enum field names (which arrive as `&str` from VIR) and
    /// other plain string-keyed identifiers that aren't VarIdents.
    pub fn from_field(s: &str) -> Self {
        Self(sanitize_string(s))
    }

    /// For codegen-generated synthetic names (theorem names, gensym'd
    /// temps like `_tactus_ret_<id>`, `_tactus_d_old_<id>`). Caller
    /// guarantees the string is already a valid Lean identifier — no
    /// further sanitization is applied.
    pub fn synthetic(s: impl Into<String>) -> Self {
        Self(s.into())
    }

    /// For hardcoded literal names referenced in generated Lean: prelude
    /// definitions (`"Nat"`, `"Int"`, `"True"`), Tactus tactics
    /// (`"tactus_auto"`, `"tactus_peel"`), Mathlib refs (`"Int.toNat"`).
    /// Caller guarantees the string is a valid Lean identifier.
    pub fn lit(s: impl Into<String>) -> Self {
        Self(s.into())
    }

    /// Borrow as `&str` for emission and equality checks.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Take ownership of the inner string.
    pub fn into_string(self) -> String {
        self.0
    }
}

impl std::fmt::Display for LeanName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// Make a raw identifier safe to emit as a Lean identifier: keyword-quote
/// with `«…»` if it collides with a Lean reserved word, otherwise squash
/// Verus-internal punctuation (`%` from `assert(P)` desugaring, `@`/`#`
/// from VIR disambiguation) to `_`. No-op fast path for the common case of
/// already-safe names.
fn sanitize_string(s: &str) -> String {
    if !needs_sanitization(s) {
        return s.to_string();
    }
    if is_lean_keyword(s) {
        format!("«{}»", s)
    } else {
        s.chars().map(|c| match c { '@' | '#' | '%' => '_', _ => c }).collect()
    }
}

fn needs_sanitization(s: &str) -> bool {
    is_lean_keyword(s) || s.bytes().any(|b| b == b'@' || b == b'#' || b == b'%')
}

/// Does the base name need disambiguation? True iff it contained
/// `%`/`@`/`#` (i.e., a Verus-internal synthetic prefix that would
/// collide with other temps after squashing). User-named locals like
/// `i`, `count` don't need disambiguation — Verus's SSA already gives
/// them distinct base strings.
fn needs_disambiguation(s: &str) -> bool {
    s.bytes().any(|b| b == b'@' || b == b'#' || b == b'%')
}

fn is_lean_keyword(s: &str) -> bool {
    matches!(s,
        "def" | "theorem" | "lemma" | "example" | "abbrev" | "instance" | "class"
        | "structure" | "inductive" | "where" | "with" | "match" | "do" | "return"
        | "if" | "then" | "else" | "let" | "have" | "show" | "by" | "at" | "fun"
        | "forall" | "exists" | "Type" | "Prop" | "Sort" | "import" | "open"
        | "namespace" | "section" | "end" | "variable" | "universe"
    )
}

#[cfg(test)]
mod tests {
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
}
