//! Shared definition of "what Tactus inlines at a call site."
//!
//! Both `sst_to_lean::walk_call` (for emission) and
//! `dep_order::collect_references` (for transitive-reference walking)
//! consult this module. The two passes USED to encode the same
//! information independently — what clauses get inlined at a call
//! site, and which functions count as the spec source for an impl —
//! and drift between them was the root cause of the 2026-05-12
//! "predicate is unresolved" regression: walk_call inlined an impl
//! method's ensures clause that referenced a spec fn, but the dep
//! walk didn't know that ensures was going to land in the rendered
//! Lean.
//!
//! Centralizing the definitions here means a future change to
//! "what gets inlined" (e.g., if Verus adds a new clause kind we
//! decide to surface, or if Tactus's #86-style impl-strengthening
//! grows another wrinkle) lands in ONE place, and both consumers
//! automatically pick it up.

use std::collections::HashMap;
use vir::ast::{Expr, Fun, FunctionKind, FunctionX};

/// Resolve `callee` to its **spec source** — the FunctionX whose
/// `require` / `ensure` clauses get inlined at call sites.
///
/// * `TraitMethodImpl { method, .. }`: redirect to the trait method
///   decl (`method`). Verus rejects impl-side `requires` declarations
///   (impls inherit), and #86's impl-strengthening composes the
///   impl's own ensures separately — so the trait decl is the spec
///   anchor.
/// * Anything else (`Static`, `TraitMethodDecl`, etc.): the callee
///   is its own spec source.
///
/// Returns `Err(method_fun)` if `callee` is a `TraitMethodImpl` but
/// the trait method decl isn't in `fn_map` (cross-crate case). The
/// two consumers handle this differently:
/// * `sst_to_lean::resolve_callee` propagates the error — emission
///   can't inline a missing spec_callee's clauses correctly.
/// * `dep_order::collect_references` falls back to the callee itself
///   (best-effort; missing decl means refs from trait-level specs
///   won't be walked, but the impl's own specs are still picked up).
pub fn spec_source<'a>(
    callee: &'a FunctionX,
    fn_map: &HashMap<&Fun, &'a FunctionX>,
) -> Result<&'a FunctionX, &'a Fun> {
    if let FunctionKind::TraitMethodImpl { method, .. } = &callee.kind {
        return fn_map.get(method).copied().ok_or(method);
    }
    Ok(callee)
}

/// The VIR-AST clauses Tactus inlines at every call site to the
/// `(callee, spec_callee)` pair.
///
/// `requires` and `ensures` are kept separate because the two
/// consumers process them differently:
/// * Emission (`sst_to_lean::walk_call`): requires render as
///   precondition theorem obligations; ensures push as post-call
///   `Hyp` frames for subsequent obligations.
/// * Refs collection (`dep_order::collect_references`): walks both
///   uniformly to add referenced spec fns to the worklist and
///   datatypes/traits to refs.
///
/// Adding a new clause kind (e.g., if Tactus ever inlines
/// `decreases` clauses at call sites) means a new field here, and
/// both consumers either consume the new field or explicitly ignore
/// it — drift surfaces as a code-review item rather than a silent
/// missing-reference bug.
pub struct CallInlinedClauses<'a> {
    /// Clauses inlined as precondition obligations at the call site.
    /// Currently `spec_callee.require`.
    pub requires: Vec<&'a Expr>,
    /// Clauses inlined as post-call hypothesis frames at the call
    /// site. Currently `spec_callee.ensure.0`, plus `callee.ensure.0`
    /// when `callee` is a `TraitMethodImpl` (per #86 impl-
    /// strengthening: caller sees the conjunction of trait + impl
    /// ensures).
    pub ensures: Vec<&'a Expr>,
}

/// Build the `CallInlinedClauses` for a given call.
///
/// The single source of truth for "what gets inlined." A function
/// for the pair (rather than two separate `requires_at_call` and
/// `ensures_at_call`) so the impl-strengthening conditional and any
/// future inlining wrinkles live in ONE place.
pub fn collect_inlined_at_call<'a>(
    callee: &'a FunctionX,
    spec_callee: &'a FunctionX,
) -> CallInlinedClauses<'a> {
    // Pointer-equality check: if the caller passed the same fn for
    // both (e.g., a Static callee where spec_source(callee) == callee),
    // we don't add a duplicate copy of `callee.ensure.0` for #86
    // strengthening (it would be the same clauses already in
    // `spec_callee.ensure.0`).
    let same_fn = std::ptr::eq(callee, spec_callee);
    let trait_impl_strengthening =
        !same_fn && matches!(callee.kind, FunctionKind::TraitMethodImpl { .. });

    let requires: Vec<&Expr> = spec_callee.require.iter().collect();
    let mut ensures: Vec<&Expr> = spec_callee.ensure.0.iter().collect();
    if trait_impl_strengthening {
        ensures.extend(callee.ensure.0.iter());
    }

    CallInlinedClauses { requires, ensures }
}
