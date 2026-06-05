//! Ret-substitution detection (#128).
//!
//! LExpr-level analysis of a callee's inlined ensures: find a top-level
//! conjunct `r == E` that uniquely determines the return value, so
//! `push_post_call_frames` can substitute `E` for `r` directly (a
//! definitional `let dest := E`) instead of emitting the
//! `∀ ret, ret == E → …` quantifier the SMT path needs. See DESIGN
//! § "Ret-substitution at call sites (#128)".

use crate::lean_ast::{and_all, BinOp, Expr as LExpr, ExprNode};

/// Peel `SpanMark` wrappers, returning the innermost non-SpanMark
/// expression. Used by the ret-substitution machinery (#128) and the
/// And-tree walker — SpanMark is a Lean-level no-op (just emits a
/// `/- @rust:LOC -/` comment) so structural pattern matching should
/// look through it.
fn peel_span_marks(e: &LExpr) -> &LExpr {
    let mut cur = e;
    while let ExprNode::SpanMark { inner, .. } = &cur.node {
        cur = inner;
    }
    cur
}

/// Flatten the *top-level* `And`-tree of `e` into its leaf conjuncts.
///
/// Recurses through `BinOp::And` only — does NOT descend into `Or`,
/// `Implies`, `Forall`, `Exists`, `If`, `Let`, `Match`, etc. The
/// "top-level" notion is what matters for ret-substitution (#128):
/// a clause `r == E` buried inside `Or(Q, r == E)` is NOT
/// uniquely-determining, so we don't want to find it. SpanMark
/// wrappers are peeled at every node since they're transparent at
/// the Lean level.
fn collect_top_and_conjuncts<'a>(e: &'a LExpr, out: &mut Vec<&'a LExpr>) {
    let peeled = peel_span_marks(e);
    if let ExprNode::BinOp { op: BinOp::And, lhs, rhs } = &peeled.node {
        collect_top_and_conjuncts(lhs, out);
        collect_top_and_conjuncts(rhs, out);
    } else {
        out.push(e);
    }
}

/// Try to find a top-level conjunct of the form `Eq(Var(target), E)`
/// or `Eq(E, Var(target))` in `conj`. Returns `Some((E, rest))`
/// where `rest` is the And of all OTHER conjuncts (or `LitBool(true)`
/// if the eq clause was the only one). Returns `None` if no matching
/// conjunct exists, or if `E` mentions `target` (self-referential).
///
/// The conservative scope (#128): only top-level `And`-tree, never
/// descending into `Or` / `Implies` / `Forall` / `Exists` / `If` /
/// `Let` / `Match`. A clause buried inside a disjunction does NOT
/// uniquely determine `target`, so we don't substitute.
///
/// SpanMark is peeled transparently. The matched eq picks the FIRST
/// conjunct in source order — for trait-method-impl callees (#86),
/// where the conjunction is `(spec_ensures) ∧ (impl_ensures)`,
/// `push_post_call_frames` orders spec first then impl. If both
/// have a `r == E` clause, we pick the spec's; the impl's becomes
/// part of `rest` and substitutes to `E_impl == E_spec` which Verus
/// guarantees is consistent (impl ⇒ trait).
pub(crate) fn extract_top_level_eq_for(
    conj: &LExpr,
    target: &crate::lean_name::LeanName,
) -> Option<(LExpr, LExpr)> {
    let mut conjuncts: Vec<&LExpr> = Vec::new();
    collect_top_and_conjuncts(conj, &mut conjuncts);

    for (idx, c) in conjuncts.iter().enumerate() {
        let peeled = peel_span_marks(c);
        let ExprNode::BinOp { op: BinOp::Eq, lhs, rhs } = &peeled.node else {
            continue;
        };
        let lhs_p = peel_span_marks(lhs);
        let rhs_p = peel_span_marks(rhs);
        let e: Option<&LExpr> = match (&lhs_p.node, &rhs_p.node) {
            (ExprNode::Var(n), _) if n.as_str() == target.as_str() => Some(rhs_p),
            (_, ExprNode::Var(n)) if n.as_str() == target.as_str() => Some(lhs_p),
            _ => None,
        };
        let Some(e) = e else { continue };
        // Reject self-referential `r == E` where E mentions r —
        // substituting `r → E` in such patterns would loop. Uses
        // the shared `lean_ast::mentions_free_var` (which tracks
        // binder scope correctly) rather than a sst_to_lean-local
        // walk.
        if crate::lean_ast::mentions_free_var(e, target.as_str()) {
            continue;
        }
        let rest: Vec<LExpr> = conjuncts.iter().enumerate()
            .filter(|(i, _)| *i != idx)
            .map(|(_, c)| (*c).clone())
            .collect();
        return Some((e.clone(), and_all(rest)));
    }
    None
}

/// Is `e` syntactically `LitBool(true)` (after peeling SpanMark)?
/// Used to skip emitting `True →` Hyp frames.
pub(crate) fn is_trivial_true(e: &LExpr) -> bool {
    matches!(peel_span_marks(e).node, ExprNode::LitBool(true))
}
