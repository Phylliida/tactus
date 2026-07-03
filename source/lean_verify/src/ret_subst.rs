//! Rendered-tree predicates for the call-inlining machinery.
//!
//! Historical note (#128 → P3): this module used to host the
//! LExpr-level ret-substitution extraction (`extract_top_level_eq_for`
//! — find a top-level conjunct `r == E` in the RENDERED ensures). That
//! extraction was untyped, so the sort reconciliation (2026-07-03)
//! needed a VIR-side "twin" walk to recover E's typ, and the two walks
//! had to mirror-match by hand. P3 (DESIGN-typed-renderer.md) made the
//! VIR-side walk the single primary — `sst_to_lean::vir_find_ret_eq`
//! finds the eq conjunct on the TYPED tree and E renders separately —
//! and the rendered-side extraction was deleted. What remains here is
//! the small rendered-tree predicate the frame-push logic still needs.

use crate::lean_ast::{Expr as LExpr, ExprNode};

/// Peel `SpanMark` wrappers, returning the innermost non-SpanMark
/// expression — SpanMark is a Lean-level no-op (just emits a
/// `/- @rust:LOC -/` comment) so structural pattern matching should
/// look through it.
fn peel_span_marks(e: &LExpr) -> &LExpr {
    let mut cur = e;
    while let ExprNode::SpanMark { inner, .. } = &cur.node {
        cur = inner;
    }
    cur
}

/// Is `e` syntactically `LitBool(true)` (after peeling SpanMark)?
/// Used to skip emitting `True →` Hyp frames.
pub(crate) fn is_trivial_true(e: &LExpr) -> bool {
    matches!(peel_span_marks(e).node, ExprNode::LitBool(true))
}
