//! Obligation naming + classification — the metadata helpers that turn
//! a Span / AssertKind / obligation expression into the strings used for
//! per-obligation theorem names, `/- @rust:LOC -/` markers, error labels,
//! and the `--emit-lean` sidecar. Pure formatting/classification, distinct
//! from the WP / obligation-walker logic in `sst_to_lean`.

use vir::messages::Span;
use vir::sst::{CallFun, Exp, ExpX, InternalFun};

use crate::lean_ast::{AssertKind, HypothesisKind, ObligationKind};
use crate::sst_to_lean::peel_transparent;

/// Read the pre-resolved start `file:line:col` from a Verus
/// `Span` for `/- @rust:LOC -/` markers in the generated Lean
/// (#51).
///
/// `Span::start_loc` is populated by
/// `rust_verify::spans::to_air_span` at SST construction time.
/// Spans built without rustc context (test fixtures, the
/// `err_air_span` diagnostic helper, the verifier's "no
/// location" placeholder) leave `start_loc` empty; we fall back
/// to `as_string` so something useful surfaces rather than an
/// empty marker.
pub(crate) fn format_rust_loc(span: &Span) -> String {
    if !span.start_loc.is_empty() {
        span.start_loc.clone()
    } else {
        span.as_string.clone()
    }
}

/// Format a `Span` for a user-facing diagnostic. Prefers the
/// pre-resolved `start_loc` (populated by `rust_verify`'s
/// `to_air_span`); falls back to `as_string` for synthetic spans.
/// Same logic as the internal `format_rust_loc` but exposed for
/// `generate.rs`'s warning emission path.
pub fn format_span_loc(span: &Span) -> String {
    format_rust_loc(span)
}

/// Snake-case name fragment for an `AssertKind`, used in theorem
/// naming (and as the `kind` string in the `--emit-lean` sidecar's
/// exec span marks). The visible per-error label still goes through
/// [`AssertKind::label`] — the fragment here is only for unique
/// identifiers in generated Lean.
pub fn kind_to_name(k: AssertKind) -> &'static str {
    match k {
        AssertKind::Obligation(ObligationKind::Plain) => "assert",
        AssertKind::Obligation(ObligationKind::Postcondition) => "postcondition",
        AssertKind::Obligation(ObligationKind::LoopInvariant) => "loop_invariant",
        AssertKind::Obligation(ObligationKind::LoopDecrease) => "loop_decrease",
        AssertKind::Hypothesis(HypothesisKind::LoopCondition) => "loop_condition",
        AssertKind::Hypothesis(HypothesisKind::BranchCondition) => "branch_condition",
        AssertKind::Obligation(ObligationKind::CallPrecondition) => "precondition",
        AssertKind::Obligation(ObligationKind::Termination) => "termination",
    }
}

/// Compress a Rust source location like
/// `"/home/me/project/src/main.rs:42:13"` into a short fragment for
/// theorem naming: drop the directory path and any extension, then
/// sanitize remaining non-identifier chars to `_`. The above example
/// becomes `"main_42_13"`. Result is appended to
/// `_tactus_<kind>_<fn>_at_<loc>_<id>`; we want it short enough that
/// a fn with many obligations doesn't produce kilobyte-long
/// theorem names. The structured `path:line:col` still goes into
/// `SpanMark` for error messages — this fragment is purely cosmetic.
pub(crate) fn sanitize_loc_for_name(loc: &str) -> String {
    // Strip everything before the last `/` (directory) and the
    // first `.` of the basename (extension).
    let after_slash = loc.rsplit('/').next().unwrap_or(loc);
    let mut basename = after_slash.to_string();
    if let Some(dot) = basename.find('.') {
        // Replace the extension with the rest (line/col), turning
        // "main.rs:42:13" into "main:42:13" (extension dropped) —
        // the `.rs` bit is noise we don't need in identifiers.
        let after_dot = &basename[dot + 1..];
        // After the dot, find where the extension ends (next non-
        // alphanumeric char). Anything from there onward is line/col.
        let ext_end = after_dot
            .find(|c: char| !c.is_ascii_alphanumeric())
            .unwrap_or(after_dot.len());
        let suffix = &after_dot[ext_end..];
        basename = format!("{}{}", &basename[..dot], suffix);
    }
    basename.chars()
        .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
        .collect()
}

/// Construct a per-obligation theorem name. Drops the `_at_<loc>`
/// suffix when `loc` is empty (synthetic / unmapped spans) so we
/// don't produce double-underscore names like
/// `_tactus_assert_<fn>_at__7`.
pub(crate) fn build_theorem_name(kind_label: &str, fn_name: &str, loc: &str, id: usize) -> String {
    if loc.is_empty() {
        format!("_tactus_{}_{}_{}", kind_label, fn_name, id)
    } else {
        let suffix = sanitize_loc_for_name(loc);
        format!("_tactus_{}_{}_at_{}_{}", kind_label, fn_name, suffix, id)
    }
}

/// Classify an assertion expression for error-message labeling.
/// `Wp::Assert` is the catch-all for obligations Verus inserts —
/// most are user `assert(P)` (kind=Plain), but the recursion
/// pass inserts `CheckDecreaseHeight` calls via `Wp::Assert`
/// which we recognize as Termination obligations. Other
/// non-Plain kinds (LoopInvariant / CallPrecondition / etc.) are
/// set explicitly at their wrapping sites in `walk_loop` /
/// `walk_call`.
pub(crate) fn detect_assert_kind(e: &Exp) -> AssertKind {
    // Peel transparent wrappers (Box / Unbox / CoerceMode /
    // Trigger / Loc) — Verus may wrap the CheckDecreaseHeight
    // call in any of these before inserting it as an Assert.
    let peeled = peel_transparent(e);
    if let ExpX::Call(CallFun::InternalFun(InternalFun::CheckDecreaseHeight), _, _) = &peeled.x {
        AssertKind::Obligation(ObligationKind::Termination)
    } else {
        AssertKind::Obligation(ObligationKind::Plain)
    }
}
