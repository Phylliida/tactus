//! User-facing message constants for Tactus-specific attributes /
//! features. Centralized here (rather than inlined at the
//! error-emission site) so that tests and other consumers can
//! reference the same `pub const` rather than duplicating the magic
//! string — phrasing edits to a message percolate to test assertions
//! automatically.
//!
//! The lens that surfaced this pattern (Lens 15 — magic-string
//! avoidance) lives in DESIGN.md § "Code review strategy". When
//! adding a new Tactus user-facing message, prefer extracting a
//! `pub const` here over a string literal at the emission site.
//!
//! Only **Tactus-controlled** messages go here. Strings emitted by
//! Lean, Z3/Verus's verification path, or other upstream sources
//! are outside our control — tests that match those should use
//! stable-substring matching against the upstream content.

// ── Attribute parsing errors ─────────────────────────────────────────

/// Error returned by `rust_verify::attributes::get_heartbeats_arg`
/// for malformed `#[verifier::heartbeats(N)]` invocations
/// (`heartbeats()`, `heartbeats(1.5)`, `heartbeats(0)`,
/// `heartbeats(1, 2)`, `heartbeats("foo")`).
pub const HEARTBEATS_ARG_ERR: &str =
    "heartbeats requires a positive integer literal \
     (e.g., #[verifier::heartbeats(1600000)])";

/// Error returned by `rust_verify::attributes` for
/// `#[verifier::tactus_tactic("")]` (empty tactic string).
pub const TACTUS_TACTIC_EMPTY_ERR: &str =
    "tactus_tactic argument must be a non-empty Lean tactic string";

/// Stable tag prefix for the `assume(P)` warning emitted by
/// `lean_verify::generate::check_exec_fn` (warnings format:
/// `"unproved assumption at <loc>: backed by..."`). The location
/// portion is dynamic, so this is a *tag* used for `contains`
/// matching rather than a full message constant.
pub const ASSUME_WARNING_TAG: &str = "unproved assumption";

/// Stable tag for the `&mut x.f` / `&mut v[i]` rejection in
/// `sst_to_lean::build_wp_assign` (error format: `"assignment with
/// non-simple LHS (got {:?}) is not yet supported"`). The Debug
/// content of the L-value is dynamic; this tag is the
/// `contains`-stable prefix.
pub const ASSIGN_NON_SIMPLE_LHS_TAG: &str = "non-simple LHS";

// ── AssertKind labels (Tactus error-format suffix) ───────────────────
//
// These appear in Tactus's per-obligation error format `at <loc>
// (<label>):` — emitted by `lean_verify::lean_process::format_error`
// via `AssertKind::label()`. Both the emission site and many tests
// reference these; centralizing the labels here keeps the format and
// the assertions in lockstep through phrasing edits.

pub const ASSERT_LABEL_POSTCONDITION: &str = "postcondition";
pub const ASSERT_LABEL_LOOP_INVARIANT: &str = "loop invariant";
pub const ASSERT_LABEL_LOOP_DECREASE: &str = "loop decrease";
pub const ASSERT_LABEL_CALL_PRECONDITION: &str = "precondition";
pub const ASSERT_LABEL_TERMINATION: &str = "termination";
pub const ASSERT_LABEL_LOOP_CONDITION: &str = "loop condition";
pub const ASSERT_LABEL_BRANCH_CONDITION: &str = "branch condition";

/// Wrap an `AssertKind` label in the parens that Tactus's error
/// formatter adds — `at <loc> (<label>):`. Both `lean_process` (emit
/// side) and tests (assertion side) call this helper, so the
/// `(...)` framing has a single definition.
pub fn paren_label(label: &str) -> String {
    format!("({})", label)
}

// ── TactusDiag help / fallback messages ──────────────────────────────

/// Prefix for the `help:` text on Tactus diagnostics pointing users
/// at the generated `.lean` artifact for offline inspection.
/// Combined with the file path: `format!("{} {}", LEAN_FILE_HELP_PREFIX, path)`.
pub const LEAN_FILE_HELP_PREFIX: &str = "generated .lean file:";

/// Body of the defensive fallback emitted by
/// `lean_verify::generate::check_proof_fn` / `check_exec_fn` when
/// Lean returns failure but reports zero error-severity diagnostics
/// (rare; either a pipeline edge or a future Lean output format
/// change). The full message is built as
/// `format!("{}: {}", <header>, NO_ERROR_DIAGNOSTICS_BODY)`.
pub const NO_ERROR_DIAGNOSTICS_BODY: &str =
    "Lean reported failure but no error-severity diagnostics were captured.\n\
     This is a Tactus pipeline bug — please file an issue with the generated .lean file.";
