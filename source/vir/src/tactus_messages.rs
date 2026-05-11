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

/// Error returned by `rust_verify::attributes::get_heartbeats_arg`
/// for malformed `#[verifier::heartbeats(N)]` invocations
/// (`heartbeats()`, `heartbeats(1.5)`, `heartbeats(0)`,
/// `heartbeats(1, 2)`, `heartbeats("foo")`).
pub const HEARTBEATS_ARG_ERR: &str =
    "heartbeats requires a positive integer literal \
     (e.g., #[verifier::heartbeats(1600000)])";
