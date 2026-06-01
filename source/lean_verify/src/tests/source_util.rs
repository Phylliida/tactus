//! Unit tests for `source_util` — extracted to `src/tests/` (a `#[path]`'d
//! `mod tests` child of `source_util`, so `use super::*` reaches private items).

use super::*;

#[test]
fn dedent_strips_common_indent() {
    let src = "    omega\n    simp_all\n";
    assert_eq!(dedent(src), "omega\nsimp_all");
}

#[test]
fn dedent_preserves_empty_lines_as_blank() {
    let src = "    omega\n\n    simp_all";
    // Empty line stays empty (no indent added).
    assert_eq!(dedent(src), "omega\n\nsimp_all");
}

#[test]
fn dedent_no_indent_passthrough() {
    let src = "omega\nsimp_all";
    assert_eq!(dedent(src), "omega\nsimp_all");
}

#[test]
fn dedent_empty_string() {
    assert_eq!(dedent(""), "");
}

#[test]
fn read_tactic_degenerate_range() {
    // start == end, start + 1 == end — both degenerate.
    assert!(read_tactic_from_source("/dev/null", 0, 0).is_none());
    assert!(read_tactic_from_source("/dev/null", 5, 5).is_none());
    assert!(read_tactic_from_source("/dev/null", 5, 6).is_none());
}

#[test]
fn read_tactic_nonexistent_file() {
    assert!(read_tactic_from_source("/no/such/path", 0, 10).is_none());
}
