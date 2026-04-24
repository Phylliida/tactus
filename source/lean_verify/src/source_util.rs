//! Source-file helpers shared between the Tactus lowering pipeline
//! (`sst_to_lean`) and the verifier's tactic-text extraction
//! (`rust_verify::verifier::read_tactic_from_source`).
//!
//! Kept in one place so the two callers can't drift — for example
//! if one fixes a `dedent` edge case and the other doesn't, the
//! same source would produce different Lean tactic text depending
//! on which path reads it.

/// Strip common leading whitespace from all non-empty lines.
///
/// Used to normalise tactic-body text extracted from the source
/// file so Lean's indentation-sensitive tactic parser doesn't see
/// the surrounding Rust indentation. Empty / whitespace-only lines
/// are preserved as empty so line numbers line up with the source.
pub fn dedent(s: &str) -> String {
    let min_indent = s
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| line.len() - line.trim_start().len())
        .min()
        .unwrap_or(0);
    let mut out = String::new();
    for (i, line) in s.lines().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        if !line.trim().is_empty() {
            out.push_str(&line[min_indent..]);
        }
    }
    out
}

/// Read the verbatim `{ ... }` tactic body from the source file at
/// the given byte range (which includes the braces) and return the
/// content between them, dedented.
///
/// Returns `None` for degenerate ranges (end ≤ start+1), ranges
/// past EOF, or unreadable files. Callers treat `None` as "span not
/// usable" and fall back to rejecting the tactic-extraction path.
pub fn read_tactic_from_source(
    file_path: &str,
    start_byte: usize,
    end_byte: usize,
) -> Option<String> {
    let src = std::fs::read_to_string(file_path).ok()?;
    if start_byte + 1 >= end_byte || end_byte > src.len() {
        return None;
    }
    let inner = &src[start_byte + 1..end_byte - 1];
    Some(dedent(inner))
}

#[cfg(test)]
mod tests {
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
}
