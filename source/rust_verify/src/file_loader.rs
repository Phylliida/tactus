//! Tactus FileLoader: sanitizes tactic blocks before rustc sees them.
//!
//! Uses tree-sitter-tactus to find tactic blocks (`by { }`, `proof { }`,
//! `assert(...) by { }`), then replaces their content with spaces.
//! Byte offsets are preserved so `Span::byte_range()` still works.
//! The verifier reads the original file later to recover verbatim tactic text.

use std::path::{Path, PathBuf};
use std::sync::Arc;

/// FileLoader that sanitizes tactic blocks before rustc lexes the source.
pub struct TactusFileLoader;

impl rustc_span::source_map::FileLoader for TactusFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        path.exists()
    }

    fn read_file(&self, path: &Path) -> Result<String, std::io::Error> {
        let source = std::fs::read_to_string(path)?;
        Ok(sanitize_tactic_blocks(&source))
    }

    fn read_binary_file(&self, path: &Path) -> Result<Arc<[u8]>, std::io::Error> {
        // Binary files (e.g., .rlib) never contain tactic blocks — read as-is.
        std::fs::read(path).map(Into::into)
    }

    fn current_directory(&self) -> Result<PathBuf, std::io::Error> {
        std::env::current_dir()
    }
}

/// Parse source with tree-sitter-tactus, find tactic block content ranges,
/// and replace their content with spaces (preserving newlines).
fn sanitize_tactic_blocks(source: &str) -> String {
    let ranges = find_tactic_block_ranges(source.as_bytes());
    if ranges.is_empty() {
        return source.to_string();
    }
    let mut out = source.as_bytes().to_vec();
    for (start, end) in ranges {
        for i in start..end {
            if out[i] != b'\n' {
                out[i] = b' ';
            }
        }
    }
    // Safe: we only wrote 0x20 (space) and preserved 0x0A (newline),
    // both valid ASCII/UTF-8 regardless of what multi-byte sequences were replaced.
    String::from_utf8(out).unwrap()
}

/// Use tree-sitter-tactus to find byte ranges of tactic block content
/// (between `{` and `}` of each tactic brace body).
fn find_tactic_block_ranges(src: &[u8]) -> Vec<(usize, usize)> {
    let lang: tree_sitter::Language = tree_sitter_tactus::LANGUAGE.into();

    let mut parser = tree_sitter::Parser::new();
    parser.set_language(&lang).expect("Error loading Tactus grammar");

    let tree = match parser.parse(src, None) {
        Some(t) => t,
        None => return Vec::new(),
    };

    let query = tree_sitter::Query::new(
        &lang,
        r#"
        (tactic_block "{" @open "}" @close)
        (proof_block "{" @open "}" @close)
        (assert_expression "by" "{" @open "}" @close)
        "#,
    ).expect("Invalid tree-sitter query");

    let open_idx = query.capture_index_for_name("open").unwrap();
    let close_idx = query.capture_index_for_name("close").unwrap();

    let mut cursor = tree_sitter::QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), src);
    let mut ranges = Vec::new();

    use tree_sitter::StreamingIterator;
    while let Some(m) = { matches.advance(); matches.get() } {
        let mut open_end = None;
        let mut close_start = None;
        for cap in m.captures {
            if cap.index == open_idx {
                open_end = Some(cap.node.end_byte());
            } else if cap.index == close_idx {
                close_start = Some(cap.node.start_byte());
            }
        }
        if let (Some(start), Some(end)) = (open_end, close_start) {
            if start < end {
                ranges.push((start, end));
            }
        }
    }

    ranges
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_no_tactic_blocks() {
        let src = "fn main() { let x = 5; }";
        assert_eq!(sanitize_tactic_blocks(src), src);
    }

    #[test]
    fn test_tactic_block_sanitized() {
        let src = "proof fn test() ensures true by { omega }";
        let sanitized = sanitize_tactic_blocks(src);
        assert_eq!(sanitized, "proof fn test() ensures true by {       }");
    }

    #[test]
    fn test_tactic_block_multiline_sanitized() {
        let src = "proof fn test() ensures true by {\n    omega\n}";
        let sanitized = sanitize_tactic_blocks(src);
        assert_eq!(sanitized, "proof fn test() ensures true by {\n         \n}");
    }

    #[test]
    fn test_unicode_sanitized() {
        let src = "proof fn test() ensures true\nby {\n    intro ⟨a, b⟩\n}";
        let sanitized = sanitize_tactic_blocks(src);
        assert!(!sanitized.contains("⟨"));
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_preserves_newlines() {
        let src = "proof fn test() ensures true\nby {\n    intro ⟨a⟩\n    omega\n}";
        let sanitized = sanitize_tactic_blocks(src);
        assert_eq!(sanitized.matches('\n').count(), src.matches('\n').count());
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_multiple_tactic_blocks() {
        let src = "proof fn a() ensures true by { omega }\nproof fn b() ensures true by { simp }";
        let sanitized = sanitize_tactic_blocks(src);
        assert_eq!(
            sanitized,
            "proof fn a() ensures true by {       }\nproof fn b() ensures true by {      }"
        );
    }

    #[test]
    fn test_assert_by_sanitized() {
        let src = "fn test() { assert(true) by { omega }; }";
        let sanitized = sanitize_tactic_blocks(src);
        assert!(!sanitized.contains("omega"));
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_plain_assert_not_sanitized() {
        let src = "fn test() { assert(x > 0); }";
        assert_eq!(sanitize_tactic_blocks(src), src);
    }

    #[test]
    fn test_regular_fn_not_sanitized() {
        let src = "fn test() { let x = 5; let y = x + 1; }";
        assert_eq!(sanitize_tactic_blocks(src), src);
    }

    #[test]
    fn test_spec_fn_not_sanitized() {
        let src = "spec fn double(x: nat) -> nat { x + x }";
        assert_eq!(sanitize_tactic_blocks(src), src);
    }

    #[test]
    fn test_byte_length_preserved() {
        let src = "proof fn test() ensures true\nby {\n    intro ⟨a, b⟩\n    /- comment } -/\n    omega\n}";
        let sanitized = sanitize_tactic_blocks(src);
        assert_eq!(sanitized.len(), src.len());
    }
}
