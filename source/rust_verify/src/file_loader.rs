//! Tactus FileLoader: sanitizes tactic blocks before rustc sees them.
//!
//! Uses tree-sitter-tactus to find tactic blocks (`by { }`, `proof { }`,
//! `assert(...) by { }`), then replaces their content with spaces.
//! Byte offsets are preserved so `Span::byte_range()` still works.
//! The verifier reads the original file later to recover verbatim tactic text.

use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Strip common leading whitespace from all non-empty lines.
pub(crate) fn dedent(s: &str) -> String {
    let min_indent = s.lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| line.len() - line.trim_start().len())
        .min()
        .unwrap_or(0);
    let mut out = String::new();
    for (i, line) in s.lines().enumerate() {
        if i > 0 { out.push('\n'); }
        if !line.trim().is_empty() {
            out.push_str(&line[min_indent..]);
        }
    }
    out
}

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

    // Only match tactic_block (= `by { }` on proof fns).
    // assert-by and proof blocks contain Verus code in vstd, not Lean.
    // Phase 2 will add proof_block and assert-by when exec fn Lean support lands.
    let query = tree_sitter::Query::new(
        &lang,
        r#"(tactic_block "{" @open "}" @close)"#,
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
    fn test_assert_by_not_sanitized() {
        // assert-by contains Verus proof code, not Lean — not sanitized (Phase 2).
        let src = "fn test() { assert(true) by { omega }; }";
        assert_eq!(sanitize_tactic_blocks(src), src);
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

    // --- Inside verus! { } macro (the real-world case) ---

    #[test]
    fn test_inside_verus_macro() {
        let src = "verus! {\nproof fn test() ensures true\nby {\n    intro ⟨a, b⟩\n}\n}";
        let sanitized = sanitize_tactic_blocks(src);
        assert!(!sanitized.contains("⟨"), "Unicode inside verus! macro must be sanitized");
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_inside_scoped_verus_macro() {
        // Real test files use ::verus_builtin_macros::verus!{ }
        let src = "::verus_builtin_macros::verus!{\nproof fn t() ensures true by { omega }\n}";
        let sanitized = sanitize_tactic_blocks(src);
        assert!(!sanitized.contains("omega"));
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_verus_macro_assert_by_not_sanitized() {
        // assert-by inside verus! must NOT be sanitized — it's Verus proof code
        let src = "verus! {\nfn test() {\n    assert(true) by { lemma_foo(); };\n}\n}";
        assert_eq!(sanitize_tactic_blocks(src), src);
    }

    #[test]
    fn test_verus_macro_assert_forall_by_not_sanitized() {
        // assert forall ... by { } inside verus! — Verus proof code, not sanitized
        let src = "verus! {\nfn test() {\n    assert forall|i: int| #[trigger] f(i) by { lemma(i); };\n}\n}";
        assert_eq!(sanitize_tactic_blocks(src), src);
    }

    #[test]
    fn test_verus_macro_mixed_tactic_and_assert() {
        // tactic_block sanitized, assert-by left alone, in same verus! block
        let src = "verus! {\n\
            proof fn lem() ensures true by { omega }\n\
            fn exec() {\n\
                assert(true) by { lemma_call(); };\n\
            }\n\
        }";
        let sanitized = sanitize_tactic_blocks(src);
        assert!(!sanitized.contains("omega"), "tactic block should be sanitized");
        assert!(sanitized.contains("lemma_call"), "assert-by should NOT be sanitized");
    }

    #[test]
    fn test_verus_macro_spec_fn_not_sanitized() {
        let src = "verus! {\nspec fn double(x: nat) -> nat { x + x }\n}";
        assert_eq!(sanitize_tactic_blocks(src), src);
    }

    // --- Paren/bracket macros stay as token trees (not parsed as statements) ---

    #[test]
    fn test_paren_macro_not_parsed() {
        let src = "println!(\"by {{ omega }}\");";
        assert_eq!(sanitize_tactic_blocks(src), src);
    }

    #[test]
    fn test_bracket_macro_not_parsed() {
        let src = "vec![1, 2, 3];";
        assert_eq!(sanitize_tactic_blocks(src), src);
    }

    // --- attributed_expression (#[trigger]) in quantifiers ---

    #[test]
    fn test_trigger_in_assert_forall() {
        // #[trigger] before the condition — must parse without errors
        // so the `by { }` is recognized as assert-by, NOT a stray tactic_block
        let src = "verus! {\nfn test() {\n    assert forall|x: int| #[trigger] f(x) by { lem(x); };\n}\n}";
        let sanitized = sanitize_tactic_blocks(src);
        assert!(sanitized.contains("lem(x)"), "#[trigger] assert-by must not be sanitized");
    }

    #[test]
    fn test_trigger_in_forall_expr() {
        let src = "verus! {\nspec fn p() -> bool { forall|x: int| #[trigger] f(x) }\n}";
        assert_eq!(sanitize_tactic_blocks(src), src);
    }

    #[test]
    fn test_unicode_focus_dot_in_verus() {
        let src = "::verus_builtin_macros::verus!{\n\
            proof fn conj(a: int, b: int)\n\
                requires a > 0, b > 0\n\
                ensures a > 0, b > 0\n\
            by {\n\
                constructor\n\
                \u{b7} omega\n\
                \u{b7} omega\n\
            }\n\
        }";
        let sanitized = sanitize_tactic_blocks(src);
        assert!(!sanitized.contains('\u{b7}'), "· must be sanitized: got {sanitized}");
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_trigger_in_exists_expr() {
        let src = "verus! {\nspec fn p() -> bool { exists|x: int| #[trigger] f(x) }\n}";
        assert_eq!(sanitize_tactic_blocks(src), src);
    }

    // --- Lean syntax edge cases inside tactic blocks (the whole point of FileLoader) ---

    #[test]
    fn test_lean_line_comment_with_brace_in_verus() {
        // `-- comment }` must not close the tactic block
        let src = "verus! {\nproof fn t() ensures true\nby {\n    -- comment with } brace\n    omega\n}\n}";
        let sanitized = sanitize_tactic_blocks(src);
        assert_eq!(sanitized.matches('}').count(), 2); // verus! closing } + tactic closing }
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_lean_block_comment_with_brace_in_verus() {
        // `/- comment } -/` must not close the tactic block
        let src = "verus! {\nproof fn t() ensures true\nby {\n    /- comment } -/\n    omega\n}\n}";
        let sanitized = sanitize_tactic_blocks(src);
        assert_eq!(sanitized.matches('}').count(), 2);
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_string_with_brace_in_tactic() {
        // `"}"` inside tactic block must not close the block
        let src = "verus! {\nproof fn t() ensures true\nby {\n    have h := \"}\"\n    omega\n}\n}";
        let sanitized = sanitize_tactic_blocks(src);
        assert_eq!(sanitized.matches('}').count(), 2);
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_nested_braces_in_tactic() {
        // Nested { } inside tactic block must balance correctly
        let src = "verus! {\nproof fn t() ensures true\nby {\n    { exact h }\n    omega\n}\n}";
        let sanitized = sanitize_tactic_blocks(src);
        assert_eq!(sanitized.matches('}').count(), 2);
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_empty_tactic_block() {
        let src = "verus! {\nproof fn t() ensures true by { }\n}";
        let sanitized = sanitize_tactic_blocks(src);
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_multiple_tactic_blocks_in_verus() {
        let src = "verus! {\n\
            proof fn a() ensures true by { omega }\n\
            proof fn b() ensures true by { simp }\n\
        }";
        let sanitized = sanitize_tactic_blocks(src);
        assert!(!sanitized.contains("omega"));
        assert!(!sanitized.contains("simp"));
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_requires_and_ensures_before_by() {
        let src = "verus! {\nproof fn t(x: nat)\n    requires x > 0\n    ensures x >= 1\nby {\n    omega\n}\n}";
        let sanitized = sanitize_tactic_blocks(src);
        assert!(!sanitized.contains("omega"));
        assert!(sanitized.contains("requires"));
        assert!(sanitized.contains("ensures"));
    }
}

// --- dedent unit tests (separate from FileLoader) ---

#[cfg(test)]
mod dedent_tests {
    use super::dedent;

    #[test]
    fn test_dedent_uniform_indent() {
        assert_eq!(dedent("    a\n    b"), "a\nb");
    }

    #[test]
    fn test_dedent_mixed_indent() {
        assert_eq!(dedent("    a\n        b\n    c"), "a\n    b\nc");
    }

    #[test]
    fn test_dedent_no_indent() {
        assert_eq!(dedent("a\nb"), "a\nb");
    }

    #[test]
    fn test_dedent_empty_lines_ignored() {
        assert_eq!(dedent("    a\n\n    b"), "a\n\nb");
    }

    #[test]
    fn test_dedent_single_line() {
        assert_eq!(dedent("    omega"), "omega");
    }

    #[test]
    fn test_dedent_empty_input() {
        assert_eq!(dedent(""), "");
    }

    #[test]
    fn test_dedent_only_whitespace() {
        // Empty lines preserved as structure, content stripped
        assert_eq!(dedent("   \n   "), "\n");
    }

    #[test]
    fn test_dedent_leading_blank_lines() {
        assert_eq!(dedent("\n\n    a\n    b"), "\n\na\nb");
    }
}
