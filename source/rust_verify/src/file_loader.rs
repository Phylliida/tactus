//! Tactus FileLoader: sanitizes tactic blocks before rustc sees them.
//!
//! Uses tree-sitter-tactus to find `tactic_block` nodes (`by { }` on proof fns)
//! and replaces their content with spaces. Byte offsets are preserved so
//! `Span::byte_range()` still works. The verifier reads the original file
//! later to recover verbatim tactic text.

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
///
/// Two categories of nodes get sanitized:
///
/// 1. **`tactic_block`** — the `by { }` at the top of a proof fn.
///    Unconditionally sanitized: tree-sitter-tactus only recognises
///    `tactic_block` at proof-fn-body position, and those always
///    contain Lean syntax. Works for both vstd (no proof fns use
///    tactic_block) and Tactus.
///
/// 2. **`proof_block`** (a `proof { }` statement inside an exec fn
///    body) and **`assert_expression` with a brace-body** (`assert(P)
///    by { … }` / `assert forall … by { … }`) — conditionally
///    sanitized, only inside functions marked
///    `#[verifier::tactus_auto]`. These constructs exist in vstd
///    carrying Rust-flavoured Verus proof code (calls to lemmas,
///    nested asserts) rather than Lean tactics; unconditional
///    sanitization would wipe vstd's proofs. The `tactus_auto`
///    attribute is the unambiguous signal that the enclosing
///    function's body routes through the Lean WP pipeline, and thus
///    that inner `proof { … }` and `assert(…) by { … }` blocks are
///    meant as Lean tactics.
fn find_tactic_block_ranges(src: &[u8]) -> Vec<(usize, usize)> {
    let lang: tree_sitter::Language = tree_sitter_tactus::LANGUAGE.into();

    let mut parser = tree_sitter::Parser::new();
    parser.set_language(&lang).expect("Error loading Tactus grammar");

    let tree = match parser.parse(src, None) {
        Some(t) => t,
        None => return Vec::new(),
    };

    let mut ranges = Vec::new();

    // Pass 1: unconditionally sanitize every tactic_block.
    collect_tactic_block_ranges(&lang, tree.root_node(), src, &mut ranges);

    // Pass 2: inside tactus_auto-marked function_items, sanitize
    // proof_block and assert_expression (with brace body) too.
    walk_tactus_auto_fns(tree.root_node(), src, &mut ranges);

    ranges
}

/// Pass 1: find every `tactic_block` node and collect the byte range
/// between its `{` and `}`.
fn collect_tactic_block_ranges<'a>(
    lang: &tree_sitter::Language,
    root: tree_sitter::Node<'a>,
    src: &[u8],
    ranges: &mut Vec<(usize, usize)>,
) {
    let query = tree_sitter::Query::new(
        lang,
        r#"(tactic_block "{" @open "}" @close)"#,
    ).expect("Invalid tree-sitter query");
    collect_brace_query(&query, root, src, ranges);
}

/// Helper: run a query that has `@open` on a `{` node and `@close` on
/// a `}` node, collecting the (open.end, close.start) byte ranges.
fn collect_brace_query<'a>(
    query: &tree_sitter::Query,
    root: tree_sitter::Node<'a>,
    src: &[u8],
    ranges: &mut Vec<(usize, usize)>,
) {
    let open_idx = query.capture_index_for_name("open").unwrap();
    let close_idx = query.capture_index_for_name("close").unwrap();
    let mut cursor = tree_sitter::QueryCursor::new();
    let mut matches = cursor.matches(query, root, src);
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
}

/// Pass 2: recursively visit `function_item` nodes; for each one
/// marked `#[verifier::tactus_auto]`, collect the inner
/// `proof_block` / `assert_expression` brace-body ranges. Nested
/// function_items inside are visited on their own (handled by the
/// outer recursion), so a non-tactus_auto fn nested inside a
/// tactus_auto one isn't incorrectly sanitized.
fn walk_tactus_auto_fns<'a>(
    node: tree_sitter::Node<'a>,
    src: &[u8],
    ranges: &mut Vec<(usize, usize)>,
) {
    if node.kind() == "function_item" && function_has_tactus_auto_attr(node, src) {
        collect_inner_lean_blocks(node, ranges);
        // Keep walking to find nested fns (Rust allows `fn f() { fn g() { … } }`),
        // but the outer-fn body is already fully scanned — no double-count.
    }
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        walk_tactus_auto_fns(child, src, ranges);
    }
}

/// `true` when any of the fn's leading `attribute_item` children
/// mentions `tactus_auto` (e.g., `#[verifier::tactus_auto]`). Done by
/// substring match on the attribute's source text — cheap, and the
/// attribute name is unambiguous.
fn function_has_tactus_auto_attr<'a>(fn_node: tree_sitter::Node<'a>, src: &[u8]) -> bool {
    let mut cursor = fn_node.walk();
    for child in fn_node.children(&mut cursor) {
        if child.kind() == "attribute_item" {
            if let Some(text) = src.get(child.byte_range()) {
                if let Ok(s) = std::str::from_utf8(text) {
                    if s.contains("tactus_auto") {
                        return true;
                    }
                }
            }
        } else if !matches!(child.kind(),
            // Attributes precede the fn signature; once we've left the
            // attribute prefix, keep scanning for more (tree-sitter
            // interleaves documentation comments / inner attrs too),
            // but bail at the body — no point descending into it.
            "block_comment" | "line_comment" | "inner_attribute_item"
        ) {
            break;
        }
    }
    false
}

/// Walk `fn_node`'s descendants, collecting brace-body ranges from
/// every `proof_block` and `assert_expression` we encounter. Uses the
/// same `{` / `}` child-scan as the tactic_block path.
fn collect_inner_lean_blocks<'a>(
    fn_node: tree_sitter::Node<'a>,
    ranges: &mut Vec<(usize, usize)>,
) {
    let mut stack: Vec<tree_sitter::Node<'a>> = vec![fn_node];
    while let Some(node) = stack.pop() {
        let kind = node.kind();
        if kind == "proof_block" || kind == "assert_expression" {
            if let Some((start, end)) = first_brace_body_range(node) {
                ranges.push((start, end));
            }
        }
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            stack.push(child);
        }
    }
}

/// Find the byte range between the first `{` child and its matching
/// `}` (the last `}` child, since `_tactic_brace_body`'s nested
/// braces are handled by `_tactic_item` and don't appear as top-level
/// children of `proof_block` / `assert_expression`). Returns `None`
/// when the node has no brace body (e.g., `assert(P) by(solver)`).
fn first_brace_body_range<'a>(node: tree_sitter::Node<'a>) -> Option<(usize, usize)> {
    let mut open_end: Option<usize> = None;
    let mut close_start: Option<usize> = None;
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        match child.kind() {
            "{" if open_end.is_none() => open_end = Some(child.end_byte()),
            "}" => close_start = Some(child.start_byte()),
            _ => {}
        }
    }
    match (open_end, close_start) {
        (Some(s), Some(e)) if s < e => Some((s, e)),
        _ => None,
    }
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

    // --- Edge cases ---

    #[test]
    fn test_garbage_input() {
        // Totally invalid input — tree-sitter should handle gracefully
        let src = "}{][)(🎉🎉🎉 not valid rust at all !!!";
        assert_eq!(sanitize_tactic_blocks(src), src);
    }

    #[test]
    fn test_empty_input() {
        assert_eq!(sanitize_tactic_blocks(""), "");
    }

    #[test]
    fn test_only_comments() {
        let src = "// just a comment\n/* block */";
        assert_eq!(sanitize_tactic_blocks(src), src);
    }

    // --- tactus_auto-aware sanitization of proof_block + assert_expression ---

    #[test]
    fn test_tactus_auto_proof_block_sanitized() {
        // Inside a `#[verifier::tactus_auto]` fn, `proof { … }` content
        // is treated as Lean tactics and sanitized.
        let src = "verus! {\n\
            #[verifier::tactus_auto]\n\
            fn compute() {\n\
                proof { have h : True := by omega }\n\
            }\n\
        }";
        let sanitized = sanitize_tactic_blocks(src);
        assert!(!sanitized.contains("omega"), "proof{{}} inside tactus_auto fn should be sanitized");
        assert!(!sanitized.contains("have h"), "proof{{}} content should be wiped");
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_tactus_auto_assert_by_sanitized() {
        // Inside a `#[verifier::tactus_auto]` fn, `assert(P) by { … }`
        // content is treated as Lean tactics and sanitized.
        let src = "verus! {\n\
            #[verifier::tactus_auto]\n\
            fn compute(x: u32) {\n\
                assert(x >= 0) by { omega }\n\
            }\n\
        }";
        let sanitized = sanitize_tactic_blocks(src);
        assert!(!sanitized.contains("omega"), "assert-by inside tactus_auto should be sanitized");
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_tactus_auto_assert_forall_by_sanitized() {
        // `assert forall|...| P by { ... }` variant inside a tactus_auto fn.
        let src = "verus! {\n\
            #[verifier::tactus_auto]\n\
            fn compute() {\n\
                assert forall|i: int| #[trigger] f(i) by { intro i; omega }\n\
            }\n\
        }";
        let sanitized = sanitize_tactic_blocks(src);
        assert!(!sanitized.contains("omega"), "assert-forall-by inside tactus_auto should be sanitized");
        assert!(!sanitized.contains("intro i"), "tactic body wiped");
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_non_tactus_auto_proof_block_preserved() {
        // vstd-style: plain (non-tactus_auto) exec fn with `proof { }`
        // containing Verus-flavoured Rust proof code. Must NOT be
        // sanitized — vstd depends on this.
        let src = "verus! {\n\
            fn compute() {\n\
                proof { assert(true); lemma_helper(); }\n\
            }\n\
        }";
        let sanitized = sanitize_tactic_blocks(src);
        assert!(sanitized.contains("lemma_helper"),
            "proof{{}} in non-tactus_auto fn must stay: got {}", sanitized);
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_non_tactus_auto_assert_by_preserved() {
        // vstd-style: `assert(P) by { lemma(); }` in a non-tactus_auto fn.
        // Content stays as Rust/Verus proof code.
        let src = "verus! {\n\
            fn compute(x: u32) {\n\
                assert(x >= 0) by { lemma_nonneg(x); }\n\
            }\n\
        }";
        let sanitized = sanitize_tactic_blocks(src);
        assert!(sanitized.contains("lemma_nonneg"),
            "assert-by in non-tactus_auto fn must stay: got {}", sanitized);
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_mixed_tactus_auto_and_plain_fns() {
        // Two fns side-by-side — only the tactus_auto one has its
        // proof-block sanitized. Exercises the per-fn discrimination.
        let src = "verus! {\n\
            #[verifier::tactus_auto]\n\
            fn a() {\n\
                proof { have h : True := by omega }\n\
            }\n\
            fn b() {\n\
                proof { assert(true); vstd_lemma(); }\n\
            }\n\
        }";
        let sanitized = sanitize_tactic_blocks(src);
        assert!(!sanitized.contains("omega"),
            "tactus_auto fn's proof{{}} sanitized");
        assert!(sanitized.contains("vstd_lemma"),
            "plain fn's proof{{}} preserved: got {}", sanitized);
    }

    #[test]
    fn test_tactus_auto_unicode_in_assert_by() {
        // The whole point of sanitizing is Unicode — verify a Lean-style
        // `⟨a, b⟩` inside an assert-by body gets wiped under tactus_auto
        // (would otherwise fail rustc lexing).
        let src = "verus! {\n\
            #[verifier::tactus_auto]\n\
            fn compute() {\n\
                assert(x == x) by { exact ⟨rfl, rfl⟩ }\n\
            }\n\
        }";
        let sanitized = sanitize_tactic_blocks(src);
        assert!(!sanitized.contains("⟨"),
            "Unicode inside tactus_auto assert-by must be sanitized");
        assert_eq!(sanitized.len(), src.len());
    }

    // --- read_tactic_from_source edge cases ---

    #[test]
    fn test_read_tactic_nonexistent_file() {
        let result = crate::verifier::read_tactic_from_source(
            "/nonexistent/path/file.rs", 0, 10,
        );
        assert!(result.is_none());
    }

    #[test]
    fn test_read_tactic_out_of_bounds() {
        let dir = std::env::temp_dir().join("tactus_test_oob");
        std::fs::write(&dir, "by { omega }").unwrap();
        let path = dir.to_str().unwrap();
        // end_byte past file length
        assert!(crate::verifier::read_tactic_from_source(path, 0, 9999).is_none());
        // start+1 >= end (degenerate range)
        assert!(crate::verifier::read_tactic_from_source(path, 5, 5).is_none());
        assert!(crate::verifier::read_tactic_from_source(path, 5, 6).is_none());
        std::fs::remove_file(&dir).ok();
    }

    #[test]
    fn test_read_tactic_normal() {
        let dir = std::env::temp_dir().join("tactus_test_normal");
        std::fs::write(&dir, "by {\n    omega\n}").unwrap();
        let path = dir.to_str().unwrap();
        // byte range covers "{\n    omega\n}" (positions 3..15)
        let result = crate::verifier::read_tactic_from_source(path, 3, 15);
        assert_eq!(result.as_deref(), Some("\nomega"));
        std::fs::remove_file(&dir).ok();
    }
}
