//! Tactus FileLoader: sanitizes tactic blocks before rustc sees them.
//!
//! Uses tree-sitter-tactus to find `tactic_block` nodes (`by { }` on proof fns)
//! and replaces their content with spaces. Byte offsets are preserved so
//! `Span::byte_range()` still works. The verifier reads the original file
//! later to recover verbatim tactic text.
//!
//! ## Original-content cache for diagnostic rendering
//!
//! At file-load time, we also cache the original (un-sanitized) content
//! in a static map. At Tactus diagnostic emission time, `spans.rs` looks
//! up the original and swaps it into rustc's `SourceFile.src` so the
//! rendered `-->` preview shows real tactic content (`omega`, etc.) rather
//! than the blank spaces the lexer saw. See
//! `spans::swap_source_for_diagnostics` for the swap mechanics.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};

/// FileLoader that sanitizes tactic blocks before rustc lexes the source.
pub struct TactusFileLoader {
    /// Whether the crate under compilation runs `--lean-backend`.
    /// When true, pass 2 treats plain exec fns (no `proof`/`spec` mode
    /// keyword, no `#[verifier::z3]` opt-out) like `tactus_auto` fns:
    /// their `proof { }` / `assert … by { }` brace bodies are Lean
    /// tactic text and get sanitized. Owner decision 2026-07-02
    /// ("flag decides"): in a lean-backend crate, block language
    /// follows the fn's routing — a Lean-routed fn's proof blocks ARE
    /// Lean; `#[verifier::z3]` keeps a fn (routing AND blocks) on the
    /// Verus/Z3 side. Must mirror the HIR-side gate
    /// (`fn_call_to_vir::enclosing_fn_has_lean_tactic_blocks`) and the
    /// routing rule (`verifier.rs` Body(Normal) dispatch).
    pub lean_backend: bool,
}

/// Cache of original (un-sanitized) file contents, populated by `read_file`
/// and consumed by `spans::swap_source_for_diagnostics`. Keyed by
/// canonicalized path so loader-side and swap-side agree even when they
/// observe different relative paths.
static ORIGINAL_CACHE: OnceLock<Mutex<HashMap<PathBuf, Arc<String>>>> = OnceLock::new();

fn cache_original(path: PathBuf, content: Arc<String>) {
    ORIGINAL_CACHE
        .get_or_init(|| Mutex::new(HashMap::new()))
        .lock()
        .unwrap()
        .insert(path, content);
}

/// Look up the original content for a file. Returns `None` if the file
/// wasn't loaded through this `FileLoader` (e.g., stdlib crates loaded by
/// rustc's default mechanism).
pub fn original_for_path(path: &Path) -> Option<Arc<String>> {
    let canonical = std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
    ORIGINAL_CACHE.get()?.lock().unwrap().get(&canonical).cloned()
}

impl rustc_span::source_map::FileLoader for TactusFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        path.exists()
    }

    fn read_file(&self, path: &Path) -> Result<String, std::io::Error> {
        let source = std::fs::read_to_string(path)?;
        // Cache the original BEFORE sanitization so diagnostic-time swaps
        // can recover the real tactic content. Key by canonical path to
        // match what `spans.rs` looks up later.
        let canonical = std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
        cache_original(canonical, Arc::new(source.clone()));
        Ok(sanitize_tactic_blocks(&source, self.lean_backend))
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
/// `lean_backend`: see `TactusFileLoader::lean_backend`.
fn sanitize_tactic_blocks(source: &str, lean_backend: bool) -> String {
    let ranges = find_tactic_block_ranges(source.as_bytes(), lean_backend);
    if ranges.is_empty() {
        return source.to_string();
    }
    let mut out = source.as_bytes().to_vec();
    for (start, end) in ranges {
        for i in start..end {
            // Preserve `\n` (line breaks) and `\r` (so CRLF line endings
            // survive intact — otherwise rustc's `normalize_src` would see
            // bare `\n` in sanitized files and CRLF in the original, and
            // the per-file `normalized_pos` table would differ between
            // the two views, breaking the diagnostic-time swap).
            if out[i] != b'\n' && out[i] != b'\r' {
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
///    sanitized, inside fns whose proof blocks are Lean tactic text:
///    * fns marked `#[verifier::tactus_auto]` (the legacy per-fn
///      opt-in, any crate), OR
///    * when `lean_backend` is set ("flag decides", 2026-07-02):
///      plain exec fns — no `proof`/`spec` mode keyword, no
///      `#[verifier::z3]` opt-out — i.e. exactly the fns the
///      verifier routes to Lean.
///    These constructs exist in vstd and in Z3-path fns carrying
///    Rust-flavoured Verus proof code (calls to lemmas, nested
///    asserts) rather than Lean tactics; sanitizing those would wipe
///    real proofs — hence the per-fn discrimination. Proof fns are
///    never in scope for pass 2: they stay Z3-routed unless their
///    whole body is a `by { }` tactic_block (pass 1).
fn find_tactic_block_ranges(src: &[u8], lean_backend: bool) -> Vec<(usize, usize)> {
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

    // Pass 2: inside Lean-tactic-bodied function_items (tactus_auto
    // attr, or Lean-routed exec fns when lean_backend), sanitize
    // proof_block and assert_expression (with brace body) too.
    walk_lean_tactic_fns(tree.root_node(), src, lean_backend, &mut ranges);

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
/// whose proof blocks are Lean tactic text — `#[verifier::tactus_auto]`
/// marked, or (under `lean_backend`) a Lean-routed exec fn — collect
/// the inner `proof_block` / `assert_expression` brace-body ranges.
fn walk_lean_tactic_fns<'a>(
    node: tree_sitter::Node<'a>,
    src: &[u8],
    lean_backend: bool,
    ranges: &mut Vec<(usize, usize)>,
) {
    if node.kind() == "function_item"
        && (function_has_tactus_auto_attr(node, src)
            || (lean_backend && is_lean_routed_exec_fn(node, src)))
    {
        collect_inner_lean_blocks(node, ranges);
        // Keep walking to find nested fns (Rust allows `fn f() { fn g() { … } }`),
        // but the outer-fn body is already fully scanned — no double-count.
    }
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        walk_lean_tactic_fns(child, src, lean_backend, ranges);
    }
}

/// Textual mirror of the verifier's `--lean-backend` routing rule
/// (`verifier.rs`, `Body(Normal)` dispatch): a plain exec fn — no
/// `proof` / `spec` mode keyword in `function_modifiers` — that
/// doesn't opt back out to Z3 with `#[verifier::z3]`. Must agree with
/// the HIR-side gate (`fn_call_to_vir::enclosing_fn_has_lean_tactic_blocks`)
/// so the blocks sanitized here are exactly the ones consumed as
/// tactic spans there. Only immediate children are scanned — the body
/// is a single `block` child, never descended into.
fn is_lean_routed_exec_fn<'a>(fn_node: tree_sitter::Node<'a>, src: &[u8]) -> bool {
    let mut cursor = fn_node.walk();
    for child in fn_node.children(&mut cursor) {
        match child.kind() {
            "function_modifiers" => {
                let mut mc = child.walk();
                for m in child.children(&mut mc) {
                    if matches!(m.kind(), "proof" | "spec") {
                        return false;
                    }
                }
            }
            "attribute_item" => {
                // `#[verifier::z3]` / `#[verifier(z3)]` — substring
                // match like `function_has_tactus_auto_attr`, but
                // require both tokens so a stray "z3" in an unrelated
                // attr (e.g. a cfg feature name) doesn't opt out.
                if let Some(text) = src.get(child.byte_range()) {
                    if let Ok(s) = std::str::from_utf8(text) {
                        if s.contains("verifier") && s.contains("z3") {
                            return false;
                        }
                    }
                }
            }
            _ => {}
        }
    }
    true
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
        assert_eq!(sanitize_tactic_blocks(src, false), src);
    }

    /// Regression for BUG-fileloader-by-in-comment.md.
    ///
    /// A `by` keyword inside a `//` comment followed by `{` on the
    /// next comment line was being treated by tree-sitter as part of
    /// a tactic structure, breaking sanitization of the real
    /// `by { ... }` later in the file. The right fix is in the
    /// grammar — see tree-sitter-tactus/grammar.js. This test
    /// pins the file-loader behavior end-to-end: the real tactic
    /// body's content gets replaced with spaces.
    #[test]
    fn test_by_in_comment_does_not_break_sanitization() {
        let src = "\
::verus_builtin_macros::verus!{
proof fn warmup() ensures true by { decide }

// `assert(P) by
// { x }`

#[verifier::tactus_auto]
fn f(x: u64) -> (r: u64) requires x < 100 ensures r == 0 {
    assert(x < 100) by { intros; omega };
    0
}
}";
        let sanitized = sanitize_tactic_blocks(src, false);
        // The real `by { intros; omega }` should have its content
        // replaced with spaces. `intros` and `omega` should not
        // appear in the sanitized source.
        let real_assert_idx = sanitized.find("by {").expect("at least one tactic block visible after sanitize");
        // Find the LAST `by {` — the real assert-by inside f.
        let last_assert_idx = sanitized.rfind("by {").expect("real assert-by still in source");
        // Inside the brace body of the last assert-by, no `intros` / `omega`.
        let close = sanitized[last_assert_idx..].find('}').expect("close brace");
        let body = &sanitized[last_assert_idx..last_assert_idx + close];
        assert!(!body.contains("intros"),
            "real assert-by body should be sanitized; got body: {:?}", body);
        assert!(!body.contains("omega"),
            "real assert-by body should be sanitized; got body: {:?}", body);
        let _ = real_assert_idx;
    }

    #[test]
    fn test_tactic_block_sanitized() {
        let src = "proof fn test() ensures true by { omega }";
        let sanitized = sanitize_tactic_blocks(src, false);
        assert_eq!(sanitized, "proof fn test() ensures true by {       }");
    }

    #[test]
    fn test_tactic_block_multiline_sanitized() {
        let src = "proof fn test() ensures true by {\n    omega\n}";
        let sanitized = sanitize_tactic_blocks(src, false);
        assert_eq!(sanitized, "proof fn test() ensures true by {\n         \n}");
    }

    /// CRLF preservation: `\r` must survive sanitization
    /// alongside `\n`. Without this, sanitized files with CRLF
    /// line endings would have bare `\n` where the original had
    /// `\r\n`, and rustc's per-file `normalized_pos` table would
    /// differ between the two views — breaking the diagnostic-
    /// time `sf.src` swap in `spans::swap_source_for_diagnostics`
    /// (which assumes `lines` and `normalized_pos` match between
    /// sanitized and original by construction).
    #[test]
    fn test_tactic_block_preserves_cr() {
        let src = "proof fn test() ensures true by {\r\n    omega\r\n}";
        let sanitized = sanitize_tactic_blocks(src, false);
        // Both `\r` and `\n` survive; only the `omega` content
        // and surrounding spaces get blanked.
        assert_eq!(sanitized, "proof fn test() ensures true by {\r\n         \r\n}");
        // Byte count preserved.
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_unicode_sanitized() {
        let src = "proof fn test() ensures true\nby {\n    intro ⟨a, b⟩\n}";
        let sanitized = sanitize_tactic_blocks(src, false);
        assert!(!sanitized.contains("⟨"));
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_preserves_newlines() {
        let src = "proof fn test() ensures true\nby {\n    intro ⟨a⟩\n    omega\n}";
        let sanitized = sanitize_tactic_blocks(src, false);
        assert_eq!(sanitized.matches('\n').count(), src.matches('\n').count());
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_multiple_tactic_blocks() {
        let src = "proof fn a() ensures true by { omega }\nproof fn b() ensures true by { simp }";
        let sanitized = sanitize_tactic_blocks(src, false);
        assert_eq!(
            sanitized,
            "proof fn a() ensures true by {       }\nproof fn b() ensures true by {      }"
        );
    }

    #[test]
    fn test_assert_by_not_sanitized() {
        // assert-by contains Verus proof code, not Lean — not sanitized (Phase 2).
        let src = "fn test() { assert(true) by { omega }; }";
        assert_eq!(sanitize_tactic_blocks(src, false), src);
    }

    #[test]
    fn test_plain_assert_not_sanitized() {
        let src = "fn test() { assert(x > 0); }";
        assert_eq!(sanitize_tactic_blocks(src, false), src);
    }

    #[test]
    fn test_regular_fn_not_sanitized() {
        let src = "fn test() { let x = 5; let y = x + 1; }";
        assert_eq!(sanitize_tactic_blocks(src, false), src);
    }

    #[test]
    fn test_spec_fn_not_sanitized() {
        let src = "spec fn double(x: nat) -> nat { x + x }";
        assert_eq!(sanitize_tactic_blocks(src, false), src);
    }

    #[test]
    fn test_byte_length_preserved() {
        let src = "proof fn test() ensures true\nby {\n    intro ⟨a, b⟩\n    /- comment } -/\n    omega\n}";
        let sanitized = sanitize_tactic_blocks(src, false);
        assert_eq!(sanitized.len(), src.len());
    }

    // --- Inside verus! { } macro (the real-world case) ---

    #[test]
    fn test_inside_verus_macro() {
        let src = "verus! {\nproof fn test() ensures true\nby {\n    intro ⟨a, b⟩\n}\n}";
        let sanitized = sanitize_tactic_blocks(src, false);
        assert!(!sanitized.contains("⟨"), "Unicode inside verus! macro must be sanitized");
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_inside_scoped_verus_macro() {
        // Real test files use ::verus_builtin_macros::verus!{ }
        let src = "::verus_builtin_macros::verus!{\nproof fn t() ensures true by { omega }\n}";
        let sanitized = sanitize_tactic_blocks(src, false);
        assert!(!sanitized.contains("omega"));
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_verus_macro_assert_by_not_sanitized() {
        // assert-by inside verus! must NOT be sanitized — it's Verus proof code
        let src = "verus! {\nfn test() {\n    assert(true) by { lemma_foo(); };\n}\n}";
        assert_eq!(sanitize_tactic_blocks(src, false), src);
    }

    #[test]
    fn test_verus_macro_assert_forall_by_not_sanitized() {
        // assert forall ... by { } inside verus! — Verus proof code, not sanitized
        let src = "verus! {\nfn test() {\n    assert forall|i: int| #[trigger] f(i) by { lemma(i); };\n}\n}";
        assert_eq!(sanitize_tactic_blocks(src, false), src);
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
        let sanitized = sanitize_tactic_blocks(src, false);
        assert!(!sanitized.contains("omega"), "tactic block should be sanitized");
        assert!(sanitized.contains("lemma_call"), "assert-by should NOT be sanitized");
    }

    #[test]
    fn test_verus_macro_spec_fn_not_sanitized() {
        let src = "verus! {\nspec fn double(x: nat) -> nat { x + x }\n}";
        assert_eq!(sanitize_tactic_blocks(src, false), src);
    }

    // --- Paren/bracket macros stay as token trees (not parsed as statements) ---

    #[test]
    fn test_paren_macro_not_parsed() {
        let src = "println!(\"by {{ omega }}\");";
        assert_eq!(sanitize_tactic_blocks(src, false), src);
    }

    #[test]
    fn test_bracket_macro_not_parsed() {
        let src = "vec![1, 2, 3];";
        assert_eq!(sanitize_tactic_blocks(src, false), src);
    }

    // --- attributed_expression (#[trigger]) in quantifiers ---

    #[test]
    fn test_trigger_in_assert_forall() {
        // #[trigger] before the condition — must parse without errors
        // so the `by { }` is recognized as assert-by, NOT a stray tactic_block
        let src = "verus! {\nfn test() {\n    assert forall|x: int| #[trigger] f(x) by { lem(x); };\n}\n}";
        let sanitized = sanitize_tactic_blocks(src, false);
        assert!(sanitized.contains("lem(x)"), "#[trigger] assert-by must not be sanitized");
    }

    #[test]
    fn test_trigger_in_forall_expr() {
        let src = "verus! {\nspec fn p() -> bool { forall|x: int| #[trigger] f(x) }\n}";
        assert_eq!(sanitize_tactic_blocks(src, false), src);
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
        let sanitized = sanitize_tactic_blocks(src, false);
        assert!(!sanitized.contains('\u{b7}'), "· must be sanitized: got {sanitized}");
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_trigger_in_exists_expr() {
        let src = "verus! {\nspec fn p() -> bool { exists|x: int| #[trigger] f(x) }\n}";
        assert_eq!(sanitize_tactic_blocks(src, false), src);
    }

    // --- Lean syntax edge cases inside tactic blocks (the whole point of FileLoader) ---

    #[test]
    fn test_lean_line_comment_with_brace_in_verus() {
        // `-- comment }` must not close the tactic block
        let src = "verus! {\nproof fn t() ensures true\nby {\n    -- comment with } brace\n    omega\n}\n}";
        let sanitized = sanitize_tactic_blocks(src, false);
        assert_eq!(sanitized.matches('}').count(), 2); // verus! closing } + tactic closing }
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_lean_block_comment_with_brace_in_verus() {
        // `/- comment } -/` must not close the tactic block
        let src = "verus! {\nproof fn t() ensures true\nby {\n    /- comment } -/\n    omega\n}\n}";
        let sanitized = sanitize_tactic_blocks(src, false);
        assert_eq!(sanitized.matches('}').count(), 2);
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_string_with_brace_in_tactic() {
        // `"}"` inside tactic block must not close the block
        let src = "verus! {\nproof fn t() ensures true\nby {\n    have h := \"}\"\n    omega\n}\n}";
        let sanitized = sanitize_tactic_blocks(src, false);
        assert_eq!(sanitized.matches('}').count(), 2);
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_nested_braces_in_tactic() {
        // Nested { } inside tactic block must balance correctly
        let src = "verus! {\nproof fn t() ensures true\nby {\n    { exact h }\n    omega\n}\n}";
        let sanitized = sanitize_tactic_blocks(src, false);
        assert_eq!(sanitized.matches('}').count(), 2);
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_empty_tactic_block() {
        let src = "verus! {\nproof fn t() ensures true by { }\n}";
        let sanitized = sanitize_tactic_blocks(src, false);
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_multiple_tactic_blocks_in_verus() {
        let src = "verus! {\n\
            proof fn a() ensures true by { omega }\n\
            proof fn b() ensures true by { simp }\n\
        }";
        let sanitized = sanitize_tactic_blocks(src, false);
        assert!(!sanitized.contains("omega"));
        assert!(!sanitized.contains("simp"));
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_requires_and_ensures_before_by() {
        let src = "verus! {\nproof fn t(x: nat)\n    requires x > 0\n    ensures x >= 1\nby {\n    omega\n}\n}";
        let sanitized = sanitize_tactic_blocks(src, false);
        assert!(!sanitized.contains("omega"));
        assert!(sanitized.contains("requires"));
        assert!(sanitized.contains("ensures"));
    }

    // --- Edge cases ---

    #[test]
    fn test_garbage_input() {
        // Totally invalid input — tree-sitter should handle gracefully
        let src = "}{][)(🎉🎉🎉 not valid rust at all !!!";
        assert_eq!(sanitize_tactic_blocks(src, false), src);
    }

    #[test]
    fn test_empty_input() {
        assert_eq!(sanitize_tactic_blocks("", false), "");
    }

    #[test]
    fn test_only_comments() {
        let src = "// just a comment\n/* block */";
        assert_eq!(sanitize_tactic_blocks(src, false), src);
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
        let sanitized = sanitize_tactic_blocks(src, false);
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
        let sanitized = sanitize_tactic_blocks(src, false);
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
        let sanitized = sanitize_tactic_blocks(src, false);
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
        let sanitized = sanitize_tactic_blocks(src, false);
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
        let sanitized = sanitize_tactic_blocks(src, false);
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
        let sanitized = sanitize_tactic_blocks(src, false);
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
        let sanitized = sanitize_tactic_blocks(src, false);
        assert!(!sanitized.contains("⟨"),
            "Unicode inside tactus_auto assert-by must be sanitized");
        assert_eq!(sanitized.len(), src.len());
    }

    // --- lean_backend "flag decides" sanitization (2026-07-02) ---

    #[test]
    fn test_lean_backend_execfn_proof_block_sanitized() {
        // In a --lean-backend crate, a plain exec fn's `proof { }` is
        // Lean tactic text — sanitized without any attribute.
        let src = "verus! {\n\
            fn compute() {\n\
                proof { have h : True := by omega }\n\
            }\n\
        }";
        let sanitized = sanitize_tactic_blocks(src, true);
        assert!(!sanitized.contains("omega"),
            "attr-less exec fn's proof{{}} sanitized under lean_backend");
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_lean_backend_execfn_assert_by_sanitized() {
        let src = "verus! {\n\
            fn compute(x: u32) {\n\
                assert(x >= 0) by { omega }\n\
            }\n\
        }";
        let sanitized = sanitize_tactic_blocks(src, true);
        assert!(!sanitized.contains("omega"),
            "attr-less exec fn's assert-by sanitized under lean_backend");
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_lean_backend_z3_optout_preserved() {
        // `#[verifier::z3]` keeps the fn (routing AND blocks) on the
        // Verus/Z3 side — its proof blocks are Verus code, untouched.
        let src = "verus! {\n\
            #[verifier::z3]\n\
            fn compute() {\n\
                proof { assert(true); lemma_helper(); }\n\
            }\n\
        }";
        let sanitized = sanitize_tactic_blocks(src, true);
        assert!(sanitized.contains("lemma_helper"),
            "z3-marked fn's proof{{}} preserved under lean_backend: got {}", sanitized);
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_lean_backend_proof_fn_assert_by_preserved() {
        // Ordinary (non-tactic-bodied) proof fns stay Z3-routed even in
        // lean-backend crates; their assert-bys are Verus proof code.
        let src = "verus! {\n\
            proof fn lem(x: int) ensures x == x {\n\
                assert(x == x) by { lemma_refl(x); }\n\
            }\n\
        }";
        let sanitized = sanitize_tactic_blocks(src, true);
        assert!(sanitized.contains("lemma_refl"),
            "proof fn's assert-by preserved under lean_backend: got {}", sanitized);
        assert_eq!(sanitized.len(), src.len());
    }

    #[test]
    fn test_lean_backend_spec_fn_preserved() {
        let src = "verus! {\nspec fn double(x: nat) -> nat { x + x }\n}";
        assert_eq!(sanitize_tactic_blocks(src, true), src);
    }

    #[test]
    fn test_lean_backend_mixed_exec_and_proof_fns() {
        // The per-fn discrimination under the flag: exec fn's block
        // sanitized, proof fn's block preserved, side by side.
        let src = "verus! {\n\
            fn a() {\n\
                proof { have h : True := by omega }\n\
            }\n\
            proof fn b() ensures true {\n\
                assert(true) by { vstd_lemma(); }\n\
            }\n\
        }";
        let sanitized = sanitize_tactic_blocks(src, true);
        assert!(!sanitized.contains("omega"), "exec fn's proof{{}} sanitized");
        assert!(sanitized.contains("vstd_lemma"),
            "proof fn's assert-by preserved: got {}", sanitized);
    }

    #[test]
    fn test_flag_off_execfn_blocks_preserved() {
        // Without --lean-backend the legacy semantics hold: attr-less
        // exec fns keep Verus proof blocks (vstd, mixed crates).
        let src = "verus! {\n\
            fn compute() {\n\
                proof { assert(true); lemma_helper(); }\n\
            }\n\
        }";
        assert_eq!(sanitize_tactic_blocks(src, false), src);
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
