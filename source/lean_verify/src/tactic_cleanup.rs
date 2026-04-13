//! Clean up Rust-tokenized tactic bodies for Lean.
//!
//! The proc macro captures tactic bodies as Rust tokens. Users write Lean-like
//! syntax using Rust-compatible forms:
//!   `unfold(double); omega()` → `unfold double\nomega`
//!   `constructor(); omega()` → `constructor\nomega`
//!
//! Semicolons separate tactic lines. `ident(args)` becomes `ident args`.
//! `ident()` becomes `ident`.

/// Clean a Rust-tokenized tactic body string into Lean tactic syntax.
///
/// Splits on semicolons (each becomes a tactic line), then converts
/// `ident(args)` → `ident args` for each statement.
pub fn clean_tactic_body(body: &str) -> String {
    body.split(';')
        .map(|stmt| clean_stmt(stmt.trim()))
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>()
        .join("\n")
}

/// Clean a single tactic statement: `ident(args)` → `ident args`.
fn clean_stmt(stmt: &str) -> String {
    if stmt.is_empty() {
        return String::new();
    }

    // Find the first `(` that could be a tactic call
    let Some(paren_pos) = stmt.find('(') else {
        return stmt.to_string();
    };

    let name = &stmt[..paren_pos];

    // Only convert if the prefix is a simple identifier (tactic name)
    if name.is_empty() || !name.chars().all(|c| c.is_alphanumeric() || c == '_' || c == '.') {
        return stmt.to_string();
    }

    // Extract balanced parens content
    let Some(inner) = balanced_parens(&stmt[paren_pos..]) else {
        return stmt.to_string();
    };

    let after = stmt[paren_pos + inner.len() + 2..].trim(); // +2 for ( and )
    let cleaned = clean_args(inner.trim());

    let mut result = name.to_string();
    if !cleaned.is_empty() {
        result.push(' ');
        result.push_str(&cleaned);
    }
    if !after.is_empty() {
        result.push(' ');
        result.push_str(&clean_stmt(after));
    }
    result
}

/// Clean tactic arguments: recursively clean nested `ident(args)` patterns.
fn clean_args(args: &str) -> String {
    if args.is_empty() {
        return String::new();
    }

    // Handle bracket-delimited lists like [sq_nonneg(re), sq_nonneg(im)]
    if args.starts_with('[') && args.ends_with(']') {
        let inner = &args[1..args.len() - 1];
        let cleaned: Vec<String> = split_respecting_depth(inner, ',')
            .iter()
            .map(|a| clean_stmt(a.trim()))
            .collect();
        return format!("[{}]", cleaned.join(", "));
    }

    // Otherwise, clean each comma-separated arg
    let parts: Vec<String> = split_respecting_depth(args, ',')
        .iter()
        .map(|a| clean_stmt(a.trim()))
        .collect();
    parts.join(", ")
}

/// Extract the content between the outermost balanced parens.
/// Input must start with `(`. Returns the content (without parens), or None if unbalanced.
fn balanced_parens(s: &str) -> Option<&str> {
    if !s.starts_with('(') {
        return None;
    }
    let mut depth: usize = 0;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(&s[1..i]);
                }
            }
            _ => {}
        }
    }
    None
}

/// Split by delimiter at the top level (depth 0), respecting balanced parens/brackets/braces.
fn split_respecting_depth(s: &str, delim: char) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut depth: usize = 0;
    for c in s.chars() {
        match c {
            '(' | '[' | '{' => {
                depth += 1;
                current.push(c);
            }
            ')' | ']' | '}' => {
                depth = depth.saturating_sub(1);
                current.push(c);
            }
            c if c == delim && depth == 0 => {
                parts.push(std::mem::take(&mut current));
            }
            _ => current.push(c),
        }
    }
    if !current.is_empty() {
        parts.push(current);
    }
    parts
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_tactics() {
        assert_eq!(clean_tactic_body("omega()"), "omega");
        assert_eq!(clean_tactic_body("omega() ;"), "omega");
        assert_eq!(clean_tactic_body("unfold(double) ; omega()"), "unfold double\nomega");
    }

    #[test]
    fn test_nested_args() {
        assert_eq!(
            clean_tactic_body("exact(Nat.mul_pos(by(omega), ih))"),
            "exact Nat.mul_pos by omega, ih"
        );
    }

    #[test]
    fn test_bracket_list() {
        assert_eq!(
            clean_tactic_body("nlinarith([sq_nonneg(re), sq_nonneg(im)])"),
            "nlinarith [sq_nonneg re, sq_nonneg im]"
        );
    }

    #[test]
    fn test_no_args() {
        assert_eq!(clean_tactic_body("constructor() ; omega() ; omega()"), "constructor\nomega\nomega");
    }

    #[test]
    fn test_passthrough() {
        // Non-ident prefixes are left as-is
        assert_eq!(clean_tactic_body("1 + 1"), "1 + 1");
    }
}
