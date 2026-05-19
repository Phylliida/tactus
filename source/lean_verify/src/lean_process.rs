use std::process::{Command, Stdio};

/// A single diagnostic from Lean's `--json` output.
#[derive(Debug, Clone, serde::Deserialize)]
pub struct LeanDiagnostic {
    pub severity: String,
    #[serde(rename = "pos")]
    pub pos: Option<LeanPos>,
    #[serde(rename = "endPos")]
    pub end_pos: Option<LeanPos>,
    #[serde(rename = "data")]
    pub data: String,
}

#[derive(Debug, Clone, serde::Deserialize)]
pub struct LeanPos {
    pub line: usize,
    pub column: usize,
}

#[derive(Debug)]
pub struct LeanResult {
    pub success: bool,
    pub diagnostics: Vec<LeanDiagnostic>,
}

/// A single formatted error diagnostic from Lean, paired with the
/// Verus `Span` of the obligation that failed (when one could be
/// resolved from the source map). The verifier uses `rust_span` as
/// the primary span of the rust_verify error, so the `-->` arrow
/// points at the failing assert / invariant / call rather than at
/// the enclosing fn signature. `None` falls back to the fn span
/// (the pre-fix behaviour) — happens for proof-fn diagnostics
/// where per-obligation spans aren't plumbed yet, and for exec-fn
/// diagnostics whose `pos.line` precedes every obligation mark
/// (rare; usually only "no goals" errors at the closing tactic).
pub struct FormattedDiag {
    pub message: String,
    pub rust_span: Option<vir::messages::Span>,
}

/// Format error diagnostics into a user-friendly string plus the
/// obligation span (when resolvable).
///
/// Parses Lean's goal state from the error data and formats it clearly:
/// - Separates the error summary from the goal state
/// - Indents the goal context (hypotheses + ⊢ goal)
/// - Includes tactic line info from the source map
///
/// The `at <loc>:` prefix is preserved in the message body even when
/// `rust_span` is `Some(...)` — Verus's diagnostic rendering shows
/// `-->` for the primary span but doesn't always make the file path
/// visible to downstream filters; keeping the explicit `at <loc>:`
/// inside the body means tests and tooling that match on the message
/// text still see the location.
pub fn format_error(
    diag: &LeanDiagnostic,
    source_map: &crate::to_lean_fn::LeanSourceMap,
) -> FormattedDiag {
    let mut out = String::new();
    let mut rust_span: Option<vir::messages::Span> = None;

    // Source location info: prefer the Rust span (from #51's
    // SpanMark instrumentation, populated for exec fns), fall
    // back to the tactic-line offset (proof fns).
    if let Some(pos) = &diag.pos {
        if let Some(mark) = source_map.find_span_mark(pos.line) {
            // `at <loc> (<kind label>):` — kind label only when
            // non-empty (Plain has no extra context worth showing).
            // `paren_label` lives in `vir::tactus_messages` so the
            // parens framing has one definition shared with tests
            // that assert against it (Lens 15).
            let label = mark.kind.label();
            if label.is_empty() {
                out.push_str(&format!("at {}:\n", mark.loc));
            } else {
                out.push_str(&format!("at {} {}:\n",
                    mark.loc, vir::tactus_messages::paren_label(label)));
            }
            rust_span = mark.rust_span.clone();
        } else if let Some(offset) = source_map.find_tactic_line(pos.line) {
            out.push_str(&format!("tactic line {}: ", offset + 1));
        }
    }

    if let Some((summary, goal_state)) = split_goal_state(&diag.data) {
        out.push_str(summary.trim());
        out.push('\n');
        for line in goal_state.lines() {
            // Filter noise: trailing "failed" from linarith
            if !line.is_empty() && line.trim() != "failed" {
                out.push_str("  ");
                out.push_str(line);
                out.push('\n');
            }
        }
    } else {
        out.push_str(&diag.data);
        out.push('\n');
    }

    FormattedDiag { message: out, rust_span }
}

/// Try to split Lean error data into a summary line and goal state.
fn split_goal_state(data: &str) -> Option<(&str, &str)> {
    if let Some(rest) = data.strip_prefix("unsolved goals\n") {
        return Some(("unsolved goals:", rest));
    }

    if let Some(newline_pos) = data.find('\n') {
        let first_line = &data[..newline_pos];
        let rest = &data[newline_pos + 1..];

        if first_line.contains("could not prove")
            || first_line.contains("failed")
            || first_line.contains("error")
        {
            return Some((first_line, rest));
        }
    }

    None
}

/// Check a Lean source file by invoking `lean --json <path>`, optionally inside a
/// Lake project so imports (e.g., Mathlib) resolve.
///
/// The source is expected to already be on disk at `file_path`; this function
/// does not write. See `generate::check_proof_fn` / `check_exec_fn` for the
/// full write-then-check flow.
///
/// **Lake bypass when `LEAN_PATH` is already set.** Running `lake env lean`
/// acquires a per-project configuration lock — fine for one-off invocations,
/// but parallel test runs hit
/// `could not acquire an exclusive configuration lock` errors when multiple
/// processes call `lake env` simultaneously. Once Mathlib's `LEAN_PATH` is
/// known (e.g., resolved once by the test harness via
/// `lake env printenv LEAN_PATH`), the parent process can export `LEAN_PATH`
/// before spawning verification subprocesses, and we run `lean` directly
/// without going through lake. The subprocess inherits `LEAN_PATH` and
/// resolves imports via that without acquiring a lock. See
/// `rust_verify_test/tests/common/mod.rs` for the harness side.
pub fn check_lean_file(
    file_path: &std::path::Path,
    lake_dir: Option<&std::path::Path>,
) -> Result<LeanResult, String> {
    let abs_path = file_path.canonicalize()
        .unwrap_or_else(|_| file_path.to_path_buf());
    let path_str = abs_path.to_string_lossy().into_owned();

    // If `LEAN_PATH` is already populated in the process environment,
    // we can skip lake entirely — Lean will resolve imports via the
    // pre-set path and we avoid lake's configuration lock. See the
    // doc comment above for the full rationale.
    let lean_path_set = std::env::var_os("LEAN_PATH")
        .map(|v| !v.is_empty())
        .unwrap_or(false);

    let (mut command, label) = match (lake_dir, lean_path_set) {
        (Some(_), true) | (None, _) => {
            // No lake_dir means we never had Mathlib intended; or
            // LEAN_PATH is already set so lake's configuration is
            // unnecessary. Either way, plain `lean`.
            let mut c = Command::new("lean");
            c.args(["--json", &path_str]);
            (c, "lean")
        }
        (Some(dir), false) => {
            let mut c = Command::new("lake");
            c.args(["env", "lean", "--json", &path_str]);
            c.current_dir(dir);
            (c, "lake env lean")
        }
    };
    command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    let output = command.output()
        .map_err(|e| format!("Failed to spawn {}: {}. Is Lean 4 installed?", label, e))?;

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let diagnostics = parse_diagnostics(&stdout);

    let has_error = diagnostics.iter().any(|d| d.severity == "error");
    let success = output.status.success() && !has_error;
    if !success && diagnostics.is_empty() && !stderr.is_empty() {
        return Err(format!("Lean failed: {}", stderr.trim()));
    }

    Ok(LeanResult { success, diagnostics })
}

/// Parse Lean's JSON diagnostic output (one JSON object per line).
fn parse_diagnostics(output: &str) -> Vec<LeanDiagnostic> {
    output.lines()
        .filter_map(|line| serde_json::from_str(line.trim()).ok())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    fn write_tmp(source: &str, suffix: &str) -> std::path::PathBuf {
        let pid = std::process::id();
        let path = std::env::temp_dir().join(format!("tactus_leanprocess_{}_{}.lean", pid, suffix));
        let mut f = std::fs::File::create(&path).expect("tmp file");
        f.write_all(source.as_bytes()).expect("write tmp");
        path
    }

    #[test]
    fn test_trivial_lean_check() {
        let path = write_tmp("theorem foo : 1 + 1 = 2 := by omega\n", "pass");
        let result = check_lean_file(&path, None);
        match result {
            Ok(r) => {
                assert!(r.success, "Lean should verify 1+1=2. Diagnostics: {:?}", r.diagnostics);
            }
            Err(e) => {
                eprintln!("Skipping test (lean not available): {}", e);
            }
        }
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_failing_lean_check() {
        let path = write_tmp("theorem foo : 1 + 1 = 3 := by omega\n", "fail");
        let result = check_lean_file(&path, None);
        match result {
            Ok(r) => {
                assert!(!r.success, "Lean should reject 1+1=3");
                assert!(
                    r.diagnostics.iter().any(|d| d.severity == "error"),
                    "Should have error diagnostics"
                );
            }
            Err(e) => {
                eprintln!("Skipping test (lean not available): {}", e);
            }
        }
        let _ = std::fs::remove_file(&path);
    }
}
