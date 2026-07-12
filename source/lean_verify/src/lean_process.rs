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
/// source location the diagnostic points at. The verifier uses
/// `location` as the primary span of the rust_verify error, so
/// the `-->` arrow points at the failing assert / invariant /
/// call rather than at the enclosing fn signature. See
/// [`crate::generate::DiagLocation`] for the three variants.
pub struct FormattedDiag {
    pub message: String,
    pub location: crate::generate::DiagLocation,
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
    use crate::generate::DiagLocation;
    let mut out = String::new();
    let mut location = DiagLocation::Unknown;

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
            if let Some(span) = mark.rust_span.clone() {
                location = DiagLocation::Direct(span);
            }
        } else if let Some(offset) = source_map.find_tactic_line(pos.line) {
            // Proof-fn diag inside the tactic body. The verifier
            // will translate `offset` to an absolute source line via
            // the fn's `tactic_span` byte range + rustc's
            // `SourceMap`. We still emit `tactic line N:` in the
            // message body as a fallback for tooling / terminals
            // that don't render `-->` (the JSON test output, etc.).
            out.push_str(&format!("tactic line {}: ", offset + 1));
            location = DiagLocation::ProofFnBodyLine(offset);
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

    FormattedDiag { message: out, location }
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
    // Extra dirs to prepend to the child's `LEAN_PATH`: the prebuilt-
    // prelude cache dir (CRATEDEFS.md step 0) and, in shared-defs mode,
    // the crate dir holding `TactusDefs_{crate}.olean` (step 1a).
    // Empty only in tests that check prelude-free fragments.
    extra_lean_paths: &[&std::path::Path],
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
    if !extra_lean_paths.is_empty() {
        let mut parts: Vec<String> = extra_lean_paths.iter()
            .map(|p| p.to_string_lossy().into_owned())
            .collect();
        match std::env::var("LEAN_PATH") {
            Ok(existing) if !existing.is_empty() => parts.push(existing),
            _ => {}
        }
        command.env("LEAN_PATH", parts.join(":"));
    }
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
pub(crate) fn parse_diagnostics(output: &str) -> Vec<LeanDiagnostic> {
    output.lines()
        .filter_map(|line| serde_json::from_str(line.trim()).ok())
        .collect()
}

#[cfg(test)]
#[path = "tests/lean_process.rs"]
mod tests;
