use std::io::Write;
use std::process::{Command, Stdio};
use std::time::Duration;

/// Maximum time to wait for Lean before giving up.
const LEAN_TIMEOUT: Duration = Duration::from_secs(120);

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

/// Format error diagnostics into a user-friendly string.
///
/// Parses Lean's goal state from the error data and formats it clearly:
/// - Separates the error summary from the goal state
/// - Indents the goal context (hypotheses + ⊢ goal)
/// - Includes tactic line info from the source map
pub fn format_error(
    diag: &LeanDiagnostic,
    source_map: &crate::to_lean_fn::LeanSourceMap,
) -> String {
    let mut out = String::new();

    // Tactic line info
    if let Some(pos) = &diag.pos {
        if let Some(offset) = source_map.find_tactic_line(pos.line) {
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

    out
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

/// Check Lean source by piping it to `lean --stdin --json`.
///
/// This is the simplest invocation mode — no Lake project, no Mathlib.
/// For Mathlib support, use `check_lean_in_project` instead.
pub fn check_lean_stdin(lean_source: &str) -> Result<LeanResult, String> {
    run_lean(&["lean", "--stdin", "--json"], lean_source, None)
}

/// Check Lean source using `lake env lean` from a Lake project directory.
///
/// This mode provides access to Mathlib and other Lake dependencies.
pub fn check_lean_in_project(
    lean_source: &str,
    project_dir: &std::path::Path,
) -> Result<LeanResult, String> {
    run_lean(
        &["lake", "env", "lean", "--stdin", "--json"],
        lean_source,
        Some(project_dir),
    )
}

fn run_lean(
    cmd: &[&str],
    lean_source: &str,
    working_dir: Option<&std::path::Path>,
) -> Result<LeanResult, String> {
    let mut command = Command::new(cmd[0]);
    command.args(&cmd[1..])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if let Some(dir) = working_dir {
        command.current_dir(dir);
    }

    let mut child = command.spawn()
        .map_err(|e| format!("Failed to spawn {}: {}. Is Lean 4 installed?", cmd[0], e))?;

    child
        .stdin
        .take()
        .unwrap()
        .write_all(lean_source.as_bytes())
        .map_err(|e| format!("Failed to write to lean stdin: {}", e))?;

    // Wait with timeout to avoid hanging on elaboration loops
    let output = match wait_with_timeout(child, LEAN_TIMEOUT)? {
        Some(out) => out,
        None => return Err("Lean timed out (120s). The proof may cause elaboration to loop.".into()),
    };

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let diagnostics = parse_diagnostics(&stdout);

    let has_error = diagnostics.iter().any(|d| d.severity == "error");
    // If no JSON diagnostics but process failed, include stderr
    let success = output.status.success() && !has_error;
    if !success && diagnostics.is_empty() && !stderr.is_empty() {
        return Err(format!("Lean failed: {}", stderr.trim()));
    }

    Ok(LeanResult {
        success,
        diagnostics,
    })
}

/// Wait for a child process with a timeout. Returns None if timed out.
/// Takes ownership of the child because `wait_with_output` requires it.
fn wait_with_timeout(
    mut child: std::process::Child,
    timeout: Duration,
) -> Result<Option<std::process::Output>, String> {
    let start = std::time::Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(_)) => {
                return child.wait_with_output()
                    .map(Some)
                    .map_err(|e| format!("Failed to read lean output: {}", e));
            }
            Ok(None) => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    return Ok(None);
                }
                std::thread::sleep(Duration::from_millis(100));
            }
            Err(e) => return Err(format!("Failed to wait for lean: {}", e)),
        }
    }
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

    #[test]
    fn test_trivial_lean_check() {
        let result = check_lean_stdin("theorem foo : 1 + 1 = 2 := by omega\n");
        match result {
            Ok(r) => {
                assert!(r.success, "Lean should verify 1+1=2. Diagnostics: {:?}", r.diagnostics);
            }
            Err(e) => {
                // Lean might not be installed in CI — skip gracefully
                eprintln!("Skipping test (lean not available): {}", e);
            }
        }
    }

    #[test]
    fn test_failing_lean_check() {
        let result = check_lean_stdin("theorem foo : 1 + 1 = 3 := by omega\n");
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
    }
}
