use std::io::Write;
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

/// Check Lean source by piping it to `lean --stdin --json`.
///
/// This is the simplest invocation mode — no Lake project, no Mathlib.
/// For Mathlib support, use `check_lean_in_project` instead.
pub fn check_lean_stdin(lean_source: &str) -> Result<LeanResult, String> {
    let mut child = Command::new("lean")
        .args(["--stdin", "--json"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("Failed to spawn lean: {}. Is Lean 4 installed?", e))?;

    child
        .stdin
        .take()
        .unwrap()
        .write_all(lean_source.as_bytes())
        .map_err(|e| format!("Failed to write to lean stdin: {}", e))?;

    let output = child
        .wait_with_output()
        .map_err(|e| format!("Failed to wait for lean: {}", e))?;

    let stdout = String::from_utf8_lossy(&output.stdout);
    let diagnostics = parse_diagnostics(&stdout);

    let has_error = diagnostics.iter().any(|d| d.severity == "error");
    let success = output.status.success() && !has_error;

    Ok(LeanResult {
        success,
        diagnostics,
    })
}

/// Parse Lean's JSON diagnostic output (one JSON object per line).
fn parse_diagnostics(output: &str) -> Vec<LeanDiagnostic> {
    let mut diagnostics = Vec::new();
    for line in output.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        match serde_json::from_str::<LeanDiagnostic>(line) {
            Ok(diag) => diagnostics.push(diag),
            Err(_) => {
                // Non-JSON output — skip (could be progress messages)
            }
        }
    }
    diagnostics
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
