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

    // Source location info: prefer the Rust span (from #51's
    // SpanMark instrumentation, populated for exec fns), fall
    // back to the tactic-line offset (proof fns).
    if let Some(pos) = &diag.pos {
        if let Some(rust_loc) = source_map.find_rust_loc(pos.line) {
            out.push_str(&format!("at {}:\n", rust_loc));
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

/// Check a Lean source file by invoking `lean --json <path>`, optionally inside a
/// Lake project so imports (e.g., Mathlib) resolve.
///
/// The source is expected to already be on disk at `file_path`; this function
/// does not write. See `generate::check_proof_fn` / `check_exec_fn` for the
/// full write-then-check flow.
pub fn check_lean_file(
    file_path: &std::path::Path,
    lake_dir: Option<&std::path::Path>,
) -> Result<LeanResult, String> {
    let abs_path = file_path.canonicalize()
        .unwrap_or_else(|_| file_path.to_path_buf());
    let path_str = abs_path.to_string_lossy().into_owned();

    let (mut command, label) = match lake_dir {
        Some(dir) => {
            let mut c = Command::new("lake");
            c.args(["env", "lean", "--json", &path_str]);
            c.current_dir(dir);
            (c, "lake env lean")
        }
        None => {
            let mut c = Command::new("lean");
            c.args(["--json", &path_str]);
            (c, "lean")
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
