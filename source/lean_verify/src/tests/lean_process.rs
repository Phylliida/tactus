//! Unit tests for `lean_process` — extracted to `src/tests/` (a `#[path]`'d
//! `mod tests` child of `lean_process`, so `use super::*` reaches private items).

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
    let result = check_lean_file(&path, None, None);
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
    let result = check_lean_file(&path, None, None);
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
