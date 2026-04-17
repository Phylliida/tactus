//! Locate the Lake project for Lean invocation.
//!
//! Tactus uses a Lake project at `tactus/lean-project/` (repo-local) to provide
//! Mathlib access. Override with `TACTUS_LEAN_PROJECT` env var.

use std::path::{Path, PathBuf};

/// Compile-time path to lean_verify crate → `tactus/source/lean_verify/`.
/// From here, `../../lean-project` = `tactus/lean-project/`.
const LEAN_VERIFY_DIR: &str = env!("CARGO_MANIFEST_DIR");

/// Find the project directory.
///
/// Uses `TACTUS_LEAN_PROJECT` env var if set, otherwise
/// `tactus/lean-project/` relative to this crate at compile time.
pub fn default_project_dir() -> PathBuf {
    if let Ok(dir) = std::env::var("TACTUS_LEAN_PROJECT") {
        return PathBuf::from(dir);
    }
    let local = Path::new(LEAN_VERIFY_DIR)
        .ancestors().nth(2)
        .unwrap_or(Path::new("."))
        .join("lean-project");
    local.canonicalize().unwrap_or(local)
}

/// Check if the project exists and has been built (has .lake/).
pub fn project_ready(project_dir: &Path) -> bool {
    project_dir.join("lakefile.lean").exists() && project_dir.join(".lake").exists()
}
