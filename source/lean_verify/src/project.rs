//! Locate the persistent Lake project for Lean invocation.
//!
//! Tactus uses a persistent Lake project at `~/.tactus/lean-project/` to provide
//! Mathlib access. The project is set up manually (see HANDOFF.md for instructions).

use std::path::{Path, PathBuf};

/// Default project location.
pub fn default_project_dir() -> Option<PathBuf> {
    dirs::home_dir().map(|h| h.join(".tactus").join("lean-project"))
}

/// Check if the project exists and has been built (has .lake/).
pub fn project_ready(project_dir: &Path) -> bool {
    project_dir.join("lakefile.lean").exists() && project_dir.join(".lake").exists()
}
