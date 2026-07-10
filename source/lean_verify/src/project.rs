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

/// Fingerprint of the Lean environment islands and oleans are built
/// against: `lean --version` output plus, when the Mathlib project
/// exists, the bytes of its `lean-toolchain` and `lake-manifest.json`
/// (the Mathlib pin). Cross-run caches must key on this — a stale
/// olean behind a toolchain bump would otherwise be trusted without
/// any later elaboration to catch the mismatch (islands have no Link
/// gate; the prelude marker had the same latent gap). Memoized per
/// process; a failed `lean --version` yields a nonce-free constant
/// that still changes when the project files do.
pub fn toolchain_fingerprint() -> &'static str {
    static FP: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    FP.get_or_init(|| {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        let version = std::process::Command::new("lean")
            .arg("--version")
            .output()
            .map(|o| String::from_utf8_lossy(&o.stdout).into_owned())
            .unwrap_or_else(|_| "no-lean".to_string());
        version.hash(&mut h);
        let dir = default_project_dir();
        for f in ["lean-toolchain", "lake-manifest.json"] {
            std::fs::read(dir.join(f)).unwrap_or_default().hash(&mut h);
        }
        format!("{:016x}", h.finish())
    })
}
