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

/// Emitter/closer BINARY identity (P3/b67): the vargo build version
/// (`VARGO_BUILD_VERSION`, set for the whole build so this crate sees the
/// same string `rust_verify::util::verus_build_info` reports) plus an
/// FNV-1a content hash of the running executable. Content, not mtime:
/// deterministic, and it catches dirty-tree rebuilds where the version
/// string is unchanged (`<sha>.dirty` for two different trees). Used by
/// the `-V cache` base key (the documented b74 hole: a rebuilt binary
/// with changed closer logic reused old Z3 verdicts) and by the W4b
/// bridge pass markers. Island/pkg verdict caches deliberately do NOT
/// use this (they key on emitted text; "this text elaborates" is a
/// binary-independent fact — see `ladder_fingerprint`).
/// Memoized per process; over-invalidates on any relink — the safe
/// direction, and "one re-verify per rebuilt binary" is the ladder
/// precedent's honest price.
pub fn emitter_fingerprint() -> &'static str {
    static FP: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    FP.get_or_init(|| {
        let version = option_env!("VARGO_BUILD_VERSION").unwrap_or("unknown");
        let mut h: u64 = 0xcbf29ce484222325;
        if let Ok(exe) = std::env::current_exe() {
            if let Ok(bytes) = std::fs::read(&exe) {
                for b in bytes {
                    h ^= b as u64;
                    h = h.wrapping_mul(0x100000001b3);
                }
            }
        }
        format!("{}:fnv1a:{:016x}", version, h)
    })
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
/// Toolchain fingerprint EXTENDED with the verus binary's own identity
/// (exe mtime + size). For the defs ladder's success/FAILURE records:
/// a FAILED record means "this BINARY failed on this render" — emitter
/// changes that only alter partition ASSEMBLY (not the hashed monolith
/// render) must not fast-path over a recorded failure. One ladder
/// retry per rebuilt binary is the honest price. Island `.verified`
/// markers deliberately do NOT use this (they key on the emitted text,
/// which the emitter always regenerates — already correct).
pub fn ladder_fingerprint() -> &'static str {
    static FP: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    FP.get_or_init(|| {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        toolchain_fingerprint().hash(&mut h);
        if let Ok(exe) = std::env::current_exe() {
            if let Ok(md) = std::fs::metadata(&exe) {
                md.len().hash(&mut h);
                if let Ok(t) = md.modified() {
                    if let Ok(d) = t.duration_since(std::time::UNIX_EPOCH) {
                        d.as_secs().hash(&mut h);
                    }
                }
            }
        }
        format!("{:016x}", h.finish())
    })
}

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
