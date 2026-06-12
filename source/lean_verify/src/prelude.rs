//! The Tactus prelude for Lean — source constant + prebuilt-module cache.
//!
//! Historically the prelude was inlined verbatim into every generated
//! `.lean` file (`Command::Raw(TACTUS_PRELUDE)`), costing ~1.3s of
//! re-elaboration per check (measured 2026-06-12, CRATEDEFS.md step 0).
//! Generated files now emit `import TactusPrelude` instead, against a
//! `.olean` built once per prelude version into a content-hashed cache
//! dir under `lean_out_root()`; `check_lean_file` puts that dir on the
//! child's `LEAN_PATH`.
//!
//! Consequence: generated files are no longer standalone — checking one
//! by hand needs the cache dir on `LEAN_PATH` (see BUILD.md).

use std::path::PathBuf;

/// The Tactus prelude source. As the prelude grows (Seq, Set, etc.),
/// edit TactusPrelude.lean directly — it's a real .lean file that can be
/// syntax-highlighted and tested independently. Still the source of
/// truth for `sanity.rs`'s prelude-name extraction.
pub const TACTUS_PRELUDE: &str = include_str!("../TactusPrelude.lean");

/// Header emitted in generated files in place of the inline prelude:
/// the import plus the prelude's file-scoped `set_option`s, which do
/// NOT propagate through `import` and must be restated per file.
pub const TACTUS_PRELUDE_IMPORT: &str = "import TactusPrelude\n\
set_option linter.unusedVariables false\n\
set_option maxHeartbeats 800000";

/// Just the file-scoped `set_option`s, for files whose prelude arrives
/// transitively through a defs-module import (CRATEDEFS.md step 1a) —
/// options never propagate through `import` and must be restated.
pub const TACTUS_SET_OPTIONS: &str = "set_option linter.unusedVariables false\n\
set_option maxHeartbeats 800000";

/// Fixed cache dir for the prebuilt prelude module:
/// `{cache_root}/prelude`, where the cache root is USER-LEVEL
/// (`$TACTUS_PRELUDE_CACHE` → `$XDG_CACHE_HOME/tactus` →
/// `~/.cache/tactus` → `{lean_out_root}/_prelude_cache` as a last
/// resort), NOT `lean_out_root()`: the e2e harness isolates each
/// test's lean-out dir, and a per-test cache would rebuild the
/// identical olean 505 times per suite run.
///
/// ONE dir, no version coexistence: when the prelude changes, the next
/// check rebuilds in place and artifacts generated against the old
/// prelude simply fail — regenerate them by re-running tactus. (A
/// content-hashed multi-version layout was tried first and dropped:
/// backwards compatibility with stale artifacts isn't worth the code.)
pub fn prelude_cache_dir() -> PathBuf {
    let root = if let Ok(d) = std::env::var("TACTUS_PRELUDE_CACHE") {
        PathBuf::from(d)
    } else if let Ok(d) = std::env::var("XDG_CACHE_HOME") {
        PathBuf::from(d).join("tactus")
    } else if let Ok(h) = std::env::var("HOME") {
        PathBuf::from(h).join(".cache").join("tactus")
    } else {
        crate::generate::lean_out_root().join("_prelude_cache")
    };
    root.join("prelude")
}

pub fn ensure_prelude_olean() -> Result<PathBuf, String> {
    let dir = prelude_cache_dir();
    let marker = dir.join("TactusPrelude.lean");
    let olean = dir.join("TactusPrelude.olean");
    // The marker records which prelude version the olean was built
    // from. It is written AFTER the olean rename, so on any crash the
    // mismatch forces a rebuild (never a stale olean behind a fresh
    // marker). Concurrent same-version builders produce identical
    // artifacts; concurrent MIXED-version builders (two different
    // tactus binaries racing this dir) can interleave badly — accepted
    // as unrealistic; `rm -rf` the cache dir recovers.
    if olean.exists() && std::fs::read_to_string(&marker).ok().as_deref() == Some(TACTUS_PRELUDE) {
        return Ok(dir);
    }
    // Build in a pid-unique subdir: `lean -o` derives the module name
    // from the source path relative to its root dir (the cwd) and
    // refuses sources outside it — cwd = the subdir makes the module
    // exactly `TactusPrelude`.
    let build = dir.join(format!("build-{}", std::process::id()));
    std::fs::create_dir_all(&build)
        .map_err(|e| format!("could not create {}: {}", build.display(), e))?;
    std::fs::write(build.join("TactusPrelude.lean"), TACTUS_PRELUDE)
        .map_err(|e| format!("could not write prelude source: {}", e))?;
    let output = std::process::Command::new("lean")
        .args(["-o", "TactusPrelude.olean", "TactusPrelude.lean"])
        .current_dir(&build)
        .output()
        .map_err(|e| format!("failed to spawn lean for prelude build: {}. Is Lean 4 installed?", e))?;
    if !output.status.success() {
        let _ = std::fs::remove_dir_all(&build);
        return Err(format!(
            "prelude .olean build failed (this is a Tactus bug — the prelude should always elaborate):\n{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        ));
    }
    std::fs::rename(build.join("TactusPrelude.olean"), &olean)
        .map_err(|e| format!("could not move prelude olean into place: {}", e))?;
    std::fs::write(&marker, TACTUS_PRELUDE)
        .map_err(|e| format!("could not write prelude marker: {}", e))?;
    let _ = std::fs::remove_dir_all(&build);
    Ok(dir)
}
