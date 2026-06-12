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

/// Content-hashed cache dir for the prebuilt prelude module:
/// `{cache_root}/prelude/{hash16}`. The hash keys the PRELUDE SOURCE,
/// so editing TactusPrelude.lean lands in a fresh dir and never races
/// a stale `.olean` (concurrent processes on the same version build
/// identical artifacts; the rename is per-file atomic).
///
/// The cache root is USER-LEVEL (`$TACTUS_PRELUDE_CACHE` →
/// `$XDG_CACHE_HOME/tactus` → `~/.cache/tactus` → `{lean_out_root}/
/// _prelude_cache` as a last resort), NOT `lean_out_root()`: the e2e
/// harness isolates each test's lean-out dir, and a per-test cache
/// would rebuild the identical olean 505 times per suite run. The
/// artifact is version-keyed and immutable — exactly the semantics of
/// a global cache (rustup-toolchain-style), warm across runs and
/// sessions.
pub fn prelude_cache_dir() -> PathBuf {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    TACTUS_PRELUDE.hash(&mut h);
    let root = if let Ok(d) = std::env::var("TACTUS_PRELUDE_CACHE") {
        PathBuf::from(d)
    } else if let Ok(d) = std::env::var("XDG_CACHE_HOME") {
        PathBuf::from(d).join("tactus")
    } else if let Ok(h) = std::env::var("HOME") {
        PathBuf::from(h).join(".cache").join("tactus")
    } else {
        crate::generate::lean_out_root().join("_prelude_cache")
    };
    root.join("prelude").join(format!("{:016x}", h.finish()))
}

/// Ensure `TactusPrelude.olean` exists in the cache dir, building it
/// with `lean -o` on first use (~2.7s, once per prelude version).
/// Returns the cache dir to prepend to the child `lean`'s `LEAN_PATH`.
///
/// Concurrency: parallel first-checks may race here. Each builds to a
/// pid-unique temp name and renames into place; same source → same
/// artifact, so last-writer-wins is correct. Losers do redundant work
/// exactly once per prelude version.
pub fn ensure_prelude_olean() -> Result<PathBuf, String> {
    let dir = prelude_cache_dir();
    let olean = dir.join("TactusPrelude.olean");
    if olean.exists() {
        return Ok(dir);
    }
    std::fs::create_dir_all(&dir)
        .map_err(|e| format!("could not create {}: {}", dir.display(), e))?;
    let src = dir.join("TactusPrelude.lean");
    std::fs::write(&src, TACTUS_PRELUDE)
        .map_err(|e| format!("could not write {}: {}", src.display(), e))?;
    let tmp_name = format!("TactusPrelude.olean.tmp-{}", std::process::id());
    let tmp = dir.join(&tmp_name);
    // Run from inside the cache dir with RELATIVE paths: lean derives
    // the module name from the source path relative to its root dir
    // (the cwd) and refuses files outside it ("must be contained in
    // root directory"). cwd = dir makes the module name exactly
    // `TactusPrelude`, which is what the generated `import` expects.
    let output = std::process::Command::new("lean")
        .arg("-o").arg(&tmp_name)
        .arg("TactusPrelude.lean")
        .current_dir(&dir)
        .output()
        .map_err(|e| format!("failed to spawn lean for prelude build: {}. Is Lean 4 installed?", e))?;
    if !output.status.success() {
        let _ = std::fs::remove_file(&tmp);
        return Err(format!(
            "prelude .olean build failed (this is a Tactus bug — the prelude should always elaborate):\n{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        ));
    }
    std::fs::rename(&tmp, &olean)
        .map_err(|e| format!("could not move prelude olean into place: {}", e))?;
    Ok(dir)
}
