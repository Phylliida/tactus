//! The Tactus prelude for Lean — source constants + prebuilt-module cache.
//!
//! **B5 split (DESIGN-transparent-automation.md §5):** the former single
//! `TactusPrelude.lean` is now TWO modules:
//!
//! * **`TactusDefs.lean`** — the vocabulary: defs, instances, decoration
//!   types, the arch-word axiom pair, and the `#tactus_check_axioms`
//!   axiom-closure enforcement command. NO tactics. This is the file in
//!   the trust/audit story; every generated artifact imports it.
//! * **`TactusSearch.lean`** — `import TactusDefs` + the discover-mode
//!   search ladder (`tactus_first` / `tactus_auto` / `tactus_case_split`
//!   / `tactus_usize_bound` / `tactus_bit_vector`). Imported ONLY by
//!   artifacts whose USER tactic texts reference those tactics (fn-level
//!   overrides, inline proofs) — never by default emission (S2c/B4
//!   removed the default search path). See `needs_search_import`.
//!
//! Historically the prelude was inlined verbatim into every generated
//! `.lean` file (`Command::Raw(TACTUS_PRELUDE)`), costing ~1.3s of
//! re-elaboration per check (measured 2026-06-12, CRATEDEFS.md step 0).
//! Generated files now emit `import TactusDefs` instead, against
//! `.olean`s built once per prelude version into a content-hashed cache
//! dir (see `prelude_cache_dir`); `check_lean_file` puts that dir on
//! the child's `LEAN_PATH`.
//!
//! Consequence: generated files are no longer standalone — checking one
//! by hand needs the cache dir on `LEAN_PATH` (see BUILD.md).

use std::path::PathBuf;

/// The TactusDefs source. As the vocabulary grows (Seq, Set, etc.),
/// edit TactusDefs.lean directly — it's a real .lean file that can be
/// syntax-highlighted and tested independently. One half of the source
/// of truth for `sanity.rs`'s prelude-name extraction.
pub const TACTUS_DEFS: &str = include_str!("../TactusDefs.lean");

/// The TactusSearch source (the search ladder). The other half of
/// `sanity.rs`'s extraction input.
pub const TACTUS_SEARCH: &str = include_str!("../TactusSearch.lean");

/// Header emitted in generated files in place of the inline prelude:
/// the import plus the prelude's file-scoped `set_option`s, which do
/// NOT propagate through `import` and must be restated per file.
pub const TACTUS_DEFS_IMPORT: &str = "import TactusDefs\n\
set_option linter.unusedVariables false\n\
set_option maxHeartbeats 800000";

/// Just the file-scoped `set_option`s, for files whose prelude arrives
/// transitively through a defs-module import (CRATEDEFS.md step 1a) —
/// options never propagate through `import` and must be restated.
pub const TACTUS_SET_OPTIONS: &str = "set_option linter.unusedVariables false\n\
set_option maxHeartbeats 800000";

/// Search-ladder tactic names, whole-word matched. If any of these
/// appears in a generated file's tactic text, the file needs
/// `import TactusSearch` — see `inject_search_import` in generate.rs.
pub const SEARCH_TACTIC_NAMES: [&str; 5] = [
    "tactus_auto",
    "tactus_first",
    "tactus_case_split",
    "tactus_bit_vector",
    "tactus_usize_bound",
];

/// Does this rendered file reference a search-ladder tactic in tactic
/// position? Scans with line comments stripped (user `--` comments may
/// mention the names; those don't need the import).
pub fn needs_search_import(source: &str) -> bool {
    let stripped = crate::generate::strip_lean_line_comments(source);
    SEARCH_TACTIC_NAMES.iter().any(|name| {
        stripped
            .split(|c: char| !(c.is_alphanumeric() || c == '_'))
            .any(|tok| tok == *name)
    })
}

/// Fixed cache dir for the prebuilt prelude modules:
/// `{cache_root}/prelude-<hash>`, where the cache root is USER-LEVEL
/// (`$TACTUS_PRELUDE_CACHE` → `$XDG_CACHE_HOME/tactus` →
/// `~/.cache/tactus` → `{lean_out_root()}/_prelude_cache` as a last
/// resort), NOT `lean_out_root()`: the e2e harness isolates each
/// test's lean-out dir, and a per-test cache would rebuild the
/// identical oleans 505 times per suite run.
///
/// ONE dir per prelude VERSION, content-addressed over BOTH module
/// sources: when either file changes, the next check rebuilds into a
/// fresh hash dir and artifacts generated against the old version
/// simply fail — regenerate them by re-running tactus. Two tactus
/// binaries with different preludes (e.g. two checkouts on one
/// machine) coexist instead of rebuilding the same dir back and
/// forth (the "concurrent mixed-version builders" race was observed
/// for real). Old version dirs linger (~8MB each); `rm -rf` the
/// cache root recovers.
/// The user-level tactus cache root (shared by the prelude olean cache
/// and the driver script install — see `prelude_cache_dir` for the
/// resolution rationale).
pub fn cache_root() -> PathBuf {
    if let Ok(d) = std::env::var("TACTUS_PRELUDE_CACHE") {
        PathBuf::from(d)
    } else if let Ok(d) = std::env::var("XDG_CACHE_HOME") {
        PathBuf::from(d).join("tactus")
    } else if let Ok(h) = std::env::var("HOME") {
        PathBuf::from(h).join(".cache").join("tactus")
    } else {
        crate::generate::lean_out_root().join("_prelude_cache")
    }
}

pub fn prelude_cache_dir() -> PathBuf {
    let root = cache_root();
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    TACTUS_DEFS.hash(&mut h);
    TACTUS_SEARCH.hash(&mut h);
    root.join(format!("prelude-{:016x}", h.finish()))
}

/// Build one module of the prelude into `build_dir` (pid-unique), with
/// `lean_path` prepended for imports (TactusSearch imports TactusDefs,
/// so the search build sees the defs build dir). `lean -o` derives the
/// module name from the source path relative to its root dir (the cwd)
/// and refuses sources outside it — cwd = the subdir makes the module
/// exactly `<name>`.
fn build_module(
    dir: &std::path::Path,
    name: &str,
    source: &str,
    lean_path: &std::path::Path,
) -> Result<(), String> {
    let build = dir.join(format!("build-{}-{}", std::process::id(), name));
    std::fs::create_dir_all(&build)
        .map_err(|e| format!("could not create {}: {}", build.display(), e))?;
    let src_path = build.join(format!("{}.lean", name));
    std::fs::write(&src_path, source)
        .map_err(|e| format!("could not write {} source: {}", name, e))?;
    let mut cmd = std::process::Command::new("lean");
    cmd.args(["-o", &format!("{}.olean", name), &format!("{}.lean", name)])
        .current_dir(&build)
        .env("LEAN_PATH", lean_path);
    let output = cmd
        .output()
        .map_err(|e| format!("failed to spawn lean for prelude build: {}. Is Lean 4 installed?", e))?;
    if !output.status.success() {
        let _ = std::fs::remove_dir_all(&build);
        return Err(format!(
            "prelude .olean build failed for {} (this is a Tactus bug — the prelude should always elaborate):\n{}{}",
            name,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        ));
    }
    std::fs::rename(build.join(format!("{}.olean", name)), dir.join(format!("{}.olean", name)))
        .map_err(|e| format!("could not move {} olean into place: {}", name, e))?;
    let _ = std::fs::remove_dir_all(&build);
    Ok(())
}

pub fn ensure_prelude_olean() -> Result<PathBuf, String> {
    let dir = prelude_cache_dir();
    let defs_lean = dir.join("TactusDefs.lean");
    let search_lean = dir.join("TactusSearch.lean");
    let defs_olean = dir.join("TactusDefs.olean");
    let search_olean = dir.join("TactusSearch.olean");
    // The marker records which prelude version the oleans were built
    // from. It is written AFTER the olean renames, so on any crash the
    // mismatch forces a rebuild (never a stale olean behind a fresh
    // marker). Marker = both module sources + toolchain fingerprint:
    // a toolchain bump with unchanged sources previously reused a stale
    // olean (latent gap — nothing later necessarily elaborates against
    // it to notice).
    let marker = dir.join("PRELUDE-MARKER");
    let marker_content = format!(
        "{}\n-- ══ TactusSearch ══\n{}\n-- toolchain: {}\n",
        TACTUS_DEFS, TACTUS_SEARCH, crate::project::toolchain_fingerprint()
    );
    let fresh = defs_olean.exists()
        && search_olean.exists()
        && std::fs::read_to_string(&marker).ok().as_deref() == Some(&marker_content);
    if fresh {
        return Ok(dir);
    }
    // Serialize rebuilds process-wide. The gate's verifier threads share
    // one process — and therefore one pid-unique `build-<pid>-<name>`
    // dir. Without the lock, every thread that sees not-fresh (e.g.
    // right after a prelude-text bump, when the new prelude-<hash> dir
    // doesn't exist yet) enters `build_module` CONCURRENTLY in the same
    // build dir, and the first finisher's `remove_dir_all(build)`
    // deletes the cwd of the others' still-running `lean` — "failed to
    // create file 'TactusDefs.olean'" (latent since the pid-unique build
    // dir; first bitten 2026-08-06 on b82's prelude bump, 230 fns red).
    // Cross-process builders need no lock: distinct pids get distinct
    // build dirs and write identical content.
    static REBUILD_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let _guard = REBUILD_LOCK
        .lock()
        .map_err(|e| format!("prelude rebuild lock poisoned: {}", e))?;
    // Re-check under the lock: a thread that got here first may have
    // completed the rebuild while we waited.
    if defs_olean.exists()
        && search_olean.exists()
        && std::fs::read_to_string(&marker).ok().as_deref() == Some(&marker_content)
    {
        return Ok(dir);
    }
    std::fs::create_dir_all(&dir)
        .map_err(|e| format!("could not create {}: {}", dir.display(), e))?;
    std::fs::write(&defs_lean, TACTUS_DEFS)
        .map_err(|e| format!("could not write TactusDefs source: {}", e))?;
    std::fs::write(&search_lean, TACTUS_SEARCH)
        .map_err(|e| format!("could not write TactusSearch source: {}", e))?;
    // Dependency order: TactusDefs stands alone; TactusSearch imports
    // it, so the search build's LEAN_PATH includes the defs dir.
    build_module(&dir, "TactusDefs", TACTUS_DEFS, &dir)?;
    build_module(&dir, "TactusSearch", TACTUS_SEARCH, &dir)?;
    std::fs::write(&marker, &marker_content)
        .map_err(|e| format!("could not write prelude marker: {}", e))?;
    Ok(dir)
}
