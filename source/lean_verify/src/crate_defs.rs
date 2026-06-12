//! Per-crate shared definitions module (CRATEDEFS.md step 1a).
//!
//! With `--tactus-crate-defs`, the crate's spec world — datatypes, spec
//! fns, classes, instances — is emitted ONCE into
//! `{lean_out_root}/{crate}/TactusDefs_{crate}.lean`, built to `.olean`,
//! and imported by every per-fn file instead of being re-rendered and
//! re-elaborated per check. Helper proof-fn theorems stay per-file (a
//! defs copy would collide with the helper's own check file — see
//! CRATEDEFS.md step 1 revision), as do broadcast-lemma axioms (they
//! resolve from the per-fn SST; fns using `broadcast use` fall back to
//! standalone emission entirely).
//!
//! Flag-gated because tiny crates LOSE: the defs build (~1.3s+)
//! outweighs its savings when the spec world is a few lines — i.e.,
//! most e2e test crates. Real multi-fn crates opt in.
//!
//! One process verifies one crate; the defs render/build is memoized
//! per crate name. `check_*` calls [`for_crate`] with `build: true`
//! before emitting (so a build failure can fall back to standalone
//! BEFORE the fn file is written); `emit_*`'s internal lookup then hits
//! the same memo, keeping the two halves consistent in both normal and
//! `--emit-lean` modes (the latter never builds — codegen only).

use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

use vir::ast::{Fun, FunctionKind, FunctionX, KrateX};

use crate::lean_ast::Command;
use crate::to_lean_type::sanitize;

pub struct CrateDefs {
    /// Lean module name: `TactusDefs_{sanitized crate name}`.
    pub module_name: String,
    /// The crate's lean-out dir — holds the defs `.lean`/`.olean` and
    /// goes on the per-fn check's `LEAN_PATH` as the import root.
    pub dir: PathBuf,
    /// The defs declaration stream. Per-fn sanity checks prepend this
    /// so identifier resolution sees exactly what Lean will see after
    /// the import.
    pub cmds: Vec<Command>,
}

static ENABLED: AtomicBool = AtomicBool::new(false);

/// Set by the verifier from `--tactus-crate-defs`, once, before any
/// check. Mirrors the install_* pattern for config that lean_verify's
/// public entry points consult internally (keeps `emit_*`/`check_*`
/// signatures and the verifier call sites unchanged).
pub fn set_enabled(on: bool) {
    ENABLED.store(on, Ordering::SeqCst);
}

/// `None` = standalone emission (flag off, gate not met, or defs build
/// failed — every caller treats `None` as "emit the full preamble per
/// file", today's behavior).
type Memo = Mutex<std::collections::HashMap<String, Option<Arc<CrateDefs>>>>;
static MEMO: OnceLock<Memo> = OnceLock::new();

pub fn for_crate(
    krate: &KrateX,
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
    build: bool,
) -> Option<Arc<CrateDefs>> {
    if !ENABLED.load(Ordering::SeqCst) {
        return None;
    }
    let memo = MEMO.get_or_init(|| Mutex::new(std::collections::HashMap::new()));
    // Held across the render+build so concurrent first-checks dedupe;
    // later calls are a map hit.
    let mut map = memo.lock().unwrap();
    if let Some(cached) = map.get(crate_name) {
        return cached.clone();
    }
    let result = build_defs(krate, crate_name, tactic_bodies, build);
    map.insert(crate_name.to_string(), result.clone());
    result
}

fn build_defs(
    krate: &KrateX,
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
    build: bool,
) -> Option<Arc<CrateDefs>> {
    // Gate: sharing pays only when ≥2 checked fns split the defs cost.
    // Proof fns with tactic bodies are each checked; exec-fn count is
    // an over-approximation (mode + body present) — over-counting just
    // risks one unprofitable defs build, never incorrectness.
    let exec_roots: Vec<&FunctionX> = krate.functions.iter()
        .map(|f| &f.x)
        .filter(|f| matches!(f.mode, vir::ast::Mode::Exec) && f.body.is_some())
        .collect();
    if tactic_bodies.len() + exec_roots.len() < 2 {
        return None;
    }

    // Same krate transform + ambient tables the per-fn emit paths
    // apply — the defs render must agree with the fn files that import
    // it. Deterministic, so the content-compare below is stable.
    let inlined_krate = crate::inline_spec::inline_marked_in_krate(krate);
    crate::generate::install_emit_tables(&inlined_krate);
    let ectx = crate::emit_ctx::EmitCtx::build(&inlined_krate, tactic_bodies);

    // Dep-walk roots: every fn any per-fn file could need spec-world
    // items for — all tactic proof fns (roots and helpers alike) and
    // all exec roots.
    let proof_roots: Vec<&FunctionX> = inlined_krate.functions.iter()
        .map(|f| &f.x)
        .filter(|f| {
            matches!(f.mode, vir::ast::Mode::Proof)
                && !matches!(
                    f.kind,
                    FunctionKind::TraitMethodDecl { .. } | FunctionKind::TraitMethodImpl { .. }
                )
                && tactic_bodies.contains_key(&f.name)
        })
        .collect();
    let exec_roots: Vec<&FunctionX> = inlined_krate.functions.iter()
        .map(|f| &f.x)
        .filter(|f| matches!(f.mode, vir::ast::Mode::Exec) && f.body.is_some())
        .collect();
    // Accessors are exec-only machinery (match lowering to
    // IsVariant/Field) and can legitimately fail elaboration for enums
    // whose field types lack Inhabited — which is why proof-fn files
    // skip them. Emit them only when an exec root could need them; a
    // failure falls back to standalone for the whole crate.
    let emit_accessors = !exec_roots.is_empty();
    let roots: Vec<&FunctionX> = proof_roots.into_iter().chain(exec_roots).collect();

    let ns = sanitize(crate_name);
    let module_name = format!("TactusDefs_{}", ns);
    let dir = crate::generate::lean_out_root().join(&ns);
    let mut cmds: Vec<Command> = Vec::new();
    // Union of every fn's tactic imports: helper bodies elaborate
    // per-file, but spec-world rendering may reference types those
    // imports provide (e.g. `Real`); a superset here is safe and
    // built once.
    let mut seen = std::collections::HashSet::new();
    for f in inlined_krate.functions.iter() {
        for imp in f.x.attrs.lean_imports.iter() {
            if seen.insert(imp.as_str()) {
                cmds.push(Command::Import(imp.clone()));
            }
        }
    }
    cmds.push(Command::Raw(crate::prelude::TACTUS_PRELUDE_IMPORT.to_string()));
    cmds.push(Command::NamespaceOpen(ns.clone()));
    cmds.push(Command::Raw("set_option autoImplicit false".to_string()));
    cmds.extend(crate::generate::spec_world_cmds(
        &inlined_krate, &ectx, &roots, emit_accessors, &[],
    ));
    cmds.push(Command::NamespaceClose(ns));

    let rendered = crate::lean_pp::pp_commands(&cmds);
    let lean_path = dir.join(format!("{}.lean", module_name));
    let olean_path = dir.join(format!("{}.olean", module_name));

    if !build {
        // `--emit-lean` codegen-only mode: write the source for
        // inspection/serving; the consumer builds the olean.
        if let Err(e) = std::fs::create_dir_all(&dir)
            .map_err(|e| e.to_string())
            .and_then(|_| std::fs::write(&lean_path, &rendered.text).map_err(|e| e.to_string()))
        {
            eprintln!("tactus: could not write {}: {} — falling back to standalone emission", lean_path.display(), e);
            return None;
        }
        return Some(Arc::new(CrateDefs { module_name, dir, cmds }));
    }

    // Build, unless the on-disk source already matches (then the olean
    // beside it was built from exactly this content — the source is
    // written AFTER a successful build, prelude-cache style, so a
    // crash can't leave a fresh source over a stale olean).
    let up_to_date = olean_path.exists()
        && std::fs::read_to_string(&lean_path).ok().as_deref() == Some(&rendered.text);
    if !up_to_date {
        if let Err(e) = build_olean(&dir, &module_name, &rendered.text, &olean_path, &lean_path) {
            eprintln!(
                "tactus: defs module build failed for crate `{}` — falling back to standalone emission.\n{}",
                crate_name, e
            );
            return None;
        }
    }
    Some(Arc::new(CrateDefs { module_name, dir, cmds }))
}

fn build_olean(
    dir: &std::path::Path,
    module_name: &str,
    source: &str,
    olean_path: &std::path::Path,
    lean_path: &std::path::Path,
) -> Result<(), String> {
    let prelude_dir = crate::prelude::ensure_prelude_olean()?;
    // cwd = a build subdir so `lean -o` derives the module name from
    // the bare file name (it refuses sources outside its root dir).
    let build = dir.join(format!("build-{}", std::process::id()));
    std::fs::create_dir_all(&build).map_err(|e| e.to_string())?;
    let src_name = format!("{}.lean", module_name);
    let out_name = format!("{}.olean", module_name);
    std::fs::write(build.join(&src_name), source).map_err(|e| e.to_string())?;
    let existing = std::env::var("LEAN_PATH").unwrap_or_default();
    let lean_path_env = if existing.is_empty() {
        prelude_dir.to_string_lossy().into_owned()
    } else {
        format!("{}:{}", prelude_dir.to_string_lossy(), existing)
    };
    let output = std::process::Command::new("lean")
        .args(["-o", &out_name, &src_name])
        .current_dir(&build)
        .env("LEAN_PATH", lean_path_env)
        .output()
        .map_err(|e| format!("failed to spawn lean: {}", e))?;
    if !output.status.success() {
        let _ = std::fs::remove_dir_all(&build);
        return Err(format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    std::fs::rename(build.join(&out_name), olean_path).map_err(|e| e.to_string())?;
    std::fs::write(lean_path, source).map_err(|e| e.to_string())?;
    let _ = std::fs::remove_dir_all(&build);
    Ok(())
}
