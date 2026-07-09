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

use crate::generate::{CheckResult, EmitOutput, TactusDiag};
use crate::lean_ast::Command;
use crate::to_lean_fn::LeanSourceMap;
use crate::to_lean_type::sanitize;

pub struct CrateDefs {
    /// Lean module name: `TactusDefs_{sanitized crate name}`.
    pub module_name: String,
    /// Whether exec-fn dep closures are included. `false` after the
    /// proof-roots-only retry (see `build_defs`): exec fns then emit
    /// standalone, while the proofs batch — whose spec needs are a
    /// subset of the proof closure by construction — keeps the module.
    pub covers_exec: bool,
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


/// Memo scope for the shared artifacts. Verus verifies in per-module
/// BUCKETS; each bucket thread's Verifier clone can hand us a
/// bucket-locally PRUNED krate and tactic-bodies map (measured on
/// tactus-group-theory: `krate fns 1155, tactic_bodies 1` for the
/// machine_group bucket). A memo keyed by crate name alone would cache
/// the first bucket's view for every other bucket. Keying by content
/// fingerprint is self-adapting: identical inputs (one full krate) →
/// one shared defs/batch; per-bucket inputs → per-bucket artifacts,
/// each self-consistent. The hash also suffixes the Lean module/file
/// names so bucket artifacts coexist in the crate dir.
fn scope_key(
    crate_name: &str,
    krate: &KrateX,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> String {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    for f in krate.functions.iter() {
        f.x.name.path.hash(&mut h);
    }
    // HashMap iteration order is nondeterministic — sort first.
    let mut keys: Vec<String> = tactic_bodies.keys().map(|k| format!("{:?}", k.path)).collect();
    keys.sort();
    keys.hash(&mut h);
    format!("{}_{:08x}", sanitize(crate_name), h.finish() as u32)
}

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
    // Held across the render+build so concurrent bucket threads dedupe;
    // later calls are a map hit. Poison-tolerant: if a previous holder
    // panicked, the map is still structurally valid (worst case: a
    // missing entry that gets rebuilt) — don't cascade the panic to
    // every other bucket.
    let scope = scope_key(crate_name, krate, tactic_bodies);
    let mut map = memo.lock().unwrap_or_else(|p| p.into_inner());
    if let Some(cached) = map.get(&scope) {
        return cached.clone();
    }
    let result = guard_build("defs module", crate_name, || {
        build_defs(krate, crate_name, &scope, tactic_bodies, build)
    });
    map.insert(scope, result.clone());
    result
}

/// Panic firewall for the shared builds: the defs/batch renders walk
/// MORE of the krate than any per-fn render ever did (roots = all
/// checkable fns), so they can reach tripwire panics in emission code
/// that per-fn files never trip. A panic here must degrade to
/// standalone emission for the crate — today's behavior — not abort
/// the whole verification run (and certainly not poison the memo for
/// every other bucket thread).
fn guard_build<T>(
    what: &str,
    crate_name: &str,
    f: impl FnOnce() -> Option<T>,
) -> Option<T> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(r) => r,
        Err(payload) => {
            let msg = payload.downcast_ref::<&str>().map(|s| s.to_string())
                .or_else(|| payload.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "<non-string panic payload>".to_string());
            eprintln!(
                "tactus: {} build panicked for crate `{}` — falling back to standalone emission.\n  {}",
                what, crate_name, msg
            );
            None
        }
    }
}

fn build_defs(
    krate: &KrateX,
    crate_name: &str,
    scope: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
    build: bool,
) -> Option<Arc<CrateDefs>> {
    if std::env::var_os("TACTUS_VERBOSE").is_some() {
        let execs = krate.functions.iter()
            .filter(|f| matches!(f.x.mode, vir::ast::Mode::Exec) && f.x.body.is_some())
            .count();
        eprintln!(
            "tactus: build_defs scope `{}`: tactic_bodies {}, exec(with body) {}, krate fns {}",
            scope, tactic_bodies.len(), execs, krate.functions.len());
    }
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
    crate::generate::install_emit_tables(&inlined_krate, crate_name);
    let ectx = crate::emit_ctx::EmitCtx::build(&inlined_krate, tactic_bodies);

    // Dep-walk roots = every fn whose per-fn FILE will import the
    // defs module — broader than the batch's theorem list: trait-
    // method-impl proof fns aren't batched (they emit per-fn), but
    // those files import defs too, so their closures must be present.
    // LEAN-PATH fns only: tactic-bodied proof fns (the map's keys) and
    // exec fns. The Lean backend is OPT-IN per fn — unmarked Verus
    // proof fns verify via Z3 and never import the defs module, so
    // including them (one session tried `|| f.body.is_some()`) builds
    // a defs for a thousand fns that will never read it, and drags in
    // closures (runtime views, DeepView) that fail elaboration and
    // waste two olean attempts per cold run. As the port migrates fns
    // to tactic bodies / tactus_auto they join these roots naturally.
    let proof_roots: Vec<&FunctionX> = inlined_krate.functions.iter()
        .map(|f| &f.x)
        .filter(|f| {
            matches!(f.mode, vir::ast::Mode::Proof)
                && tactic_bodies.contains_key(&f.name)
        })
        .collect();
    let exec_roots: Vec<&FunctionX> = inlined_krate.functions.iter()
        .map(|f| &f.x)
        .filter(|f| matches!(f.mode, vir::ast::Mode::Exec) && f.body.is_some())
        .collect();

    // Attempt 1: full roots (proof + exec; accessors iff exec present).
    // Attempt 2 (build mode only, on Lean failure): proof roots only —
    // exec fns' dep closures can contain broken-in-baseline corners
    // (e.g. the closure-ABI frontier: bare-arrow Fn instances,
    // builtinSpecFun) that no lenient RENDER skip can catch because
    // they fail in LEAN, not in codegen. The proof closure is exactly
    // what the passing per-fn proof files already elaborate, so it is
    // clean by construction; exec fns fall back to standalone, where a
    // broken closure breaks only its own file — today's behavior.
    let full_roots: Vec<&FunctionX> =
        proof_roots.iter().copied().chain(exec_roots.iter().copied()).collect();
    // Attempt ladder, narrowing on each Lean failure:
    //   1. full roots + broadcast union  — execs + everything
    //   2. proof roots + broadcast union — drops broken exec closures
    //   3. proof roots, NO union         — drops broken broadcast axioms
    // The union is KRATE-WIDE (any per-fn collected set is a subset),
    // so a single un-elaboratable axiom in it (e.g. vstd's array-view
    // axioms → `array_view` → the `Tactus.index` closure fragment)
    // sinks attempts 1 AND 2 regardless of roots. Attempt 3 then
    // yields the minimal clean defs — exactly the pre-(c) proof-roots
    // module — so tactic lemmas that need NO broadcast axiom (the
    // common case for migrated arithmetic/structural lemmas) still
    // ride it. A lemma needing a CLEAN axiom that an UNRELATED broken
    // axiom dragged down is the case for the iterative-repair build
    // (drop only the erroring item by line attribution; CRATEDEFS
    // follow-ups) — not yet needed at current Lean-path populations.
    let attempts: [(&[&FunctionX], bool, bool, bool); 3] = [
        (&full_roots, !exec_roots.is_empty(), true, true),
        (&proof_roots, false, false, true),
        (&proof_roots, false, false, false),
    ];
    let mut prev: Option<(usize, bool, bool)> = None;
    for (attempt, &(roots, emit_accessors, covers_exec, with_bc_union)) in attempts.iter().enumerate() {
        // Emit-lean mode never runs Lean, so there's nothing to learn
        // from later attempts — just emit attempt 1 and return.
        if attempt > 0 && !build {
            break;
        }
        // Skip an attempt identical to the previous one (no exec roots
        // ⇒ full == proof; the union flag is the only remaining axis).
        if let Some((plen, pcov, punion)) = prev {
            if roots.len() == plen && covers_exec == pcov && with_bc_union == punion {
                continue;
            }
        }
        prev = Some((roots.len(), covers_exec, with_bc_union));
        match render_and_build(
            &inlined_krate, &ectx, crate_name, scope, roots,
            emit_accessors, covers_exec, with_bc_union, build,
        ) {
            Ok(defs) => return Some(Arc::new(defs)),
            Err(e) => {
                let stage = match (covers_exec, with_bc_union) {
                    (true, _) => "full roots",
                    (false, true) => "proof roots + broadcast union",
                    (false, false) => "proof roots, no union",
                };
                let next = if attempt + 1 < attempts.len() && build {
                    "retrying narrower"
                } else {
                    "falling back to standalone emission"
                };
                eprintln!(
                    "tactus: defs module build failed for crate `{}` ({}) — {}\n{}",
                    crate_name, stage, next, e,
                );
            }
        }
    }
    None
}

#[allow(clippy::too_many_arguments)]
fn render_and_build(
    inlined_krate: &KrateX,
    ectx: &crate::emit_ctx::EmitCtx,
    crate_name: &str,
    scope: &str,
    roots: &[&FunctionX],
    emit_accessors: bool,
    covers_exec: bool,
    with_bc_union: bool,
    build: bool,
) -> Result<CrateDefs, String> {
    let ns = sanitize(crate_name);
    // Scope-suffixed: per-bucket artifacts coexist (see scope_key).
    let module_name = format!("TactusDefs_{}", scope);
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
    // Union of emittable broadcast axioms (CRATEDEFS 1c fix c): per-fn
    // files collect a SUBSET of these (default-on-import groups +
    // fn-specific reveals); with the axioms in the defs module, the
    // import replaces local re-emission and the broadcast gate on the
    // exec/WP path can lift. They also join the dep walk — their
    // ensures reference spec fns (Seq.len etc.) that must be emitted.
    let bc_union: Vec<&FunctionX> = if with_bc_union {
        crate::broadcast_collect::all_emittable_broadcast_lemmas(inlined_krate)
    } else {
        Vec::new()
    };
    let walk_roots: Vec<&FunctionX> = roots.iter().copied()
        .chain(bc_union.iter().copied())
        .collect();
    cmds.extend(crate::generate::spec_world_cmds(
        inlined_krate, ectx, &walk_roots, emit_accessors, &bc_union, true,
    ));
    cmds.push(Command::NamespaceClose(ns));

    let rendered = crate::lean_pp::pp_commands(&cmds);
    let lean_path = dir.join(format!("{}.lean", module_name));
    let olean_path = dir.join(format!("{}.olean", module_name));

    if !build {
        std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
        std::fs::write(&lean_path, &rendered.text).map_err(|e| e.to_string())?;
        return Ok(CrateDefs { module_name, covers_exec, dir, cmds });
    }

    let up_to_date = olean_path.exists()
        && std::fs::read_to_string(&lean_path).ok().as_deref() == Some(&rendered.text);
    if !up_to_date {
        std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
        build_olean(&dir, &module_name, &rendered.text, &olean_path, &lean_path)?;
    }
    Ok(CrateDefs { module_name, covers_exec, dir, cmds })
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
        // The successful-build path writes the source only AFTER the
        // olean rename (marker ordering) — so on failure, dump it
        // under a non-marker name or the diagnostics reference a file
        // that doesn't exist.
        let failed = lean_path.with_extension("lean.failed");
        let _ = std::fs::write(&failed, source);
        return Err(format!(
            "(failing source dumped to {})\n{}{}",
            failed.display(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    std::fs::rename(build.join(&out_name), olean_path).map_err(|e| e.to_string())?;
    std::fs::write(lean_path, source).map_err(|e| e.to_string())?;
    let _ = std::fs::remove_dir_all(&build);
    Ok(())
}

// ── Proof batch (CRATEDEFS.md step 1b) ─────────────────────────────────
//
// All ordinary proof fns (Mode::Proof, non-trait-method, with a tactic
// body) emit as theorems into ONE `TactusProofs_{crate}.lean` that
// imports the defs module — topologically ordered, so a root
// referencing a helper references an earlier theorem in the same file
// and every helper elaborates exactly once. The file is checked with a
// single `lean --json` run; per-fn results are attributed by theorem
// line region (regions computed exactly, by rendering the header and
// each theorem chunk separately and accumulating line counts).
//
// Failure semantics (intentional, documented in CRATEDEFS.md): an
// error inside theorem T's region fails T only — a root whose helper
// fails reports green while the helper reports red (the root
// elaborated against the helper's STATEMENT; the crate still fails
// overall). An error outside every region (header breakage, no
// position) poisons the batch → per-fn standalone fallback.

struct Region {
    fun: Fun,
    fn_short: String,
    start: usize,
    end: usize, // exclusive
    tactic_start_line: usize,
    tactic_line_count: usize,
}

pub struct ProofBatch {
    pub file_path: PathBuf,
    regions: Vec<Region>,
    /// Per-fn formatted failures from the one Lean run; fns absent
    /// from this map passed. Always empty in `build: false` mode.
    failed: std::collections::HashMap<Fun, Vec<TactusDiag>>,
}

impl ProofBatch {
    fn region(&self, f: &Fun) -> Option<&Region> {
        self.regions.iter().find(|r| &r.fun == f)
    }

    pub fn covers(&self, f: &Fun) -> bool {
        self.region(f).is_some()
    }

    /// The per-fn check result, read off the cached batch run.
    pub fn result_for(&self, f: &Fun) -> CheckResult {
        match self.failed.get(f) {
            Some(errors) => CheckResult::Failed { errors: errors.clone(), warnings: vec![] },
            None => CheckResult::Success { warnings: vec![] },
        }
    }

    /// The `--emit-lean` sidecar view: the batch file plus this fn's
    /// tactic position within it.
    pub fn emit_output(&self, f: &Fun) -> Option<EmitOutput> {
        let r = self.region(f)?;
        Some(EmitOutput {
            file_path: self.file_path.clone(),
            source_map: LeanSourceMap::ProofFn {
                fn_name: r.fn_short.clone(),
                tactic_start_line: r.tactic_start_line,
                tactic_line_count: r.tactic_line_count,
            },
            warnings: vec![],
        })
    }
}

type BatchMemo = Mutex<std::collections::HashMap<String, Option<Arc<ProofBatch>>>>;
static BATCH_MEMO: OnceLock<BatchMemo> = OnceLock::new();

pub fn proof_batch(
    krate: &KrateX,
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
    build: bool,
) -> Option<Arc<ProofBatch>> {
    if !ENABLED.load(Ordering::SeqCst) {
        return None;
    }
    let memo = BATCH_MEMO.get_or_init(|| Mutex::new(std::collections::HashMap::new()));
    let scope = scope_key(crate_name, krate, tactic_bodies);
    let mut map = memo.lock().unwrap_or_else(|p| p.into_inner());
    if let Some(cached) = map.get(&scope) {
        return cached.clone();
    }
    let result = guard_build("proofs batch", crate_name, || {
        build_batch(krate, crate_name, &scope, tactic_bodies, build)
    });
    map.insert(scope, result.clone());
    result
}

/// DFS post-order over textual tactic references, ALL nodes emitted
/// (unlike `collect_referenced_proof_fns`, which excludes roots — here
/// every fn is both a root and a candidate).
fn ordered_batch_fns<'a>(
    fns: &[(&'a FunctionX, &'a str)],
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> Vec<&'a FunctionX> {
    fn visit<'a>(
        f: &'a FunctionX,
        fns: &[(&'a FunctionX, &'a str)],
        tactic_bodies: &std::collections::HashMap<Fun, String>,
        visited: &mut std::collections::HashSet<&'a Fun>,
        ordered: &mut Vec<&'a FunctionX>,
    ) {
        if !visited.insert(&f.name) {
            return;
        }
        if let Some(body) = tactic_bodies.get(&f.name) {
            let code = crate::generate::strip_lean_line_comments(body);
            for (cand, name) in fns {
                if cand.name != f.name && crate::generate::ident_appears(&code, name) {
                    visit(cand, fns, tactic_bodies, visited, ordered);
                }
            }
        }
        ordered.push(f);
    }
    let mut visited = std::collections::HashSet::new();
    let mut ordered = Vec::new();
    for (f, _) in fns {
        visit(f, fns, tactic_bodies, &mut visited, &mut ordered);
    }
    ordered
}

fn build_batch(
    krate: &KrateX,
    crate_name: &str,
    scope: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
    build: bool,
) -> Option<Arc<ProofBatch>> {
    // The batch rides the defs module (its theorems resolve the spec
    // world through the import) — defs gate/fallback decisions apply.
    let defs = for_crate(krate, crate_name, tactic_bodies, build)?;

    let inlined_krate = crate::inline_spec::inline_marked_in_krate(krate);
    crate::generate::install_emit_tables(&inlined_krate, crate_name);
    let ectx = crate::emit_ctx::EmitCtx::build(&inlined_krate, tactic_bodies);

    let batched: Vec<(&FunctionX, &str)> = inlined_krate.functions.iter()
        .map(|f| &f.x)
        .filter(|f| {
            matches!(f.mode, vir::ast::Mode::Proof)
                && !matches!(
                    f.kind,
                    FunctionKind::TraitMethodDecl { .. } | FunctionKind::TraitMethodImpl { .. }
                )
                && tactic_bodies.contains_key(&f.name)
        })
        .map(|f| (f, crate::to_lean_type::short_name(&f.name.path)))
        .collect();
    if batched.is_empty() {
        return None;
    }
    let ordered = ordered_batch_fns(&batched, tactic_bodies);
    // Gated: the e2e harness treats unexpected stderr lines as
    // failures (it parses the child's stderr as diagnostics), and this
    // is the only ALWAYS-printing line in the module — everything else
    // prints on failure paths only.
    if std::env::var_os("TACTUS_VERBOSE").is_some() {
        eprintln!(
            "tactus: proofs batch for crate `{}`: {} theorems (tactic_bodies {}, krate fns {})",
            crate_name, ordered.len(), tactic_bodies.len(), inlined_krate.functions.len());
    }

    let ns = sanitize(crate_name);
    let mut header_cmds: Vec<Command> = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for (f, _) in &batched {
        for imp in f.attrs.lean_imports.iter() {
            if seen.insert(imp.as_str()) {
                header_cmds.push(Command::Import(imp.clone()));
            }
        }
    }
    header_cmds.push(Command::Import(defs.module_name.clone()));
    header_cmds.push(Command::Raw(crate::prelude::TACTUS_SET_OPTIONS.to_string()));
    header_cmds.push(Command::NamespaceOpen(ns.clone()));
    header_cmds.push(Command::Raw("set_option autoImplicit false".to_string()));

    // Exact line accounting: render the header and each theorem chunk
    // separately (write_command is compositional — `pp_commands` just
    // appends), so every theorem's region INCLUDING its signature is
    // known, and anything outside all regions is header/footer.
    let header = crate::lean_pp::pp_commands(&header_cmds);
    let mut text = header.text;
    let mut all_cmds = header_cmds;
    let mut line = text.bytes().filter(|&b| b == b'\n').count() + 1;
    let mut regions: Vec<Region> = Vec::new();
    for f in &ordered {
        let body = tactic_bodies.get(&f.name).expect("batched fns have tactic bodies");
        let cmd = Command::Theorem(crate::to_lean_fn::proof_fn_to_ast(f, body, &ectx));
        let chunk = crate::lean_pp::pp_commands(std::slice::from_ref(&cmd));
        let chunk_lines = chunk.text.bytes().filter(|&b| b == b'\n').count();
        let rel_tactic_start = chunk.landmarks.tactic_starts.first().copied().unwrap_or(1);
        regions.push(Region {
            fun: f.name.clone(),
            fn_short: crate::to_lean_type::short_name(&f.name.path).to_string(),
            start: line,
            end: line + chunk_lines,
            tactic_start_line: line + rel_tactic_start - 1,
            tactic_line_count: body.lines().count().max(1),
        });
        text.push_str(&chunk.text);
        all_cmds.push(cmd);
        line += chunk_lines;
    }
    let footer_cmd = Command::NamespaceClose(ns.clone());
    text.push_str(&crate::lean_pp::pp_commands(std::slice::from_ref(&footer_cmd)).text);
    all_cmds.push(footer_cmd);

    // Sanity over defs + batch: what Lean sees through the import.
    #[cfg(debug_assertions)]
    {
        let combined: Vec<Command> =
            defs.cmds.iter().cloned().chain(all_cmds.iter().cloned()).collect();
        if let Err(reason) = crate::generate::debug_check(&combined) {
            eprintln!(
                "tactus: proofs batch failed codegen sanity for crate `{}` — falling back to per-fn emission.\n{}",
                crate_name, reason
            );
            return None;
        }
    }

    let file_path = defs.dir.join(format!("TactusProofs_{}.lean", scope));
    if let Err(e) = std::fs::create_dir_all(&defs.dir)
        .map_err(|e| e.to_string())
        .and_then(|_| std::fs::write(&file_path, &text).map_err(|e| e.to_string()))
    {
        eprintln!("tactus: could not write {}: {} — falling back to per-fn emission", file_path.display(), e);
        return None;
    }

    if !build {
        return Some(Arc::new(ProofBatch { file_path, regions, failed: Default::default() }));
    }

    // The one Lean run for every ordinary proof fn in the crate.
    let prelude_dir = match crate::prelude::ensure_prelude_olean() {
        Ok(d) => d,
        Err(e) => {
            eprintln!("tactus: {} — falling back to per-fn emission", e);
            return None;
        }
    };
    let proj = crate::project::default_project_dir();
    let lake_dir = if crate::project::project_ready(&proj) { Some(proj.as_path()) } else { None };
    let extra: Vec<&std::path::Path> = vec![&prelude_dir, &defs.dir];
    let run = match crate::lean_process::check_lean_file(&file_path, lake_dir, &extra) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("tactus: proofs batch run failed for crate `{}` — falling back to per-fn emission.\n{}", crate_name, e);
            return None;
        }
    };

    let mut failed: std::collections::HashMap<Fun, Vec<TactusDiag>> = Default::default();
    for d in run.diagnostics.iter().filter(|d| d.severity == "error") {
        let Some(region) = d.pos.as_ref()
            .and_then(|p| regions.iter().find(|r| r.start <= p.line && p.line < r.end))
        else {
            // Header/footer breakage or position-less error: not
            // attributable to one fn — poison the batch so every fn
            // re-checks standalone (conservative, today's behavior).
            eprintln!(
                "tactus: proofs batch error outside any theorem region for crate `{}` (line {:?}, {} regions spanning {}..{}) — falling back to per-fn emission.\n{}",
                crate_name,
                d.pos.as_ref().map(|p| p.line),
                regions.len(),
                regions.first().map(|r| r.start).unwrap_or(0),
                regions.last().map(|r| r.end).unwrap_or(0),
                d.data
            );
            return None;
        };
        let source_map = LeanSourceMap::ProofFn {
            fn_name: region.fn_short.clone(),
            tactic_start_line: region.tactic_start_line,
            tactic_line_count: region.tactic_line_count,
        };
        let formatted = crate::lean_process::format_error(d, &source_map);
        failed.entry(region.fun.clone()).or_default().push(TactusDiag {
            message: format!("Lean tactic failed for {}:\n\n{}", region.fn_short, formatted.message),
            location: formatted.location,
            help: Some(format!("{} {}",
                vir::tactus_messages::LEAN_FILE_HELP_PREFIX, file_path.display())),
        });
    }
    if !run.success && failed.is_empty() {
        eprintln!(
            "tactus: proofs batch failed with no attributable diagnostics for crate `{}` — falling back to per-fn emission",
            crate_name
        );
        return None;
    }
    Some(Arc::new(ProofBatch { file_path, regions, failed }))
}
