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
//! Always on, whatever the crate size: tiny crates pay a defs build
//! (~1.3s cold) that sharing doesn't strictly repay, but every crate
//! goes through the SAME pipeline — no size heuristic silently
//! switching behavior underfoot. Warm runs hit the content-keyed
//! defs memo and cross-run caches, so the cost is a cold-run-only
//! constant.
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
    /// Lean module name: `TactusDefs_{scope}`.
    pub module_name: String,
    /// The scope string (`{crate}_{fingerprint}`) the module name is
    /// built from — sibling modules (Stmts/Link) derive their names
    /// from this instead of string surgery on `module_name` (M5d-0).
    pub scope: String,
    /// Whether any defs part was rebuilt NON-superset this run (M5e):
    /// consumers (stmt/pkg oleans) may skip re-elaboration across runs
    /// only when this is false — a pure append (old declarations all
    /// present, identical, in order) cannot invalidate a consumer
    /// olean, but any other change can.
    pub breaking: bool,
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

/// `None` = standalone emission (flag off, or defs build
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
pub(crate) fn scope_key(
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

/// Which verification path is asking for defs. Proof-path callers
/// always receive the verifier's full `vir_crate` (verified:
/// verifier.rs check_proof_fn), so in package-check mode their scope
/// can be the STABLE crate name — file names survive appends, and the
/// `up_to_date` compare turns into real cross-run incrementality. The
/// exec path receives `simplified_krate` (a second legitimate scope)
/// and keeps the content fingerprint so the two can never collide.
#[derive(Clone, Copy, PartialEq)]
pub enum ScopeKind {
    Proof,
    Exec,
}

pub fn for_crate(
    krate: &KrateX,
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
    build: bool,
    kind: ScopeKind,
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
    let scope = if crate::generate::package_check_enabled() {
        // Stable names for BOTH scopes (M5d-3 gave Proof; the exec
        // family joining makes island .lean text append-stable too —
        // fingerprint scopes rename the defs dir on any crate change,
        // churning every island's import line). `_exec` suffix keeps
        // the two families from colliding on one module name.
        match kind {
            ScopeKind::Proof => sanitize(crate_name),
            ScopeKind::Exec => format!("{}_exec", sanitize(crate_name)),
        }
    } else {
        // The kind is part of the scope identity in EVERY mode: the
        // two kinds build different content with different ladders,
        // and on small crates the proof/exec krates can hash
        // identically — a shared memo entry would serve one kind a
        // defs the other's consumers must reject (covers_exec
        // filter), starving exec islands of accessors.
        match kind {
            ScopeKind::Proof => scope_key(crate_name, krate, tactic_bodies),
            ScopeKind::Exec => {
                format!("{}_exec", scope_key(crate_name, krate, tactic_bodies))
            }
        }
    };
    let mut map = memo.lock().unwrap_or_else(|p| p.into_inner());
    if let Some(cached) = map.get(&scope) {
        return cached.clone();
    }
    let result = guard_build("defs module", crate_name, || {
        build_defs(krate, crate_name, &scope, tactic_bodies, build, kind)
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
    kind: ScopeKind,
) -> Option<Arc<CrateDefs>> {
    if std::env::var_os("TACTUS_VERBOSE").is_some() {
        let execs = krate.functions.iter()
            .filter(|f| matches!(f.x.mode, vir::ast::Mode::Exec) && f.x.body.is_some())
            .count();
        eprintln!(
            "tactus: build_defs scope `{}`: tactic_bodies {}, exec(with body) {}, krate fns {}",
            scope, tactic_bodies.len(), execs, krate.functions.len());
    }
    // No size gate: every crate builds its defs module, however small.
    // A ≥2-checked-fns threshold used to skip the build for tiny crates
    // (the ~1.3s defs build outweighs sharing there), but a heuristic
    // that silently switches which pipeline a crate gets is worse than
    // the second it saves — predictability over the micro-win
    // (2026-07-12, Danielle). Cross-run content-keyed caching keeps the
    // repeated cost near zero anyway.
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
                && (tactic_bodies.contains_key(&f.name)
                    // WP-routed proof fns: a Verus-code body with no
                    // tactic block still lowers to WP obligations whose
                    // stmt defs reference the fn's spec world — it must
                    // be a dep-walk root like any tactic fn (surfaced
                    // when the defs size gate was removed: an
                    // empty-body proof fn's contract referenced spec
                    // fns absent from the defs module). Over-inclusion
                    // only widens the walk; bodyless externals stay
                    // out.
                    || f.body.is_some())
        })
        .collect();
    let exec_roots: Vec<&FunctionX> = inlined_krate.functions.iter()
        .map(|f| &f.x)
        .filter(|f| matches!(f.mode, vir::ast::Mode::Exec) && f.body.is_some())
        .collect();
    // SPEC-mode trait-method-impl fns join the roots: trait INSTANCE
    // emission renders every impl's spec-method body as an instance
    // field (`sub := fun … => lib.Rational.sub_spec …`), regardless of
    // whether any batched theorem mentions it — so the walk must cover
    // those bodies' closures too. Without this, a spec fn reachable
    // ONLY through an instance field (tactus-algebra's sub_spec =
    // add∘neg, div_spec = mul∘recip — used solely via trait dispatch)
    // is dropped from the defs module while the instance still
    // references it: unknown identifier, defs elaboration fails, the
    // whole crate falls back to island emission (B6 corpus, 2026-07-19).
    let instance_field_roots: Vec<&FunctionX> = inlined_krate.functions.iter()
        .map(|f| &f.x)
        .filter(|f| {
            matches!(f.mode, vir::ast::Mode::Spec)
                && matches!(&f.kind, vir::ast::FunctionKind::TraitMethodImpl { .. })
                && f.body.is_some()
        })
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
    let full_roots: Vec<&FunctionX> = proof_roots
        .iter()
        .copied()
        .chain(exec_roots.iter().copied())
        .chain(instance_field_roots.iter().copied())
        .collect();
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
    // Kind-specific ladders (M6.1b — re-landed after the dual-krate
    // change unified the render worlds; the shape-coupling hazard that
    // reverted the first attempt is gone because BOTH scopes now
    // render spec fns from the vir krate):
    //
    // Exec scope: exec coverage or nothing. A narrower rung renders
    // proof-roots content the consumer gate (`covers_exec` filter in
    // check_exec_fn) can never import — building it was the
    // "double defs family" dead weight. Accessors stay ON when exec
    // roots exist: obligation bodies are SST/accessor-shaped even
    // though spec-fn bodies are match-shaped.
    //
    // Proof scope: consumers never need exec coverage, so the old
    // full-roots attempt was a guaranteed-wasted elaboration on every
    // cold run — start at the proof rung.
    // WP-routed proof fns (Verus-code body, no tactic block) lower
    // through the SAME SST/accessor-shaped path as exec obligations —
    // their stmt defs reference `isSome`/`<Variant>_valN` accessors,
    // so accessor emission must not key on exec roots alone (surfaced
    // when the defs size gate was removed).
    let wp_routed_proof_present = inlined_krate.functions.iter().any(|f| {
        matches!(f.x.mode, vir::ast::Mode::Proof)
            && f.x.body.is_some()
            && !tactic_bodies.contains_key(&f.x.name)
    });
    // Proof-scope roots also carry the instance-field closure: trait
    // instances emit in both scopes, so both walks must cover the
    // spec fns their fields reference (see instance_field_roots).
    let proof_roots_with_instances: Vec<&FunctionX> = proof_roots
        .iter()
        .copied()
        .chain(instance_field_roots.iter().copied())
        .collect();
    let attempts: Vec<(&[&FunctionX], bool, bool, bool)> = match kind {
        ScopeKind::Exec => vec![
            (&full_roots, !exec_roots.is_empty() || wp_routed_proof_present, true, true),
        ],
        ScopeKind::Proof => vec![
            (&proof_roots_with_instances, wp_routed_proof_present, false, true),
            (&proof_roots_with_instances, false, false, false),
        ],
    };
    // Ladder sidecar (`<scope>.ladder`): which attempt won last run,
    // the winner's content hash, and the toolchain fingerprint. A
    // failing attempt is EXPENSIVE (a full defs elaboration that
    // errors) and was re-paid every run — with the sidecar, warm runs
    // jump straight to the recorded winner; its unchanged render then
    // rides the content-compare skip, so nothing elaborates at all.
    // If the winner's render CHANGED, the krate changed: restart the
    // full ladder (an earlier, broader attempt might now succeed).
    let ladder_path = crate::generate::lean_out_root()
        .join(sanitize(crate_name))
        .join(format!("{}.ladder", scope));
    let fp = crate::project::ladder_fingerprint();
    let mut recorded: Option<(usize, String)> = if build {
        std::fs::read_to_string(&ladder_path).ok().and_then(|t| {
            // `v1 ` format version prefix (M6.2 fold-in): unversioned
            // or future-versioned records read as absent → full
            // ladder retry, which is always safe.
            let mut it = t.split_whitespace();
            if it.next() != Some("v1") {
                return None;
            }
            match (it.next(), it.next(), it.next()) {
                (Some(a), Some(h), Some(f)) if f == fp => {
                    a.parse::<usize>().ok().map(|a| (a, h.to_string()))
                }
                _ => None,
            }
        })
    } else {
        None
    };
    // Total-failure record: `FAILED <h1> <h2> <h3> <fp>` — per-attempt
    // render hashes from the run where every attempt failed. Renders
    // are cheap and deterministic; when they all match, re-running the
    // ladder would fail identically, so skip it (islands fall back to
    // standalone emission exactly as they did that run). Any changed
    // render → full retry (broader coverage might now elaborate).
    let render_hash_only = |roots: &[&FunctionX], emit_accessors: bool,
                            covers_exec: bool, with_bc_union: bool| -> Option<String> {
        render_and_build(
            &inlined_krate, &ectx, crate_name, scope, roots,
            emit_accessors, covers_exec, with_bc_union, false, true,
        ).ok().map(|(_, h)| h)
    };
    if build {
        if let Some(t) = std::fs::read_to_string(&ladder_path).ok() {
            let parts: Vec<&str> = t.split_whitespace().collect();
            if parts.len() == 3 + attempts.len()
                && parts[0] == "v1"
                && parts[1] == "FAILED"
                && parts[parts.len() - 1] == fp
            {
                let all_match = attempts.iter().enumerate().all(|(i, &(r, ea, ce, bu))| {
                    render_hash_only(r, ea, ce, bu).as_deref() == Some(parts[2 + i])
                });
                if all_match {
                    return None;
                }
            }
        }
    }
    'ladder: loop {
        let mut prev: Option<(usize, bool, bool)> = None;
        for (attempt, &(roots, emit_accessors, covers_exec, with_bc_union)) in attempts.iter().enumerate() {
            // Emit-lean mode never runs Lean, so there's nothing to learn
            // from later attempts — just emit attempt 1 and return.
            if attempt > 0 && !build {
                break;
            }
            if let Some((win, _)) = &recorded {
                if attempt < *win {
                    continue; // known-failing attempt from last run
                }
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
                emit_accessors, covers_exec, with_bc_union, build, false,
            ) {
                Ok((defs, content_hash)) => {
                    if let Some((win, h)) = &recorded {
                        if attempt == *win && *win > 0 && *h != content_hash {
                            recorded = None;
                            continue 'ladder;
                        }
                    }
                    if build {
                        let _ = std::fs::create_dir_all(
                            ladder_path.parent().expect("ladder path has a parent"));
                        let _ = std::fs::write(
                            &ladder_path, format!("v1 {} {} {}\n", attempt, content_hash, fp));
                    }
                    return Some(Arc::new(defs));
                }
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
        if build {
            let hashes: Vec<String> = attempts.iter()
                .map(|&(r, ea, ce, bu)| {
                    render_hash_only(r, ea, ce, bu).unwrap_or_else(|| "render-error".to_string())
                })
                .collect();
            let _ = std::fs::create_dir_all(
                ladder_path.parent().expect("ladder path has a parent"));
            let _ = std::fs::write(
                &ladder_path, format!("v1 FAILED {} {}\n", hashes.join(" "), fp));
        }
        return None;
    }
}

/// M5d-3 partition plan over the tagged spec-world stream. Pure and
/// deterministic: same stream -> same plan -> byte-same files (the
/// `up_to_date` content-compare depends on this).
///
/// The rule (stated here once, and in every generated file header):
/// - BASE: datatypes, classes, instances, and every spec fn an
///   instance transitively needs (so instances never reach forward).
/// - One part per source module (SCC-merged when module-level cycles
///   arise from the projection): the remaining spec-fn groups.
/// - UMBRELLA (keeps the `TactusDefs_<scope>` name, so consumers are
///   untouched): imports every part, then carries proof-method
///   classes + broadcast axioms — both emitted last and referenced
///   only from outside defs.
struct DefsPartition {
    /// Command indices (into the item stream) per destination.
    base: Vec<usize>,
    /// (part name suffix, item indices, imported part suffixes) in
    /// build (topological) order.
    parts: Vec<(String, Vec<usize>, Vec<String>)>,
    umbrella: Vec<usize>,
}

fn module_suffix(f: &Fun) -> String {
    let segs = &f.path.segments;
    if segs.len() <= 1 {
        return "root".to_string();
    }
    segs[..segs.len() - 1].iter()
        .map(|s| sanitize(s))
        .collect::<Vec<_>>()
        .join("_")
}

fn plan_partition(
    n_cmds: usize,
    segs: &[(usize, crate::generate::DefsSeg)],
) -> DefsPartition {
    use crate::generate::DefsSeg;
    use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

    // Expand segments into (range, tag) pairs.
    let mut ranges: Vec<(std::ops::Range<usize>, &DefsSeg)> = Vec::new();
    for (i, (start, tag)) in segs.iter().enumerate() {
        let end = segs.get(i + 1).map(|(s, _)| *s).unwrap_or(n_cmds);
        ranges.push((*start..end, tag));
    }

    // fn -> group id, per-group data (module, refs, indices).
    let mut fn_group: HashMap<&Fun, usize> = HashMap::new();
    let mut groups: Vec<(String, &Vec<Fun>, &Vec<Fun>, Vec<usize>)> = Vec::new();
    for (range, tag) in &ranges {
        if let DefsSeg::FnGroup { fns, refs } = tag {
            let gid = groups.len();
            for f in fns.iter() {
                fn_group.insert(f, gid);
            }
            let module = fns.first().map(module_suffix)
                .unwrap_or_else(|| "root".to_string());
            groups.push((module, fns, refs, range.clone().collect()));
        }
    }

    // Base pull: fns any instance needs, transitively closed over
    // group refs. Simple worklist — stated rule, no hidden fixpoint.
    let mut base_groups: HashSet<usize> = HashSet::new();
    let mut work: Vec<&Fun> = Vec::new();
    for (_, tag) in &ranges {
        if let DefsSeg::Instance { prereq_fns } | DefsSeg::ProofClasses { prereq_fns } = tag {
            work.extend(prereq_fns.iter());
        }
    }
    while let Some(f) = work.pop() {
        if let Some(&gid) = fn_group.get(f) {
            if base_groups.insert(gid) {
                work.extend(groups[gid].2.iter());
            }
        }
    }

    // Module graph over non-base groups (BTree for determinism).
    let mut module_first_seen: Vec<String> = Vec::new();
    let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (gid, (module, _, refs, _)) in groups.iter().enumerate() {
        if base_groups.contains(&gid) {
            continue;
        }
        if !module_first_seen.contains(module) {
            module_first_seen.push(module.clone());
        }
        let e = edges.entry(module.clone()).or_default();
        for r in refs.iter() {
            if let Some(&tgid) = fn_group.get(r) {
                if !base_groups.contains(&tgid) {
                    let tm = &groups[tgid].0;
                    if tm != module {
                        e.insert(tm.clone());
                    }
                }
            }
        }
    }

    // SCC-merge module cycles (iterative DFS Tarjan, deterministic
    // over first-appearance order). Merged part name = members joined
    // in sorted order — visible in the filename, no hidden state.
    let sccs = tarjan_sccs(&module_first_seen, &edges);
    let mut module_part: HashMap<String, usize> = HashMap::new();
    let mut part_names: Vec<String> = Vec::new();
    for scc in &sccs {
        let mut names = scc.clone();
        names.sort();
        let pname = names.join("__and__");
        let pid = part_names.len();
        part_names.push(pname);
        for m in scc {
            module_part.insert(m.clone(), pid);
        }
    }

    // Part-level imports + item assignment (original order preserved).
    let mut part_items: Vec<Vec<usize>> = vec![Vec::new(); part_names.len()];
    let mut part_imports: Vec<BTreeSet<String>> = vec![BTreeSet::new(); part_names.len()];
    for (gid, (module, _, refs, idxs)) in groups.iter().enumerate() {
        if base_groups.contains(&gid) {
            continue;
        }
        let pid = module_part[module];
        part_items[pid].extend(idxs.iter().copied());
        for r in refs.iter() {
            if let Some(&tgid) = fn_group.get(r) {
                if !base_groups.contains(&tgid) {
                    let tpid = module_part[&groups[tgid].0];
                    if tpid != pid {
                        part_imports[pid].insert(part_names[tpid].clone());
                    }
                }
            }
        }
    }

    // Route the remaining ranges.
    let mut base: Vec<usize> = Vec::new();
    let mut umbrella: Vec<usize> = Vec::new();
    for (range, tag) in &ranges {
        match tag {
            DefsSeg::Base | DefsSeg::Instance { .. }
            | DefsSeg::ProofClasses { .. } => base.extend(range.clone()),
            DefsSeg::BcAxiom => umbrella.extend(range.clone()),
            DefsSeg::FnGroup { fns, .. } => {
                let gid = fns.first().and_then(|f| fn_group.get(f)).copied();
                if gid.map(|g| base_groups.contains(&g)).unwrap_or(true) {
                    base.extend(range.clone());
                }
                // non-base group indices were assigned above
            }
        }
    }

    // Faithfulness check (transparency = faithfulness): the partition
    // is a SPLIT — every item command routed exactly once, none
    // invented, none dropped. Debug builds assert it.
    #[cfg(debug_assertions)]
    {
        let mut seen = vec![0usize; n_cmds];
        for &i in base.iter().chain(umbrella.iter())
            .chain(part_items.iter().flatten()) {
            seen[i] += 1;
        }
        assert!(seen.iter().all(|&c| c == 1),
            "defs partition must route every command exactly once");
    }

    DefsPartition {
        base,
        parts: part_names.into_iter()
            .zip(part_items)
            .zip(part_imports)
            .map(|((n, i), imp)| (n, i, imp.into_iter().collect()))
            .collect(),
        umbrella,
    }
}

/// Tarjan SCCs over the module graph; result in reverse-topological
/// order (dependencies first) — exactly the build order we need.
/// Iterative, deterministic (nodes in first-appearance order, edge
/// sets are BTreeSets).
fn tarjan_sccs(
    nodes: &[String],
    edges: &std::collections::BTreeMap<String, std::collections::BTreeSet<String>>,
) -> Vec<Vec<String>> {
    use std::collections::HashMap;
    let idx_of: HashMap<&str, usize> =
        nodes.iter().enumerate().map(|(i, n)| (n.as_str(), i)).collect();
    let succ: Vec<Vec<usize>> = nodes.iter()
        .map(|n| edges.get(n).map(|es| {
            es.iter().filter_map(|t| idx_of.get(t.as_str()).copied()).collect()
        }).unwrap_or_default())
        .collect();
    let n = nodes.len();
    let (mut index, mut low, mut on_stack) =
        (vec![usize::MAX; n], vec![0usize; n], vec![false; n]);
    let (mut stack, mut sccs): (Vec<usize>, Vec<Vec<String>>) = (Vec::new(), Vec::new());
    let mut counter = 0usize;
    for root in 0..n {
        if index[root] != usize::MAX {
            continue;
        }
        // (node, next-successor position)
        let mut call: Vec<(usize, usize)> = vec![(root, 0)];
        while let Some(&mut (v, ref mut pi)) = call.last_mut() {
            if *pi == 0 {
                index[v] = counter;
                low[v] = counter;
                counter += 1;
                stack.push(v);
                on_stack[v] = true;
            }
            if let Some(&w) = succ[v].get(*pi) {
                *pi += 1;
                if index[w] == usize::MAX {
                    call.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
            } else {
                if low[v] == index[v] {
                    let mut scc = Vec::new();
                    while let Some(w) = stack.pop() {
                        on_stack[w] = false;
                        scc.push(nodes[w].clone());
                        if w == v {
                            break;
                        }
                    }
                    scc.reverse();
                    sccs.push(scc);
                }
                let done_low = low[v];
                call.pop();
                if let Some(&mut (u, _)) = call.last_mut() {
                    low[u] = low[u].min(done_low);
                }
            }
        }
    }
    sccs
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
    // Render + hash WITHOUT touching the filesystem (ladder failure-
    // record checks). The returned CrateDefs is unbuilt scaffolding —
    // callers use only the hash.
    hash_only: bool,
) -> Result<(CrateDefs, String), String> {
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
    cmds.push(Command::Raw(crate::prelude::TACTUS_DEFS_IMPORT.to_string()));
    // Option B: no namespace wrapper (decls carry full dotted names).
    let _ = &ns;
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
    // `head` = everything before the item stream (imports, prelude,
    // namespace open, options) — replicated per partition part.
    let head: Vec<Command> = cmds.clone();
    let (item_cmds, segs) = crate::generate::spec_world_cmds_tagged(
        inlined_krate, crate_name, ectx, &walk_roots, emit_accessors, &bc_union, true,
    );
    cmds.extend(item_cmds.iter().cloned());

    // Content hash of the full rendered stream — the ladder sidecar's
    // change detector (build_defs): stable across runs because the
    // render is deterministic. Computed on the SAME text either
    // render path elaborates (partition is a pure function of it).
    let rendered = crate::lean_pp::pp_commands(&cmds);
    let content_hash = {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        rendered.text.hash(&mut h);
        // The PARTITION is part of the content identity: a seg-tagging
        // change moves commands between parts without touching the
        // monolith text (e.g. the mid-stream axiom-flush placement
        // fix), and the ladder's success/failure records must not
        // fast-path over it. Hash the seg boundaries + tags.
        for (pos, seg) in &segs {
            pos.hash(&mut h);
            std::mem::discriminant(seg).hash(&mut h);
            if let crate::generate::DefsSeg::FnGroup { fns, .. } = seg {
                for f in fns {
                    format!("{:?}", f.path).hash(&mut h);
                }
            }
        }
        format!("{:016x}", h.finish())
    };
    if hash_only {
        return Ok((CrateDefs {
            module_name, scope: scope.to_string(), covers_exec, dir, cmds,
            breaking: false,
        }, content_hash));
    }

    // Partitioned defs (M5d-3) in package modes: same commands, same
    // per-chain order, split per source module — `cmds` stays the full
    // monolith stream so every consumer (sanity concat, debuggers)
    // sees the SAME world either way.
    if crate::generate::package_enabled() || crate::generate::package_check_enabled() {
        return render_partitioned(
            &module_name, scope, &dir, &ns, covers_exec,
            cmds, &head, &item_cmds, &segs, build,
        ).map(|d| (d, content_hash));
    }

    let lean_path = dir.join(format!("{}.lean", module_name));
    let olean_path = dir.join(format!("{}.olean", module_name));

    if !build {
        std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
        std::fs::write(&lean_path, &rendered.text).map_err(|e| e.to_string())?;
        return Ok((CrateDefs {
            scope: scope.to_string(), module_name, covers_exec, dir, cmds,
            breaking: false,
        }, content_hash));
    }

    let up_to_date = olean_path.exists()
        && std::fs::read_to_string(&lean_path).ok().as_deref() == Some(&rendered.text);
    if !up_to_date {
        std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
        build_olean(&dir, &module_name, &rendered.text, &olean_path, &lean_path)?;
    }
    // Monolith: any rebuild is conservatively breaking (no manifest).
    Ok((CrateDefs {
        module_name, scope: scope.to_string(), covers_exec, dir, cmds,
        breaking: !up_to_date,
    }, content_hash))
}

/// Partitioned defs render + build (M5d-3). Files, in build order:
/// `<name>__base` (machinery), one `<name>__<module>` per source
/// module (SCC-merged), and the UMBRELLA under the original
/// `TactusDefs_<scope>` name (imports all parts + proof classes +
/// broadcast axioms) — consumers import the umbrella and see the
/// monolith's exact environment.
///
/// Rebuild rule (conservative pre-M5e): a file rebuilds when its
/// content changed OR any file it imports rebuilt this run — Lean
/// trusts LEAN_PATH at load time, so a consumer must never pair a
/// stale olean with a rebuilt dependency.
#[allow(clippy::too_many_arguments)]
fn render_partitioned(
    umbrella_name: &str,
    scope: &str,
    dir: &std::path::Path,
    ns: &str,
    covers_exec: bool,
    full_cmds: Vec<Command>,
    head: &[Command],
    item_cmds: &[Command],
    segs: &[(usize, crate::generate::DefsSeg)],
    build: bool,
) -> Result<CrateDefs, String> {
    let mut plan = plan_partition(item_cmds.len(), segs);
    // Companion-citation imports (2026-07-19): the part-import graph
    // follows fn-graph REFS, but a `decreasing_by` tactic can cite the
    // seq-measure companion theorems (`Seq.subrange_tail_len_lt`,
    // `Seq.drop_{first,last}_len_lt`) — a TEXT dependency the graph
    // can't see. tactus-algebra's __poly part recursed on subrange
    // while the companion lived in the drop_last impl's part, two
    // segments away: unknown identifier, defs elaboration failed,
    // island fallback. For each companion name: find the part whose
    // items DEFINE it (`theorem <ns>…name`), then make every part
    // whose item text cites it import the definer.
    {
        let cmd_text = |i: usize| crate::lean_pp::pp_command(&item_cmds[i]);
        for comp in ["subrange_tail_len_lt", "drop_first_len_lt", "drop_last_len_lt"] {
            let def_marker = format!("Seq.{}", comp);
            let definer: Option<(usize, String)> = plan.parts.iter().enumerate()
                .find_map(|(pi, (name, items, _))| {
                    items.iter().any(|&i| {
                        let t = cmd_text(i);
                        t.contains(&def_marker) && t.contains("theorem ")
                            && t.find("theorem ").map_or(false, |k| {
                                t[k..].contains(&def_marker)
                            })
                    })
                    .then(|| (pi, name.clone()))
                });
            if let Some((def_pi, def_name)) = definer {
                // Only LATER parts may import the definer (parts are
                // in topological build order; a forward import would
                // reference an olean that doesn't exist yet).
                for pi in (def_pi + 1)..plan.parts.len() {
                    let cites = plan.parts[pi].1.iter()
                        .any(|&i| cmd_text(i).contains(&def_marker));
                    if cites && !plan.parts[pi].2.contains(&def_name) {
                        plan.parts[pi].2.push(def_name.clone());
                    }
                }
            }
        }
    }
    // Extra imports go FIRST: the head's prelude block is a multi-line
    // Raw (import + set_options), so anything after it is no longer in
    // Lean's import section. Import order is irrelevant; position isn't.
    let make_file = |header: &str, extra_imports: &[String], items: &[usize]| -> Vec<Command> {
        let mut cmds: Vec<Command> = Vec::new();
        cmds.push(Command::Raw(format!(
            "-- tactus defs part: {} (base = machinery + instance closure; \
one part per source module, SCC-merged; umbrella = interface)", header)));
        cmds.extend(extra_imports.iter().map(|m| Command::Import(m.clone())));
        cmds.extend(head.iter().cloned());
        cmds.extend(items.iter().map(|&i| item_cmds[i].clone()));
        // Option B: no namespace wrapper (decls carry full dotted
        // names), so no close either.
        cmds
    };

    let base_name = format!("{}__base", umbrella_name);
    // (module name, file cmds, imported module names) in build order.
    let mut files: Vec<(String, Vec<Command>, Vec<String>)> = Vec::new();
    if plan.parts.is_empty() {
        // Single-file collapse: with no per-module parts, base +
        // umbrella merge into ONE module named `umbrella_name` —
        // consumers import that name either way, and concatenating
        // base items then umbrella items elaborates in exactly the
        // order the two-file split did (umbrella imported base).
        // Saves one full `lean` process (each pays the prelude olean
        // import) per crate; on e2e-test-sized crates the defs chain
        // halves.
        let items: Vec<usize> =
            plan.base.iter().chain(plan.umbrella.iter()).cloned().collect();
        files.push((
            umbrella_name.to_string(),
            make_file("base+umbrella (single-file collapse)", &[], &items),
            Vec::new(),
        ));
    } else {
        files.push((base_name.clone(), make_file("base", &[], &plan.base), Vec::new()));
        for (suffix, items, imports) in &plan.parts {
            let name = format!("{}__{}", umbrella_name, suffix);
            let mut imp: Vec<String> = vec![base_name.clone()];
            imp.extend(imports.iter().map(|i| format!("{}__{}", umbrella_name, i)));
            files.push((name, make_file(suffix, &imp, items), imp));
        }
        let all_parts: Vec<String> = files.iter().map(|(n, _, _)| n.clone()).collect();
        files.push((
            umbrella_name.to_string(),
            make_file("umbrella", &all_parts, &plan.umbrella),
            all_parts,
        ));
    }

    // M5e superset waiver: per part, a MANIFEST of one hash per item
    // command (DefaultHasher — key-stable across runs of one binary).
    // A rebuild whose old manifest is an order-preserving subsequence
    // of the new one is an APPEND: old declarations all present,
    // identical, before any new ones — existing consumer oleans stay
    // valid (kernel weakening; Lean elaborates top-down, so the old
    // prefix elaborates in an identical environment). Anything else is
    // BREAKING, and breaking propagates through imports (Lean imports
    // are transitive).
    let cmd_hash = |c: &Command| -> u64 {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        crate::lean_pp::pp_commands(std::slice::from_ref(c)).text.hash(&mut h);
        h.finish()
    };
    let is_subsequence = |old: &[u64], new: &[u64]| -> bool {
        let mut it = new.iter();
        old.iter().all(|o| it.any(|n| n == o))
    };
    let mut breaking: std::collections::HashSet<String> = Default::default();
    std::fs::create_dir_all(dir).map_err(|e| e.to_string())?;
    // Decision pass (serial, no lean runs): render, compare manifests,
    // decide which files need building, and propagate `breaking`
    // exactly as the old build-in-order loop did — own_superset is a
    // pure manifest comparison, independent of the lean run itself.
    struct PartBuild {
        name: String,
        rendered_text: String,
        lean_path: std::path::PathBuf,
        olean_path: std::path::PathBuf,
        /// Written only AFTER a successful build: a fresh manifest
        /// over a stale olean would let consumers treat the old build
        /// as a pure append and skip re-elaboration.
        manifest_path: std::path::PathBuf,
        manifest_text: String,
        level: usize,
    }
    let mut to_build: Vec<PartBuild> = Vec::new();
    let mut build_level: std::collections::HashMap<String, usize> = Default::default();
    for (name, cmds, imports) in &files {
        let rendered = crate::lean_pp::pp_commands(cmds);
        let lean_path = dir.join(format!("{}.lean", name));
        let olean_path = dir.join(format!("{}.olean", name));
        let manifest_path = dir.join(format!("{}.manifest", name));
        let new_manifest: Vec<u64> = cmds.iter().map(&cmd_hash).collect();
        let write_manifest = || -> Result<(), String> {
            let text: String = new_manifest.iter()
                .map(|h| format!("{:016x}\n", h)).collect();
            std::fs::write(&manifest_path, text).map_err(|e| e.to_string())
        };
        if !build {
            std::fs::write(&lean_path, &rendered.text).map_err(|e| e.to_string())?;
            write_manifest()?;
            continue;
        }
        let import_breaking = imports.iter().any(|i| breaking.contains(i));
        let content_same = olean_path.exists()
            && std::fs::read_to_string(&lean_path).ok().as_deref() == Some(&rendered.text);
        if content_same && !import_breaking {
            continue; // unchanged, or upstream changes were pure appends
        }
        let old_manifest: Option<Vec<u64>> = std::fs::read_to_string(&manifest_path)
            .ok()
            .map(|t| t.lines().filter_map(|l| u64::from_str_radix(l, 16).ok()).collect());
        // Level = 1 + deepest import that is itself being rebuilt this
        // run (imports satisfied by an existing olean don't order us).
        let level = imports.iter()
            .filter_map(|i| build_level.get(i))
            .max()
            .map(|l| l + 1)
            .unwrap_or(0);
        build_level.insert(name.clone(), level);
        to_build.push(PartBuild {
            name: name.clone(),
            rendered_text: rendered.text,
            lean_path,
            olean_path,
            manifest_path,
            manifest_text: new_manifest.iter()
                .map(|h| format!("{:016x}\n", h)).collect(),
            level,
        });
        let own_superset = old_manifest
            .map(|o| is_subsequence(&o, &new_manifest))
            .unwrap_or(false); // no manifest = first build = breaking
        if import_breaking || !own_superset {
            breaking.insert(name.clone());
        }
    }
    // Build pass: level-parallel over the dependency DAG (the old loop
    // was fully serial — 107 parts × ~0.9s = ~95s of gt's lean phase).
    // Files within a level are independent by construction.
    if !to_build.is_empty() {
        let jobs = std::env::var("TACTUS_DEFS_BUILD_JOBS").ok()
            .and_then(|v| v.parse::<usize>().ok())
            .unwrap_or_else(|| {
                std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4).min(8)
            })
            .max(1);
        let max_level = to_build.iter().map(|p| p.level).max().unwrap_or(0);
        for lvl in 0..=max_level {
            let level_parts: Vec<&PartBuild> =
                to_build.iter().filter(|p| p.level == lvl).collect();
            let next = std::sync::atomic::AtomicUsize::new(0);
            let errors: std::sync::Mutex<Vec<String>> = std::sync::Mutex::new(Vec::new());
            std::thread::scope(|scope| {
                for _ in 0..jobs.min(level_parts.len()) {
                    let level_parts = &level_parts;
                    let next = &next;
                    let errors = &errors;
                    scope.spawn(move || loop {
                        let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        let Some(p) = level_parts.get(i) else { break };
                        match build_olean(
                            dir, &p.name, &p.rendered_text, &p.olean_path, &p.lean_path,
                        ) {
                            Ok(()) => {
                                if let Err(e) =
                                    std::fs::write(&p.manifest_path, &p.manifest_text)
                                {
                                    errors.lock().unwrap().push(format!(
                                        "defs part `{}` manifest: {}", p.name, e));
                                }
                            }
                            Err(e) => {
                                errors.lock().unwrap()
                                    .push(format!("defs part `{}`: {}", p.name, e));
                            }
                        }
                    });
                }
            });
            let errs = errors.into_inner().unwrap();
            if let Some(e) = errs.into_iter().next() {
                return Err(e);
            }
        }
    }
    Ok(CrateDefs {
        module_name: umbrella_name.to_string(),
        scope: scope.to_string(),
        covers_exec,
        dir: dir.to_path_buf(),
        cmds: full_cmds,
        breaking: !breaking.is_empty(),
    })
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
    // Per-module (not just per-pid): parts build in parallel now, and
    // the failure path removes the whole build dir.
    let build = dir.join(format!("build-{}-{}", std::process::id(), module_name));
    std::fs::create_dir_all(&build).map_err(|e| e.to_string())?;
    let src_name = format!("{}.lean", module_name);
    let out_name = format!("{}.olean", module_name);
    std::fs::write(build.join(&src_name), source).map_err(|e| e.to_string())?;
    let existing = std::env::var("LEAN_PATH").unwrap_or_default();
    // `dir` is on the path so partitioned defs parts resolve their
    // sibling imports (base / other parts) — harmless for monoliths.
    let mut lean_path_env = format!("{}:{}",
        prelude_dir.to_string_lossy(), dir.to_string_lossy());
    if !existing.is_empty() {
        lean_path_env = format!("{}:{}", lean_path_env, existing);
    }
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
            // --emit-lean sidecar: no Lean run follows and nothing
            // may cache.
            first_theorem_line: None,
            changed: true,
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
    let defs = for_crate(krate, crate_name, tactic_bodies, build, ScopeKind::Proof)?;

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
    // Option B: no namespace wrapper (decls carry full dotted names).
    let _ = &ns;
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
    // Option B: no namespace wrapper — nothing to close.
    let _ = &ns;

    // Sanity over defs + batch: what Lean sees through the import.
    // Unconditional in all build profiles (see `generate::debug_check`).
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
