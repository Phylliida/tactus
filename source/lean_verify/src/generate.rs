//! Orchestrates Lean file generation and verification.
//!
//! Build a `Vec<Command>` via the AST, pretty-print once, and invoke Lean
//! on the resulting `.lean` file. Per-declaration writers live in
//! `to_lean_fn` / `sst_to_lean`; this file only sequences them and handles
//! artifact I/O.

use std::path::{Path, PathBuf};
use vir::ast::*;
use vir::sst::{FuncCheckSst, FunctionSst};
use crate::dep_order::{self, FnGroup};
use crate::lean_ast::Command;
use crate::lean_pp::pp_commands;
use crate::lean_process;

use crate::project;
use crate::sanity;
use crate::sst_to_lean;
use crate::to_lean_fn::{self, LeanSourceMap};
use crate::to_lean_type::{lean_name, sanitize, short_name};

// ── Artifact location ──────────────────────────────────────────────────

/// Where to write generated Lean artifacts.
///
/// Priority: `$TACTUS_LEAN_OUT` → `$CARGO_TARGET_DIR/tactus-lean` → `./target/tactus-lean`.
/// The last fallback is CWD-relative, which works correctly when Tactus is
/// invoked from a Cargo project root (cargo's convention) but will scatter
/// artifacts if invoked from elsewhere. Set `$TACTUS_LEAN_OUT` explicitly
/// for reproducible builds outside Cargo.
pub(crate) fn lean_out_root() -> PathBuf {
    // ALWAYS absolute: these dirs end up on the Lean child's
    // `LEAN_PATH`, where a relative entry resolves against the CHILD's
    // cwd — which under `lake env lean` is the lake project dir, not
    // ours. A relative root here cost a day of debugging on
    // tactus-group-theory (defs imports failing only on the lake
    // branch; see CRATEDEFS.md 1c).
    let root = if let Ok(dir) = std::env::var("TACTUS_LEAN_OUT") {
        PathBuf::from(dir)
    } else if let Ok(dir) = std::env::var("CARGO_TARGET_DIR") {
        PathBuf::from(dir).join("tactus-lean")
    } else {
        PathBuf::from("target").join("tactus-lean")
    };
    std::path::absolute(&root).unwrap_or(root)
}

/// Compute the on-disk artifact path for a given function.
/// Structure: `{root}/{crate}/{fn_lean_name_with_underscores}.lean`.
/// Dots in Lean names (module separators) become `__` so the file name stays flat.
fn lean_file_path(crate_name: &str, fn_path: &vir::ast::Path) -> PathBuf {
    let ns = sanitize(crate_name);
    // `lean_name_relative`: the filename is an artifact key, not Lean text —
    // the root-anchor prefix (`_root_.{ns}.`) must not leak into it, and
    // neither should «»-quoting of reserved-word fn names (finding #8).
    let leaf = crate::to_lean_type::lean_name_relative(fn_path)
        .replace(['«', '»'], "")
        .replace('.', "__");
    lean_out_root().join(ns).join(format!("{}.lean", leaf))
}

/// On-disk path for the `--emit-lean` sidecar: `{root}/{crate}/sourcemap.json`,
/// alongside the crate's generated `.lean` files (so the Tactus server finds
/// the map next to the artifacts it indexes).
pub fn sourcemap_path(crate_name: &str) -> PathBuf {
    lean_out_root().join(sanitize(crate_name)).join("sourcemap.json")
}

/// Like `write_lean_file`, returning whether the content CHANGED
/// (file absent or different) — the cross-run skip signal (M5e).
fn write_lean_file_tracked(path: &Path, source: &str) -> Result<bool, String> {
    let changed = std::fs::read_to_string(path).ok().as_deref() != Some(source);
    if changed {
        write_lean_file(path, source)?;
    }
    Ok(changed)
}

fn write_lean_file(path: &Path, source: &str) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)
            .map_err(|e| format!("could not create {}: {}", parent.display(), e))?;
    }
    std::fs::write(path, source)
        .map_err(|e| format!("could not write {}: {}", path.display(), e))
}

// ── Preamble builder ───────────────────────────────────────────────────

/// Codegen mode for `krate_preamble` — distinguishes the two entry
/// points (proof fns vs exec fns). Determines whether to emit
/// per-variant accessor fns for multi-variant inductives.
///
/// Bitvec / future per-fn preamble extras come through the
/// `theorems` parameter's `requires_preamble` (see right-way #4),
/// not through this enum. The enum is purely about the proof-fn
/// vs exec-fn structural distinction.
enum PreambleConfig {
    /// Proof fns: native match rendering (no accessor fns). The
    /// historical caveat ("accessors for types with non-Inhabited
    /// fields break elaboration even when unused") is LIFTED — M6.0
    /// moved accessors to `[Nonempty]` + `Classical.ofNonempty`, so
    /// they elaborate for any field type. Proof fns keep native match
    /// purely as the better rendering.
    ProofFn,
    /// Exec fns: emit accessor fns for desugared match (via
    /// `IsVariant` / `Field`).
    ExecFn,
    /// Package emission (DESIGN-emit-module.md M2): proof-fn rendering
    /// (no accessors) with NO helper theorems — helpers arrive as
    /// hypothesis binders typed by their statement defs, and the
    /// statement defs arrive via the Stmts module import. Only valid
    /// in shared-defs mode (callers guarantee `defs` is `Some`).
    ProofFnPackage,
    /// Exec package emission (DESIGN-exec-packages.md M6.2): like
    /// ProofFnPackage — no helper theorems (hypothesis binders), no
    /// LOCAL accessors either: the full-roots exec defs module carries
    /// the accessor fns (M6.0b census), and callers gate on
    /// `defs.covers_exec` before choosing this config.
    ExecFnPackage,
}

impl PreambleConfig {
    /// Whether the preamble should emit per-variant accessor fns
    /// for multi-variant inductives.
    fn emit_accessors(&self) -> bool {
        matches!(self, PreambleConfig::ExecFn)
    }
}

/// Word-boundary check: does identifier `word` occur in `text` not as
/// part of a larger identifier? Byte-level so it's safe across the
/// Unicode in Lean tactic bodies (`word` is an ASCII identifier, and
/// ASCII bytes never appear inside a multi-byte UTF-8 sequence; a
/// continuation byte before/after counts as a boundary, which is
/// correct).
pub(crate) fn ident_appears(text: &str, word: &str) -> bool {
    let (t, w) = (text.as_bytes(), word.as_bytes());
    if w.is_empty() || w.len() > t.len() {
        return false;
    }
    let is_ident = |c: u8| c.is_ascii_alphanumeric() || c == b'_';
    (0..=t.len() - w.len()).any(|s| {
        &t[s..s + w.len()] == w
            && (s == 0 || !is_ident(t[s - 1]))
            && (s + w.len() == t.len() || !is_ident(t[s + w.len()]))
    })
}

/// Drop `--`-to-end-of-line Lean comments so a proof-fn name merely
/// mentioned in a comment doesn't count as a reference. (A real lemma
/// reference is tactic code, before any trailing comment; a `--` inside
/// a string literal would over-strip, but string literals in tactic
/// proofs are vanishingly rare.)
pub(crate) fn strip_lean_line_comments(body: &str) -> String {
    body.lines()
        .map(|l| match l.find("--") {
            Some(i) => &l[..i],
            None => l,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Proof-fn bodies are raw Lean tactic text (a `TacticBlock` span), so
/// VIR dep-walking can't see `have := helper` lemma calls — those
/// references exist only as text. Find the proof fns a root transitively
/// references by scanning tactic bodies for their names, returned in
/// TOPOLOGICAL order (a dependency before anything that references it)
/// via DFS post-order. Roots are excluded — they emit as the file's main
/// theorem. This fixes BUG-proof-fn-dep-walker-over-includes.md: only the
/// root's actual downward dependencies land in its file, correctly
/// ordered, so a proof fn that merely *depends on* the root (and would
/// forward-reference it) is no longer dragged in. `candidates` pairs each
/// emittable proof fn with the short name it's referenced by in Lean.
fn collect_referenced_proof_fns<'a>(
    roots: &[&'a FunctionX],
    candidates: &[(&'a FunctionX, &'a str)],
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> Vec<&'a FunctionX> {
    fn visit<'a>(
        f: &'a FunctionX,
        candidates: &[(&'a FunctionX, &'a str)],
        tactic_bodies: &std::collections::HashMap<Fun, String>,
        root_names: &std::collections::HashSet<&'a Fun>,
        visited: &mut std::collections::HashSet<&'a Fun>,
        ordered: &mut Vec<&'a FunctionX>,
    ) {
        if !visited.insert(&f.name) {
            return;
        }
        if let Some(body) = tactic_bodies.get(&f.name) {
            let code = strip_lean_line_comments(body);
            for (cand, name) in candidates {
                if cand.name != f.name && ident_appears(&code, name) {
                    visit(cand, candidates, tactic_bodies, root_names, visited, ordered);
                }
            }
        }
        // Post-order: emit `f` after its dependencies. Roots emit
        // separately as the file's main theorem, so skip them here.
        if !root_names.contains(&f.name) {
            ordered.push(f);
        }
    }
    let root_names: std::collections::HashSet<&Fun> =
        roots.iter().map(|f| &f.name).collect();
    let mut visited: std::collections::HashSet<&Fun> = std::collections::HashSet::new();
    let mut ordered: Vec<&FunctionX> = Vec::new();
    for r in roots {
        visit(r, candidates, tactic_bodies, &root_names, &mut visited, &mut ordered);
    }
    ordered
}

/// Build the shared preamble: imports, prelude, namespace-open, and entity
/// declarations transitively referenced by `root_fns`. Returns a (preamble
/// Vec, namespace) pair. Callers append the theorem command and the matching
/// `end <ns>` command.
///
/// Per-fn preamble fragments (e.g., the BitVec instances #130 needs)
/// are aggregated from each theorem's `requires_preamble`, deduped,
/// and emitted at the appropriate spot — `Import` fragments before
/// the prelude, `PreludeAddendum` fragments after. Callers don't
/// need to thread feature flags through; the theorems themselves
/// declare what they need.
///
/// Note: reference collection walks VIR-AST bodies. For exec fns the SST
/// body has additional shapes synthesized by Verus's recursion pass —
/// notably `CheckDecreaseHeight` — which reference Self (already in the
/// krate) and the decrease expression (which is itself a VIR-AST `Expr`
/// reachable via `f.decrease`). So in practice the VIR-AST walk picks up
/// every entity the SST body references too. If `sst_to_lean` ever starts
/// referencing a Function or Datatype that ONLY appears in synthesized SST
/// (not in any VIR-AST shape), extend this to walk the SST body as well.
fn krate_preamble(
    krate: &KrateX,
    imports: &[String],
    crate_name: &str,
    root_fns: &[&FunctionX],
    config: PreambleConfig,
    theorems: &[crate::lean_ast::Theorem],
    tactic_bodies: &std::collections::HashMap<Fun, String>,
    // Cross-crate broadcast lemmas (#122) the root fn brings into
    // scope via `broadcast use <group>;`. Emitted as Lean axioms and
    // added to the dep-walk roots so the spec fns / datatypes their
    // require/ensure reference also land in the preamble. Empty for
    // proof fns and exec fns without `broadcast use`.
    broadcast_lemmas: &[&Fun],
    // Shared-defs mode (CRATEDEFS.md step 1a): when `Some`, the
    // crate's spec world (datatypes / spec fns / classes / instances)
    // lives in the prebuilt defs module and this file imports it
    // instead of re-rendering it. Helper proof-fn theorems and the
    // root stay per-file in both modes. Callers guarantee
    // `broadcast_lemmas` is empty in defs mode (broadcast-using fns
    // fall back to standalone — their axioms extend the dep walk in
    // ways a once-per-crate defs build can't know).
    defs: Option<&crate::crate_defs::CrateDefs>,
) -> (Vec<Command>, String) {
    let emit_accessors = config.emit_accessors();

    // Compute helpers_to_emit: proof fns the root might invoke as
    // lemmas from `have _ := lemma args` in its tactic body. Always
    // excluded: `root_fns` themselves (each emits as its file's main
    // theorem), proof fns without a tactic body in `tactic_bodies`
    // (uninterp trait method decls etc.), and `TraitMethodDecl` /
    // `TraitMethodImpl` (those live inside class/instance declarations,
    // not as standalone theorems).
    //
    // These helpers' dep-walk roots feed into the spec-fn dep walk
    // alongside `root_fns`, so any spec fn / datatype / trait the
    // helpers transitively reference also lands in the preamble.
    // See BUG-no-helper-proof-fn-call-from-exec.md. Computed up here
    // (before the import block) because the file's imports are the union
    // over exactly the fns emitted into it — root_fns + helpers_to_emit.
    let root_fn_set: std::collections::HashSet<&Fun> =
        root_fns.iter().map(|f| &f.name).collect();
    let is_emittable_helper =
        |f: &&FunctionX| is_emittable_tactic_proof_fn(f, tactic_bodies);
    let helpers_to_emit: Vec<&FunctionX> = match config {
        // Proof-fn file: include ONLY the root's transitive downward
        // dependencies (proof fns its tactic body references, recursively),
        // in topological order (deps first). Proof-fn bodies are raw Lean
        // text so the references are found by textual scan, not VIR
        // dep-walking. This fixes the over-inclusion that previously
        // emitted EVERY proof fn into every file — which, combined with
        // the root emitting last, forward-referenced the root from any
        // proof fn that depended on it. See
        // BUG-proof-fn-dep-walker-over-includes.md.
        PreambleConfig::ProofFn => {
            let candidates: Vec<(&FunctionX, &str)> = krate.functions.iter()
                .map(|f| &f.x)
                .filter(is_emittable_helper)
                .map(|f| (f, short_name(&f.name.path)))
                .collect();
            collect_referenced_proof_fns(root_fns, &candidates, tactic_bodies)
        }
        // Exec-fn file: an exec root's helper references live in
        // `proof { }` / `assert(..) by { }` blocks read at codegen, not
        // available here, so keep the safe over-approximation (every
        // emittable proof fn). A helper can't forward-reference an exec
        // root — no proof fn depends on an exec fn — so the proof-fn
        // forward-reference bug doesn't arise; among-helper ordering
        // stays source order (correct in the common helper-before-caller
        // case).
        PreambleConfig::ExecFn => krate.functions.iter()
            .map(|f| &f.x)
            .filter(is_emittable_helper)
            .filter(|f| !root_fn_set.contains(&f.name))
            .collect(),
        // Package mode: helpers are hypothesis binders on the root
        // theorem (typed by statement defs from the Stmts module
        // import), never inline theorems. Exec package mode kills the
        // ExecFn over-approximation above for good: at package-emit
        // time the obligations' tactic texts ARE available (from the
        // SST), so the emitter scans them for the precise helper set.
        PreambleConfig::ProofFnPackage | PreambleConfig::ExecFnPackage => Vec::new(),
    };
    // Aggregate fragments across all theorems. Dedup preserves
    // first-occurrence order via a HashSet for membership and a
    // Vec for ordering.
    let mut seen_fragments: std::collections::HashSet<&crate::lean_ast::PreambleFragment>
        = std::collections::HashSet::new();
    let mut ordered_fragments: Vec<&crate::lean_ast::PreambleFragment> = Vec::new();
    for theorem in theorems {
        for frag in &theorem.requires_preamble {
            if seen_fragments.insert(frag) {
                ordered_fragments.push(frag);
            }
        }
    }
    let mut cmds: Vec<Command> = Vec::new();
    // File-level imports (declared at the top of the source `verus! { }`
    // block) are attached per-fn at macro-expansion time, gated on
    // `tactic_by` / `tactus_auto`. Under `--lean-backend` an exec fn routes to
    // Lean WITHOUT carrying that attr (e.g. a plain `fn main`), so its own
    // `lean_imports` is empty — yet its preamble emits proof fns whose bodies
    // may use `nlinarith` / `ring` / … So emit the union of imports over the
    // fns ACTUALLY emitted into this file: `root_fns` + `helpers_to_emit`.
    //
    // This is scoped to the file's content, not the whole krate: a per-fn file
    // gets the imports of its root + the helper proof fns its preamble actually
    // contains — NOT a blanket union of every source file's imports in the
    // crate. (For an exec-fn file the over-approximation puts every emittable
    // proof fn in the preamble, so its imports legitimately span those fns'
    // source files; for a proof-fn file it's just the downward closure.) The
    // passed `imports` (this fn's own) seed the order.
    let mut seen_imports: std::collections::HashSet<&str> = std::collections::HashSet::new();
    let emitted_fn_imports = root_fns.iter().chain(helpers_to_emit.iter())
        .flat_map(|f| f.attrs.lean_imports.iter());
    for imp in imports.iter().chain(emitted_fn_imports) {
        if seen_imports.insert(imp.as_str()) {
            cmds.push(Command::Import(imp.clone()));
        }
    }
    // Theorem-required Imports go before the prelude — Lean's
    // `import` statements must precede any other commands at file top.
    for frag in &ordered_fragments {
        if let crate::lean_ast::PreambleFragment::Import(s) = frag {
            cmds.push(Command::Import(s.clone()));
        }
    }
    match defs {
        Some(d) => {
            cmds.push(Command::Import(d.module_name.clone()));
            // set_options don't propagate through `import` — restate.
            cmds.push(Command::Raw(crate::prelude::TACTUS_SET_OPTIONS.to_string()));
        }
        None => {
            // Prebuilt-prelude import (CRATEDEFS.md step 0): the 429-line
            // prelude used to be inlined here, re-elaborated in every file
            // (~1.3s/check). `check_lean_file` puts the cache dir holding
            // `TactusPrelude.olean` on the child's LEAN_PATH.
            cmds.push(Command::Raw(crate::prelude::TACTUS_DEFS_IMPORT.to_string()));
        }
    }
    // Theorem-required PreludeAddendums go after the prelude — they
    // typically declare instances that depend on the prelude's
    // definitions and on the imports above.
    for frag in &ordered_fragments {
        if let crate::lean_ast::PreambleFragment::PreludeAddendum(s) = frag {
            cmds.push(Command::Raw(s.clone()));
        }
    }
    let ns = sanitize(crate_name);
    // Option B naming: no `namespace` wrapper — decls carry their full
    // dotted names at root scope (see `lean_name`).
    let _ = &ns;
    // Disable Lean's autoImplicit for the generated user-derived decls (spec
    // fns + datatypes + theorems). Guardrail: a free identifier in a theorem
    // signature is ALWAYS a codegen bug (Tactus emits explicit binders,
    // type-params included), but autoImplicit would silently auto-bind it as
    // an implicit `{x}` and the broken theorem "verifies" — which is exactly
    // how the unbound-`i` loop bug (BUG-preloop-assert-modvar-unbound.md)
    // passed in release while the debug-only sanity check rejected it. With
    // autoImplicit off, Lean itself rejects any unbound reference in EVERY
    // build profile, independent of the debug checker. Placed after the
    // namespace so the hand-written prelude / addendums (which may legitimately
    // use autobound) are unaffected. Validated zero-false-positive across the
    // full e2e suite + every tutorial chapter. See DESIGN § "autoImplicit
    // guardrail".
    cmds.push(Command::Raw("set_option autoImplicit false".to_string()));
    // Krate-level tables (the all-fn map, shell traits, trait
    // out-params, assoc-type impls), built once. `ectx.fn_map` is the
    // all-fn map (spec + proof + exec, no filtering) — shared with
    // `collect_references` so the dep walk can resolve
    // TraitMethodImpl→method redirects and walk into exec-callee specs
    // via the `call_inlining` abstraction.
    let ectx = crate::emit_ctx::EmitCtx::build(krate, tactic_bodies);
    // Resolve broadcast lemma `Fun` identities (#122) to their
    // `FunctionX` via the all-fn map. Cross-crate lemmas live in the
    // merged krate (via `merge_krates`) with body=None but
    // require/ensure intact — that's the broadcast fact we emit.
    let bc_lemma_funcs: Vec<&FunctionX> = broadcast_lemmas.iter()
        .filter_map(|f| ectx.fn_map.get(f).copied())
        .collect();
    // Extended root set for dep walking: root_fns + helpers +
    // broadcast lemmas. The dep walk picks up all transitive spec-fn
    // / datatype refs from each, so they can be emitted (helpers as
    // theorems, broadcast lemmas as axioms) without unresolved-
    // reference errors — e.g. `axiom_seq_push_len`'s ensures
    // references `seq.Seq.len`/`push`, which must be in the preamble.
    let dep_walk_roots: Vec<&FunctionX> = root_fns.iter().copied()
        .chain(helpers_to_emit.iter().copied())
        .chain(bc_lemma_funcs.iter().copied())
        .collect();
    if defs.is_none() {
        cmds.extend(spec_world_cmds(krate, crate_name, &ectx, &dep_walk_roots, emit_accessors, &bc_lemma_funcs, false));
    }
    // (defs mode: bc axioms come from the defs module's import — the
    // union emitted there is a superset of this fn's collected set.)
    // Emit proof-fn theorems for helper proof fns the root fn might
    // invoke from `proof { have _ := some_lemma args }` blocks (or
    // `assert(P) by { have _ := some_lemma args }`). Without this,
    // exec fn theorems can't reference helper proof fns by name —
    // "Unknown identifier `some_lemma`". See
    // BUG-no-helper-proof-fn-call-from-exec.md.
    //
    // Emitted AFTER instances because helper proof fns may use
    // typeclass dispatch on trait methods (`Trait.method val`) which
    // requires the corresponding `instance` to be already declared.
    // Their transitive spec-fn / datatype / trait refs were already
    // added to the preamble via `dep_walk_roots` extension at the
    // top of this fn, so all dependencies are in scope by this
    // point.
    //
    // Skip within the loop:
    // * root_fns themselves (the proof fn we're checking IS its own
    //   file's main theorem; emitting it twice would conflict)
    // * proof fns without a tactic body in `tactic_bodies` (these
    //   are either trait method decls without defaults, or impl
    //   methods whose body is the user's `by { }` tactic — both
    //   emit elsewhere)
    // * `FunctionKind::TraitMethodDecl` / `TraitMethodImpl` — those
    //   live inside class/instance declarations, not as standalone
    //   theorems
    //
    // Ordering: `helpers_to_emit` is already topologically sorted for
    // proof-fn files (deps first, via `collect_referenced_proof_fns`'s
    // DFS post-order), so a helper that references another helper sees
    // it declared first. Exec-fn files keep source order (no helper can
    // forward-reference the exec root). A true cycle of mutually-
    // referencing proof fns would still need a Lean `mutual` block —
    // out of scope and not observed.
    for f in &helpers_to_emit {
        let tactic_body = tactic_bodies.get(&f.name)
            .expect("helpers_to_emit is built from tactic_bodies — \
                     every entry has a tactic body");
        cmds.push(Command::Theorem(to_lean_fn::proof_fn_to_ast(
            f, tactic_body, &ectx,
        )));
    }
    (cmds, ns)
}

/// The crate's "spec world": classes, datatypes (with accessors when
/// `emit_accessors`), spec fns and trait instances in topological
/// order, plus broadcast-lemma axioms at the end. Extracted from
/// `krate_preamble` so the shared-defs module (CRATEDEFS.md step 1a)
/// can render exactly this block once per crate with roots = all
/// checkable fns, while standalone files keep rendering it per file.
/// Does this fn's BODY call a `BuiltinSpecFun` (closure
/// `call_requires`/`call_ensures` etc.)? The renderer has no faithful
/// Lean form for those (variadic) — it emits a literal
/// `builtinSpecFun`, which elaborates as an unknown identifier.
/// Body-slot sibling of `broadcast_collect`'s require/ensure-slot
/// filter; consulted by the shared-defs render, where one such spec fn
/// (e.g. vstd's `pervasive.strictly_cloned`, pulled in by clone-impl
/// exec fns) would poison the whole module. Per-fn standalone files
/// keep today's behavior (the one referencing file fails in Lean).
fn body_references_builtin_spec_fun(func: &FunctionX) -> bool {
    use std::cell::Cell;
    use vir::visitor::VisitorControlFlow;
    let found = Cell::new(false);
    let mut visit = |e: &vir::ast::Expr| {
        if let ExprX::Call(CallTarget::BuiltinSpecFun(..), ..) = &e.x {
            found.set(true);
            VisitorControlFlow::Stop(())
        } else {
            VisitorControlFlow::Recurse
        }
    };
    if let Some(body) = &func.body {
        vir::ast_visitor::expr_visitor_walk(body, &mut visit);
    }
    found.get()
}

/// Segment tag for defs partitioning (M5d-3): commands from a
/// segment's start index up to the next segment's start carry its tag.
/// `Base` = the entangled machinery (datatypes, classes, instances,
/// instance-prereq spec fns) that stays in one part; `FnGroup` = the
/// partitionable bulk; `ProofClasses`/`BcAxiom` are emitted last and
/// referenced only from OUTSIDE defs — they ride the umbrella.
#[derive(Clone)]
pub(crate) enum DefsSeg {
    Base,
    /// One spec-fn group (single or mutual): the fns it defines and the
    /// fn-level references its bodies/signatures make (edge source for
    /// the module graph; datatype refs resolve to Base implicitly).
    FnGroup { fns: Vec<Fun>, refs: Vec<Fun> },
    /// A trait instance: the spec fns it needs emitted first — these
    /// get pulled into Base (transitively) so instances can stay there.
    Instance { prereq_fns: Vec<Fun> },
    /// Proof-method trait class decls: consumed by INSTANCES (which
    /// live in Base), so they route to Base too — and like instances,
    /// the spec fns their method signatures reference must be pulled
    /// into Base first (M6.5 finding: umbrella routing broke every
    /// crate whose ladder reached a proof-trait impl).
    ProofClasses { prereq_fns: Vec<Fun> },
    BcAxiom,
}

/// Fn-level references of one spec fn: body call refs + nothing else
/// (signature datatype refs point at Base, which every part imports).
fn spec_fn_refs(f: &FunctionX) -> Vec<Fun> {
    let mut refs: Vec<&Fun> = Vec::new();
    if let Some(body) = &f.body {
        dep_order::collect_fun_refs(body, &mut refs);
    }
    refs.into_iter().cloned().collect()
}

// ── W7d (bootstrap-33): defs-layer certificate wire helpers ──────────────
//
// The generate-side glue between spec-fn / datatype emission and the
// flag-gated `sst_serialize::emit_def_cert` / `emit_dt_cert` writers. Both
// are no-ops unless `--tactus-emit-cert`; the fail-loud + census discipline
// (an uncertifiable poly/curried/struct fixture is logged + skipped, never
// aborts the run) lives inside the `emit_*` entry points.

/// Emit the defs-layer `def_eq` certificate for a spec fn whose emitted
/// commands include a plain `@[reducible] def`. Only the `Command::Def` form
/// bridges — a `DefCurried` (structural-recursion curried form) or an `Axiom`
/// (bodyless / `eq_def` / builtin-bodied spec fn) has no `ldef_to_defdata`
/// mirror and is skipped. `augmented` is the same `FunctionX`
/// `spec_fn_to_ast` lowered, so its VIR fields correspond to that exact def.
fn maybe_emit_def_cert(augmented: &FunctionX, emitted: &[Command], crate_name: &str) {
    if !crate::sst_serialize::cert_emit_enabled() {
        return;
    }
    let def = match emitted.iter().find_map(|c| match c {
        Command::Def(d) => Some(d),
        _ => None,
    }) {
        Some(d) => d,
        None => return,
    };
    // A `Command::Def` implies a body (bodyless spec fns emit an `Axiom`);
    // guard anyway so the `&VirExpr` hand-off is total.
    let body = match &augmented.body {
        Some(b) => b,
        None => return,
    };
    crate::sst_serialize::emit_def_cert(
        crate_name,
        &augmented.name,
        &augmented.typ_params,
        &augmented.params,
        &augmented.ret.x.typ,
        body,
        def,
    );
}

/// Collect every emitted `Command::Datatype` (recursing into `mutual` blocks)
/// so the W7d dt-cert pass can pair each VIR datatype with its rendered form.
fn collect_emitted_datatypes<'a>(
    cmds: &'a [Command],
    out: &mut Vec<&'a crate::lean_ast::Datatype>,
) {
    for c in cmds {
        match c {
            Command::Datatype(d) => out.push(d),
            Command::Mutual(inner) => collect_emitted_datatypes(inner, out),
            _ => {}
        }
    }
}

pub(crate) fn spec_world_cmds(
    krate: &KrateX,
    // W7d: the crate name (unsanitized) — threaded only to reach the
    // flag-gated `emit_def_cert`/`emit_dt_cert` defs-layer cert writers, which
    // key their `{crate}/cert/` output dir on `sanitize(crate_name)`. Verdict-
    // neutral: a no-op unless `--tactus-emit-cert`.
    crate_name: &str,
    ectx: &crate::emit_ctx::EmitCtx,
    dep_walk_roots: &[&FunctionX],
    emit_accessors: bool,
    bc_lemma_funcs: &[&FunctionX],
    // Shared-defs mode renders with roots = ALL checkable fns — a
    // strictly wider walk than any per-fn file's, so it can reach
    // constructs whose renderers carry "unsupported" panic tripwires
    // that no per-fn render ever trips (e.g. a spec fn used only by
    // exec fns that get rejected at the SST stage, before their
    // preamble would walk). Lenient mode skips such items (loudly)
    // instead of panicking: an item nobody checkable needs costs
    // nothing — matching baseline reachability — and one somebody
    // needs produces that fn's per-fn unknown-identifier failure
    // instead of process death. Standalone renders stay strict so the
    // tripwires keep guarding per-fn emission.
    lenient: bool,
) -> Vec<Command> {
    spec_world_cmds_tagged(krate, crate_name, ectx, dep_walk_roots, emit_accessors, bc_lemma_funcs, lenient).0
}

pub(crate) fn spec_world_cmds_tagged(
    krate: &KrateX,
    // W7d: unsanitized crate name for the defs-layer cert writers (see
    // `spec_world_cmds`). Flag-gated no-op unless `--tactus-emit-cert`.
    crate_name: &str,
    ectx: &crate::emit_ctx::EmitCtx,
    dep_walk_roots: &[&FunctionX],
    emit_accessors: bool,
    bc_lemma_funcs: &[&FunctionX],
    lenient: bool,
) -> (Vec<Command>, Vec<(usize, DefsSeg)>) {
    // Returns whether the commands were actually pushed — lenient mode can
    // swallow a panic and skip; emissions that DEPEND on a prior item
    // having landed (the seq measure companion) consult the result
    // (2026-07-09 review, finding #7).
    let push_lenient = |cmds: &mut Vec<Command>, what: &str, f: &mut dyn FnMut() -> Vec<Command>| -> bool {
        if !lenient {
            cmds.extend(f());
            return true;
        }
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f())) {
            Ok(v) => {
                cmds.extend(v);
                true
            }
            Err(payload) => {
                let msg = payload.downcast_ref::<&str>().map(|s| s.to_string())
                    .or_else(|| payload.downcast_ref::<String>().cloned())
                    .unwrap_or_else(|| "<non-string panic payload>".to_string());
                eprintln!("tactus: skipped un-renderable {} in shared defs: {}", what, msg);
                false
            }
        }
    };
    let mut cmds: Vec<Command> = Vec::new();
    let mut segs: Vec<(usize, DefsSeg)> = vec![(0, DefsSeg::Base)];
    let all_fns: Vec<&FunctionX> = krate.functions.iter().map(|f| &f.x).collect();
    let spec_fn_map = dep_order::build_spec_fn_map(&all_fns);
    let mut refs =
        dep_order::collect_references(&spec_fn_map, &ectx.fn_map, &all_fns, dep_walk_roots);

    // Transitive trait-bound closure: when a trait emits its class
    // declaration, parent-trait bounds (e.g., `trait Sub: Super`
    // produces `class Sub (Self : Type) [Super Self]`) reference the
    // parent trait. The parent must therefore also be in scope. We
    // iterate to a fixed point: for each trait in refs.traits, add
    // its own typ_bound traits.
    //
    // Bounded by the number of traits in the krate — typically small.
    loop {
        let before = refs.traits.len();
        let new_parents: Vec<&str> = krate.traits.iter()
            .filter(|tr| refs.traits.contains(short_name(&tr.x.name)))
            .flat_map(|tr| tr.x.typ_bounds.iter())
            .filter_map(|bound| match &**bound {
                vir::ast::GenericBoundX::Trait(vir::ast::TraitId::Path(p), _) =>
                    Some(short_name(p)),
                _ => None,
            })
            .collect();
        for n in new_parents {
            refs.traits.insert(n);
        }
        if refs.traits.len() == before { break; }
    }

    // Decide which trait_impls will emit. Two conditions both
    // must hold:
    //
    // 1. The trait itself is reached (refs.traits contains it) —
    //    something in the proof brought the trait into scope, via
    //    typ_bounds, Dynamic-dispatch call, or the inlined-spec
    //    walk through a trait method decl.
    // 2. The implementor type is reached (refs.datatypes contains
    //    it) — the proof references the concrete type somewhere
    //    (Ctor, param type, etc.). For non-datatype implementors
    //    (primitives, type params), this check is vacuously true.
    //
    // Earlier iterations (2026-05-12) tried "any method_impl is in
    // needed_fn_set" as the gate, but it failed for default-
    // inheriting impls: when `impl Foo for Q {}` inherits a method
    // and the proof calls `q.method()`, Verus's resolution goes
    // through the trait method decl, so no specific impl method
    // appears in needed_fn_set — the gate would skip emission, but
    // the inlined ensures would still render `Foo.method q` which
    // requires the instance for Lean dispatch.
    //
    // The (trait ∩ datatype) gate captures the same property
    // structurally: if the proof reaches both the trait abstraction
    // AND the concrete implementor, the pairing IS in use, and the
    // instance is needed to bridge typeclass dispatch from the
    // trait method decl to the concrete impl.
    //
    // The set of traits whose Instance will emit is derived next —
    // those traits' classes MUST also emit (the Instance references
    // the class). This is the structural co-dependency that the
    // pre-2026-05-12 `refs.traits`-only gate hid by accident.
    let groups = dep_order::order_spec_fns(&spec_fn_map, &ectx.fn_map, &all_fns, dep_walk_roots);

    // F2a (DESIGN-lean-all-proofs-followons.md): the seq measure
    // companion below cites `seq.axiom_seq_subrange_len` by name, but
    // the axiom reaches `bc_lemma_funcs` only when some `broadcast use`
    // group happens to carry it — a file that emits `Seq.drop_first`/
    // `drop_last` without it silently lost the companion, and every
    // recursion through the drop defs failed termination (68/81
    // residual errors, DESIGN-lean-all-proofs.md §10.1). Force the
    // axiom into the schedule exactly when a drop def will emit.
    // Closure-safe: the trigger means the drop def is in `groups`, and
    // its body IS `subrange`/`len` — every name in the axiom's ensures
    // is already dep-walked. Sound by the same stipulation argument as
    // the final forced flush (vstd verified the lemma; #122). The
    // landed-gate at the companion site stays as a backstop.
    let bc_lemma_funcs: Vec<&FunctionX> = {
        let mut v = bc_lemma_funcs.to_vec();
        let drop_def_emits = groups.iter().any(|g| match g {
            dep_order::FnGroup::Single(f) => {
                let rel = crate::to_lean_type::lean_name_relative(&f.name.path);
                rel == "Seq.drop_first" || rel == "Seq.drop_last"
            }
            dep_order::FnGroup::Mutual(_) => false,
        });
        let ax_present = v.iter().any(|a| {
            crate::to_lean_type::lean_name_relative(&a.name.path)
                == "seq.axiom_seq_subrange_len"
        });
        if drop_def_emits && !ax_present {
            if let Some(ax) = all_fns.iter().find(|a| {
                crate::to_lean_type::lean_name_relative(&a.name.path)
                    == "seq.axiom_seq_subrange_len"
            }) {
                v.push(ax);
            }
        }
        v
    };
    let bc_lemma_funcs: &[&FunctionX] = &bc_lemma_funcs;

    // Un-emittable traits: a trait whose `class` we can't render because
    // at least one method decl is absent from the merged krate's function
    // map — i.e. stripped cross-crate (e.g. `core::clone::Clone::clone`,
    // dragged in by a `HashMap` bound). Without the method's `FunctionX`
    // we can't render its class field faithfully, so we skip the class
    // AND every instance of it; code that dispatches through such a trait
    // then fails gracefully (unresolved reference → "tactus_auto failed")
    // instead of panicking in `trait_to_ast`. That panic stays as a
    // tripwire for genuine SAME-crate bugs (where every method should be
    // present). Shared with `collect_broadcast_lemma_funs`'s broadcast-
    // path filter via `expr_shared::unemittable_traits` (#122).

    let instances_to_emit: Vec<(&TraitImpl, Vec<&FunctionX>)> = krate.trait_impls.iter()
        .filter_map(|ti| {
            let trait_short = short_name(&ti.x.trait_path);
            if !refs.traits.contains(trait_short) { return None; }
            // Skip instances of un-emittable (shell) traits. The shell
            // CLASS still emits (a harmless empty marker that resolves any
            // stray reference), but its INSTANCES must NOT: now that
            // `drop_unemittable_trait_bounds` strips every `[clone.Clone
            // X]` / `[cmp.PartialEq X]` bound at the rendering chokepoint,
            // nothing ever synthesizes a shell-trait instance — so they're
            // dead. Worse, they DANGLE: a shell instance like `{A}
            // [marker.Copy A] : clone.Clone A` carries its own bound on
            // ANOTHER trait (`marker.Copy`), which may not be emitted in
            // this crate (it isn't, absent a `HashMap` to pull it in) →
            // "Unknown identifier marker.Copy". (An earlier RC1 revision
            // emitted these instances; the HashMap case only elaborated
            // because marker.Copy happened to be reached there. Surfaced
            // by a coverage probe on a bare `<T: Clone>` fn — #122.)
            if ectx.unemittable.contains(&ti.x.trait_path) { return None; }
            // Implementor type check: trait_typ_args[0] is Self.
            // For Dt::Path (a concrete user datatype), require it
            // to be in refs.datatypes. For anything else (primitive,
            // generic, tuple), vacuously pass — those don't have
            // emit-side declarations that could fail to materialize.
            let implementor_reached = match ti.x.trait_typ_args.first().map(|t| &**t) {
                Some(TypX::Datatype(Dt::Path(p), _, _)) =>
                    refs.datatypes.contains(short_name(p)),
                _ => true,
            };
            if !implementor_reached { return None; }
            let method_impls: Vec<&FunctionX> = all_fns.iter()
                .filter(|f| matches!(&f.kind, FunctionKind::TraitMethodImpl { impl_path, .. }
                    if impl_path == &ti.x.impl_path))
                .copied()
                .collect();
            Some((ti, method_impls))
        })
        .collect();
    // Includes each emitted instance's PREMISE-bound traits alongside
    // its own trait: a blanket instance like vstd's Copy→Clone
    // (`instance [marker.Copy A] : clone.Clone A`) references the
    // premise class in its binder list, so the class must emit or the
    // instance is an unknown-identifier error (found via
    // tactus-group-theory's apply_hom_symbol_exec). Marker shells are
    // contentless, so over-pulling is sound and cheap.
    let traits_with_emitted_impl: std::collections::HashSet<&str> = instances_to_emit.iter()
        .flat_map(|(ti, _)| {
            std::iter::once(short_name(&ti.x.trait_path)).chain(
                ti.x.typ_bounds.iter().filter_map(|b| match &**b {
                    GenericBoundX::Trait(vir::ast::TraitId::Path(p), _) => Some(short_name(p)),
                    _ => None,
                }),
            )
        })
        .collect();

    // Per-impl projection substitution (Bug B step 2). One ImplSubst
    // per `impl_path`, built once from the impl's signature typs
    // (trait_typ_args + assoc_type_impl values + method ret/param
    // typs). Consumed by both `trait_impl_to_ast` (instance side)
    // and `impl_subst::maybe_augment_impl_method` (impl method
    // standalone side) so both sites see the same fresh-binder
    // names. See `impl_subst.rs` module docs.

    // Compute per-impl natural-name prefix `[Self, Trait, "impl"]`
    // for impl method standalone defs. The full def path becomes
    // `<Self>.<Trait>.impl.<method>` (e.g., `Bar.Counter.impl.raw`,
    // `Wrap.View.impl.view`).
    //
    // The `impl` marker between Trait and method is load-bearing.
    // Without it, `Wrap.View.view`'s body would have a Lean
    // namespace-resolution conflict: Lean climbs namespaces looking
    // for `View.view`, reaches `Wrap.View` namespace (which is the
    // def's prefix namespace), would find the def itself as the
    // match, producing a recursive self-reference instead of
    // resolving to the trait class method `test_crate.View.view`.
    //
    // With `Wrap.View.impl.view`, the namespace stack is `Wrap.View
    // .impl → Wrap.View → Wrap → test_crate`. Lookup of `View.view`
    // climbs past `Wrap.View.impl` and `Wrap.View` (no `view`
    // declaration at either), then past `Wrap` (no `Wrap.View.view`
    // declaration — only the `Wrap.View.impl` namespace exists),
    // and lands at `test_crate.View.view`. ✓
    //
    // Collisions are handled by construction for most cases (different
    // traits → different paths; inherent vs trait → different paths
    // since inherent stays at Verus's `impl__N.method` emission).
    // The remaining edge: `impl Foo<int> for Bar` and `impl Foo<bool>
    // for Bar` both map to `Bar.Foo.impl.method`. Counted below;
    // collisions fall back to `impl__N.method`.
    let impl_name_prefixes: std::collections::HashMap<vir::ast::Path, Vec<vir::ast::Ident>> = {
        use std::collections::HashMap;
        let impl_marker: vir::ast::Ident = std::sync::Arc::new("impl".to_string());
        // First pass: build tentative `[Self, Trait, "impl"]` prefix
        // per impl. Collect (prefix, method_short) pairs to detect
        // multi-impl name collisions.
        let mut per_method: HashMap<(Vec<vir::ast::Ident>, String), usize> = HashMap::new();
        let mut tentative_per_impl: HashMap<vir::ast::Path, Vec<vir::ast::Ident>> = HashMap::new();
        for (ti, method_impls) in &instances_to_emit {
            let Some(self_typ) = ti.x.trait_typ_args.first() else { continue; };
            let Some(self_short) = crate::to_lean_type::type_short_name(self_typ) else { continue; };
            let trait_short = crate::to_lean_type::short_name(&ti.x.trait_path).to_string();
            let prefix = vec![
                std::sync::Arc::new(self_short),
                std::sync::Arc::new(trait_short),
                impl_marker.clone(),
            ];
            for f in method_impls {
                if let Some(method_short) = f.name.path.segments.last().map(|s| s.to_string()) {
                    *per_method.entry((prefix.clone(), method_short)).or_insert(0) += 1;
                }
            }
            tentative_per_impl.insert(ti.x.impl_path.clone(), prefix);
        }
        // Second pass: only rename when NONE of the impl's method
        // names collide with another impl's at the same prefix.
        let mut result: HashMap<vir::ast::Path, Vec<vir::ast::Ident>> = HashMap::new();
        for (ti, method_impls) in &instances_to_emit {
            let Some(prefix) = tentative_per_impl.get(&ti.x.impl_path) else { continue; };
            let any_collision = method_impls.iter().any(|f| {
                let Some(ms) = f.name.path.segments.last().map(|s| s.to_string()) else {
                    return false;
                };
                per_method.get(&(prefix.clone(), ms)).copied().unwrap_or(0) > 1
            });
            if !any_collision {
                result.insert(ti.x.impl_path.clone(), prefix.clone());
            }
        }
        result
    };

    let impl_substs: std::collections::HashMap<vir::ast::Path, crate::impl_subst::ImplSubst> =
        instances_to_emit.iter().map(|(ti, method_impls)| {
            let assoc_types_for_impl: Vec<&AssocTypeImplX> = krate.assoc_type_impls.iter()
                .filter(|a| a.x.impl_path == ti.x.impl_path)
                .map(|a| &a.x)
                .collect();
            // Iterator over all typs that may contain projections
            // worth lifting: instance target args, assoc-type-impl
            // values, and each impl method's return + param typs.
            let typs_iter = ti.x.trait_typ_args.iter()
                .chain(assoc_types_for_impl.iter().map(|a| &a.typ))
                .chain(method_impls.iter().flat_map(|f| {
                    std::iter::once(&f.ret.x.typ)
                        .chain(f.params.iter().map(|p| &p.x.typ))
                }));
            let mut subst = crate::impl_subst::ImplSubst::build(
                &ti.x.typ_params,
                &ti.x.typ_bounds,
                typs_iter,
                &ectx.trait_outparams,
            );
            let name_prefix = impl_name_prefixes.get(&ti.x.impl_path).cloned();
            subst.set_method_context(&ti.x, method_impls, name_prefix);
            (ti.x.impl_path.clone(), subst)
        }).collect();

    // Split traits-to-emit into two groups by whether any of their
    // methods are proof-fn (Mode::Proof). Proof-fn class fields render
    // their ensures INLINE in the class declaration; the ensures can
    // reference free-standing spec fns, which must be in scope at
    // emission time. So proof-fn-bearing classes emit AFTER spec fns.
    //
    // Classes WITHOUT proof-fn methods emit BEFORE spec fns (old
    // behavior). This matches the pre-2026-05-15 ordering for the
    // common case: spec fns can reference class methods via typeclass
    // dispatch (e.g., `spec fn use_size<T: HasSize>(x: T) -> Nat {
    // x.size() }`), which requires the class to be in scope at the
    // spec fn's emission.
    //
    // True cyclic dependencies (class A's proof-fn ensures references
    // free-standing spec fn F, AND F references class A via typeclass
    // dispatch) would need a topological-sort approach or a `mutual`
    // emission. No current test exercises this; flag as future work
    // if it surfaces.
    let trait_has_proof_method = |tr: &TraitX| -> bool {
        tr.methods.iter().any(|m| {
            ectx.fn_map.get(m)
                .map(|f| matches!(f.mode, vir::ast::Mode::Proof))
                .unwrap_or(false)
        })
    };
    // Shared emission gate for both class-emission loops (the only
    // difference between them is the `trait_has_proof_method` polarity +
    // ordering relative to spec fns). Emit a trait's `class` iff it's
    // emittable AND something brings it into scope (a typ_bound /
    // dispatch reference, or an instance of it will emit).
    // Un-emittable traits now emit as method-less *marker shells*
    // (drop the stripped methods, keep the header) rather than being
    // skipped — see `trait_to_ast`'s `shell` param. Skipping left
    // dangling `[clone.Clone Self]` superclass binders on emittable
    // subclasses (`marker.Copy`), which failed to elaborate and
    // cascaded; the shell makes those binders resolve. The shell
    // asserts nothing (no methods, no laws), so it's sound and is the
    // trait-level analog of external-body opaque-type emission (#122).
    let should_emit_class = |tr: &TraitX| -> bool {
        let n = short_name(&tr.name);
        refs.traits.contains(n) || traits_with_emitted_impl.contains(n)
    };
    for tr in &krate.traits {
        if !trait_has_proof_method(&tr.x) && should_emit_class(&tr.x) {
            push_lenient(&mut cmds, "trait class",
                &mut || vec![Command::Class(to_lean_fn::trait_to_ast(&tr.x, ectx))]);
        }
    }

    // Synthetic instances for the Fn-trait family at LITERAL ARROW types
    // (BUG-vstd-preamble-cluster.md bug 1, Fn half). Verus spec closures
    // render as Lean arrows (`Int → A`, `TypX::SpecFn`), and vstd
    // signatures like `Seq::new(len, f: impl Fn(int) -> A)` emit
    // `[ops.function.Fn impl_1 Int Output]` brackets that must
    // synthesize AT the arrow type — both in goals applying `Seq.new` to
    // a closure and in the emitted seq broadcast-axiom DECLARATIONS
    // themselves (`axiom_seq_new_len`'s `(f : Int → A)`). Rust-side each
    // closure is a unique anonymous type whose Fn impl the compiler
    // provides; the Lean rendering collapses closures to arrows, so the
    // compiler-provided instance is synthesized here (vstd's Ref/Box
    // blankets arrive as ordinary krate instances; the arrow one can't —
    // no Rust type names it). The blanket `marker.Tuple` instance is
    // sound the same way marker shells are: a contentless class asserts
    // nothing. Each emits only when its class was emitted; ordered
    // parents-first (FnOnce → FnMut → Fn) so each `extends` field
    // synthesizes from the previous.
    {
        use crate::lean_ast::{BinOp, BinderKind, Expr as LExpr, ExprNode, Binder as LBinder};
        // `lean_name_relative`: this set is keyed against literal names
        // below (`emitted.contains("marker.Tuple")`) — a key set, not Lean
        // text, so it must not carry the root-anchor prefix.
        let emitted: std::collections::HashSet<String> = krate.traits.iter()
            .filter(|tr| should_emit_class(&tr.x))
            .map(|tr| crate::to_lean_type::lean_name_relative(&tr.x.name))
            .collect();
        let tp = |n: &str| LExpr::var_tp(n);
        // These names are literals (no VIR path to route through
        // `lean_name`), so qualify with the crate namespace by hand —
        // Option B renders every crate-internal global as its full
        // dotted name at root scope (no namespace wrapper to resolve
        // the relative form anymore).
        let qual = |n: &str| match crate::to_lean_type::crate_ns() {
            Some(ns) => format!("{}.{}", ns, n),
            None => n.to_string(),
        };
        let arrow = || LExpr::new(ExprNode::BinOp {
            op: BinOp::Implies,
            lhs: Box::new(tp("A")),
            rhs: Box::new(tp("B")),
        });
        if emitted.contains("marker.Tuple") {
            cmds.push(Command::Instance(crate::lean_ast::Instance {
                binders: vec![LBinder::typ_param("A", BinderKind::Implicit)],
                target: LExpr::app(LExpr::var_lit(&qual("marker.Tuple")), vec![tp("A")]),
                methods: vec![],
            }));
        }
        for cls in ["ops.function.FnOnce", "ops.function.FnMut", "ops.function.Fn"] {
            if emitted.contains(cls) {
                cmds.push(Command::Instance(crate::lean_ast::Instance {
                    binders: vec![
                        LBinder::typ_param("A", BinderKind::Implicit),
                        LBinder::typ_param("B", BinderKind::Implicit),
                        LBinder::instance(
                            LExpr::app(LExpr::var_lit(&qual("marker.Tuple")), vec![tp("A")])),
                    ],
                    target: LExpr::app(LExpr::var_lit(&qual(cls)), vec![arrow(), tp("A"), tp("B")]),
                    methods: vec![],
                }));
            }
        }
    }

    // Filter datatypes to those referenced by the proof/exec fns and
    // not synthesized closure types (#93), then transitively close over
    // field-type references and group into SCCs so mutually recursive
    // datatypes (#109) emit as `mutual ... end` blocks.
    //
    // Seed extra datatype roots from the EMITTED instance heads
    // (trait_typ_args + assoc-type values). An external-body opaque type
    // that appears ONLY in an instance head — e.g. `DefaultHasher` in
    // the synthesized `instance : hash.BuildHasher RandomState
    // DefaultHasher` — is never reached by the fn-body dep-walk, so its
    // `axiom T : Type` would never emit ("Unknown constant
    // DefaultHasher"). Walking the instance heads we're about to emit
    // closes that gap. (#122 RC3)
    let mut instance_seed_paths: std::collections::HashSet<&vir::ast::Path> =
        std::collections::HashSet::new();
    for (ti, _) in &instances_to_emit {
        for t in ti.x.trait_typ_args.iter() {
            dep_order::walk_typ_paths(t, &mut |q| { instance_seed_paths.insert(q); });
        }
        for a in krate.assoc_type_impls.iter().filter(|a| a.x.impl_path == ti.x.impl_path) {
            dep_order::walk_typ_paths(&a.x.typ, &mut |q| { instance_seed_paths.insert(q); });
        }
    }
    let referenced_dts = collect_referenced_datatypes(krate, &refs, &instance_seed_paths);
    // Set of paths for external-body datatypes (`transparency == Never`).
    // Used by `datatype_decl_cmd` to drop `deriving Inhabited` when a
    // variant field references such a type — Lean's auto-derived
    // Inhabited produces a *computable* instance that would depend on
    // the external-body's axiomatic Inhabited (which has no executable
    // code), failing the compiler IR check. A manual `noncomputable
    // instance` is emitted instead by `datatype_inhabited_instance_cmd`.
    let external_body_paths: std::collections::HashSet<&vir::ast::Path> = referenced_dts.iter()
        .filter(|dt| matches!(dt.transparency, DatatypeTransparency::Never))
        .filter_map(|dt| match &dt.name {
            Dt::Path(p) => Some(p),
            Dt::Tuple(_) => None,
        })
        .collect();
    for group in dep_order::order_datatypes(&referenced_dts) {
        push_lenient(&mut cmds, "datatype group",
            &mut || to_lean_fn::datatype_group_to_cmds(&group, emit_accessors, &external_body_paths));
    }

    // W7d: emit the defs-layer `dt_eq` certificate for each datatype that
    // was actually emitted as an `inductive` above. A flag-gated no-op (the
    // default emit path is untouched); the reference transcriber gates
    // poly/tuple/struct fixtures fail-loud + census inside `emit_dt_cert`.
    // Done as a post-loop pass (not inside the loop closure) purely so the
    // group-emit line stays byte-identical; matched by rendered name against
    // the just-pushed `Command::Datatype`s so a mutual SCC pairs correctly.
    if crate::sst_serialize::cert_emit_enabled() {
        let mut emitted_dts: Vec<&crate::lean_ast::Datatype> = Vec::new();
        collect_emitted_datatypes(&cmds, &mut emitted_dts);
        for dtx in referenced_dts.iter() {
            let want = match &dtx.name {
                Dt::Path(p) => crate::to_lean_type::lean_name(p),
                Dt::Tuple(_) => continue,
            };
            if let Some(dt) = emitted_dts.iter().find(|d| d.name == want) {
                crate::sst_serialize::emit_dt_cert(
                    crate_name, &dtx.name, &dtx.typ_params, &dtx.variants, dt);
            }
        }
    }

    // TraitMethodImpl spec fns ARE emitted as standalone defs in
    // addition to their Instance method. This is the canonical Lean
    // idiom for instance fields with interdependencies: define a
    // helper in the type's namespace (the standalone def) and have
    // the instance reference it. Lean's `instance` construction
    // can't forward-reference siblings (instances aren't available
    // for synthesis during their own definition — see Lean reference
    // manual § "Instance Declarations"), so an impl method whose
    // body references another sibling spec method needs the
    // standalone form to resolve. Call sites in goals/ensures use
    // the class-qualified form via typeclass dispatch
    // (`to_lean_expr::call_to_node`); instance method bodies use
    // bare standalone-def references via `strip_class_qualifier`.
    // Lift associated-type projections (`<X as Trait>::N` over an
    // abstract type-param, un-renderable because Tactus emits assoc types
    // as `outParam`). TraitMethodImpl methods use the pre-built per-impl
    // subst (with method_context for sibling rewrites + name prefix);
    // standalone generic spec fns build their own subst from their own
    // typ_params/bounds (RC2 — e.g. `hash_map_deep_view_impl`). Both are
    // no-ops for fns without projections.
    // `[Nonempty T]` inference (#122 layer 5): a fn that (transitively)
    // `choose`s over type-param T renders `Classical.epsilon`, which Lean
    // requires `[Nonempty T]` for. Computed once over the call graph; the
    // synthetic bound is appended at augment time so it rides the ordinary
    // trait-bound rendering and never leaks into class/dep emission.
    // Multi-variant datatype paths, for Seed 3 (accessor uses demand
    // `[Nonempty A]` — see `compute_nonempty_needs`).
    let multi_variant_dts: std::collections::HashSet<&vir::ast::Path> = krate.datatypes.iter()
        .filter(|d| d.x.variants.len() > 1)
        .filter_map(|d| match &d.x.name {
            vir::ast::Dt::Path(p) => Some(p),
            vir::ast::Dt::Tuple(_) => None,
        })
        .collect();
    let nonempty_needs = crate::nonempty::compute_nonempty_needs(
        &all_fns,
        &|p| multi_variant_dts.contains(p),
    );
    let add_nonempty = |f: vir::ast::FunctionX, name: &Fun| -> vir::ast::FunctionX {
        match nonempty_needs.get(name) {
            Some(need) => crate::nonempty::add_fn_nonempty_bounds(f, need),
            None => f,
        }
    };
    // Nonempty bounds are added BEFORE impl_subst augmentation (N1):
    // a projection-typed need (`[Nonempty <X as Trait>::N]`) must ride
    // `augment_function`'s existing-bound rewrite so it lands on the
    // synthetic `_tactus_assoc_*` binder. Param-indexed needs are
    // order-insensitive (augmentation APPENDS typ params, so
    // pre-augment indices stay valid).
    let augment = |f: &vir::ast::FunctionX| -> vir::ast::FunctionX {
        let with_ne = add_nonempty(f.clone(), &f.name);
        if matches!(f.kind, FunctionKind::TraitMethodImpl { .. }) {
            crate::impl_subst::maybe_augment_impl_method(&with_ne, &impl_substs)
        } else {
            crate::impl_subst::maybe_augment_standalone_fn(&with_ne, &ectx.trait_outparams)
        }
    };
    // Per-instance / proof-class emit helpers — take `&mut cmds` rather
    // than capturing it, so they coexist with the group-emit borrows.
    let emit_instance = |cmds: &mut Vec<Command>, j: usize| {
        let (ti, method_impls) = &instances_to_emit[j];
        let assoc_types: Vec<&AssocTypeImplX> = krate.assoc_type_impls.iter()
            .filter(|a| a.x.impl_path == ti.x.impl_path)
            .map(|a| &a.x)
            .collect();
        let empty_subst = crate::impl_subst::ImplSubst::default();
        let subst = impl_substs.get(&ti.x.impl_path).unwrap_or(&empty_subst);
        // `[Nonempty T]` bounds the instance inherits from its method-impl
        // fns (e.g. the `DeepView (HashMap …)` instance whose `deep_view`
        // calls the choosing `hash_map_deep_view_impl`).
        let ne_bounds: Vec<vir::ast::GenericBound> = crate::nonempty::instance_nonempty_bounds(
            &nonempty_needs, method_impls, &ti.x.typ_params)
            .iter()
            // Projection-typed bounds must land on the synthetic
            // `_tactus_assoc_*` binders, same as the fn-side path
            // (which rides `augment_function`'s bound rewrite).
            .map(|b| subst.rewrite_bound(b))
            .collect();
        cmds.push(Command::Instance(
            to_lean_fn::trait_impl_to_ast(&ti.x, method_impls, &assoc_types, subst, &ne_bounds, ectx)
        ));
    };
    // Spec fns the proof-class method SIGNATURES reference (requires/
    // ensures exprs of TraitMethodDecl fns of qualifying traits) — the
    // Base pull for ProofClasses segs, mirroring Instance prereqs.
    let proof_class_prereq_fns: Vec<Fun> = {
        let qualifying: std::collections::HashSet<&vir::ast::Path> = krate.traits.iter()
            .filter(|tr| trait_has_proof_method(&tr.x) && should_emit_class(&tr.x))
            .map(|tr| &tr.x.name)
            .collect();
        let mut refs: Vec<&Fun> = Vec::new();
        for f in krate.functions.iter().map(|f| &f.x) {
            if let FunctionKind::TraitMethodDecl { trait_path, .. } = &f.kind {
                if qualifying.contains(trait_path) {
                    for e in f.require.iter().chain(f.ensure.0.iter()) {
                        dep_order::collect_fun_refs(e, &mut refs);
                    }
                }
            }
        }
        let mut seen = std::collections::HashSet::new();
        refs.into_iter().filter(|f| seen.insert((*f).clone())).cloned().collect()
    };
    // Classes WITH proof-fn methods: their Prop-typed fields reference
    // spec fns, and proof-trait instances reference them — so they sit at
    // the spec-fn/instance boundary (after the last spec-fn group).
    let emit_proof_classes = |cmds: &mut Vec<Command>| {
        for tr in &krate.traits {
            if trait_has_proof_method(&tr.x) && should_emit_class(&tr.x) {
                cmds.push(Command::Class(to_lean_fn::trait_to_ast(&tr.x, ectx)));
            }
        }
    };

    // Topologically order spec-fn groups and trait instances together so
    // the spec-fn↔instance dependency DAG is respected in one pass: an
    // instance a spec-fn body dispatches to (`hash_map_deep_view_impl`'s
    // `m@` → `View (HashMap …)`) emits BEFORE that spec fn; an instance
    // whose body references a spec-fn def (`DeepView (HashMap …)` →
    // `hash_map_deep_view_impl`) emits AFTER it. Instances nothing
    // dispatches to keep their trailing slot (zero drift). See
    // `dep_order::order_emission`.
    let instance_keys: Vec<_> = instances_to_emit.iter()
        .map(|(ti, methods)| (&ti.x.impl_path, methods.clone()))
        .collect();
    let order = dep_order::order_emission(&groups, &instance_keys);
    let last_group_pos = order.iter()
        .rposition(|s| matches!(s, dep_order::EmitStep::Group(_)));

    // Broadcast axioms: emit each at the EARLIEST point its own references
    // allow (B3, DESIGN-lean-all-proofs-bugs.md). They used to emit LAST,
    // after every def — but a recursive def's `decreasing_by` tactic can
    // only use axioms that PRECEDE it textually, and the seq length axioms
    // (`axiom_seq_subrange_len` etc.) are exactly what measures recursing
    // through `drop_first`/`drop_last` need. An axiom is ready once every
    // spec-fn group / trait instance its require/ensure references has been
    // processed; axioms with no such references flush before the first
    // group (datatypes and classes are already above). Soundness unchanged
    // (same stipulation argument as before — vstd verified the lemma;
    // emission position only affects visibility).
    let fn_group_of: std::collections::HashMap<&Fun, usize> = {
        let mut m = std::collections::HashMap::new();
        for (i, g) in groups.iter().enumerate() {
            match g {
                FnGroup::Single(f) => { m.insert(&f.name, i); }
                FnGroup::Mutual(fs) => { for f in fs { m.insert(&f.name, i); } }
            }
        }
        m
    };
    let instance_of: std::collections::HashMap<&vir::ast::Path, usize> = instance_keys.iter()
        .enumerate()
        .map(|(j, (ip, _))| (*ip, j))
        .collect();
    let axiom_deps: Vec<(std::collections::HashSet<usize>, std::collections::HashSet<usize>)> =
        bc_lemma_funcs.iter().map(|f| {
            let mut gdeps = std::collections::HashSet::new();
            let mut ideps = std::collections::HashSet::new();
            for spec in f.require.iter().chain(f.ensure.0.iter()).chain(f.ensure.1.iter()) {
                // Fun-level deps via dep_order's OWN collector — it covers
                // ConstVar / StaticVar / ExecFnByName / Fuel / the
                // DynamicResolved target, which a hand-rolled Call-only
                // match missed (2026-07-09 review, finding #5: a broadcast
                // lemma mentioning a spec const flushed before the const's
                // def — reproduced as a forward reference in the defs
                // module).
                let mut funs: Vec<&vir::ast::Fun> = Vec::new();
                dep_order::collect_fun_refs(spec, &mut funs);
                for fun in funs {
                    if let Some(&gi) = fn_group_of.get(fun) {
                        gdeps.insert(gi);
                    }
                }
                // Instance deps: the dispatch dictionaries on calls.
                dep_order::walk_expr(spec, &mut |e| {
                    if let ExprX::Call(CallTarget::Fun(_, _, _, impl_paths, _, _), _, _) = &e.x {
                        for ip in impl_paths.iter() {
                            if let ImplPath::TraitImplPath(p) = ip {
                                if let Some(&j) = instance_of.get(p) {
                                    ideps.insert(j);
                                }
                            }
                        }
                    }
                });
            }
            (gdeps, ideps)
        }).collect();
    // Index of the subrange-len axiom among the broadcast axioms — the
    // seq measure companion cites it, so its successful emission gates
    // the companion (finding #7).
    let subrange_ax_idx: Option<usize> = bc_lemma_funcs.iter().position(|a| {
        crate::to_lean_type::lean_name_relative(&a.name.path) == "seq.axiom_seq_subrange_len"
    });
    let mut axiom_done: Vec<bool> = vec![false; bc_lemma_funcs.len()];
    // Whether each axiom's push actually landed (vs lenient-skipped) —
    // consulted by the seq measure companion gate (finding #7).
    let mut axiom_ok: Vec<bool> = vec![false; bc_lemma_funcs.len()];
    let mut processed_groups: std::collections::HashSet<usize> = std::collections::HashSet::new();
    let mut processed_instances: std::collections::HashSet<usize> = std::collections::HashSet::new();
    // `force`: final flush — emit stragglers even if a dep was never
    // processed (lenient mode can skip groups; the axiom must still land,
    // matching the old always-at-the-end behavior).
    let flush_ready_axioms = |cmds: &mut Vec<Command>,
                              done: &mut Vec<bool>,
                              ok: &mut Vec<bool>,
                              pg: &std::collections::HashSet<usize>,
                              pi: &std::collections::HashSet<usize>,
                              force: bool| {
        for (ai, f) in bc_lemma_funcs.iter().enumerate() {
            if done[ai] {
                continue;
            }
            // The subrange-len axiom is cited by the seq measure
            // companion FROM ITS OWN PART (parts cannot import the
            // umbrella) — the companion site emits it in-part. Only
            // the final forced flush may emit it here (crates whose
            // closure never reaches drop_first/drop_last).
            if !force && Some(ai) == subrange_ax_idx {
                continue;
            }
            let (gd, id) = &axiom_deps[ai];
            if force || (gd.iter().all(|g| pg.contains(g)) && id.iter().all(|j| pi.contains(j))) {
                done[ai] = true;
                // Lift assoc-type projections in the lemma's ensure/require
                // (e.g. `axiom_hashmap_deepview_borrow`'s `<K as DeepView>::V`)
                // — same generalized projection-lifting as standalone spec
                // fns. No-op for projection-free lemmas (the common case).
                ok[ai] = push_lenient(cmds, "broadcast axiom", &mut || {
                    // A lemma whose facts dispatch to a `choose`-using fn
                    // needs `[Nonempty T]` too. Nonempty bounds FIRST,
                    // augmentation second (same order as `augment`) —
                    // projection-typed bounds must ride the bound rewrite
                    // onto the synthetic `_tactus_assoc_*` binders.
                    let with_ne = add_nonempty((*f).clone(), &f.name);
                    let augmented = crate::impl_subst::maybe_augment_standalone_fn(
                        &with_ne,
                        &ectx.trait_outparams,
                    );
                    vec![to_lean_fn::broadcast_lemma_axiom_cmd(&augmented, ectx)]
                });
            }
        }
    };
    // Partition placement (M6 defs): every mid-stream axiom flush is
    // bracketed as DefsSeg::BcAxiom so the axioms land in the UMBRELLA
    // (which imports every part). Without the bracket they ride the
    // enclosing Base-tagged gap — and all Base ranges concatenate into
    // the FIRST part, physically placing axioms before their deps'
    // declarations in later parts (post-merge census regression:
    // `Unknown constant Seq.empty` in TactusDefs_lib__base).
    segs.push((cmds.len(), DefsSeg::BcAxiom));
    flush_ready_axioms(&mut cmds, &mut axiom_done, &mut axiom_ok, &processed_groups, &processed_instances, false);
    segs.push((cmds.len(), DefsSeg::Base));

    // No spec-fn groups at all: proof classes have nothing to wait on.
    if last_group_pos.is_none() {
        segs.push((cmds.len(), DefsSeg::ProofClasses {
            prereq_fns: proof_class_prereq_fns.clone(),
        }));
        push_lenient(&mut cmds, "proof-method trait classes", &mut || {
            let mut tmp = Vec::new();
            emit_proof_classes(&mut tmp);
            tmp
        });
        segs.push((cmds.len(), DefsSeg::Base));
    }
    // One-shot flag for the drop-k subrange-tail companion (see its
    // emission site below): first drop-head pass wins.
    let mut subrange_tail_companion_emitted = false;
    for (pos, step) in order.iter().enumerate() {
        // Whether this step's own emission landed (vs lenient-skipped) —
        // gates dependent follow-ups (the seq measure companion).
        let mut step_pushed = false;
        match step {
            dep_order::EmitStep::Group(i) => match &groups[*i] {
                FnGroup::Single(f) => {
                    if lenient && body_references_builtin_spec_fun(f) {
                        // Prop-returning: emit an uninterpreted
                        // signature axiom so dependents (e.g. vstd's
                        // `cloned` → `strictly_cloned`) stay
                        // renderable. Others: skip as before. NOT
                        // `continue` — the loop tail's proof-class
                        // emission must still run when this is the
                        // last group.
                        if let Some(ax) = to_lean_fn::builtin_spec_fn_signature_axiom(f, ectx) {
                            segs.push((cmds.len(), DefsSeg::FnGroup {
                                fns: vec![f.name.clone()], refs: spec_fn_refs(f),
                            }));
                            cmds.push(ax);
                            segs.push((cmds.len(), DefsSeg::Base));
                        } else {
                            eprintln!(
                                "tactus: skipped builtin-bodied spec fn `{}` in shared defs (no Lean form for BuiltinSpecFun)",
                                short_name(&f.name.path));
                        }
                    } else {
                    segs.push((cmds.len(), DefsSeg::FnGroup {
                        fns: vec![f.name.clone()], refs: spec_fn_refs(f),
                    }));
                    step_pushed = push_lenient(&mut cmds, "spec fn", &mut || {
                        let augmented = augment(f);
                        let out = to_lean_fn::spec_fn_to_ast(&augmented, ectx);
                        // W7d: emit the defs-layer `def_eq` cert for the
                        // emitted `def` (flag-gated no-op; fail-loud + census
                        // inside `emit_def_cert`). Inside the closure so the
                        // panic-catch wraps it too.
                        maybe_emit_def_cert(&augmented, &out, crate_name);
                        out
                    });
                    // bootstrap-47: for a suffix-recursive spec fn (e.g.
                    // `drop_base_run`), emit its `{fn}_len_le` monotonicity
                    // companion RIGHT AFTER the def, riding this fn's own
                    // FnGroup seg — so a later consumer (`split_q`, same or
                    // an importing part) resolves it via the part-import
                    // chain — and register its name so that consumer's
                    // `decreasing_by` chaining rung cites it. Gated on the
                    // def having landed (`step_pushed`) and on `push_lenient`.
                    if step_pushed {
                        if let Some((mono_name, cmd)) =
                            seq_suffix_mono_companion_cmd(f, &all_fns)
                        {
                            if push_lenient(&mut cmds, "seq suffix mono companion",
                                &mut || vec![cmd.clone()])
                            {
                                to_lean_fn::register_suffix_mono_name(mono_name);
                            }
                        }
                    }
                    segs.push((cmds.len(), DefsSeg::Base));
                    }
                }
                FnGroup::Mutual(fns) => {
                    if lenient && fns.iter().any(|f| body_references_builtin_spec_fun(f)) {
                        // Signature axioms don't need the mutual
                        // block (no bodies); all-or-nothing per group
                        // so intra-group references stay resolvable.
                        let axioms: Vec<_> = fns.iter()
                            .filter_map(|f| to_lean_fn::builtin_spec_fn_signature_axiom(f, ectx))
                            .collect();
                        if axioms.len() == fns.len() {
                            segs.push((cmds.len(), DefsSeg::FnGroup {
                                fns: fns.iter().map(|f| f.name.clone()).collect(),
                                refs: fns.iter().flat_map(|f| spec_fn_refs(f)).collect(),
                            }));
                            cmds.extend(axioms);
                            segs.push((cmds.len(), DefsSeg::Base));
                        } else {
                            eprintln!(
                                "tactus: skipped builtin-bodied mutual spec-fn group in shared defs (no Lean form for BuiltinSpecFun)");
                        }
                    } else {
                    segs.push((cmds.len(), DefsSeg::FnGroup {
                        fns: fns.iter().map(|f| f.name.clone()).collect(),
                        refs: fns.iter().flat_map(|f| spec_fn_refs(f)).collect(),
                    }));
                    push_lenient(&mut cmds, "mutual spec fns", &mut || {
                        // Sibling references inside the `mutual` block
                        // render as full dotted names like everything
                        // else — Lean resolves mutual-group cross-refs
                        // by declared name (Option B; the former
                        // relative-rendering machinery is retired).
                        let inner: Vec<Command> = fns.iter()
                            .flat_map(|f| {
                                let augmented = augment(f);
                                let out = to_lean_fn::spec_fn_to_ast(&augmented, ectx);
                                // W7d: per-fn `def_eq` cert (flag-gated no-op).
                                maybe_emit_def_cert(&augmented, &out, crate_name);
                                out
                            })
                            .collect();
                        vec![Command::Mutual(inner)]
                    });
                    segs.push((cmds.len(), DefsSeg::Base));
                    }
                }
            },
            dep_order::EmitStep::Instance(j) => {
                let prereq_fns: Vec<Fun> = instance_keys.get(*j)
                    .map(|(_, methods)| methods.iter()
                        .flat_map(|m| {
                            std::iter::once(m.name.clone())
                                .chain(spec_fn_refs(m))
                        })
                        .collect())
                    .unwrap_or_default();
                segs.push((cmds.len(), DefsSeg::Instance { prereq_fns }));
                step_pushed = push_lenient(&mut cmds, "trait instance", &mut || {
                    let mut tmp = Vec::new();
                    emit_instance(&mut tmp, *j);
                    tmp
                });
                segs.push((cmds.len(), DefsSeg::Base));
            }
        }
        // Mark the step processed (even when lenient mode SKIPPED its
        // body — a waiting axiom must not wait forever) and flush any
        // broadcast axiom whose references are now all in.
        match step {
            dep_order::EmitStep::Group(i) => { processed_groups.insert(*i); }
            dep_order::EmitStep::Instance(j) => { processed_instances.insert(*j); }
        }
        // Partition placement follows CONSUMERS, not stream position:
        // flushed axioms are consumed by pkg/island theorems, which
        // import the UMBRELLA — so tag BcAxiom (umbrella). Stream
        // position can't work per-part: dep-order and module-partition
        // disagree (a hoisted-early `Seq.empty` group is tagged into
        // the seq part while a flush after an instance step would sit
        // in base — base imports nothing). The one IN-PART consumer
        // (the seq measure companion citing axiom_seq_subrange_len) is
        // handled at the companion site below, and mid-stream flushes
        // SKIP that axiom.
        segs.push((cmds.len(), DefsSeg::BcAxiom));
        flush_ready_axioms(&mut cmds, &mut axiom_done, &mut axiom_ok, &processed_groups, &processed_instances, false);
        segs.push((cmds.len(), DefsSeg::Base));
        // vstd seq measure companions (B3): right after `Seq.drop_first`/
        // `Seq.drop_last` emits (and after the axiom flush above — the
        // subrange-len axiom's deps precede this def's group, so the
        // axiom is already down), emit its proven `_len_lt` theorem for
        // `DECREASING_BY_TACTIC`'s seq branch.
        if let dep_order::EmitStep::Group(i) = step {
            if let FnGroup::Single(f) = &groups[*i] {
                let rel = crate::to_lean_type::lean_name_relative(&f.name.path);
                if rel == "Seq.drop_first" || rel == "Seq.drop_last" {
                    // Gates (finding #7): the def itself AND the subrange
                    // axiom the canned proof cites must have actually
                    // landed — lenient mode can skip either, and an
                    // unguarded companion referencing a never-declared
                    // name would poison the whole shared-defs file.
                    // Emit the subrange axiom HERE, in this fn's part
                    // (mid-stream flushes skip it): the companion cites
                    // it and parts cannot import the umbrella. Both ride
                    // the fn's own group seg so later parts' decreasing_by
                    // (which cites the companion) resolves via the part
                    // import chain.
                    if step_pushed {
                        segs.push((cmds.len(), DefsSeg::FnGroup {
                            fns: vec![f.name.clone()], refs: spec_fn_refs(f),
                        }));
                        if let Some(ai) = subrange_ax_idx {
                            if !axiom_done[ai] {
                                axiom_done[ai] = true;
                                let ax = bc_lemma_funcs[ai];
                                axiom_ok[ai] = push_lenient(&mut cmds, "broadcast axiom", &mut || {
                                    let with_ne = add_nonempty(ax.clone(), &ax.name);
                                    let augmented = crate::impl_subst::maybe_augment_standalone_fn(
                                        &with_ne, &ectx.trait_outparams,
                                    );
                                    vec![to_lean_fn::broadcast_lemma_axiom_cmd(&augmented, ectx)]
                                });
                            }
                        }
                        let ax_landed = subrange_ax_idx.map_or(false, |i| axiom_ok[i]);
                        if ax_landed {
                            if let Some(cmd) =
                                seq_measure_companion_cmd(f, &rel, &all_fns, bc_lemma_funcs)
                            {
                                push_lenient(&mut cmds, "seq measure companion", &mut || vec![cmd.clone()]);
                            }
                            // Drop-k companion (bootstrap-46, gate hoisted
                            // 2026-07-19): emit the general
                            // `Seq.subrange_tail_len_lt` ONCE, on the FIRST
                            // drop-head pass — drop_first OR drop_last
                            // (the name derivation only strips the trailing
                            // method segment, identical for both). The old
                            // `rel == "Seq.drop_first"` gate left a crate
                            // that recurses on `subrange u k (len u)` but
                            // only ever uses drop_LAST without the
                            // companion — tactus-algebra's poly fns, the
                            // LIMITATION note's predicted counterexample:
                            // its whole defs module failed termination and
                            // the crate fell back to island emission.
                            if !subrange_tail_companion_emitted {
                                if let Some(cmd) =
                                    seq_subrange_tail_companion_cmd(f, &all_fns, bc_lemma_funcs)
                                {
                                    subrange_tail_companion_emitted = true;
                                    push_lenient(&mut cmds, "seq subrange-tail companion", &mut || vec![cmd.clone()]);
                                }
                            }
                        }
                        segs.push((cmds.len(), DefsSeg::Base));
                    }
                }
            }
        }
        if Some(pos) == last_group_pos {
            segs.push((cmds.len(), DefsSeg::ProofClasses {
                prereq_fns: proof_class_prereq_fns.clone(),
            }));
            push_lenient(&mut cmds, "proof-method trait classes", &mut || {
                let mut tmp = Vec::new();
                emit_proof_classes(&mut tmp);
                tmp
            });
            segs.push((cmds.len(), DefsSeg::Base));
        }
    }
    // Broadcast axioms now emit INCREMENTALLY via flush_ready_axioms
    // (dependency-ordered, main's B-series fix) — mid-stream axioms
    // ride whatever DefsSeg is current, which is sound for the
    // partition (they land after their deps, and the umbrella
    // re-exports every part). The final forced flush below catches
    // stragglers; tag it BcAxiom so those land in the umbrella like
    // the old always-at-the-end position.
    segs.push((cmds.len(), DefsSeg::BcAxiom));
    // Final forced flush: any broadcast axiom not yet emitted (a dep that
    // never appeared in `order`, or lenient-mode edge cases) lands here —
    // the old always-at-the-end position. Sound by the same argument as
    // cross-crate axiomatized ensures: vstd verified the lemma
    // (`vargo build` → 0 errors); we stipulate it. The user opted in
    // explicitly with `broadcast use <group>;` (#122).
    flush_ready_axioms(&mut cmds, &mut axiom_done, &mut axiom_ok, &processed_groups, &processed_instances, true);
    (cmds, segs)
}

/// vstd seq measure companion (B3, DESIGN-lean-all-proofs-bugs.md): when
/// the crate emits `Seq.drop_first` / `Seq.drop_last` (vstd defs over the
/// axiomatized `seq.Seq`), emit a PROVEN `{def}_len_lt` theorem right
/// after the def so `DECREASING_BY_TACTIC`'s seq branch can discharge the
/// `len (drop_X w) < len w` termination goals of fns recursing through
/// them. Proven from `axiom_seq_subrange_len` with a canned tactic
/// (validated against Lean 4.25.0) — a theorem, not an axiom: zero
/// axiom-surface growth. Returns `None` when the subrange-len axiom or
/// `seq.Seq.len` isn't part of this emission — recursive users then fail
/// termination exactly as before, and the tactic's `apply` branch fails
/// over on the unknown companion name.
fn seq_measure_companion_cmd(
    f: &FunctionX,
    rel_name: &str,
    all_fns: &[&FunctionX],
    bc_lemma_funcs: &[&FunctionX],
) -> Option<Command> {
    // (subrange start, subrange end matches `len s` vs `len s - 1`) —
    // mirrors the defs' bodies: drop_first = subrange 1 (len s),
    // drop_last = subrange 0 (len s - 1).
    let (j_arg, k_minus_one) = match rel_name {
        "Seq.drop_first" => ("1", false),
        "Seq.drop_last" => ("0", true),
        _ => return None,
    };
    let ax = bc_lemma_funcs.iter().find(|a| {
        crate::to_lean_type::lean_name_relative(&a.name.path) == "seq.axiom_seq_subrange_len"
    })?;
    let len_fn = all_fns.iter().find(|a| {
        crate::to_lean_type::lean_name_relative(&a.name.path) == "seq.Seq.len"
    })?;
    // The `seq.Seq` datatype path = the len fn's path minus its last
    // segment ("seq.Seq.len" → "seq.Seq").
    let seq_path = {
        let lp = &len_fn.name.path;
        let segs: Vec<_> = lp.segments.iter().take(lp.segments.len() - 1).cloned().collect();
        if segs.is_empty() {
            return None;
        }
        std::sync::Arc::new(vir::ast::PathX {
            krate: lp.krate.clone(),
            segments: std::sync::Arc::new(segs),
        })
    };
    let df = crate::to_lean_type::lean_name(&f.name.path);
    let len = crate::to_lean_type::lean_name(&len_fn.name.path);
    let ax_n = crate::to_lean_type::lean_name(&ax.name.path);
    let seq_t = crate::to_lean_type::lean_name(&seq_path);
    let k_expr = if k_minus_one {
        format!("{} A s - 1", len)
    } else {
        format!("{} A s", len)
    };
    // The axiom's hypothesis (`0 <= j <= k <= s.len()`, a chained
    // comparison) has TWO attested renderings — a let-bound left-assoc
    // conjunction (VIR chained-op desugar with lets) and a bare
    // right-assoc `∧` chain (`Multi(Chained)` via `and_all`) — and the
    // old anonymous-ctor proof `⟨⟨_, _⟩, _⟩` only elaborated against
    // the first (F2a follow-up; the divergence itself is a two-paths
    // rendering split worth unifying, DESIGN-lean-all-proofs-followons
    // F6 neighborhood). Bare `omega` closes every attested shape —
    // conjunction goals split natively and lets zeta-reduce (validated
    // empirically on all three forms, Lean 4.25.0).
    Some(Command::Raw(format!(
        "theorem {df}_len_lt (A : Type) [Nonempty A] (s : {seq_t} A)\n    \
         (h : ¬ {len} A s = 0) :\n    \
         {len} A ({df} A s) < {len} A s := by\n  \
         have hx := {ax_n} A s {j_arg} ({k_expr}) (by omega)\n  \
         simp only [{df}]\n  \
         omega",
    )))
}

/// Companion for **drop-k** seq measures: a general
/// `Seq.subrange_tail_len_lt` proving `len (subrange s j (len s)) < len s`
/// for any `j ≥ 1`. Unlike `seq_measure_companion_cmd` (which is keyed to a
/// specific `drop_first`/`drop_last` *def* head), this handles a raw
/// `subrange u k (len u)` recursion for arbitrary `k` — e.g.
/// `m3_blinker.ffnf` recursing on `subrange u 2 (len u)`, which has no
/// `drop_{first,last}` head for `apply` to unify (bootstrap-46).
///
/// Emitted ONCE, piggy-backed on the `Seq.drop_first` emission site (by
/// which point `axiom_seq_subrange_len`, `Seq.len` and `Seq.subrange` are
/// all in scope and the axiom has landed). The theorem lands in the SAME
/// `Seq.*` namespace as `drop_first_len_lt` (derived from the drop_first
/// fn's qualified name), so `DECREASING_BY_TACTIC`'s
/// `apply {ns}.Seq.subrange_tail_len_lt` rung resolves via the part-import
/// chain exactly like the drop_first companion. Proven from
/// `axiom_seq_subrange_len` with a canned tactic (validated against Lean
/// 4.25.0) — a theorem, not an axiom. Returns `None` when the subrange-len
/// axiom, `Seq.len` or `Seq.subrange` isn't part of this emission.
///
/// LIMITATION: emitted only on the `Seq.drop_first` site, so a crate that
/// recurses on `subrange s k (len s)` WITHOUT also emitting `Seq.drop_first`
/// would not get it. Every attested drop-k user (m3_blinker.ffnf) also uses
/// `drop_first`, so this holds today; a future counterexample is an easy
/// follow-up (hoist the emission to the axiom-flush site).
fn seq_subrange_tail_companion_cmd(
    drop_first_fn: &FunctionX,
    all_fns: &[&FunctionX],
    bc_lemma_funcs: &[&FunctionX],
) -> Option<Command> {
    let ax = bc_lemma_funcs.iter().find(|a| {
        crate::to_lean_type::lean_name_relative(&a.name.path) == "seq.axiom_seq_subrange_len"
    })?;
    let len_fn = all_fns.iter().find(|a| {
        crate::to_lean_type::lean_name_relative(&a.name.path) == "seq.Seq.len"
    })?;
    let subrange_fn = all_fns.iter().find(|a| {
        crate::to_lean_type::lean_name_relative(&a.name.path) == "seq.Seq.subrange"
    })?;
    // The `seq.Seq` datatype path = the len fn's path minus its last segment.
    let seq_path = {
        let lp = &len_fn.name.path;
        let segs: Vec<_> = lp.segments.iter().take(lp.segments.len() - 1).cloned().collect();
        if segs.is_empty() {
            return None;
        }
        std::sync::Arc::new(vir::ast::PathX {
            krate: lp.krate.clone(),
            segments: std::sync::Arc::new(segs),
        })
    };
    // Name the theorem in drop_first's OWN namespace (`{ns}.Seq.…`), so the
    // tactic's `q("Seq.subrange_tail_len_lt")` citation resolves identically
    // to the `drop_first_len_lt` companion. Derive `{ns}.Seq` by stripping
    // the trailing method segment off drop_first's qualified name
    // (`lib.Seq.drop_first` → `lib.Seq`).
    let df = crate::to_lean_type::lean_name(&drop_first_fn.name.path);
    let ns_seq = match df.rsplit_once('.') {
        Some((pre, _)) => pre.to_string(),
        None => return None,
    };
    let thm = format!("{ns_seq}.subrange_tail_len_lt");
    let len = crate::to_lean_type::lean_name(&len_fn.name.path);
    let subrange = crate::to_lean_type::lean_name(&subrange_fn.name.path);
    let ax_n = crate::to_lean_type::lean_name(&ax.name.path);
    let seq_t = crate::to_lean_type::lean_name(&seq_path);
    Some(Command::Raw(format!(
        "theorem {thm} (A : Type) [Nonempty A] (s : {seq_t} A) (j : Int)\n    \
         (h1 : 1 ≤ j) (h2 : j ≤ {len} A s) :\n    \
         {len} A ({subrange} A s j ({len} A s)) < {len} A s := by\n  \
         have hx := {ax_n} A s j ({len} A s) (by omega)\n  \
         omega",
    )))
}

// ── bootstrap-47: suffix-recursive length-monotonicity companion ──────────
//
// A per-USER-fn companion `{fn}_len_le : len (f W) ≤ len W` for a spec fn
// `f : Seq E → Seq E` whose body is EXACTLY `if <guard> then W else
// f(W.drop_first())` (guard exposing `len W = 0` as a top-level disjunct) —
// e.g. `m3_blinker.drop_base_run`. `split_q` recurses on
// `drop_base_run(W.drop_first())`; its termination goal
// `len (drop_base_run (drop_first W)) < len W` needs the COMPOSITION of this
// monotonicity fact with `drop_first_len_lt`, which `decreasing_by_tactic`'s
// chaining rung supplies (`Nat.lt_of_le_of_lt`).
//
// Unlike the generic `seq_*_companion_cmd` theorems (proven once, generic
// over the element type), this is MONOMORPHIC — bound to a specific user fn
// and its concrete Seq element type — and proven by `fun_induction` on the
// fn's own auto-generated `.induct`. That makes a SOUND detector critical:
// `push_lenient` only catches Rust panics, not Lean elaboration failures, so
// a false positive (emitting an unprovable companion) would poison the whole
// defs file. The detector therefore requires the EXACT structural shape the
// canned tactic provably discharges (validated standalone against the real
// oleans, Lean 4.25.0 — see `/tmp/probe_splitq.lean`). A false NEGATIVE is
// harmless: the fn just keeps failing termination exactly as it does today.

/// If `typ` (decoration/box-peeled) is `Seq<E>`, return `(seq-datatype path,
/// element typ)`.
fn seq_datatype_and_elem(typ: &Typ) -> Option<(&vir::ast::Path, &Typ)> {
    let t = crate::to_lean_type::peel_typ_wrappers(typ);
    if let TypX::Datatype(Dt::Path(p), args, _) = &**t {
        if crate::to_lean_type::lean_name_relative(p) == "seq.Seq" && args.len() == 1 {
            return Some((p, &args[0]));
        }
    }
    None
}

/// Strip transparent expression wrappers (empty block, ghost, proof-in-spec,
/// never-to-any) so the structural matchers see through the desugaring of
/// `{ W }` / `{ f(...) }` block bodies.
fn peel_mono_expr(e: &Expr) -> &Expr {
    match &e.x {
        ExprX::Block(stmts, Some(inner)) if stmts.is_empty() => peel_mono_expr(inner),
        ExprX::Ghost { expr, .. } => peel_mono_expr(expr),
        ExprX::ProofInSpec(inner) => peel_mono_expr(inner),
        ExprX::NeverToAny(inner) => peel_mono_expr(inner),
        _ => e,
    }
}

/// `e` (peeled) is a plain read of the local variable `name`.
fn is_read_of_var(e: &Expr, name: &VarIdent) -> bool {
    match &peel_mono_expr(e).x {
        ExprX::Var(v) => v == name,
        ExprX::ReadPlace(place, _) => matches!(&place.x, PlaceX::Local(v) if v == name),
        ExprX::ImplicitReborrowOrSpecRead(place, _, _) =>
            matches!(&place.x, PlaceX::Local(v) if v == name),
        _ => false,
    }
}

/// `e` (peeled) is `W.drop_first()` for the local `pname`.
fn is_drop_first_of_var(e: &Expr, pname: &VarIdent) -> bool {
    if let ExprX::Call(CallTarget::Fun(_, h, _, _, _, _), args, _) = &peel_mono_expr(e).x {
        if crate::to_lean_type::lean_name_relative(&h.path) == "Seq.drop_first" && args.len() == 1 {
            return is_read_of_var(&args[0], pname);
        }
    }
    false
}

/// `e` (peeled) is the self-recursive call `f(W.drop_first())`.
fn is_self_drop_first_recursion(e: &Expr, self_path: &vir::ast::Path, pname: &VarIdent) -> bool {
    if let ExprX::Call(CallTarget::Fun(_, g, _, _, _, _), args, _) = &peel_mono_expr(e).x {
        if g.path == *self_path && args.len() == 1 {
            return is_drop_first_of_var(&args[0], pname);
        }
    }
    false
}

/// `e` (peeled) is `W.len() == 0` (either operand order).
fn is_len_eq_zero(e: &Expr, pname: &VarIdent) -> bool {
    if let ExprX::Binary(BinaryOp::Eq(_), a, b) = &peel_mono_expr(e).x {
        return (is_len_of_var(a, pname) && is_int_zero(b))
            || (is_len_of_var(b, pname) && is_int_zero(a));
    }
    false
}

/// `e` (peeled) is `W.len()` for the local `pname`.
fn is_len_of_var(e: &Expr, pname: &VarIdent) -> bool {
    if let ExprX::Call(CallTarget::Fun(_, g, _, _, _, _), args, _) = &peel_mono_expr(e).x {
        if crate::to_lean_type::lean_name_relative(&g.path) == "seq.Seq.len" && args.len() == 1 {
            return is_read_of_var(&args[0], pname);
        }
    }
    false
}

/// `e` (peeled) is the integer literal `0`.
fn is_int_zero(e: &Expr) -> bool {
    matches!(&peel_mono_expr(e).x, ExprX::Const(Constant::Int(n)) if n.to_string() == "0")
}

/// True iff the guard is an OR-tree with `len(pname) == 0` as one of its
/// top-level disjuncts. This is exactly what makes the `else` branch's
/// `¬guard` yield `len W ≠ 0` (which `omega` reads, over any opaque
/// non-arith disjuncts) — and also exactly what makes recursion on
/// `W.drop_first()` terminate, so the shape is self-consistent.
fn guard_or_tree_has_len_zero(e: &Expr, pname: &VarIdent) -> bool {
    match &peel_mono_expr(e).x {
        ExprX::Binary(BinaryOp::Or, l, r) =>
            guard_or_tree_has_len_zero(l, pname) || guard_or_tree_has_len_zero(r, pname),
        _ => is_len_eq_zero(peel_mono_expr(e), pname),
    }
}

/// Length-monotonicity companion for a **suffix-recursive** spec fn (see the
/// section comment above). Returns `(theorem name, command)` — the name is
/// registered in the mono-companion bag so later fns' `decreasing_by` cite
/// it — or `None` when `f` is not suffix-recursive or the seq primitives
/// (`seq.Seq.len`, `Seq.drop_first`) aren't part of this emission.
fn seq_suffix_mono_companion_cmd(
    f: &FunctionX,
    all_fns: &[&FunctionX],
) -> Option<(String, Command)> {
    // ── strict structural detection ──
    if f.mode != Mode::Spec { return None; }
    if f.params.len() != 1 { return None; }
    if f.decrease.is_empty() { return None; }
    let pname = &f.params[0].x.name;
    let (seq_path, elem) = seq_datatype_and_elem(&f.params[0].x.typ)?;
    // return type must also be `Seq<_>` (the fn returns its own recursion).
    seq_datatype_and_elem(&f.ret.x.typ)?;
    let body = f.body.as_ref()?;
    let (guard, then_e, else_e) = match &peel_mono_expr(body).x {
        ExprX::If(g, t, Some(e)) => (g, t, e),
        _ => return None,
    };
    // Exactly one branch is the identity `W`; the other the `f(drop_first W)`
    // recursion. (`fun_induction`'s base/step cases close regardless of which
    // branch is which — `omega` for identity, the IH+drop_first chain for
    // recursion — so position is immaterial.)
    let then_id = is_read_of_var(then_e, pname);
    let else_id = is_read_of_var(else_e, pname);
    let rec_e = if then_id && !else_id {
        else_e
    } else if else_id && !then_id {
        then_e
    } else {
        return None;
    };
    if !is_self_drop_first_recursion(rec_e, &f.name.path, pname) { return None; }
    if !guard_or_tree_has_len_zero(guard, pname) { return None; }

    // ── emit the proven companion (monomorphic in the element type) ──
    let len_fn = all_fns.iter().find(|a| {
        crate::to_lean_type::lean_name_relative(&a.name.path) == "seq.Seq.len"
    })?;
    let drop_first_fn = all_fns.iter().find(|a| {
        crate::to_lean_type::lean_name_relative(&a.name.path) == "Seq.drop_first"
    })?;
    let fn_n = crate::to_lean_type::lean_name(&f.name.path);
    let len = crate::to_lean_type::lean_name(&len_fn.name.path);
    let seq_t = crate::to_lean_type::lean_name(seq_path);
    let df = crate::to_lean_type::lean_name(&drop_first_fn.name.path);
    // Render the concrete Seq element type; parenthesize if it's an
    // application (so it stays a single type argument).
    let elem_str = crate::lean_pp::pp_expr(&crate::to_lean_type::typ_to_expr(elem));
    let elem_arg = if elem_str.chars().any(|c| c.is_whitespace()) {
        format!("({elem_str})")
    } else {
        elem_str
    };
    let mono_name = format!("{fn_n}_len_le");
    // `fun_induction {fn} W` uses `{fn}.induct` (auto-generated for the WF-
    // recursive def), giving a base case (guard true → the fn reduces to
    // `W`) and a step case (guard false → the recursive call, with an IH).
    //
    // The proof is deliberately COUNT-FREE (no `rename_i`) and
    // if-REDUCING, because the in-gate ambient env diverges from a naive
    // standalone elaboration in two load-bearing ways (the bootstrap-45/46
    // Decidable-resolution divergence, confirmed by reproducing against the
    // real emitted oleans with the gate's prelude):
    //   1. the disjunctive guard `len W = 0 ∨ …` elaborates as a `dite`,
    //      and `fun_induction` leaves `{fn} x` UNFOLDED in the goal as
    //      `len (if <guard> then x else {fn} (drop_first x)) ≤ len x` —
    //      which `omega` cannot simplify;
    //   2. the base case has only TWO introduced hypotheses (var + guard,
    //      no IH), so a fixed `rename_i x h ih` overflows ("too many
    //      variable names").
    // So: `try split` reduces the goal's `if` (a no-op when the ambient env
    // already reduced it); then per resulting goal, `omega` closes the
    // trivial `len x ≤ len x`; `apply Nat.le_trans <;> (assumption |
    // Nat.le_of_lt ∘ drop_first_len_lt)` chains the IH (found by
    // `assumption`, accessibility-agnostic) with `len (drop_first x) < len x`
    // (`apply` reads `x` off the goal, `omega` reads `¬ len x = 0` off the
    // negated guard); `(simp_all only [TERM])` mops up the
    // vacuous guard-contradiction branches `split` can introduce. Validated
    // against the real emitted `m3_blinker` oleans under BOTH the gate
    // prelude and a plain-`∨` prelude (bootstrap-47).
    let cmd = Command::Raw(format!(
        "theorem {mono_name} (W : {seq_t} {elem_arg}) :\n    \
         {len} {elem_arg} ({fn_n} W) ≤ {len} {elem_arg} W := by\n  \
         fun_induction {fn_n} W <;> (try split) <;>\n    \
         first\n      \
         | omega\n      \
         | (apply Nat.le_trans <;>\n          \
         first\n            \
         | assumption\n            \
         | (apply Nat.le_of_lt; apply {df}_len_lt <;> (first | assumption | omega | (simp_all only [{ts}] <;> omega) | simp_all only [{ts}])))\n      \
         | (simp_all only [{ts}] <;> omega)\n      \
         | simp_all only [{ts}]",
        ts = crate::tactic_select::TERM_SIMP_LEMMAS,
    ));
    Some((mono_name, cmd))
}

/// Ambient thread-local tables every render path needs installed
/// first. The SINGLE install chokepoint: every render entry point
/// (`emit_proof_fn`, `emit_exec_fn`, `crate_defs::for_crate`) calls
/// this — never call the individual installers directly, so the pair
/// can't drift apart. Folding these two tables into EmitCtx/RenderCtx
/// was considered and REJECTED (REFACTORING2.md "EmitCtx follow-ups"):
/// ctx would have to reach `lean_name` — called from `typ_to_node` and
/// ~34 direct sites across 10 files — for two krate-derived, idempotent
/// tables whose absence fails loudly (unreferenceable names / missing
/// bound hypotheses), not silently.
pub(crate) fn install_emit_tables(krate: &KrateX, crate_name: &str) {
    // Crate namespace first: if a future table builder renders names via
    // `lean_name`, it must see the CURRENT crate's root-anchor, not a
    // stale one from a previous emission on this thread.
    crate::to_lean_type::install_crate_ns(crate_name);

    install_inherent_method_renames(krate);
    install_datatype_field_bounds(krate);
    // Decl set AFTER the rename table: it stores naturalized relative
    // names (`Seq.first`, not `impl__3.first`), so the renames must be
    // consultable while building it.
    install_crate_decls(krate);
    // bootstrap-47: reset the suffix-mono companion bag at every emission
    // entry. The defs build (crate_defs::build_defs) routes through here
    // ONCE before its spec-fn loop, which then populates the bag; per-fn
    // proof/exec emissions also route through here, clearing any names a
    // prior defs build left so their `decreasing_by` never cites an
    // out-of-file companion.
    to_lean_fn::clear_suffix_mono_names();
}

/// Build the set of relative Lean names this krate's emission can declare —
/// fns, datatypes, traits (variants/fields ride on their datatype's name;
/// constructor heads render as `{datatype}.{variant}` whose head segment is
/// what reference-anchoring keys on). See `to_lean_type::CRATE_DECLS`.
fn install_crate_decls(krate: &KrateX) {
    // Fingerprint cache: install_emit_tables runs once per emitted fn and
    // this set costs O(krate) String renders to build — O(N²) per crate
    // uncached (2026-07-09 review, finding #10). Keyed on the krate's
    // address plus shape counts; a false hit would need the allocator to
    // reuse the exact address for a different krate with identical
    // fn/datatype/trait counts on the same thread, and the failure mode
    // is loud (wrong anchoring → Lean unknown identifier), not silent.
    type Fp = (usize, usize, usize, usize);
    thread_local! {
        static DECLS_CACHE: std::cell::RefCell<
            Option<(Fp, std::sync::Arc<std::collections::HashSet<String>>)>,
        > = std::cell::RefCell::new(None);
    }
    let fp: Fp = (
        krate as *const KrateX as usize,
        krate.functions.len(),
        krate.datatypes.len(),
        krate.traits.len(),
    );
    let cached = DECLS_CACHE.with(|c| {
        c.borrow().as_ref().filter(|(k, _)| *k == fp).map(|(_, v)| v.clone())
    });
    let decls = match cached {
        Some(d) => d,
        None => {
            let mut decls = std::collections::HashSet::new();
            for f in krate.functions.iter() {
                decls.insert(crate::to_lean_type::lean_name_relative(&f.x.name.path));
            }
            for d in krate.datatypes.iter() {
                if let vir::ast::Dt::Path(p) = &d.x.name {
                    decls.insert(crate::to_lean_type::lean_name_relative(p));
                }
            }
            for tr in krate.traits.iter() {
                decls.insert(crate::to_lean_type::lean_name_relative(&tr.x.name));
            }
            let decls = std::sync::Arc::new(decls);
            DECLS_CACHE.with(|c| *c.borrow_mut() = Some((fp, decls.clone())));
            decls
        }
    };
    crate::to_lean_type::install_crate_decls(decls);
}


// ── Check results ──────────────────────────────────────────────────────

/// Where in the user's source a Tactus diagnostic points. Three
/// mutually-exclusive cases — split as an enum rather than two
/// `Option` fields on `TactusDiag` so the prior encoding's
/// permitted-but-meaningless states (notably "both Some") are
/// structurally unrepresentable. Picking which variant to
/// construct forces the producer to decide what the diagnostic
/// is pointing at, rather than setting two Options independently
/// and hoping the consumer interprets them consistently.
///
/// Same pattern DESIGN.md § "Type-system-enforced invariants"
/// applies elsewhere (`AssertKind` sum split, `LoopInvKind`,
/// etc.): runtime exclusivity → enum, type system carries the
/// guarantee.
#[derive(Clone)]
pub enum DiagLocation {
    /// Exec-fn obligation: the obligation's own Verus `Span`
    /// (cloned from the SST node by `sst_to_lean`). The verifier
    /// uses this directly as the primary span — no further
    /// resolution needed.
    Direct(vir::messages::Span),
    /// Proof-fn diagnostic inside the `by { ... }` tactic body,
    /// at the given 0-indexed line offset within the body. The
    /// verifier resolves this to a source-line `Span` at
    /// emission time via the fn's `tactic_span` byte range
    /// (which lives in the verifier's `FunctionAttrsX`, not in
    /// `lean_verify`, so the resolution can't happen here).
    ProofFnBodyLine(usize),
    /// No source-position info available — pre-Lean rejections
    /// (sanity-check failures, codegen-rejected fn shapes), or
    /// the rare "Lean failed with zero error diagnostics"
    /// fallback. The verifier emits with the enclosing fn's span
    /// so the user still gets `-->` to the right ballpark.
    Unknown,
}

/// A single rejection record from a Tactus check. The verifier
/// reports each as its own `MessageLevel::Error`, with `location`
/// determining the `-->` arrow's target. `help` is the .lean
/// artifact path (attached so users can `cat` the file even when
/// their terminal has clipped the error body).
#[derive(Clone)]
pub struct TactusDiag {
    pub message: String,
    pub location: DiagLocation,
    pub help: Option<String>,
}

#[must_use]
pub enum CheckResult {
    /// Lean verified the proof successfully. `warnings` carries
    /// non-fatal diagnostics — currently used for `assume(P)` site
    /// notifications (each `assume` is a soundness escape hatch
    /// backed by `sorry`).
    Success { warnings: Vec<String> },
    /// Lean rejected the proof. `errors` carries one entry per
    /// failing obligation; the verifier emits each as a separate
    /// `MessageLevel::Error` so users get rustc-style per-error
    /// `-->` arrows pointing at the failing site. `warnings`
    /// carries non-fatal diagnostics (assume sites, etc.) that are
    /// worth surfacing even when verification itself fails.
    Failed { errors: Vec<TactusDiag>, warnings: Vec<String> },
    /// Lean could not be invoked (not installed, project missing, etc.)
    Error(String),
}

// ── Entry points ───────────────────────────────────────────────────────

/// Check a tactic proof fn.
/// The codegen-only ("emit") output: the written `.lean` path and its
/// source map, plus any codegen warnings. Produced by `emit_proof_fn` /
/// `emit_exec_fn` — the half of `check_*` that stops before running Lean.
/// `check_*` runs Lean on top of this; the `--emit-lean` path serializes
/// `source_map` into the sidecar instead of running Lean.
pub struct EmitOutput {
    pub file_path: PathBuf,
    pub source_map: LeanSourceMap,
    pub warnings: Vec<String>,
    /// Line of the island's first `theorem` head (pp landmark).
    /// Everything before it is emitter preamble; the island sorry
    /// gate treats sorry warnings at/after it as user-written.
    pub first_theorem_line: Option<usize>,
    /// Whether the island's `.lean` content changed this run
    /// (tracked write) — the cross-run cache skip signal.
    pub changed: bool,
}

/// Codegen-only half of `check_proof_fn`: inline pass → preamble → theorem →
/// pretty-print → write `.lean` → sanity check. Stops before the Lean run.
/// `Err(CheckResult)` carries a write error or sanity rejection so callers
/// surface it uniformly.
/// Build + install the inherent-impl-method rename table (consulted by
/// `to_lean_type::lean_name`). Maps each inherent method's raw path name
/// (`impl__0.view`) to its type-qualified form (`Holder.view`), recovering
/// the Self type from the method's receiver (`&self`/`self`, the first
/// param). Called at the top of each per-fn render entry so the table is
/// populated before any `lean_name` call for that fn's file — covering the
/// standalone def AND every call site uniformly. Inherent methods without a
/// receiver-derived type (e.g. assoc fns) keep the disambiguated marker
/// form. Idempotent across fns of the same crate.
fn install_inherent_method_renames(krate: &KrateX) {
    let mut map = std::collections::HashMap::new();
    for f in krate.functions.iter() {
        let fx = &f.x;
        if !matches!(fx.kind, vir::ast::FunctionKind::Static) { continue; }
        if !fx.attrs.print_as_method { continue; }
        if !fx.name.path.segments.iter().any(|s| s.contains("impl&%")) { continue; }
        let Some(self_short) = fx.params.first()
            .and_then(|p| crate::to_lean_type::type_short_name(&p.x.typ)) else { continue; };
        let Some(method) = fx.name.path.segments.last() else { continue; };
        let key = crate::to_lean_type::lean_name_raw(&fx.name.path);
        let naturalized = format!("{}.{}", self_short, crate::to_lean_type::sanitize(method));
        map.insert(key, naturalized);
    }
    crate::to_lean_type::set_inherent_method_renames(map);
}

/// Build + install the datatype-field-bounds table (consulted by
/// `to_lean_sst_expr::type_bound_predicate`). Maps each single-variant
/// struct datatype to its fields' `(lean accessor, typ)` so a struct param's
/// fixed-width fields get the same `0 ≤ … < 256` bound a numeric param does.
/// Enums (multi-variant) are omitted — their field bounds are
/// variant-conditional, deferred. Called at each per-fn render entry.
fn install_datatype_field_bounds(krate: &KrateX) {
    let mut map: std::collections::HashMap<vir::ast::Path, Vec<(String, vir::ast::Typ)>> =
        std::collections::HashMap::new();
    for d in krate.datatypes.iter() {
        let dx = &d.x;
        if dx.variants.len() != 1 { continue; }
        let vir::ast::Dt::Path(path) = &dx.name else { continue; };
        // STRUCTS only: a struct is a single-variant datatype whose variant
        // is eponymous (named after the type) — its field projection is
        // `e.<field>` directly. A single-variant ENUM (e.g. `enum Pair {
        // Mk(u64) }`) has a non-eponymous variant, needs variant-guarded
        // access (`Mk_val0`), and its field bound is variant-conditional —
        // excluded here (the field projection would otherwise be malformed).
        let variant = &dx.variants[0];
        if variant.name.as_str() != crate::to_lean_type::short_name(path) { continue; }
        let fields: Vec<(String, vir::ast::Typ)> = variant.fields.iter().map(|f| {
            // Single-variant accessor: `valN` for numeric (tuple-struct)
            // fields, sanitized name otherwise — matches `field_access_name`.
            let raw = f.name.as_str();
            let accessor = match raw.parse::<usize>() {
                Ok(n) => format!("val{}", n),
                Err(_) => crate::to_lean_type::sanitize(raw),
            };
            (accessor, f.a.0.clone())
        }).collect();
        map.insert(path.clone(), fields);
    }
    crate::to_lean_sst_expr::set_datatype_fields(map);

    // Sibling table, ALL datatypes ALL variants, raw field names:
    // declared ctor-slot typs for the Box::new-erasure re-wrap
    // (expr_shared::CTOR_FIELD_TYPS).
    let mut ctor_map: std::collections::HashMap<
        vir::ast::Path,
        (Vec<vir::ast::Ident>, std::collections::HashMap<String, Vec<(String, vir::ast::Typ)>>),
    > = std::collections::HashMap::new();
    for d in krate.datatypes.iter() {
        let dx = &d.x;
        let vir::ast::Dt::Path(path) = &dx.name else { continue; };
        let tps: Vec<vir::ast::Ident> = dx.typ_params.iter().map(|(id, _)| id.clone()).collect();
        let variants: std::collections::HashMap<String, Vec<(String, vir::ast::Typ)>> = dx
            .variants
            .iter()
            .map(|v| {
                (
                    v.name.as_str().to_string(),
                    v.fields.iter().map(|f| (f.name.as_str().to_string(), f.a.0.clone())).collect(),
                )
            })
            .collect();
        ctor_map.insert(path.clone(), (tps, variants));
    }
    crate::expr_shared::set_ctor_field_typs(ctor_map);
}

pub fn emit_proof_fn(
    krate: &KrateX,
    proof_fn: &FunctionX,
    tactic_body: &str,
    imports: &[String],
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> Result<EmitOutput, CheckResult> {
    install_emit_tables(krate, crate_name);
    // Shared-defs lookup (CRATEDEFS.md step 1a). Memo-consistent with
    // the `check_proof_fn` build: in check mode the defs were already
    // built (or poisoned to None) before this runs; in `--emit-lean`
    // mode this writes the defs source without building. Takes the
    // pre-inline krate — `for_crate` applies its own inline pass.
    // TODO(M6.5): emit-module mode still writes proof-family artifacts;
    // unify with `unified_package_defs` once build=false covers_exec
    // semantics are settled (the ladder decides covers_exec, and this
    // path deliberately skips the build).
    let defs = crate::crate_defs::for_crate(krate, crate_name, tactic_bodies, false, crate::crate_defs::ScopeKind::Proof);
    // Package emission (M2, --tactus-emit-module): additive artifact
    // under pkg/; islands (and the batch) remain the checking
    // authority, so failures warn loudly but never fail the fn. Hooked
    // BEFORE the batch early-return so batched fns get package
    // artifacts too.
    if package_enabled() {
        match &defs {
            Some(d) => {
                match emit_package_proof_fn(
                    krate, proof_fn, tactic_body, imports, crate_name, tactic_bodies, d,
                ) {
                    Ok(PkgEmitOutcome::Single { .. }) | Ok(PkgEmitOutcome::Mutual { .. }) => {}
                    Ok(PkgEmitOutcome::UnsupportedScc(reason)) => eprintln!(
                        "tactus: package emission skipped for `{}`: {}",
                        short_name(&proof_fn.name.path), reason
                    ),
                    Err(e) => eprintln!(
                        "tactus: package emission failed for `{}` ({}); island artifact unaffected",
                        short_name(&proof_fn.name.path), e
                    ),
                }
                // Link module (M3): once per scope; content is fully
                // determined by the krate, so any fn's emission can
                // trigger the build.
                link_for_crate(krate, crate_name, tactic_bodies, d);
            }
            None => eprintln!(
                "tactus: --tactus-emit-module requires the shared-defs module \
                 (build failed or gate unmet); package emission skipped for `{}`",
                short_name(&proof_fn.name.path)
            ),
        }
    }
    // Batch route (step 1b): a batched proof fn's artifact IS the batch
    // file; return its position within it for the sidecar. (In check
    // mode `check_proof_fn` returns before reaching here for covered
    // fns; this path serves `--emit-lean`.)
    if let Some(b) = crate::crate_defs::proof_batch(krate, crate_name, tactic_bodies, false) {
        if let Some(out) = b.emit_output(&proof_fn.name) {
            return Ok(out);
        }
    }
    // Layer 7 — inline `#[verifier::inline]` spec fns on the VIR-AST so that
    // proof-fn goals and broadcast-lemma clauses agree with Verus's
    // SST-inlined exec goals. One krate-level pass, before any rendering; the
    // root fn is re-fetched from the inlined krate so its goal inlines too and
    // dep-walk roots don't reference the dropped inline-fn defs. See
    // `inline_spec`.
    let inlined_krate = crate::inline_spec::inline_marked_in_krate(krate);
    let proof_fn = inlined_krate.functions.iter()
        .find(|f| f.x.name == proof_fn.name).map(|f| &f.x)
        .expect("root proof fn present in inlined krate (proof fns are never #[inline])");
    let krate = &inlined_krate;

    // Proof fns render match expressions natively (spec fns
    // preserve match through to VIR-AST), so accessor fns are
    // unnecessary and would fail elaboration for enum types whose
    // field types lack Inhabited.
    //
    // Empty theorem slice — proof fns produce a single theorem that
    // gets appended after the preamble, but it doesn't carry its
    // own preamble fragments (proof fns don't use `by(bit_vector)`
    // etc. via the structured path; if they ever need extra
    // imports, those go through the explicit `imports` parameter).
    let (mut cmds, ns) = krate_preamble(
        krate, imports, crate_name, &[proof_fn], PreambleConfig::ProofFn, &[], tactic_bodies,
        &[], defs.as_deref(),
    );
    // Krate-level tables for proof_fn_to_ast (fn_map for the
    // nat-coercion call-arg bridge, shell traits for bound filtering).
    // Built locally here (vs. threaded from krate_preamble) since
    // proof_fn_to_ast is called outside the preamble.
    let ectx = crate::emit_ctx::EmitCtx::build(krate, tactic_bodies);
    cmds.push(Command::Theorem(to_lean_fn::proof_fn_to_ast(proof_fn, tactic_body, &ectx)));
    let _ = ns;

    // Pretty-print and write the .lean file BEFORE the sanity check.
    // The artifact is always written when codegen produces a command
    // stream, even if sanity rejects — so error messages can name
    // the .lean path for inspection and `cat`-style debugging works
    // regardless of which step fails.
    let rendered = pp_commands(&cmds);
    // One proof fn per file → exactly one `Tactic::Raw` emission.
    let source_map = proof_fn_source_map(
        &proof_fn.name, rendered.landmarks.tactic_starts.first().copied(), tactic_body);

    let file_path = lean_file_path(crate_name, &proof_fn.name.path);
    let changed = match write_lean_file_tracked(&file_path, &rendered.text) {
        Ok(c) => c,
        Err(e) => return Err(CheckResult::Error(e)),
    };

    let cmds_for_sanity: Vec<Command> = match &defs {
        // Sanity resolves identifiers over the command stream; in defs
        // mode the spec world arrives via import, so check against the
        // concatenation — exactly what Lean sees.
        Some(d) => d.cmds.iter().cloned().chain(cmds.iter().cloned()).collect(),
        None => cmds.clone(),
    };
    if let Err(reason) = debug_check(&cmds_for_sanity) {
        return Err(CheckResult::Failed {
            errors: vec![TactusDiag {
                message: reason,
                location: DiagLocation::Unknown,
                help: Some(format!("{} {}",
                    vir::tactus_messages::LEAN_FILE_HELP_PREFIX, file_path.display())),
            }],
            warnings: vec![],
        });
    }

    Ok(EmitOutput {
        file_path, source_map, warnings: vec![], changed,
        first_theorem_line: rendered.landmarks.theorem_heads.first().copied(),
    })
}

/// Verify a proof fn: emit its `.lean` (via `emit_proof_fn`), then run Lean.
pub fn check_proof_fn(
    krate: &KrateX,
    proof_fn: &FunctionX,
    tactic_body: &str,
    imports: &[String],
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> CheckResult {
    // Package-check route (M5a, --tactus-package-check): tactic proof
    // fns verify via their PACKAGE module instead of an island. `None`
    // = the route can't run (defs unavailable) — fall through to the
    // island path below.
    if package_check_enabled() {
        if let Some(result) = check_proof_fn_via_package(
            krate, proof_fn, tactic_body, imports, crate_name, tactic_bodies,
        ) {
            return result;
        }
    }
    // Build (or fetch) the shared defs module FIRST: `emit_proof_fn`'s
    // internal lookup is a memo hit on whatever this call cached, so
    // the emitted import and the built artifact can't disagree. A
    // build failure caches `None` → standalone emission, today's path.
    let defs = crate::crate_defs::for_crate(krate, crate_name, tactic_bodies, true, crate::crate_defs::ScopeKind::Proof);
    // Batch route (CRATEDEFS.md step 1b): ordinary proof fns verify in
    // ONE Lean run over TactusProofs_{crate}.lean; the first covered fn
    // builds + runs it, the rest read the cached per-fn attribution.
    // Trait-method-impl proof fns aren't batched and continue below.
    let batch = crate::crate_defs::proof_batch(krate, crate_name, tactic_bodies, true);
    if let Some(b) = &batch {
        if b.covers(&proof_fn.name) {
            return b.result_for(&proof_fn.name);
        }
    }
    let EmitOutput { file_path, source_map, first_theorem_line, changed, .. } =
        match emit_proof_fn(krate, proof_fn, tactic_body, imports, crate_name, tactic_bodies) {
            Ok(o) => o,
            Err(cr) => return cr,
        };
    let marker = file_path.with_extension("verified");
    if island_cache_ok(&marker, changed, &defs) {
        ISLAND_CACHED_VERDICTS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        // Live-path parity: success warnings are the sorry-filtered
        // set, which is empty by construction (sorry is fatal here).
        return CheckResult::Success { warnings: vec![] };
    }
    let _ = std::fs::remove_file(&marker);

    let dir = project::default_project_dir();
    let lake_dir = if project::project_ready(&dir) { Some(dir.as_path()) } else { None };
    let prelude_dir = match crate::prelude::ensure_prelude_olean() {
        Ok(d) => d,
        Err(e) => return CheckResult::Error(e),
    };
    let mut extra_paths: Vec<&std::path::Path> = vec![&prelude_dir];
    if let Some(d) = &defs {
        extra_paths.push(&d.dir);
    }
    let result = lean_process::check_lean_file(&file_path, lake_dir, &extra_paths);
    if let Ok(r) = &result {
        if r.success {
            if let Some(fail) = island_sorry_failure(
                r, first_theorem_line, &proof_fn.name.path, &file_path, &source_map)
            {
                return fail;
            }
            let _ = std::fs::write(&marker, crate::project::toolchain_fingerprint());
        }
    }
    format_lean_check_result(result, proof_fn, &file_path, &source_map)
}

/// Islands have no Link gate behind them — package-mode fallback fns
/// are cycle-poisoned out of the Link closure, and exec fns are never
/// in it — so a `sorry`/`admit` that elaborates (a warning to Lean)
/// would verify with no fatal layer anywhere. On the island path it
/// is therefore FATAL. The package path keeps warning-at-fn-level +
/// fatal Link sorryAx backstop (layered defense; both test-pinned).
/// Island verdict cache (cross-run). Marker = `<island>.verified`
/// holding the toolchain fingerprint; it exists IFF the last completed
/// Lean run on exactly this island text, against this toolchain,
/// succeeded. Skip additionally requires the imported defs family had
/// no breaking rebuild this run (superset appends keep consumer
/// validity — same kernel-weakening argument as the package cache;
/// with fingerprint-scoped defs, any crate change renames the defs
/// module and thus changes the island text itself). Sorry can't hide
/// in a cached verdict: it is FATAL on island paths, so no marker is
/// ever written over one. The marker is REMOVED before any live run —
/// a crashed or failed run leaves no stale trust behind.
fn island_cache_ok(
    marker: &Path,
    changed: bool,
    defs: &Option<std::sync::Arc<crate::crate_defs::CrateDefs>>,
) -> bool {
    if changed || defs.as_ref().is_some_and(|d| d.breaking) {
        return false;
    }
    let hit = std::fs::read_to_string(marker).ok().as_deref()
        == Some(crate::project::toolchain_fingerprint());
    if hit {
        static NOTE: std::sync::Once = std::sync::Once::new();
        NOTE.call_once(|| {
            eprintln!("note: tactus: island cache: reusing prior verdicts \
for unchanged islands (`.verified` markers)");
        });
    }
    hit
}

/// Lean positions `declaration uses 'sorry'` at the DECLARATION HEAD
/// (not the sorry literal), and re-warns per declaration whose term
/// contains it — so neither tactic-region membership nor counting
/// emitted placeholders can discriminate. Structure can: islands are
/// emitter preamble (classes / instances / spec defs — where the
/// TACTIC_BODY_FALLBACK placeholders for trait-method defaults live,
/// their obligations Verus-checked) followed by theorems (where user
/// tactic text lives). Sorry warnings at/after the FIRST theorem head
/// are user-written and fatal; earlier ones warn. No position or no
/// theorem landmark → fatal (unknown provenance).
fn island_sorry_failure(
    r: &lean_process::LeanResult,
    first_theorem_line: Option<usize>,
    fn_path: &vir::ast::Path,
    file_path: &Path,
    source_map: &LeanSourceMap,
) -> Option<CheckResult> {
    let user_written = |d: &lean_process::LeanDiagnostic| -> bool {
        match (&d.pos, first_theorem_line) {
            (Some(p), Some(t)) => p.line >= t,
            _ => true,
        }
    };
    let errors: Vec<TactusDiag> = r.diagnostics.iter()
        .filter(|d| d.severity == "warning" && d.data.contains("sorry") && user_written(d))
        .map(|d| {
            let formatted = lean_process::format_error(d, source_map);
            TactusDiag {
                message: format!(
                    "sorry is fatal on the per-fn path (no Link gate covers {}): {}",
                    short_name(fn_path), formatted.message),
                location: formatted.location,
                help: Some(format!("{} {}",
                    vir::tactus_messages::LEAN_FILE_HELP_PREFIX, file_path.display())),
            }
        })
        .collect();
    if errors.is_empty() {
        None
    } else {
        Some(CheckResult::Failed { errors, warnings: vec![] })
    }
}

/// Shared diagnostics chokepoint for island AND package-check proof-fn
/// failures: format Lean's `--json` diagnostics through the source map
/// so both paths point at identical Rust spans.
fn format_lean_check_result(
    result: Result<lean_process::LeanResult, String>,
    proof_fn: &FunctionX,
    file_path: &Path,
    source_map: &LeanSourceMap,
) -> CheckResult {
    // Deliberately narrowed to `sorry` (the soundness escape hatch):
    // generic Lean warnings are dominated by lints/hints on GENERATED
    // shapes (defensive termination_by on non-recursive fns, emitted
    // simp lists) — surfacing them all fights the emitter's own noise.
    // A broader warning policy is future work (review follow-up).
    let lean_warnings = |r: &lean_process::LeanResult| -> Vec<String> {
        r.diagnostics.iter()
            .filter(|d| d.severity == "warning" && d.data.contains("sorry"))
            .map(|d| {
                let formatted = lean_process::format_error(d, source_map);
                format!("Lean warning in {}: {}",
                    short_name(&proof_fn.name.path), formatted.message)
            })
            .collect()
    };
    match result {
        // Warning-severity diagnostics (e.g. `declaration uses 'sorry'`)
        // surface on success — previously dropped by island AND package
        // paths alike (review finding). The soundness backstop for
        // sorry stays the Link gate's fatal sorryAx check; this is the
        // fn-level signal.
        Ok(r) if r.success => {
            // Sorry is fatal on EVERY per-fn path (island and package
            // alike). The Link gate's sorryAx check remains the
            // backstop for cached verdicts, but it only runs when a
            // crate HAS a Link module — an exec-only crate below that
            // bar (surfaced when the defs size gate was removed) would
            // otherwise verify a user-written `sorry` with nothing but
            // a warning. Generated shapes never emit sorry, so any
            // sorry diagnostic here is user tactic text.
            let sorries: Vec<TactusDiag> = r.diagnostics.iter()
                .filter(|d| d.severity == "warning" && d.data.contains("sorry"))
                .map(|d| {
                    let formatted = lean_process::format_error(d, source_map);
                    TactusDiag {
                        message: format!(
                            "sorry is fatal on the per-fn path (no Link gate covers {}): {}",
                            short_name(&proof_fn.name.path), formatted.message),
                        location: formatted.location,
                        help: Some(format!("{} {}",
                            vir::tactus_messages::LEAN_FILE_HELP_PREFIX, file_path.display())),
                    }
                })
                .collect();
            if !sorries.is_empty() {
                return CheckResult::Failed { errors: sorries, warnings: vec![] };
            }
            CheckResult::Success { warnings: lean_warnings(&r) }
        }
        Ok(r) => {
            let fn_short = short_name(&proof_fn.name.path);
            // Header parity with the island paths: exec islands say
            // "tactus_auto failed" (check_exec_fn), proof islands say
            // "tactic failed" — this formatter serves BOTH via the
            // package routes, so choose by mode (e2e tests pin the
            // phrasing; surfaced when the defs size gate was removed).
            let header = if matches!(proof_fn.mode, vir::ast::Mode::Exec) {
                format!("Lean tactus_auto failed for {}", fn_short)
            } else {
                format!("Lean tactic failed for {}", fn_short)
            };
            let help = Some(format!("{} {}",
                vir::tactus_messages::LEAN_FILE_HELP_PREFIX, file_path.display()));
            let errors: Vec<TactusDiag> = r.diagnostics.iter()
                .filter(|d| d.severity == "error")
                .map(|d| {
                    let formatted = lean_process::format_error(d, source_map);
                    TactusDiag {
                        message: format!("{}:\n\n{}", header, formatted.message),
                        location: formatted.location,
                        help: help.clone(),
                    }
                })
                .collect();
            // If Lean reported zero error-severity diagnostics (rare;
            // either a "no errors but Lean still failed" edge or the
            // `r.success` check above didn't match), surface a single
            // pointed-but-vague rejection so we don't silently swallow
            // the rejection.
            let errors = if errors.is_empty() {
                vec![TactusDiag {
                    message: format!("{}: {}", header,
                        vir::tactus_messages::NO_ERROR_DIAGNOSTICS_BODY),
                    location: DiagLocation::Unknown,
                    help,
                }]
            } else {
                errors
            };
            CheckResult::Failed { errors, warnings: lean_warnings(&r) }
        }
        Err(e) => CheckResult::Error(e),
    }
}

/// Codegen-only half of `check_exec_fn`: inline pass → SST→WP theorems →
/// preamble → pretty-print → write `.lean` → sanity check. Stops before the
/// Lean run. `Err(CheckResult)` carries a rejection / write error / sanity
/// failure (each already carrying any collected warnings).
// ── Package emission (emit-module, DESIGN-emit-module.md M2) ───────────
//
// Additive artifact stream behind `--tactus-emit-module`: alongside each
// island file, write the package-mode layers — a per-crate Stmts module
// (every tactic proof fn's contract as a reducible statement def, M1's
// renderer) and a per-fn Proofs module whose theorem takes its direct
// tactic-referenced helpers as hypothesis binders instead of
// re-elaborating them. Islands remain the checking authority; package
// files are emission-only until M4 wires build orchestration (olean
// builds + LEAN_PATH). Requires shared-defs mode (the Stmts module
// imports the defs module for the spec world).

static PACKAGE_ENABLED: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

/// Called once from the verifier with `args.tactus_emit_module`.
pub fn set_package_enabled(on: bool) {
    PACKAGE_ENABLED.store(on, std::sync::atomic::Ordering::SeqCst);
}
pub(crate) fn package_enabled() -> bool {
    PACKAGE_ENABLED.load(std::sync::atomic::Ordering::SeqCst)
}

static PACKAGE_CHECK_ENABLED: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

/// Called once from the verifier with `args.tactus_package_check`
/// (M5a). Package-check subsumes package EMISSION for the fns it
/// covers, but the emit-hook flag stays independent — gate mode and
/// check mode are separate dials.
pub fn set_package_check_enabled(on: bool) {
    PACKAGE_CHECK_ENABLED.store(on, std::sync::atomic::Ordering::SeqCst);
}
pub(crate) fn package_check_enabled() -> bool {
    PACKAGE_CHECK_ENABLED.load(std::sync::atomic::Ordering::SeqCst)
}

static BRIDGE_ENABLED: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

/// Called once from the verifier with `args.tactus_bridge` (W4a,
/// bootstrap-38). When on, the package gate additionally elaborates the
/// refWp↔production `decide` bridge over every emitted obligation cert
/// (INSIDE the gate — the same `example : goals_eq (ref_wp ctx sst) goals
/// = 1 := by decide` the probe `run.sh` scripts append externally). Opt-in
/// and verdict-neutral in W4a: PASS/FAIL is collected and reported, never
/// turned into a verification error (W4c does that). Needs tactus-core's
/// oleans on the elaboration path — see `run_bridge_step`.
pub fn set_bridge_enabled(on: bool) {
    BRIDGE_ENABLED.store(on, std::sync::atomic::Ordering::SeqCst);
}
pub(crate) fn bridge_enabled() -> bool {
    BRIDGE_ENABLED.load(std::sync::atomic::Ordering::SeqCst)
}

/// Package oleans built by per-fn checks THIS PROCESS (M5c): the
/// crate-end gate consults this to skip re-elaborating modules the
/// per-fn path already built — same-process writes, so no staleness
/// question. Keyed by the module's `.lean` path.
/// One constructor for proof-fn source maps (review finding: this was
/// hand-built at 3 sites, and it's load-bearing for diagnostic
/// attribution). `tactic_start` fallback is 1 — Lean lines are
/// 1-indexed; the fallback is unreachable for these modules (they
/// exist to hold a tactic) but a 0 would misattribute by one.
fn proof_fn_source_map(
    fn_name: &Fun,
    tactic_start: Option<usize>,
    tactic_body: &str,
) -> to_lean_fn::LeanSourceMap {
    to_lean_fn::LeanSourceMap::ProofFn {
        fn_name: short_name(&fn_name.path).to_string(),
        tactic_start_line: tactic_start.unwrap_or(1),
        tactic_line_count: tactic_body.lines().count().max(1),
    }
}

/// Per-key once-cell dedup (review finding: memo locks were held
/// across lean subprocess spawns, serializing unrelated bucket
/// threads). The global lock is held only for the entry lookup;
/// same-key callers serialize on the CELL (correct dedup), different
/// keys proceed in parallel.
fn memo_cell<K: Eq + std::hash::Hash + Clone, V>(
    memo: &'static std::sync::OnceLock<
        std::sync::Mutex<std::collections::HashMap<K, std::sync::Arc<std::sync::OnceLock<V>>>>>,
    key: &K,
) -> std::sync::Arc<std::sync::OnceLock<V>> {
    let m = memo.get_or_init(Default::default);
    let mut map = m.lock().unwrap_or_else(|p| p.into_inner());
    map.entry(key.clone()).or_default().clone()
}

/// Per-scope package graph (M5d-0, review finding): the inline
/// transform and the tactic-body dependency scan are scope-wide and
/// deterministic, but the per-fn check path re-paid them PER FN
/// (full krate clone + O(fns²·body) ident scans). Owned form so it
/// memoizes; consumers build a cheap borrowed view per call.
pub(crate) struct PkgGraph {
    inlined: std::sync::Arc<KrateX>,
    /// Emittable tactic proof fns, krate order (names).
    fns: Vec<Fun>,
    /// Direct helper deps by name.
    deps_of: std::collections::HashMap<Fun, Vec<Fun>>,
}

impl PkgGraph {
    /// Borrowed view in the shape the emitters consume — O(krate)
    /// hash lookups; the expensive work happened once at memo fill.
    fn view(&self) -> (Vec<&FunctionX>, std::collections::HashMap<&Fun, Vec<&FunctionX>>) {
        let by_name: std::collections::HashMap<&Fun, &FunctionX> =
            self.inlined.functions.iter().map(|f| (&f.x.name, &f.x)).collect();
        let fns: Vec<&FunctionX> =
            self.fns.iter().filter_map(|n| by_name.get(n).copied()).collect();
        let deps_of = self.fns.iter()
            .filter_map(|n| {
                let fx = *by_name.get(n)?;
                let deps: Vec<&FunctionX> = self.deps_of.get(n)?
                    .iter().filter_map(|d| by_name.get(d).copied()).collect();
                Some((&fx.name, deps))
            })
            .collect();
        (fns, deps_of)
    }
}

static PKG_GRAPH_MEMO: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<
        String, std::sync::Arc<std::sync::OnceLock<std::sync::Arc<PkgGraph>>>>>,
> = std::sync::OnceLock::new();

fn package_graph_for(
    krate: &KrateX,
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> std::sync::Arc<PkgGraph> {
    let key = crate::crate_defs::scope_key(crate_name, krate, tactic_bodies);
    let cell = memo_cell(&PKG_GRAPH_MEMO, &key);
    cell.get_or_init(|| {
        let inlined = std::sync::Arc::new(crate::inline_spec::inline_marked_in_krate(krate));
        let (fns, deps_of) = {
            let (fns_b, deps_b) = package_dep_graph(&inlined, tactic_bodies);
            let fns: Vec<Fun> = fns_b.iter().map(|f| f.name.clone()).collect();
            let deps_of: std::collections::HashMap<Fun, Vec<Fun>> = deps_b.iter()
                .map(|(k, v)| ((*k).clone(), v.iter().map(|f| f.name.clone()).collect()))
                .collect();
            (fns, deps_of)
        };
        std::sync::Arc::new(PkgGraph { inlined, fns, deps_of })
    }).clone()
}

/// C-2 (M6.3) exec obligation registry: what the Link module needs to
/// close exec obligations — recorded at pkg-emission time because the
/// obligations exist only in the SST (per-fn, at check time), while
/// `build_link_module` runs from the AST-level graph. Keyed by defs
/// scope; in package-check mode the Link builds exactly once, at the
/// crate gate, AFTER all per-fn checks — so the registry is complete
/// when read. Only `Ok(Single)` emissions record (island-fallback fns
/// have no pkg module to compose); Link elaboration re-checks every
/// imported module, so recording at emit (not verify) time keeps the
/// same semantics as the proof-fn side's krate enumeration.
struct ExecLinkEntry {
    /// pkg module leaf (import name).
    leaf: String,
    /// (obligation theorem name, helper deps in BINDER ORDER — the
    /// closed form applies `<dep>_closed` in exactly this order).
    obligations: Vec<(String, Vec<vir::ast::Path>)>,
    /// Stable dotted fn name (`lib.u_gapp_nil`) — the per-FN closed
    /// theorem's name root (Link-discharge L1).
    fn_name: String,
    /// Mode::Proof — only proof fns get per-fn closed theorems (true
    /// exec fns are skipped by design, DESIGN-link-discharge.md §3.4).
    is_proof: bool,
}

static EXEC_LINK_REGISTRY: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<String, Vec<ExecLinkEntry>>>,
> = std::sync::OnceLock::new();

fn record_exec_link_entry(scope: &str, entry: ExecLinkEntry) {
    let map = EXEC_LINK_REGISTRY.get_or_init(Default::default);
    let mut map = map.lock().unwrap_or_else(|p| p.into_inner());
    let entries = map.entry(scope.to_string()).or_default();
    // Re-emission of the same fn (memo miss across bucket threads)
    // replaces its entry — obligations are derived deterministically.
    entries.retain(|e| e.leaf != entry.leaf);
    entries.push(entry);
}

/// Cached-verdict observability (M6.2 fold-in): how many fns skipped
/// Lean entirely this run on a cross-run cached verdict. Reported in
/// the package gate note.
static PKG_CACHED_VERDICTS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
/// Link-discharge L1 census (per process, reported via the gate note).
static DISCHARGE_CLOSED: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
static DISCHARGE_PENDING: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
static DISCHARGE_DETAIL: std::sync::OnceLock<std::sync::Mutex<String>> =
    std::sync::OnceLock::new();
static ISLAND_CACHED_VERDICTS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

// N3-M0 closer census counters (DESIGN-N3-provenance-scripts.md §8):
// bumped once per emitted theorem by `census_bump` (the emitter sets
// the class alongside the closer selection); read once per crate run
// by `closer_census_report`. Six counters, one per `CloserCensus`
// variant — atomic like the other per-crate tallies above.
static CENSUS_S1_OMEGA: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
static CENSUS_RUNG_ONLY: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
static CENSUS_FORM_B: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
static CENSUS_FORM_E: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
static CENSUS_FORM_BE: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
static CENSUS_USER: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
static CENSUS_SCRIPT_A: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
static CENSUS_SCRIPT_B: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
static CENSUS_SCRIPT_C: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

/// Increment the census counter for one emitted theorem.
pub fn census_bump(c: crate::lean_ast::CloserCensus) {
    use std::sync::atomic::Ordering::Relaxed;
    match c {
        crate::lean_ast::CloserCensus::S1Omega => CENSUS_S1_OMEGA.fetch_add(1, Relaxed),
        crate::lean_ast::CloserCensus::RungOnly => CENSUS_RUNG_ONLY.fetch_add(1, Relaxed),
        crate::lean_ast::CloserCensus::RungFormB => CENSUS_FORM_B.fetch_add(1, Relaxed),
        crate::lean_ast::CloserCensus::RungFormE => CENSUS_FORM_E.fetch_add(1, Relaxed),
        crate::lean_ast::CloserCensus::RungFormBE => CENSUS_FORM_BE.fetch_add(1, Relaxed),
        crate::lean_ast::CloserCensus::User => CENSUS_USER.fetch_add(1, Relaxed),
        crate::lean_ast::CloserCensus::ScriptFormA => CENSUS_SCRIPT_A.fetch_add(1, Relaxed),
        crate::lean_ast::CloserCensus::ScriptFormB => CENSUS_SCRIPT_B.fetch_add(1, Relaxed),
        crate::lean_ast::CloserCensus::ScriptFormC => CENSUS_SCRIPT_C.fetch_add(1, Relaxed),
    };
}

/// The N4 summary line (DESIGN-N3 §8): one line per crate run, printed
/// unconditionally at crate end (empty when nothing was emitted — the
/// Lean backend wasn't in play). Script classes join in M2; the
/// ratchet asserts the script share never decreases from then on.
pub fn closer_census_report() -> String {
    use std::sync::atomic::Ordering::Relaxed;
    let s1 = CENSUS_S1_OMEGA.load(Relaxed);
    let rung = CENSUS_RUNG_ONLY.load(Relaxed);
    let b = CENSUS_FORM_B.load(Relaxed);
    let e = CENSUS_FORM_E.load(Relaxed);
    let be = CENSUS_FORM_BE.load(Relaxed);
    let u = CENSUS_USER.load(Relaxed);
    let sa = CENSUS_SCRIPT_A.load(Relaxed);
    let sb = CENSUS_SCRIPT_B.load(Relaxed);
    let sc = CENSUS_SCRIPT_C.load(Relaxed);
    if s1 + rung + b + e + be + u + sa + sb + sc == 0 {
        return String::new();
    }
    format!(
        "tactus: closers: {} script (A:{} B:{} C:{}) / {} s1-omega / {} rung:formB / {} rung:formE / {} rung:formB+formE / {} rung-only / {} user-supplied",
        sa + sb + sc, sa, sb, sc, s1, b, e, be, rung, u
    )
}

static PKG_OLEAN_BUILT: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashSet<std::path::PathBuf>>,
> = std::sync::OnceLock::new();

fn record_pkg_olean_built(path: &Path) {
    PKG_OLEAN_BUILT.get_or_init(Default::default)
        .lock().unwrap_or_else(|p| p.into_inner())
        .insert(path.to_path_buf());
}
fn pkg_olean_built(path: &Path) -> bool {
    PKG_OLEAN_BUILT.get_or_init(Default::default)
        .lock().unwrap_or_else(|p| p.into_inner())
        .contains(path)
}

/// Module-level verdict for a mutual module: success, or Lean's
/// parsed `--json` diagnostics for per-member region attribution.
struct MutualVerdict {
    success: bool,
    diagnostics: Vec<lean_process::LeanDiagnostic>,
}

/// Mutual-module verdict memo: the first member's check elaborates the
/// SCC's module (fast `lean -o` path; on failure, a `--json` re-run
/// captures diagnostics); every member reads the shared verdict and
/// formats its OWN region's errors (M5b).
static MUTUAL_CHECK_MEMO: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<
        std::path::PathBuf,
        std::sync::Arc<std::sync::OnceLock<std::sync::Arc<MutualVerdict>>>>>,
> = std::sync::OnceLock::new();

/// Stmts-olean memo for the package-check path: the `.lean` is written
/// by `stmts_for_crate`; this builds its olean once per scope per
/// process (pkg modules import it). `Err` is cached — fail once, not
/// once per fn.
static STMTS_OLEAN_MEMO: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<
        String, std::sync::Arc<std::sync::OnceLock<Result<(), String>>>>>,
> = std::sync::OnceLock::new();

/// Ensure ONE stmt module's olean exists (M5d-2; the `.lean` was
/// written by the partition build, which emission always runs first).
/// Returns whether the olean was already built this process (reused).
/// `may_skip` (M5e): the module's `.lean` content is unchanged AND
/// the defs it imports had no breaking rebuild — its existing olean
/// is still valid, so priming the memo without a lean run is sound.
fn ensure_stmt_olean(
    module: &str,
    defs: &crate::crate_defs::CrateDefs,
    prelude_dir: &Path,
    may_skip: bool,
) -> Result<bool, String> {
    let key = module.to_string();
    let cell = memo_cell(&STMTS_OLEAN_MEMO, &key);
    let pre = cell.get().is_some();
    let skipped = std::cell::Cell::new(false);
    cell.get_or_init(|| {
        if may_skip && defs.dir.join(format!("{}.olean", module)).exists() {
            skipped.set(true);
            return Ok(());
        }
        let base_path = format!("{}:{}", prelude_dir.display(), defs.dir.display());
        let mut failures: Vec<(String, String)> = Vec::new();
        run_lean(&defs.dir, module, true, &base_path, &mut failures);
        match failures.pop() {
            None => Ok(()),
            Some((_, out)) => Err(format!("stmt olean build failed ({}):\n{}", module, out)),
        }
    }).clone().map(|()| pre || skipped.get())
}

/// Verify one tactic proof fn via its package module (M5a). Two-phase:
/// `lean -o` builds the olean — the fast path, and the olean is
/// exactly what the crate-end Link pass needs — and only on failure do
/// we re-run through `check_lean_file --json` for span-mapped
/// diagnostics (failures are the rare case; the double elaboration
/// prices in only where a human is about to read output).
/// C-1 family unification (DESIGN-exec-packages.md M6.3/C): the ONE
/// defs family package machinery verifies against — the FULL-ROOTS
/// (exec) family when it covers exec, else the proof family as
/// degradation. One family means one stmt partition and one Link for
/// the whole crate; on the happy path the proof-only ladder is never
/// attempted. Selection is memoized per scope inside `for_crate`, so
/// the choice is stable within a run.
/// One lean-routed verification job, as data for `prime_lean_driver` —
/// mirrors the verifier's `TactusLeanJob` without importing its type.
pub enum PrimeJob<'a> {
    Proof { f: &'a FunctionX, tactic_body: &'a str, imports: &'a [String] },
    Exec {
        f: &'a FunctionX,
        fn_sst: &'a FunctionSst,
        check: &'a FuncCheckSst,
        imports: &'a [String],
    },
}

/// Package-emission outcomes produced by the prime pass, consumed by
/// the per-fn check paths. The stash (rather than re-emitting in the
/// worker) matters for M5e: emission computes each module's `changed`
/// flag by comparing against the on-disk content BEFORE writing — a
/// second emission would always see "unchanged" and could take the
/// cross-run cache shortcut on a fn that genuinely changed this run.
static PRIME_OUTCOMES: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<Fun, Result<PkgEmitOutcome, String>>>,
> = std::sync::OnceLock::new();

fn stash_prime_outcome(f: &Fun, outcome: Result<PkgEmitOutcome, String>) {
    PRIME_OUTCOMES.get_or_init(Default::default)
        .lock().unwrap()
        .insert(f.clone(), outcome);
}

fn take_prime_outcome(f: &Fun) -> Option<Result<PkgEmitOutcome, String>> {
    PRIME_OUTCOMES.get()?.lock().unwrap().remove(f)
}

/// Prime the persistent-driver pool for this crate's per-fn package
/// phase (DESIGN-lean-driver.md). Called once before the verifier's
/// worker pool:
/// 1. spawn `workers` drivers, base snapshot (defs umbrella) on each;
/// 2. run package EMISSION for every job (pure Rust, stashing each
///    outcome for the worker's check path), collecting the full stmt
///    module set;
/// 3. build stmt oleans through the drivers (workers-parallel, memo
///    shared with the check path via `ensure_stmt_olean`);
/// 4. establish the WIDE snapshot (defs + every stmt) on each driver,
///    so per-fn pkg checks elaborate as ~ms branches.
/// A no-op when the driver is disabled, the crate is below the routing
/// floor, or the crate has no package defs. Failure never surfaces —
/// checks fall back to process-per-file.
/// Returns a claim-order permutation of `jobs` (largest emitted pkg
/// module first — pkg text size is a good proxy for elaboration time,
/// and starting the slowest check first minimizes the pool's critical
/// path). Identity order when priming is skipped.
pub fn prime_lean_driver(
    krate: &KrateX,
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
    jobs: &[PrimeJob],
    workers: usize,
) -> Vec<usize> {
    let identity = || (0..jobs.len()).collect::<Vec<usize>>();
    if !crate::driver_client::enabled() {
        return identity();
    }
    // Routing economics: the driver's fixed cost (boot + two
    // importModules ≈ 3.5s) beats process-per-file (~2s/fn) only once
    // a crate has enough lean-routed fns. Below the floor the ordinary
    // path is faster — tiny e2e crates stay as they are; big crates
    // (tactus-core, gt) amortize the prime across hundreds of ms-cost
    // checks.
    let min_jobs = std::env::var("TACTUS_DRIVER_MIN_JOBS").ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(6);
    if jobs.len() < min_jobs {
        return identity();
    }
    install_emit_tables(krate, crate_name);
    let Some(defs) = unified_package_defs(krate, crate_name, tactic_bodies) else {
        return identity();
    };
    let Ok(prelude_dir) = crate::prelude::ensure_prelude_olean() else {
        return identity();
    };
    let base_path = format!("{}:{}", prelude_dir.display(), defs.dir.display());
    let merged = merged_lean_path(&base_path);
    if !crate::driver_client::spawn_pool(&merged, workers, &[defs.module_name.clone()]) {
        return identity();
    }

    // Emission pass: write pkg + stmt modules for every job, stash the
    // outcome, collect the stmt set (module → any-changed) and each
    // job's pkg module size (for the claim-order permutation).
    let mut stmts: std::collections::BTreeMap<String, bool> = Default::default();
    let mut sizes: Vec<u64> = vec![0; jobs.len()];
    for (ji, job) in jobs.iter().enumerate() {
        let (name, outcome) = match job {
            PrimeJob::Proof { f, tactic_body, imports } => (
                &f.name,
                emit_package_proof_fn(
                    krate, f, tactic_body, imports, crate_name, tactic_bodies, &defs,
                ),
            ),
            PrimeJob::Exec { f, fn_sst, check, imports } => (
                &f.name,
                emit_package_exec_fn(
                    krate, f, fn_sst, check, imports, crate_name, tactic_bodies, &defs,
                ),
            ),
        };
        match &outcome {
            Ok(PkgEmitOutcome::Single { stmt_modules, path, .. })
            | Ok(PkgEmitOutcome::Mutual { stmt_modules, path, .. }) => {
                for (m, ch) in stmt_modules {
                    *stmts.entry(m.clone()).or_default() |= *ch;
                }
                sizes[ji] = std::fs::metadata(path).map(|md| md.len()).unwrap_or(0);
            }
            _ => {}
        }
        stash_prime_outcome(name, outcome);
    }

    // Stmt oleans, workers-parallel through the drivers (the memo in
    // `ensure_stmt_olean` makes the worker-phase calls no-ops).
    let stmt_list: Vec<(&String, bool)> = stmts.iter().map(|(m, ch)| (m, *ch)).collect();
    let next = std::sync::atomic::AtomicUsize::new(0);
    std::thread::scope(|scope| {
        for _ in 0..workers.max(1).min(stmt_list.len().max(1)) {
            let stmt_list = &stmt_list;
            let next = &next;
            let defs = &defs;
            let prelude_dir = &prelude_dir;
            scope.spawn(move || loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let Some((m, ch)) = stmt_list.get(i) else { break };
                let may_skip = !*ch && !defs.breaking;
                let _ = ensure_stmt_olean(m.as_str(), defs, prelude_dir, may_skip);
            });
        }
    });

    // Wide snapshot over defs + every stmt whose olean exists (a
    // failed stmt build must not sink the snapshot; its pkg checks
    // fall back).
    let mut wide: Vec<String> = vec![defs.module_name.clone()];
    wide.extend(stmt_list.iter()
        .filter(|(m, _)| defs.dir.join(format!("{m}.olean")).exists())
        .map(|(m, _)| (*m).clone()));
    crate::driver_client::add_snapshot_all("wide", &wide);
    // Search-ladder variant: pkg files whose closers needed the search
    // rung additionally import TactusSearch. Give them their own
    // superset snapshot — minimal-covering selection keeps everyone
    // else on plain "wide".
    let mut wide_search = wide.clone();
    wide_search.push("TactusSearch".to_string());
    crate::driver_client::add_snapshot_all("wide_search", &wide_search);

    let mut order = identity();
    order.sort_by_key(|&i| std::cmp::Reverse(sizes[i]));
    order
}

fn unified_package_defs(
    krate: &KrateX,
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> Option<std::sync::Arc<crate::crate_defs::CrateDefs>> {
    crate::crate_defs::for_crate(
        krate, crate_name, tactic_bodies, true, crate::crate_defs::ScopeKind::Exec,
    ).filter(|d| d.covers_exec)
    .or_else(|| crate::crate_defs::for_crate(
        krate, crate_name, tactic_bodies, true, crate::crate_defs::ScopeKind::Proof,
    ))
}

fn check_proof_fn_via_package(
    krate: &KrateX,
    proof_fn: &FunctionX,
    tactic_body: &str,
    imports: &[String],
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> Option<CheckResult> {
    install_emit_tables(krate, crate_name);
    // Silent fallback: defs build failures (already reported loudly by
    // `guard_build`) verify via islands exactly as pre-M6.5; the
    // crate-end gate note summarizes.
    let defs = unified_package_defs(krate, crate_name, tactic_bodies)?;
    let prelude_dir = match crate::prelude::ensure_prelude_olean() {
        Ok(d) => d,
        Err(e) => return Some(CheckResult::Error(e)),
    };
    let base_path = format!("{}:{}", prelude_dir.display(), defs.dir.display());
    // Consume the prime pass's stashed emission if there is one (see
    // PRIME_OUTCOMES: re-emitting would corrupt the changed flags).
    let emitted = take_prime_outcome(&proof_fn.name).unwrap_or_else(|| {
        emit_package_proof_fn(
            krate, proof_fn, tactic_body, imports, crate_name, tactic_bodies, &defs,
        )
    });
    match emitted {
        Ok(PkgEmitOutcome::Single { leaf, path, source_map, stmt_modules, changed }) => {
            // Cross-run cache (M5e): everything this module sees is
            // unchanged (own text, stmt imports, defs non-breaking) and
            // its olean exists — the prior verdict stands. Sorry
            // remains gated: the Link pass re-checks the closure every
            // run, so a cached fn can't smuggle one through.
            let olean = path.with_extension("olean");
            let cacheable = !changed
                && stmt_modules.iter().all(|(_, ch)| !ch)
                && !defs.breaking
                && olean.exists();
            if cacheable {
                record_pkg_olean_built(&path);
                PKG_CACHED_VERDICTS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                return Some(CheckResult::Success { warnings: vec![] });
            }
            for (m, ch) in &stmt_modules {
                let may_skip = !ch && !defs.breaking;
                if let Err(e) = ensure_stmt_olean(m, &defs, &prelude_dir, may_skip) {
                    return Some(CheckResult::Error(e));
                }
            }
            // One `--json -o` pass: olean for the Link gate AND parsed
            // diagnostics, so warnings survive the fast path.
            let pkg_dir = path.parent().expect("pkg file has a parent").to_path_buf();
            let result = run_lean_json(&pkg_dir, &leaf, true, &base_path);
            if matches!(&result, Ok(r) if r.success) {
                record_pkg_olean_built(&path);
            }
            Some(format_lean_check_result(result, proof_fn, &path, &source_map))
        }
        Ok(PkgEmitOutcome::Mutual { leaf, path, members, stmt_modules, changed }) => {
            for (m, ch) in &stmt_modules {
                let may_skip = !ch && !defs.breaking;
                if let Err(e) = ensure_stmt_olean(m, &defs, &prelude_dir, may_skip) {
                    return Some(CheckResult::Error(e));
                }
            }
            let cacheable = !changed
                && stmt_modules.iter().all(|(_, ch)| !ch)
                && !defs.breaking
                && path.with_extension("olean").exists();
            let cell = memo_cell(&MUTUAL_CHECK_MEMO, &path);
            let verdict = cell.get_or_init(|| {
                if cacheable {
                    return std::sync::Arc::new(MutualVerdict {
                        success: true, diagnostics: vec![],
                    });
                }
                let pkg_dir = path.parent().expect("pkg file has a parent");
                // One `--json -o` pass; diagnostics stored on success
                // too, so members can surface own-region WARNINGS
                // (sorry etc.), not just errors.
                match run_lean_json(pkg_dir, &leaf, true, &base_path) {
                    Ok(r) => std::sync::Arc::new(MutualVerdict {
                        success: r.success, diagnostics: r.diagnostics,
                    }),
                    Err(_) => std::sync::Arc::new(MutualVerdict {
                        success: false, diagnostics: vec![],
                    }),
                }
            }).clone();
            let me_early = members.iter().find(|m| m.fun == proof_fn.name)
                .expect("proof fn is a member of its own SCC module");
            let owner_start_of = |line: usize| members.iter()
                .filter(|m| m.tactic_start <= line)
                .map(|m| m.tactic_start)
                .max();
            let own_region = |d: &lean_process::LeanDiagnostic| {
                match d.pos.as_ref().map(|p| owner_start_of(p.line)) {
                    Some(Some(start)) => start == me_early.tactic_start,
                    _ => true, // module-level: attributed to everyone
                }
            };
            if verdict.success {
                record_pkg_olean_built(&path);
                let warnings: Vec<String> = verdict.diagnostics.iter()
                    .filter(|d| d.severity == "warning" && d.data.contains("sorry"))
                    .filter(|d| own_region(d))
                    .map(|d| {
                        let formatted = lean_process::format_error(d, &me_early.source_map);
                        format!("Lean warning in {}: {}", me_early.short, formatted.message)
                    })
                    .collect();
                return Some(CheckResult::Success { warnings });
            }
            // Verdict is module-level — mutual members are an
            // INSEPARABLE unit (each cites the other), so every member
            // fails when the module does. Attribution is region-based:
            // an error belongs to the member whose tactic region
            // contains it; errors before the first region (imports /
            // preamble) belong to everyone.
            let me = me_early;
            let own: Vec<lean_process::LeanDiagnostic> = verdict.diagnostics.iter()
                .filter(|d| d.severity == "error")
                .filter(|d| own_region(d))
                .cloned()
                .collect();
            Some(if own.is_empty() {
                // Own region clean — the failure lives in a partner.
                let partners: Vec<&str> = members.iter()
                    .filter(|m| m.fun != proof_fn.name)
                    .map(|m| m.short.as_str())
                    .collect();
                CheckResult::Failed {
                    errors: vec![TactusDiag {
                        message: format!(
                            "Lean mutual module `{}` failed: `{}`'s own proof region is \
                             clean, but mutual members verify as a unit and partner(s) \
                             {} have errors (see their diagnostics)",
                            leaf, me.short, partners.join(", ")
                        ),
                        location: DiagLocation::Unknown,
                        help: Some(format!("{} {}",
                            vir::tactus_messages::LEAN_FILE_HELP_PREFIX, path.display())),
                    }],
                    warnings: vec![],
                }
            } else {
                // Own-region errors through the shared chokepoint with
                // this member's OWN source map — same spans as islands.
                format_lean_check_result(
                    Ok(lean_process::LeanResult { success: false, diagnostics: own }),
                    proof_fn, &path, &me.source_map,
                )
            })
        }
        // Unsupported shapes and emission failures FALL BACK to the
        // island path (`None` — check_proof_fn continues): islands are
        // the proven route, packages the upgrade. The Link builder
        // excludes these fns via its cycle-poisoning pass, so the gate
        // still covers everything that DID take the package route; the
        // fallback is reported, not silent.
        Ok(PkgEmitOutcome::UnsupportedScc(reason)) => {
            eprintln!(
                "tactus: package-check falling back to island for `{}`: {}",
                short_name(&proof_fn.name.path), reason
            );
            None
        }
        Err(e) => {
            eprintln!(
                "tactus: package-check falling back to island for `{}` (emission failed: {})",
                short_name(&proof_fn.name.path), e
            );
            None
        }
    }
}

/// The population that gets statement defs in the Stmts module and can
/// arrive as hypothesis binders at use sites — identical to the island
/// preamble's `helpers_to_emit` filter (proof mode, not a trait method,
/// has a tactic body), so the package and island views of "what is a
/// helper lemma" cannot diverge.
fn is_emittable_tactic_proof_fn(
    f: &FunctionX,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> bool {
    matches!(f.mode, vir::ast::Mode::Proof)
        && !matches!(
            f.kind,
            FunctionKind::TraitMethodDecl { .. } | FunctionKind::TraitMethodImpl { .. }
        )
        && tactic_bodies.contains_key(&f.name)
}

/// Lean module name of the crate's Stmts module, derived from the defs
/// module name so the two scope-naming schemes cannot drift.
/// Sibling-module name from the defs SCOPE (not string surgery on the
/// defs module name — review finding: `replacen` breaks silently if
/// defs naming ever changes).
fn scope_module_name(kind: &str, defs: &crate::crate_defs::CrateDefs) -> String {
    format!("Tactus{}_{}", kind, defs.scope)
}

fn stmts_module_name(defs: &crate::crate_defs::CrateDefs) -> String {
    scope_module_name("Stmts", defs)
}

/// Per-fn stmt module name: `TactusStmts_<scope>__<fn>` (M5d-2). A new
/// lemma creates a NEW file; nothing existing changes — the structural
/// append-safety the M5 design asks for. A pkg module's import list of
/// these IS its dependency manifest.
fn stmt_fn_module_name(defs: &crate::crate_defs::CrateDefs, f: &Fun) -> String {
    format!("{}__{}", stmts_module_name(defs),
        lean_name(&f.path).replace('.', "__"))
}

/// The per-fn stmt partition: for each emittable proof fn, its stmt
/// module name + the module's full command stream (for per-fn sanity
/// concatenation — identifier resolution must see what Lean will see).
/// name, module cmds (sanity concat), content-changed-this-run (M5e).
type StmtPartition =
    std::collections::HashMap<Fun, (String, std::sync::Arc<Vec<Command>>, bool)>;

/// Partition memo: one build + N file writes per scope per process.
/// `None` = a previous attempt failed (fail once, warn once), same
/// semantics as the defs memo. Keyed by the scope-bearing stmts name.
static STMT_PARTITION_MEMO: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<
        String, Option<std::sync::Arc<StmtPartition>>>>,
> = std::sync::OnceLock::new();

/// Build + write the crate's Stmts module: `import <defs module>` plus a
/// statement def for every emittable tactic proof fn. Written into
/// `defs.dir` so one directory serves as the import root for both
/// modules. Returns the command stream (for per-fn sanity
/// concatenation — identifier resolution must see what Lean will see).
///
/// The krate gets the same `inline_spec` pass the theorem path applies,
/// so statement defs and theorem goals agree — the statement-identity
/// property (§4.1).
fn stmt_partition_for(
    krate: &KrateX,
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
    defs: &crate::crate_defs::CrateDefs,
) -> Option<std::sync::Arc<StmtPartition>> {
    let key = stmts_module_name(defs);
    let memo = STMT_PARTITION_MEMO.get_or_init(Default::default);
    if let Some(hit) = memo.lock().unwrap_or_else(|p| p.into_inner()).get(&key) {
        return hit.clone();
    }
    let entry = match build_stmt_partition(krate, crate_name, tactic_bodies, defs) {
        Ok(part) => Some(std::sync::Arc::new(part)),
        Err(e) => {
            eprintln!(
                "tactus: Stmts partition build failed for crate `{}` ({}); \
                 package emission disabled for this scope",
                crate_name, e
            );
            None
        }
    };
    memo.lock().unwrap_or_else(|p| p.into_inner()).insert(key, entry.clone());
    entry
}

/// Build + write ONE stmt module per emittable proof fn (M5d-2): each
/// contains `import <defs>` + that fn's statement def. The preamble is
/// identical across modules (roots are empty in ProofFnPackage mode) —
/// built once, cloned per fn.
fn build_stmt_partition(
    krate: &KrateX,
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
    defs: &crate::crate_defs::CrateDefs,
) -> Result<StmtPartition, String> {
    let inlined_krate = crate::inline_spec::inline_marked_in_krate(krate);
    let (preamble, ns) = krate_preamble(
        &inlined_krate, &[], crate_name, &[], PreambleConfig::ProofFnPackage, &[],
        tactic_bodies, &[], Some(defs),
    );
    let ectx = crate::emit_ctx::EmitCtx::build(&inlined_krate, tactic_bodies);
    let mut out: StmtPartition = Default::default();
    for f in inlined_krate.functions.iter().map(|f| &f.x) {
        if !is_emittable_tactic_proof_fn(f, tactic_bodies) {
            continue;
        }
        let mut cmds = preamble.clone();
        cmds.push(to_lean_fn::proof_fn_stmt_cmd(f, &ectx));
        // Sanity over what Lean will see: defs stream + this module.
        #[cfg(debug_assertions)]
        {
            let concat: Vec<Command> =
                defs.cmds.iter().cloned().chain(cmds.iter().cloned()).collect();
            debug_check(&concat)?;
        }
        let rendered = pp_commands(&cmds);
        let name = stmt_fn_module_name(defs, &f.name);
        let path = defs.dir.join(format!("{}.lean", name));
        let changed = write_lean_file_tracked(&path, &rendered.text)?;
        out.insert(f.name.clone(), (name, std::sync::Arc::new(cmds), changed));
    }
    Ok(out)
}

/// Package-mode Proofs module for one tactic proof fn: the island's
/// theorem with direct tactic-referenced helpers prepended as
/// hypothesis binders (`(<short name> : <name>_stmt)` — the binder name
/// is exactly what the raw tactic text references, so the body
/// elaborates unchanged), importing the Stmts module instead of
/// re-elaborating helper theorems. Written under `pkg/` next to the
/// island files.
/// What package emission did for one fn — the emit-hook logs
/// `UnsupportedScc`, the M4 gate collects module leafs to elaborate.
pub enum PkgEmitOutcome {
    /// Single-fn Proofs module written.
    Single {
        leaf: String,
        path: std::path::PathBuf,
        /// Tactic-line → Rust-span mapping, same mechanism as island
        /// emission — package-check failures point at the same source
        /// locations island failures do.
        source_map: to_lean_fn::LeanSourceMap,
        /// Stmt modules this pkg module imports (self + direct deps,
        /// M5d-2), with each one's content-changed flag (M5e) — the
        /// check path ensures exactly these oleans.
        stmt_modules: Vec<(String, bool)>,
        /// Whether this pkg module's own content changed this run.
        changed: bool,
    },
    /// Fn is a member of a supported mutual SCC; leaf/path name the
    /// SCC's canonical module (same for every member); `members`
    /// carries per-member attribution maps (M5b).
    Mutual {
        leaf: String,
        path: std::path::PathBuf,
        members: std::sync::Arc<Vec<MutualMember>>,
        /// Stmt modules of all SCC members (M5d-2), with changed flags.
        stmt_modules: Vec<(String, bool)>,
        /// Whether the mutual module's own content changed this run.
        changed: bool,
    },
    /// Fn is on a cycle with SCC-external helper deps — not
    /// package-expressible; payload = human-readable reason.
    UnsupportedScc(String),
}

fn emit_package_proof_fn(
    krate: &KrateX,
    proof_fn: &FunctionX,
    tactic_body: &str,
    imports: &[String],
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
    defs: &crate::crate_defs::CrateDefs,
) -> Result<PkgEmitOutcome, String> {
    let g = package_graph_for(krate, crate_name, tactic_bodies);
    let view = g.view();
    emit_package_proof_fn_inner(
        &g.inlined, &view, proof_fn, tactic_body, imports, crate_name,
        tactic_bodies, defs,
    )
}

/// Inner emission over an ALREADY-INLINED krate + dep graph — the M4
/// gate calls this directly so a whole-crate pass pays the inline
/// transform and the tactic-body dependency scan once, not per fn.
fn emit_package_proof_fn_inner(
    inlined_krate: &KrateX,
    (fns, deps_of): &(Vec<&FunctionX>, std::collections::HashMap<&Fun, Vec<&FunctionX>>),
    proof_fn: &FunctionX,
    tactic_body: &str,
    imports: &[String],
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
    defs: &crate::crate_defs::CrateDefs,
) -> Result<PkgEmitOutcome, String> {
    let stmts = stmt_partition_for(inlined_krate, crate_name, tactic_bodies, defs)
        .ok_or("Stmts partition unavailable")?;
    let proof_fn = inlined_krate.functions.iter()
        .find(|f| f.x.name == proof_fn.name).map(|f| &f.x)
        .expect("root proof fn present in inlined krate");
    // Mutual SCC route (M3.5): fns on a direct-reference cycle emit as
    // ONE canonical module holding a `mutual … end` block — within-SCC
    // references stay direct (same block), `termination_by` comes from
    // each member's `decreases`. Only supported when the SCC has no
    // EXTERNAL helper deps (see `scc_external_deps`).
    if let Some(scc) = package_scc_of(proof_fn, fns, deps_of) {
        let ext = scc_external_deps(&scc, deps_of);
        if !ext.is_empty() {
            return Ok(PkgEmitOutcome::UnsupportedScc(format!(
                "mutual tactic SCC {{{}}} has helper deps outside the SCC ({}) — \
                 unsupported: external deps arrive as hypothesis binders, which \
                 verbatim mutual references cannot pass",
                scc.iter().map(|f| short_name(&f.name.path)).collect::<Vec<_>>().join(", "),
                ext.iter().map(|f| short_name(&f.name.path)).collect::<Vec<_>>().join(", "),
            )));
        }
        let leaf = mutual_module_leaf(&scc);
        let stmt_modules: Vec<(String, bool)> = scc.iter()
            .filter_map(|f| stmts.get(&f.name).map(|(n, _, ch)| (n.clone(), *ch)))
            .collect();
        let (path, members, changed) = emit_package_mutual_scc(
            inlined_krate, &scc, imports, crate_name, tactic_bodies, defs, &stmts,
        )?;
        return Ok(PkgEmitOutcome::Mutual { leaf, path, members, stmt_modules, changed });
    }
    // Direct helper references: same textual scan the island helper
    // walk uses (`collect_referenced_proof_fns`), but non-recursive —
    // each helper's own Proofs module carries its own hypotheses, and
    // the Link module (M3) composes the closed forms. The shared
    // `direct_helper_deps` enumeration is load-bearing: Link applies
    // closed forms in exactly this order.
    let deps = direct_helper_deps(proof_fn, tactic_body, inlined_krate, tactic_bodies);
    // Imports = stmt modules of self + direct deps (M5d-2): the import
    // list IS the dependency manifest, readable off the artifact.
    let needed: Vec<&FunctionX> = std::iter::once(proof_fn)
        .chain(deps.iter().copied())
        .collect();
    // (name, content-changed) — dedup preserves first occurrence.
    let stmt_modules: Vec<(String, bool)> = {
        let mut seen = std::collections::HashSet::new();
        needed.iter()
            .filter_map(|f| stmts.get(&f.name)
                .map(|(n, _, ch)| (n.clone(), *ch)))
            .filter(|(n, _)| seen.insert(n.clone()))
            .collect()
    };
    let mut file_imports: Vec<String> = imports.to_vec();
    file_imports.extend(stmt_modules.iter().map(|(n, _)| n.clone()));
    let (mut cmds, ns) = krate_preamble(
        inlined_krate, &file_imports, crate_name, &[proof_fn],
        PreambleConfig::ProofFnPackage, &[], tactic_bodies, &[], Some(defs),
    );
    let ectx = crate::emit_ctx::EmitCtx::build(inlined_krate, tactic_bodies);
    let mut thm = to_lean_fn::proof_fn_to_ast(proof_fn, tactic_body, &ectx);
    let hyps: Vec<crate::lean_ast::Binder> = deps.iter()
        .map(|f| to_lean_fn::helper_hyp_binder(&f.name.path))
        .collect();
    thm.binders.splice(0..0, hyps);
    cmds.push(Command::Theorem(thm));
    // Sanity over the full import concatenation: defs + the imported
    // stmt modules + this. (debug builds only.)
    #[cfg(debug_assertions)]
    {
        let concat: Vec<Command> = defs.cmds.iter()
            .chain(needed.iter()
                .filter_map(|f| stmts.get(&f.name))
                .flat_map(|(_, c, _)| c.iter()))
            .chain(cmds.iter())
            .cloned().collect();
        debug_check(&concat)?;
    }
    #[cfg(not(debug_assertions))]
    let _ = &stmts;
    let rendered = pp_commands(&cmds);
    let leaf = lean_name(&proof_fn.name.path).replace('.', "__");
    let path = lean_out_root().join(sanitize(crate_name)).join("pkg")
        .join(format!("{}.lean", leaf));
    let changed = write_lean_file_tracked(&path, &rendered.text)?;
    let source_map = proof_fn_source_map(
        &proof_fn.name, rendered.landmarks.tactic_starts.first().copied(), tactic_body);
    Ok(PkgEmitOutcome::Single { leaf, path, source_map, stmt_modules, changed })
}

/// Per-member attribution info for one theorem inside a mutual
/// module: where its tactic body starts in the emitted file (region
/// boundary for diagnostic ownership) and its own source map.
pub struct MutualMember {
    pub fun: Fun,
    pub short: String,
    pub tactic_start: usize,
    pub source_map: to_lean_fn::LeanSourceMap,
}

/// Mutual-SCC-module memo: written once per canonical path per
/// process; the value carries the per-member maps so memo-hit callers
/// (every member after the first) can still attribute diagnostics.
static MUTUAL_MEMO: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<
        std::path::PathBuf, (std::sync::Arc<Vec<MutualMember>>, bool)>>,
> = std::sync::OnceLock::new();

/// Package module for a mutual tactic SCC: one file, all members'
/// theorems in a `mutual … end` block (the M0 probe's `MutualEO`
/// shape). No hypothesis binders — the SCC has no external deps
/// (caller checked) and within-SCC references resolve inside the
/// block. Known limitation: fn-level Mathlib imports are taken from
/// whichever member's emission call writes first; a member-specific
/// import missing from the first writer surfaces as a Lean error at
/// package elaboration (M4), not silently.
fn emit_package_mutual_scc(
    inlined_krate: &KrateX,
    scc: &[&FunctionX],
    imports: &[String],
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
    defs: &crate::crate_defs::CrateDefs,
    stmts: &std::sync::Arc<StmtPartition>,
) -> Result<(std::path::PathBuf, std::sync::Arc<Vec<MutualMember>>, bool), String> {
    let path = lean_out_root().join(sanitize(crate_name)).join("pkg")
        .join(format!("{}.lean", mutual_module_leaf(scc)));
    {
        let memo = MUTUAL_MEMO.get_or_init(Default::default);
        if let Some((members, changed)) = memo.lock().unwrap_or_else(|p| p.into_inner()).get(&path) {
            return Ok((path, members.clone(), *changed)); // written by another member's call
        }
    }
    let mut file_imports: Vec<String> = imports.to_vec();
    file_imports.extend(scc.iter().map(|f| stmt_fn_module_name(defs, &f.name)));
    let (mut cmds, ns) = krate_preamble(
        inlined_krate, &file_imports, crate_name, scc,
        PreambleConfig::ProofFnPackage, &[], tactic_bodies, &[], Some(defs),
    );
    let ectx = crate::emit_ctx::EmitCtx::build(inlined_krate, tactic_bodies);
    let block: Vec<Command> = scc.iter()
        .map(|f| {
            let body = tactic_bodies.get(&f.name)
                .ok_or_else(|| format!("no tactic body for SCC member {}", short_name(&f.name.path)))?;
            Ok(Command::Theorem(to_lean_fn::proof_fn_to_ast(f, body, &ectx)))
        })
        .collect::<Result<_, String>>()?;
    cmds.push(Command::Mutual(block));
    #[cfg(debug_assertions)]
    {
        let concat: Vec<Command> = defs.cmds.iter()
            .chain(scc.iter()
                .filter_map(|f| stmts.get(&f.name))
                .flat_map(|(_, c, _)| c.iter()))
            .chain(cmds.iter())
            .cloned().collect();
        debug_check(&concat)?;
    }
    #[cfg(not(debug_assertions))]
    let _ = &stmts;
    let rendered = pp_commands(&cmds);
    let changed = write_lean_file_tracked(&path, &rendered.text)?;
    // One tactic_starts entry per Tactic::Raw in emission order = one
    // per SCC member. A member's diagnostic REGION starts at its
    // tactic start; theorem-header errors land in the preceding
    // region (or pre-first = module-level) — rare, and module-level
    // errors are attributed to every member anyway.
    let members: Vec<MutualMember> = scc.iter().zip(rendered.landmarks.tactic_starts.iter())
        .map(|(f, start)| {
            let body = tactic_bodies.get(&f.name).map(|s| s.as_str()).unwrap_or("");
            MutualMember {
                fun: f.name.clone(),
                short: short_name(&f.name.path).to_string(),
                tactic_start: *start,
                source_map: proof_fn_source_map(&f.name, Some(*start), body),
            }
        })
        .collect();
    let members = std::sync::Arc::new(members);
    MUTUAL_MEMO.get_or_init(Default::default)
        .lock().unwrap_or_else(|p| p.into_inner())
        .insert(path.clone(), (members.clone(), changed));
    Ok((path, members, changed))
}

// ── Package gate (M4) ───────────────────────────────────────────────

/// Result of the crate-level package gate.
pub struct PackageGateReport {
    /// Modules elaborated (defs + stmts + pkg modules + Link).
    pub modules: usize,
    /// Of `modules`, how many were reused from per-fn package checks
    /// (oleans built earlier this process — M5c).
    pub reused: usize,
    /// Cross-run cached verdicts this process (M6.2 fold-in): fns that
    /// skipped Lean entirely on a pkg / island cached verdict.
    pub pkg_cached: usize,
    pub island_cached: usize,
    /// Mutual SCCs that could not be package-expressed (reasons).
    pub skipped_sccs: Vec<String>,
    /// (module leaf, lean output) per failed elaboration.
    pub failures: Vec<(String, String)>,
    /// W4a (bootstrap-38): the in-gate refWp↔production bridge. `None`
    /// when `--tactus-bridge` is off (no bridge run) or when tactus-core
    /// oleans could not be located (a loud note instead of a verdict);
    /// `Some` carries a one-line summary the gate prints verbatim. The
    /// bridge is INFORMATIONAL in W4a — its outcome never enters
    /// `failures` and so never becomes a verification error.
    pub bridge_note: Option<String>,
    /// Link-discharge L1 census: per-fn closed theorems emitted
    /// (zero-spine class) / proof fns pending (woven premises).
    pub discharge_closed: usize,
    pub discharge_pending: usize,
    /// One-line kind/reason breakdown for the gate note.
    pub discharge_detail: String,
}

/// Crate-level package gate (DESIGN-emit-module.md M4): regenerate the
/// FULL-krate package — one scope, independent of verification
/// bucketing (the fingerprint-keyed memos keep bucket-scope artifacts
/// from colliding) — then elaborate it bottom-up: defs and stmts
/// oleans, every pkg Proofs/mutual module (`lean -o` IS its
/// elaboration), and finally Link, whose elaboration is the
/// kernel-checked composition + axiom-closure verdict. Islands remain
/// the per-fn authority; the gate turns the package from a checkable
/// artifact into a checked claim.
pub fn check_package(
    krate: &KrateX,
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> Result<PackageGateReport, String> {
    install_emit_tables(krate, crate_name);
    let defs = unified_package_defs(krate, crate_name, tactic_bodies)
        .ok_or("shared-defs module unavailable (defs build failed)")?;
    let g = package_graph_for(krate, crate_name, tactic_bodies);
    let graph = g.view();
    let mut leafs: Vec<String> = Vec::new();
    let mut seen_leafs: std::collections::HashSet<String> = Default::default();
    let mut stmt_mods: Vec<(String, bool)> = Vec::new();
    let mut seen_stmts: std::collections::HashSet<String> = Default::default();
    let mut skipped_sccs: Vec<String> = Vec::new();
    let mut seen_skips: std::collections::HashSet<String> = Default::default();
    let mut failures: Vec<(String, String)> = Vec::new();
    for f in graph.0.clone() {
        let body = match tactic_bodies.get(&f.name) {
            Some(b) => b.clone(),
            None => continue,
        };
        match emit_package_proof_fn_inner(
            &g.inlined, &graph, f, &body, &f.attrs.lean_imports, crate_name,
            tactic_bodies, &defs,
        ) {
            Ok(PkgEmitOutcome::Single { leaf, stmt_modules, .. }) => {
                leafs.push(leaf);
                for (m, ch) in stmt_modules {
                    if seen_stmts.insert(m.clone()) {
                        stmt_mods.push((m, ch));
                    }
                }
            }
            Ok(PkgEmitOutcome::Mutual { leaf, stmt_modules, .. }) => {
                if seen_leafs.insert(leaf.clone()) {
                    leafs.push(leaf);
                }
                for (m, ch) in stmt_modules {
                    if seen_stmts.insert(m.clone()) {
                        stmt_mods.push((m, ch));
                    }
                }
            }
            Ok(PkgEmitOutcome::UnsupportedScc(reason)) => {
                if seen_skips.insert(reason.clone()) {
                    skipped_sccs.push(reason);
                }
            }
            Err(e) => failures.push((short_name(&f.name.path).to_string(), e)),
        }
    }
    link_for_crate(krate, crate_name, tactic_bodies, &defs);
    // Elaborate bottom-up. defs.olean was built by `for_crate(build =
    // true)`; stmts + pkg modules build here; Link elaborates last.
    let prelude_dir = crate::prelude::ensure_prelude_olean()?;
    let base_path = format!("{}:{}", prelude_dir.display(), defs.dir.display());
    let mut reused = 0usize;
    // Skip work the per-fn package checks already did this process
    // (M5c): stmts olean via its memo, pkg modules via the built-set.
    // Per-fn stmt oleans (M5d-2): ensure each collected module, reusing
    // whatever the per-fn checks already built this process.
    for (m, ch) in &stmt_mods {
        let may_skip = !ch && !defs.breaking;
        match ensure_stmt_olean(m, &defs, &prelude_dir, may_skip) {
            Ok(true) => reused += 1,
            Ok(false) => {}
            Err(e) => failures.push((m.clone(), e)),
        }
    }
    if !failures.is_empty() {
        // stmts (or an emission) failed — every pkg module would fail
        // derivatively; report the root cause, not the cascade.
        return Ok(PackageGateReport {
            modules: 1 + stmt_mods.len(), reused,
            pkg_cached: PKG_CACHED_VERDICTS.load(std::sync::atomic::Ordering::Relaxed),
            discharge_closed: DISCHARGE_CLOSED.load(std::sync::atomic::Ordering::Relaxed),
            discharge_pending: DISCHARGE_PENDING.load(std::sync::atomic::Ordering::Relaxed),
            discharge_detail: DISCHARGE_DETAIL.get_or_init(Default::default)
                .lock().unwrap_or_else(|p| p.into_inner()).clone(),
            island_cached: ISLAND_CACHED_VERDICTS.load(std::sync::atomic::Ordering::Relaxed),
            skipped_sccs, failures, bridge_note: None,
        });
    }
    let pkg_dir = lean_out_root().join(sanitize(crate_name)).join("pkg");
    for leaf in &leafs {
        if pkg_olean_built(&pkg_dir.join(format!("{}.lean", leaf))) {
            reused += 1;
        } else {
            run_lean(&pkg_dir, leaf, true, &base_path, &mut failures);
        }
    }
    let link_path = format!("{}:{}", base_path, pkg_dir.display());
    let link_mod = link_module_name(&defs);
    run_lean(&pkg_dir, &link_mod, false, &link_path, &mut failures);
    // W4a (bootstrap-38): the in-gate refWp↔production bridge, opt-in via
    // `--tactus-bridge`. Verdict-neutral — its outcome is a note, not a
    // `failures` entry, so it cannot change the gate's error count in W4a.
    let bridge_note = if bridge_enabled() && failures.is_empty() {
        Some(run_bridge_step(crate_name, &base_path))
    } else {
        None
    };
    Ok(PackageGateReport {
        modules: 1 + stmt_mods.len() + leafs.len() + 1,
        reused,
        pkg_cached: PKG_CACHED_VERDICTS.load(std::sync::atomic::Ordering::Relaxed),
        discharge_closed: DISCHARGE_CLOSED.load(std::sync::atomic::Ordering::Relaxed),
        discharge_pending: DISCHARGE_PENDING.load(std::sync::atomic::Ordering::Relaxed),
            discharge_detail: DISCHARGE_DETAIL.get_or_init(Default::default)
                .lock().unwrap_or_else(|p| p.into_inner()).clone(),
        island_cached: ISLAND_CACHED_VERDICTS.load(std::sync::atomic::Ordering::Relaxed),
        skipped_sccs,
        failures,
        bridge_note,
    })
}

/// W4a (bootstrap-38): elaborate the refWp↔production `decide` bridge over
/// every emitted obligation cert, INSIDE the package gate. This is the
/// external probe `run.sh` logic (probe9/probe11) promoted in-process: for
/// each `<out>/<crate>/cert/<leaf>.cert.lean` that carries a
/// `cert_<leaf>_goals` (an obligation cert — all-excluded fns emit no goal
/// section and are skipped), append the bridge
///   `example : lib.goals_eq (lib.ref_wp cert_<leaf>_ctx cert_<leaf>_sst)
///                            cert_<leaf>_goals = 1 := by decide`
/// and elaborate it against tactus-core's oleans (which carry `ref_wp` /
/// `goals_eq` + the mirror ctors that `TactusDefs_lib_exec` imports).
///
/// Provenance (the crux, settled for W4a): tactus-core's built `out/lib`
/// is located via `$TACTUS_CORE_OUT` — the same explicit-env-var
/// convention as `$TACTUS_PRELUDE` / `$TACTUS_CORE_VOCAB`. Auto-discovery
/// across checkout layouts is deliberately avoided. When the var is unset
/// (or the dir is missing `TactusDefs_lib_exec.olean`), the bridge SKIPS
/// with a loud note — opt-in, so no default gate path breaks. The dir's
/// olean content-hash is recorded in the note as an audit trail and to
/// stage W4b's cache key.
///
/// Returns the one-line summary the gate prints verbatim.
fn run_bridge_step(crate_name: &str, base_path: &str) -> String {
    let core_out = match std::env::var("TACTUS_CORE_OUT") {
        Ok(d) if !d.is_empty() => PathBuf::from(d),
        _ => {
            return "bridge skipped: $TACTUS_CORE_OUT unset (opt-in \
                    --tactus-bridge needs tactus-core's out/lib oleans)"
                .to_string();
        }
    };
    if !core_out.join("TactusDefs_lib_exec.olean").exists() {
        return format!(
            "bridge skipped: {} has no TactusDefs_lib_exec.olean \
             (build tactus-core, or point $TACTUS_CORE_OUT at its out/lib)",
            core_out.display(),
        );
    }
    let core_hash = core_olean_hash(&core_out);

    let cert_dir = lean_out_root().join(sanitize(crate_name)).join("cert");
    let mut certs: Vec<PathBuf> = match std::fs::read_dir(&cert_dir) {
        Ok(rd) => rd
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.to_string_lossy().ends_with(".cert.lean"))
            .collect(),
        Err(_) => Vec::new(),
    };
    // Deterministic order (read_dir is unordered): stable note + logs.
    certs.sort();

    // Bridge modules land beside the pkg modules, in their own subdir.
    let bridge_dir = lean_out_root().join(sanitize(crate_name)).join("bridge");
    if std::fs::create_dir_all(&bridge_dir).is_err() {
        return format!("bridge skipped: could not create {}", bridge_dir.display());
    }
    // tactus-core oleans FIRST so `TactusDefs_lib_exec` + `lib.*` resolve.
    let bridge_path = format!("{}:{}", core_out.display(), base_path);

    let mut checked = 0usize;
    let mut passed = 0usize;
    let mut failed_names: Vec<String> = Vec::new();
    for cert in &certs {
        let leaf = cert
            .file_name()
            .and_then(|s| s.to_str())
            .map(|s| s.trim_end_matches(".cert.lean"))
            .unwrap_or("");
        if leaf.is_empty() {
            continue;
        }
        let body = match std::fs::read_to_string(cert) {
            Ok(b) => b,
            Err(_) => continue,
        };
        // Only obligation certs (a `cert_<leaf>_goals` def) are bridgeable;
        // an all-excluded fn emits ctx+sst but no goal section, and the
        // `= 1` bridge would reference an undefined name (a false FAIL).
        if !body.contains(&format!("def cert_{}_goals", leaf)) {
            continue;
        }
        checked += 1;
        let module = format!("Bridge_{}", leaf);
        let mut text = body;
        text.push_str(&format!(
            "\n-- ── W4a in-gate bridge (bootstrap-38) ──\n\
             set_option maxRecDepth 8000\n\
             example : {ns}.goals_eq ({ns}.ref_wp cert_{leaf}_ctx cert_{leaf}_sst) \
             cert_{leaf}_goals = 1 := by decide\n",
            ns = crate::sst_serialize::cert_ns(),
            leaf = leaf,
        ));
        if std::fs::write(bridge_dir.join(format!("{}.lean", module)), &text).is_err() {
            failed_names.push(leaf.to_string());
            continue;
        }
        let mut local_failures: Vec<(String, String)> = Vec::new();
        run_lean(&bridge_dir, &module, false, &bridge_path, &mut local_failures);
        if local_failures.is_empty() {
            passed += 1;
        } else {
            failed_names.push(leaf.to_string());
        }
    }

    let failed = checked - passed;
    let mut note = format!(
        "{} obligations bridge-checked against tactus-core ({} passed, {} failed) \
         [core-olean {}]",
        checked, passed, failed, core_hash,
    );
    if !failed_names.is_empty() {
        note.push_str(&format!("; failed: {}", failed_names.join(", ")));
    }
    note
}

/// FNV-1a over the sorted `.olean` files in `dir` (name + bytes). A
/// dependency-free content hash of the tactus-core build the bridge ran
/// against — audit trail for W4a, and the seed of W4b's bridge cache key
/// (a core-logic change to `ref_wp`/`goals_eq` flips this digest, so a
/// future cache cannot silently reuse a stale PASS). Placeholder for the
/// SHA-256 §6 vendoring will bring, matching `vocab_hash`'s FNV-1a style.
fn core_olean_hash(dir: &Path) -> String {
    let mut oleans: Vec<PathBuf> = match std::fs::read_dir(dir) {
        Ok(rd) => rd
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.extension().map(|x| x == "olean").unwrap_or(false))
            .collect(),
        Err(_) => return "unreadable".to_string(),
    };
    oleans.sort();
    let mut h: u64 = 0xcbf29ce484222325;
    let mut mix = |bytes: &[u8]| {
        for &b in bytes {
            h ^= b as u64;
            h = h.wrapping_mul(0x100000001b3);
        }
    };
    for p in &oleans {
        if let Some(name) = p.file_name().and_then(|s| s.to_str()) {
            mix(name.as_bytes());
        }
        if let Ok(bytes) = std::fs::read(p) {
            mix(&bytes);
        }
    }
    format!("fnv1a:{:016x}", h)
}

/// Prepend `lean_path` to any inherited `LEAN_PATH` — one definition
/// shared by the plain and `--json` lean runners (review finding:
/// this merge was drifting toward four inline copies).
fn merged_lean_path(lean_path: &str) -> String {
    match std::env::var("LEAN_PATH") {
        Ok(existing) if !existing.is_empty() => format!("{}:{}", lean_path, existing),
        _ => lean_path.to_string(),
    }
}

/// Run `lean --json` on `<module>.lean` with cwd `dir` (same cwd /
/// module-name constraint as `run_lean`), optionally producing the
/// olean, and parse the diagnostics — success is exit-ok AND no
/// error-severity diagnostic, mirroring `check_lean_file`. One pass
/// gives the package-check path both its olean and its warnings
/// (review finding: the exit-code-only fast path silently dropped
/// warning diagnostics, `sorry`'s included — on BOTH this path and,
/// historically, islands).
fn run_lean_json(
    dir: &Path,
    module: &str,
    produce_olean: bool,
    lean_path: &str,
) -> Result<lean_process::LeanResult, String> {
    if let Some(r) =
        crate::driver_client::try_check(dir, module, produce_olean, &merged_lean_path(lean_path))
    {
        return Ok(r);
    }
    let mut args: Vec<String> = vec!["--json".to_string()];
    if produce_olean {
        args.push("-o".to_string());
        args.push(format!("{}.olean", module));
    }
    args.push(format!("{}.lean", module));
    let output = std::process::Command::new("lean")
        .args(&args)
        .current_dir(dir)
        .env("LEAN_PATH", merged_lean_path(lean_path))
        .output()
        .map_err(|e| format!("failed to spawn lean: {}", e))?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let diagnostics = lean_process::parse_diagnostics(&stdout);
    let has_error = diagnostics.iter().any(|d| d.severity == "error");
    let success = output.status.success() && !has_error;
    if !success && diagnostics.is_empty() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        if !stderr.trim().is_empty() {
            return Err(format!("Lean failed: {}", stderr.trim()));
        }
    }
    Ok(lean_process::LeanResult { success, diagnostics })
}

/// Run `lean` on `<module>.lean` with cwd `dir` (so `-o` derives the
/// module name from the bare file name — same constraint as
/// `crate_defs::build_olean`), optionally producing the olean.
/// `lean_path` is prepended to any inherited `LEAN_PATH` (the harness
/// presets one; check.sh doesn't — CRATEDEFS 1c).
fn run_lean(
    dir: &Path,
    module: &str,
    produce_olean: bool,
    lean_path: &str,
    failures: &mut Vec<(String, String)>,
) {
    if let Some(r) =
        crate::driver_client::try_check(dir, module, produce_olean, &merged_lean_path(lean_path))
    {
        if !r.success {
            let text = r.diagnostics.iter()
                .map(|d| {
                    let (l, c) = d.pos.as_ref().map(|p| (p.line, p.column)).unwrap_or((0, 0));
                    format!("{module}.lean:{l}:{c}: {}: {}", d.severity, d.data)
                })
                .collect::<Vec<_>>()
                .join("\n");
            failures.push((module.to_string(), text));
        }
        return;
    }
    let mut args: Vec<String> = Vec::new();
    if produce_olean {
        args.push("-o".to_string());
        args.push(format!("{}.olean", module));
    }
    args.push(format!("{}.lean", module));
    match std::process::Command::new("lean")
        .args(&args)
        .current_dir(dir)
        .env("LEAN_PATH", merged_lean_path(lean_path))
        .output()
    {
        Ok(out) if out.status.success() => {}
        Ok(out) => failures.push((
            module.to_string(),
            format!(
                "{}{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            ),
        )),
        Err(e) => failures.push((module.to_string(), format!("failed to spawn lean: {}", e))),
    }
}

/// A fn's DIRECT tactic-referenced helper lemmas, in krate order —
/// the single enumeration shared by `emit_package_proof_fn` (hypothesis
/// binder order) and `link_for_crate` (closed-form application order).
/// One chokepoint so the theorem's binders and Link's arguments cannot
/// disagree.
fn direct_helper_deps<'a>(
    root: &FunctionX,
    tactic_body: &str,
    krate: &'a KrateX,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> Vec<&'a FunctionX> {
    let code = strip_lean_line_comments(tactic_body);
    krate.functions.iter()
        .map(|f| &f.x)
        .filter(|f| is_emittable_tactic_proof_fn(f, tactic_bodies))
        .filter(|f| f.name != root.name
            && ident_appears(&code, short_name(&f.name.path)))
        .collect()
}

/// The direct-reference graph over all emittable tactic proof fns:
/// (nodes in krate order, node → direct deps). Shared by the SCC
/// detection in `emit_package_proof_fn` and the topo walk in
/// `build_link_module` so the two views of the graph cannot diverge.
fn package_dep_graph<'a>(
    krate: &'a KrateX,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> (Vec<&'a FunctionX>, std::collections::HashMap<&'a Fun, Vec<&'a FunctionX>>) {
    let fns: Vec<&FunctionX> = krate.functions.iter()
        .map(|f| &f.x)
        .filter(|f| is_emittable_tactic_proof_fn(f, tactic_bodies))
        .collect();
    let deps_of = fns.iter()
        .map(|f| {
            let body = tactic_bodies.get(&f.name).map(|s| s.as_str()).unwrap_or("");
            (&f.name, direct_helper_deps(f, body, krate, tactic_bodies))
        })
        .collect();
    (fns, deps_of)
}

/// The mutual SCC containing `root`, if any: members (in krate order)
/// that both reach and are reached by `root` in the direct-reference
/// graph. `None` for the common non-mutual case (singleton SCC —
/// self-recursion is handled by `termination_by` on the single
/// theorem, not by a mutual block).
fn package_scc_of<'a>(
    root: &FunctionX,
    fns: &[&'a FunctionX],
    deps_of: &std::collections::HashMap<&'a Fun, Vec<&'a FunctionX>>,
) -> Option<Vec<&'a FunctionX>> {
    fn reach<'a>(
        from: &Fun,
        edges: impl Fn(&Fun) -> Vec<&'a Fun>,
    ) -> std::collections::HashSet<&'a Fun> {
        let mut seen: std::collections::HashSet<&Fun> = Default::default();
        let mut stack: Vec<&Fun> = edges(from);
        while let Some(n) = stack.pop() {
            if seen.insert(n) {
                stack.extend(edges(n));
            }
        }
        seen
    }
    let fwd = reach(&root.name, |n| {
        deps_of.get(n).into_iter().flatten().map(|f| &f.name).collect()
    });
    if !fwd.contains(&root.name) {
        return None; // root not on any cycle
    }
    let bwd = reach(&root.name, |n| {
        deps_of.iter()
            .filter(|(_, ds)| ds.iter().any(|d| &d.name == n))
            .map(|(k, _)| *k)
            .collect()
    });
    let members: Vec<&FunctionX> = fns.iter()
        .filter(|f| fwd.contains(&f.name) && bwd.contains(&f.name))
        .copied()
        .collect();
    (members.len() > 1).then_some(members)
}

/// A mutual SCC's helper deps OUTSIDE the SCC (union over members,
/// deduped, krate order). Must be EMPTY for the SCC to be package-
/// emittable: external deps arrive as hypothesis binders, and a
/// mutual reference in verbatim tactic text (`lemma_odd k`) cannot
/// pass hypothesis arguments the user never wrote.
fn scc_external_deps<'a>(
    scc: &[&'a FunctionX],
    deps_of: &std::collections::HashMap<&'a Fun, Vec<&'a FunctionX>>,
) -> Vec<&'a FunctionX> {
    let member_names: std::collections::HashSet<&Fun> =
        scc.iter().map(|f| &f.name).collect();
    let mut seen: std::collections::HashSet<&Fun> = Default::default();
    scc.iter()
        .flat_map(|f| deps_of.get(&f.name).into_iter().flatten().copied())
        .filter(|d| !member_names.contains(&d.name) && seen.insert(&d.name))
        .collect()
}

/// Canonical pkg module leaf for a mutual SCC: `mutual__<first member
/// leaf>` (krate order — deterministic, and cannot collide with a
/// single-fn leaf).
fn mutual_module_leaf(scc: &[&FunctionX]) -> String {
    format!("mutual__{}", lean_name(&scc[0].name.path).replace('.', "__"))
}

/// Lean module name of the crate's Link module, scope-consistent with
/// defs/stmts naming.
fn link_module_name(defs: &crate::crate_defs::CrateDefs) -> String {
    scope_module_name("Link", defs)
}

/// Link-module memo — same keying and poisoned-`None` semantics as
/// `STMTS_MEMO`.
static LINK_MEMO: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<String, Option<()>>>,
> = std::sync::OnceLock::new();

/// Build + write the crate's Link module (DESIGN-emit-module.md §2.1
/// M3): the machine-generated closure that turns per-fn
/// hypothesis-passing theorems into stmt-typed CLOSED theorems —
///
///   noncomputable def <name>_closed : <name>_stmt := <name> <dep>_closed …
///
/// in dependency order, each followed by
/// `#tactus_check_axioms <name>_closed [<Boundary>]`, where Boundary =
/// the axiom names the defs module declares (broadcast lemmas, uninterp
/// spec fns, external-body Inhabited stipulations — the crate's entire
/// declared trust surface beyond the prelude). This is where the
/// composition argument becomes kernel-checked: circular dependencies
/// cannot elaborate, statement drift cannot typecheck, and the axiom
/// closure of every closed theorem is machine-verified against the
/// declared set.
///
/// Cycles in the direct-reference graph (mutual tactic lemmas — which
/// island emission cannot express either) are skipped with a loud
/// comment in the artifact and an eprintln.
///
/// No `debug_check` here: Link's references live in the imported pkg
/// modules, whose command streams are per-call and not retained. Its
/// names are derived from the same krate enumeration that emitted
/// those modules (`direct_helper_deps`, `stmt_name`), and Lean
/// elaboration of the package is the authoritative check.
fn link_for_crate(
    krate: &KrateX,
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
    defs: &crate::crate_defs::CrateDefs,
) {
    let key = link_module_name(defs);
    let memo = LINK_MEMO.get_or_init(Default::default);
    if memo.lock().unwrap_or_else(|p| p.into_inner()).contains_key(&key) {
        return;
    }
    let result = build_link_module(krate, crate_name, tactic_bodies, defs)
        .map_err(|e| {
            eprintln!(
                "tactus: Link module build failed for crate `{}` ({})",
                crate_name, e
            );
        })
        .ok();
    memo.lock().unwrap_or_else(|p| p.into_inner()).insert(key, result);
}

fn build_link_module(
    krate: &KrateX,
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
    defs: &crate::crate_defs::CrateDefs,
) -> Result<(), String> {
    use crate::lean_ast::{Def, Expr as LExpr};
    let g = package_graph_for(krate, crate_name, tactic_bodies);
    let (fns, deps_of) = g.view();
    let inlined_krate: &KrateX = &g.inlined;
    // Partition mutual SCCs: SUPPORTED (no external deps — emitted as
    // one mutual-block module, M3.5) get eta-closed FIRST and their
    // members pre-marked Black; UNSUPPORTED (external deps) fall
    // through to the cycle-poisoning DFS below, matching the emission
    // side's rejection.
    let mut supported_sccs: Vec<Vec<&FunctionX>> = Vec::new();
    let mut in_supported: std::collections::HashSet<&Fun> = Default::default();
    for f in &fns {
        if in_supported.contains(&f.name) {
            continue;
        }
        if let Some(scc) = package_scc_of(f, &fns, &deps_of) {
            if scc_external_deps(&scc, &deps_of).is_empty() {
                for m in &scc {
                    in_supported.insert(&m.name);
                }
                supported_sccs.push(scc);
            }
        }
    }
    // Dependency order via DFS post-order over direct refs, with
    // tri-state marks for cycle detection. Remaining cycle members
    // (unsupported SCCs) are excluded — their pkg theorems were
    // rejected at emission for the same reason.
    #[derive(Clone, Copy, PartialEq)]
    enum Mark { White, Gray, Black }
    fn visit<'a>(
        f: &'a FunctionX,
        deps_of: &std::collections::HashMap<&Fun, Vec<&'a FunctionX>>,
        marks: &mut std::collections::HashMap<&'a Fun, Mark>,
        ordered: &mut Vec<&'a FunctionX>,
        cyclic: &mut Vec<String>,
    ) -> bool {
        match marks.get(&f.name).copied().unwrap_or(Mark::White) {
            Mark::Black => return true,
            Mark::Gray => return false, // back-edge: cycle
            Mark::White => {}
        }
        marks.insert(&f.name, Mark::Gray);
        let mut ok = true;
        for d in deps_of.get(&f.name).into_iter().flatten() {
            if !visit(d, deps_of, marks, ordered, cyclic) {
                ok = false;
            }
        }
        if ok {
            marks.insert(&f.name, Mark::Black);
            ordered.push(f);
        } else {
            // Leave Gray→cyclic: everything on the path through a
            // back-edge stays unclosed.
            marks.insert(&f.name, Mark::White);
            cyclic.push(short_name(&f.name.path).to_string());
        }
        ok
    }
    let mut marks = std::collections::HashMap::new();
    // Supported-SCC members are pre-marked Black (already closed via
    // their mutual module, emitted before the ordered loop) so
    // dependents pass straight through them.
    for scc in &supported_sccs {
        for m in scc {
            marks.insert(&m.name, Mark::Black);
        }
    }
    let mut ordered: Vec<&FunctionX> = Vec::new();
    let mut cyclic: Vec<String> = Vec::new();
    for f in &fns {
        visit(f, &deps_of, &mut marks, &mut ordered, &mut cyclic);
    }
    cyclic.sort();
    cyclic.dedup();
    if !cyclic.is_empty() {
        eprintln!(
            "tactus: Link for `{}` skips {} fn(s) with cyclic tactic references \
             (mutual tactic lemmas are unsupported, matching island emission): {}",
            crate_name, cyclic.len(), cyclic.join(", ")
        );
    }
    // Boundary: every axiom the defs module declares. The closure
    // check whitelists exactly these (plus core + prelude, hardcoded
    // in the prelude's elab command).
    let boundary: Vec<String> = defs.cmds.iter()
        .filter_map(|c| match c {
            Command::Axiom(a) => Some(a.name.clone()),
            _ => None,
        })
        .collect();
    let boundary_list = boundary.join(", ");

    let mut cmds: Vec<Command> = Vec::new();
    cmds.push(Command::Import(defs.module_name.clone()));
    // Stmt names arrive transitively via the pkg module imports below
    // (Lean imports are transitive) — no monolithic stmts module
    // exists anymore (M5d-2).
    for scc in &supported_sccs {
        cmds.push(Command::Import(mutual_module_leaf(scc)));
    }
    for f in &ordered {
        cmds.push(Command::Import(lean_name(&f.name.path).replace('.', "__")));
    }
    // C-2 (M6.3): exec obligation entries — imports join the header,
    // closed forms append after the proof-fn loop (obligations are
    // LEAVES: nothing references them, their deps are proof fns whose
    // closed forms precede them).
    let mut exec_entries: Vec<ExecLinkEntry> = EXEC_LINK_REGISTRY
        .get_or_init(Default::default)
        .lock().unwrap_or_else(|p| p.into_inner())
        .remove(&defs.scope)
        .unwrap_or_default();
    // Registration order is COMPLETION order now that per-fn checks
    // run on a worker pool (verifier.rs tactus_lean_jobs) — sort so
    // the Link file's content stays deterministic run-to-run (entries
    // are leaves; nothing orders against them).
    exec_entries.sort_by(|a, b| a.leaf.cmp(&b.leaf));
    for e in &exec_entries {
        cmds.push(Command::Import(e.leaf.clone()));
    }
    cmds.push(Command::Raw(crate::prelude::TACTUS_SET_OPTIONS.to_string()));
    // Option B: no namespace wrapper — decl names are fully qualified.
    let ns = sanitize(crate_name);
    let _ = &ns;
    if !cyclic.is_empty() {
        cmds.push(Command::Raw(format!(
            "-- SKIPPED (cyclic tactic references with SCC-external helper deps, \
             cannot close): {}\n",
            cyclic.join(", ")
        )));
    }
    // Mutual SCC members close by eta (parameterized theorem type is
    // definitionally the stmt abbrev — M0 finding F3); no deps by
    // construction, so they precede everything.
    for scc in &supported_sccs {
        for f in scc {
            let name = lean_name(&f.name.path);
            cmds.push(Command::Def(Def {
                attrs: Vec::new(),
                name: format!("{}_closed", name),
                binders: Vec::new(),
                ret_ty: LExpr::var_lit(&to_lean_fn::stmt_name(&f.name.path)),
                body: LExpr::var_lit(&name),
                termination_by: Vec::new(),
                termination_structural: false,
                decreasing_by: None,
            }));
            cmds.push(Command::Raw(format!(
                "#tactus_check_axioms {}_closed [{}]\n", name, boundary_list
            )));
        }
    }
    for f in &ordered {
        let name = lean_name(&f.name.path);
        let body_head = LExpr::var_lit(&name);
        let body = tactic_bodies.get(&f.name).map(|s| s.as_str()).unwrap_or("");
        let args: Vec<LExpr> = direct_helper_deps(f, body, &inlined_krate, tactic_bodies)
            .into_iter()
            .map(|d| LExpr::var_lit(&format!("{}_closed", lean_name(&d.name.path))))
            .collect();
        let closed_body = if args.is_empty() {
            body_head
        } else {
            LExpr::app(body_head, args)
        };
        cmds.push(Command::Def(Def {
            attrs: Vec::new(),
            name: format!("{}_closed", name),
            binders: Vec::new(),
            ret_ty: LExpr::var_lit(&to_lean_fn::stmt_name(&f.name.path)),
            body: closed_body,
            termination_by: Vec::new(),
            termination_structural: false,
            decreasing_by: None,
        }));
        cmds.push(Command::Raw(format!(
            "#tactus_check_axioms {}_closed [{}]\n", name, boundary_list
        )));
    }
    // Exec obligation closed forms (C-2/M6.3): the soundness headline —
    // exec obligations join the composition + sorryAx/axiom closure.
    for e in &exec_entries {
        for (thm_name, dep_paths) in &e.obligations {
            let args: Vec<LExpr> = dep_paths.iter()
                .map(|p| LExpr::var_lit(&format!("{}_closed", lean_name(p))))
                .collect();
            let body_head = LExpr::var_lit(thm_name);
            let closed_body = if args.is_empty() {
                body_head
            } else {
                LExpr::app(body_head, args)
            };
            cmds.push(Command::Def(Def {
                attrs: Vec::new(),
                name: format!("{}_closed", thm_name),
                binders: Vec::new(),
                ret_ty: LExpr::var_lit(&format!("{}_stmt", thm_name)),
                body: closed_body,
                termination_by: Vec::new(),
                termination_structural: false,
                decreasing_by: None,
            }));
            cmds.push(Command::Raw(format!(
                "#tactus_check_axioms {}_closed [{}]\n", thm_name, boundary_list
            )));
        }
    }
    // Link-discharge (bootstrap-73 L1/L2): per-fn closed theorems
    // synthesized from the spine sidecars — zero-spine re-exports,
    // straight-line positional applications, and fix synthesis for
    // lowered-match recursion (probe34 shapes). Fixpoint over the
    // callee-dependency order; everything unsynthesizable is PENDING
    // with a reason, reported via the package-gate note. True exec
    // fns are skipped by design (DESIGN-link-discharge.md §3.4).
    let ns = sanitize(crate_name);
    // Field accessor naming — matches `field_access_name`: `val<N>` for
    // tuple-style numeric field idents, sanitized name otherwise.
    let accessor_of = |f: &vir::ast::Binder<(vir::ast::Typ, vir::ast::Mode, vir::ast::Visibility)>| -> String {
        match f.name.as_str().parse::<usize>() {
            Ok(n) => format!("val{}", n),
            Err(_) => crate::to_lean_type::sanitize(f.name.as_str()),
        }
    };
    let mut dt_variants: std::collections::HashMap<String, Vec<(String, Vec<String>)>> =
        Default::default();
    // Per-dt field table WITH VIR typs (the Lean model erases u64→Int;
    // bounds live only in the Verus typing — R-b builds wf from here).
    let mut dt_fields: std::collections::HashMap<
        String, Vec<(String, Vec<(String, vir::ast::Typ)>)>> = Default::default();
    for d in inlined_krate.datatypes.iter() {
        if let vir::ast::Dt::Path(p) = &d.x.name {
            let rel = crate::to_lean_type::lean_name_relative(p);
            dt_variants.insert(
                rel.clone(),
                d.x.variants.iter()
                    .map(|v| (v.name.to_string(),
                              v.fields.iter().map(|f| accessor_of(f)).collect()))
                    .collect(),
            );
            dt_fields.insert(
                rel,
                d.x.variants.iter()
                    .map(|v| (v.name.to_string(),
                              v.fields.iter()
                                  .map(|f| (accessor_of(f), f.a.0.clone()))
                                  .collect()))
                    .collect(),
            );
        }
    }
    // R-b wf predicates. A field is a BOUND conjunct when its VIR typ
    // carries a range (`type_bound_predicate` fires — u64 etc.); a REC
    // conjunct when it is a (Box-wrapped) scalar-carrying datatype.
    let bound_var = crate::lean_name::LeanName::synthetic("x".to_string());
    let field_bound_pred = |t: &vir::ast::Typ, var: &str| -> Option<String> {
        let v = crate::lean_ast::Expr::var(crate::lean_name::LeanName::synthetic(var.to_string()));
        crate::to_lean_sst_expr::type_bound_predicate(&v, t)
            .map(|p| crate::lean_pp::pp_expr(&p))
    };
    let is_bounded = |t: &vir::ast::Typ| -> bool {
        let v = crate::lean_ast::Expr::var(bound_var.clone());
        crate::to_lean_sst_expr::type_bound_predicate(&v, t).is_some()
    };
    let field_dt = |t: &vir::ast::Typ| -> Option<(String, bool)> {
        let txt = crate::lean_pp::pp_expr(&crate::to_lean_type::typ_to_expr(t));
        match txt.strip_prefix("Tactus.Box ") {
            Some(r) => r.strip_prefix(&format!("{}.", ns)).map(|x| (x.to_string(), true)),
            None => txt.strip_prefix(&format!("{}.", ns)).map(|x| (x.to_string(), false)),
        }
    };
    // Scalar-carrying fixpoint.
    let mut scalar_carrying: std::collections::HashSet<String> = Default::default();
    loop {
        let mut grew = false;
        for (rel, vars) in &dt_fields {
            if scalar_carrying.contains(rel) {
                continue;
            }
            let carries = vars.iter().any(|(_, fs)| fs.iter().any(|(_, t)| {
                is_bounded(t)
                    || field_dt(t).map(|(d, _)| scalar_carrying.contains(&d)).unwrap_or(false)
            }));
            if carries {
                scalar_carrying.insert(rel.clone());
                grew = true;
            }
        }
        if !grew {
            break;
        }
    }
    // Wf structure + def texts, topological over rec-field edges
    // (cross-dt cycles would need mutual blocks — none exist here;
    // census loudly if one appears).
    let mut wf_infos: std::collections::HashMap<String, crate::link_discharge::WfInfo> =
        Default::default();
    // R-c: richer conjunct table for the preservation synthesizer.
    let mut wf_specs: std::collections::HashMap<String, crate::wf_synth::DtWfSpec> =
        Default::default();
    let mut wf_def_texts: std::collections::HashMap<String, String> = Default::default();
    let mut wf_deps: std::collections::HashMap<String, Vec<String>> = Default::default();
    // Sorted iteration: hash-set order varies per process, and this
    // loop's order reaches emitted wf-def text order downstream.
    let mut scalar_carrying_sorted: Vec<&String> = scalar_carrying.iter().collect();
    scalar_carrying_sorted.sort();
    for rel in scalar_carrying_sorted {
        let vars = &dt_fields[rel];
        let mut info_vars: std::collections::HashMap<String, Vec<crate::link_discharge::WfComp>> =
            Default::default();
        let mut clauses: Vec<String> = Vec::new();
        let mut deps: Vec<String> = Vec::new();
        let mut self_rec = false;
        let mut spec_vars: std::collections::HashMap<String, Vec<(usize, crate::wf_synth::ConjKind)>> =
            Default::default();
        for (vname, fs) in vars {
            let mut comps: Vec<crate::link_discharge::WfComp> = Vec::new();
            let mut spec_conjs: Vec<(usize, crate::wf_synth::ConjKind)> = Vec::new();
            let mut conj_texts: Vec<String> = Vec::new();
            let mut pat_vars: Vec<String> = Vec::new();
            for (i, (acc, t)) in fs.iter().enumerate() {
                let var = format!("x{}", i);
                if let Some(pred) = field_bound_pred(t, &var) {
                    comps.push(crate::link_discharge::WfComp {
                        accessor: acc.clone(), rec: false });
                    spec_conjs.push((i, crate::wf_synth::ConjKind::Bound));
                    conj_texts.push(format!("({})", pred));
                    pat_vars.push(var);
                } else if let Some((d, boxed)) = field_dt(t) {
                    if scalar_carrying.contains(&d) {
                        comps.push(crate::link_discharge::WfComp {
                            accessor: acc.clone(), rec: true });
                        spec_conjs.push((i, crate::wf_synth::ConjKind::Rec {
                            dt: d.clone(), boxed }));
                        conj_texts.push(format!(
                            "{}Wf {}{}", d, var, if boxed { ".deref" } else { "" }));
                        pat_vars.push(var);
                        if d == *rel { self_rec = true; } else { deps.push(d); }
                    } else {
                        pat_vars.push("_".to_string());
                    }
                } else {
                    pat_vars.push("_".to_string());
                }
            }
            let pat = if fs.is_empty() {
                format!("{}.{}.{}", ns, rel, vname)
            } else {
                format!("{}.{}.{} {}", ns, rel, vname, pat_vars.join(" "))
            };
            let body = if conj_texts.is_empty() {
                "True".to_string()
            } else {
                conj_texts.join(" ∧ ")
            };
            clauses.push(format!("  | {} => {}", pat, body));
            info_vars.insert(vname.clone(), comps);
            spec_vars.insert(vname.clone(), spec_conjs);
        }
        // Struct-style dts (single variant named after the type) emit
        // as Lean `structure`s — no matchable constructor; use field
        // projections instead.
        let is_struct = vars.len() == 1 && vars[0].0 == *rel;
        let mut text = if is_struct {
            let (_, fs) = &vars[0];
            let mut conj_texts: Vec<String> = Vec::new();
            for (acc, t) in fs.iter() {
                let proj = format!("x.{}", acc);
                if let Some(pred) = field_bound_pred(t, &proj) {
                    conj_texts.push(format!("({})", pred));
                } else if let Some((d, boxed)) = field_dt(t) {
                    if scalar_carrying.contains(&d) {
                        conj_texts.push(format!(
                            "{}Wf {}{}", d, proj, if boxed { ".deref" } else { "" }));
                    }
                }
            }
            let body = if conj_texts.is_empty() {
                "True".to_string()
            } else {
                conj_texts.join(" ∧ ")
            };
            format!("def {}Wf (x : {}.{}) : Prop :=\n  {}\n", rel, ns, rel, body)
        } else {
            format!(
                "def {}Wf (x : {}.{}) : Prop :=\n  match x with\n{}\n",
                rel, ns, rel, clauses.join("\n"))
        };
        if self_rec && !is_struct {
            text.push_str("termination_by structural x\n");
        }
        wf_infos.insert(rel.clone(), crate::link_discharge::WfInfo { variants: info_vars });
        wf_specs.insert(rel.clone(), crate::wf_synth::DtWfSpec { variants: spec_vars });
        wf_def_texts.insert(rel.clone(), text);
        wf_deps.insert(rel.clone(), deps);
    }
    let mut sidecars: std::collections::HashMap<String, crate::link_discharge::FnSidecar> =
        Default::default();
    let mut discharge_fns: Vec<(String, String)> = Vec::new(); // (rel, dotted)
    let mut pending: std::collections::HashMap<String, String> = Default::default();
    for e in &exec_entries {
        if !e.is_proof {
            continue;
        }
        let rel = e
            .fn_name
            .strip_prefix(&format!("{}.", ns))
            .unwrap_or(&e.fn_name)
            .to_string();
        let spine_path = lean_out_root()
            .join(&ns)
            .join("pkg")
            .join(format!("{}.spine.json", e.leaf));
        match std::fs::read_to_string(&spine_path)
            .ok()
            .and_then(|t| crate::link_discharge::parse_sidecar(&t))
        {
            Some(sc) => {
                sidecars.insert(rel.clone(), sc);
                discharge_fns.push((rel, e.fn_name.clone()));
            }
            None => {
                pending.insert(rel, "sidecar missing/unparseable".to_string());
            }
        }
    }
    // R-c: candidate spec fns for wf-preservation synthesis — every
    // spec fn with a body whose return type is a scalar-carrying dt.
    let mut spec_fn_x: std::collections::HashMap<String, &vir::ast::FunctionX> =
        Default::default();
    for f in inlined_krate.functions.iter() {
        if f.x.mode != vir::ast::Mode::Spec || f.x.body.is_none() {
            continue;
        }
        spec_fn_x.insert(
            crate::to_lean_type::lean_name_relative(&f.x.name.path),
            &f.x,
        );
    }
    let mut wf_sigs: std::collections::HashMap<String, crate::wf_synth::FnWfSig> =
        Default::default();
    // Sorted for run-to-run determinism (map iteration order is not).
    let mut spec_fn_x_sorted: Vec<(&String, &&vir::ast::FunctionX)> =
        spec_fn_x.iter().collect();
    spec_fn_x_sorted.sort_by_key(|(rel, _)| *rel);
    for (rel, fx) in spec_fn_x_sorted {
        let Some((ret_d, false)) = field_dt(&fx.ret.x.typ) else { continue };
        if !scalar_carrying.contains(&ret_d) {
            continue;
        }
        let params: Vec<(String, crate::wf_synth::ParamKind)> = fx
            .params
            .iter()
            .map(|pr| {
                let name = crate::lean_name::LeanName::from_var_ident(&pr.x.name)
                    .into_string();
                let kind = if let Some(pred) = field_bound_pred(&pr.x.typ, &name) {
                    crate::wf_synth::ParamKind::Bounded(pred)
                } else {
                    match field_dt(&pr.x.typ) {
                        Some((d, false)) if scalar_carrying.contains(&d) => {
                            crate::wf_synth::ParamKind::Dt(d)
                        }
                        _ => crate::wf_synth::ParamKind::Other,
                    }
                };
                (name, kind)
            })
            .collect();
        wf_sigs.insert(rel.clone(), crate::wf_synth::FnWfSig { params, ret_dt: ret_d });
    }
    let ectx_link = crate::emit_ctx::EmitCtx::build(krate, tactic_bodies);
    let def_of = |rel: &str| -> Option<crate::lean_ast::Def> {
        let fx = spec_fn_x.get(rel)?;
        let cmds = crate::to_lean_fn::spec_fn_to_ast(fx, &ectx_link);
        cmds.into_iter().find_map(|c| match c {
            Command::Def(d) if d.name == format!("{}.{}", ns, rel) => Some(d),
            _ => None,
        })
    };

    let mut wf_lemma_texts: Vec<String> = Vec::new();
    let mut wf_lemma_sigs: std::collections::HashMap<String, crate::wf_synth::FnWfSig> =
        Default::default();
    let mut wf_census: Vec<String> = Vec::new();
    let mut closed: std::collections::HashMap<String, crate::link_discharge::ClosedMeta> =
        Default::default();
    let mut closed_texts: Vec<(String, String, &'static str)> = Vec::new();
    let mut synth_phase_done = true;
    loop {
        let mut round: Vec<(String, String, String, &'static str,
            crate::link_discharge::ClosedMeta)> = Vec::new();
        for (rel, dotted) in &discharge_fns {
            if closed.contains_key(rel) {
                continue;
            }
            let ctx = crate::link_discharge::Ctx {
                sidecars: &sidecars,
                closed: &closed,
                variants: &dt_variants,
                wf: &wf_infos,
                wf_lemmas: &wf_lemma_sigs,
                wf_specs: &wf_specs,
                ns: &ns,
            };
            match crate::link_discharge::try_close(rel, &sidecars[rel], &ctx) {
                crate::link_discharge::Outcome::Closed { text, kind, meta } => {
                    round.push((rel.clone(), dotted.clone(), text, kind, meta));
                }
                crate::link_discharge::Outcome::Pending(r) => {
                    pending.insert(rel.clone(), r);
                }
            }
        }
        if round.is_empty() {
            // R-c demand collection: wf-transport pendings name the
            // offending value; the head spec fn is the demand. Iterate:
            // deeper demands surface only after earlier lemmas unblock
            // resolution (Loop arm behind Ret arm etc.).
            let _ = &synth_phase_done;
            let mut queue: Vec<String> = Vec::new();
            // Iterate key-sorted: values() order varies per process
            // and the queue order reaches synthesized-lemma order.
            let mut pending_sorted: Vec<(&String, &String)> = pending.iter().collect();
            pending_sorted.sort_by_key(|(k, _)| *k);
            for (_, reason) in pending_sorted {
                let Some(start) = reason.find("wf-transport for arg `") else { continue };
                let _ = start;
                let rest = &reason[start + 22..];
                let Some(end) = rest.find('`') else { continue };
                let text = &rest[..end];
                let head = text
                    .trim_start_matches('(')
                    .split_whitespace()
                    .next()
                    .unwrap_or("");
                if let Some(g) = head.strip_prefix(&format!("{}.", ns)) {
                    if wf_sigs.contains_key(g)
                        && !wf_lemma_sigs.contains_key(g)
                        && !queue.contains(&g.to_string())
                    {
                        queue.push(g.to_string());
                    }
                }
            }
            if queue.is_empty() {
                break;
            }
            // Closure over def-body spec-fn refs.
            let mut want: Vec<String> = Vec::new();
            let mut defs: std::collections::HashMap<String, crate::lean_ast::Def> =
                Default::default();
            while let Some(g) = queue.pop() {
                if want.contains(&g) {
                    continue;
                }
                match def_of(&g) {
                    Some(d) => {
                        for r in crate::wf_synth::body_spec_refs(&d, &ns, &wf_sigs) {
                            if !want.contains(&r) {
                                queue.push(r);
                            }
                        }
                        defs.insert(g.clone(), d);
                        want.push(g);
                    }
                    None => wf_census.push(format!("{}: def unavailable", g)),
                }
            }
            // Topological synthesis (callees first); cycles census.
            // Previously-synthesized lemmas count as done (their texts
            // are already emitted; dependents may reference them).
            let mut done: std::collections::HashSet<String> =
                wf_lemma_sigs.keys().cloned().collect();
            loop {
                let mut progressed = false;
                for g in &want {
                    if done.contains(g) || !defs.contains_key(g) {
                        continue;
                    }
                    let refs = crate::wf_synth::body_spec_refs(&defs[g], &ns, &wf_sigs);
                    if !refs.iter().all(|r| r == g || done.contains(r) || !defs.contains_key(r)) {
                        continue;
                    }
                    let sctx = crate::wf_synth::SynthCtx {
                        ns: &ns,
                        dts: &wf_specs,
                        sigs: &wf_sigs,
                        accessors: &dt_variants,
                        done: &done,
                    };
                    match crate::wf_synth::synth_wf_lemma(&sctx, g, &defs[g], &wf_sigs[g]) {
                        Ok(text) => {
                            wf_lemma_texts.push(text);
                            wf_lemma_sigs.insert(g.clone(), wf_sigs[g].clone());
                            done.insert(g.clone());
                            synth_phase_done = false;
                        }
                        Err(e) => {
                            wf_census.push(format!("{}: {}", g, e));
                            defs.remove(g);
                        }
                    }
                    progressed = true;
                }
                if !progressed {
                    break;
                }
            }
            for g in &want {
                if !done.contains(g) && defs.contains_key(g) {
                    wf_census.push(format!("{}: dependency cycle", g));
                }
            }
            if synth_phase_done {
                break; // no NEW lemma this round — quiesced for real
            }
            synth_phase_done = true;
            continue; // re-run the fixpoint with lemmas available
        }
        for (rel, dotted, text, kind, meta) in round {
            pending.remove(&rel);
            closed.insert(rel, meta);
            closed_texts.push((dotted, text, kind));
        }
    }
    if !closed_texts.is_empty() {
        cmds.push(Command::Raw(format!("namespace {}\n", ns)));
        // R-b: wf defs referenced by the closed theorems, dependencies
        // first (transitively). Unreferenced wf defs are not emitted.
        let all_text: String = closed_texts
            .iter()
            .map(|(_, t, _)| t.as_str())
            .chain(wf_lemma_texts.iter().map(|t| t.as_str()))
            .collect::<Vec<_>>()
            .join("\u{1}");
        let mut wf_needed: Vec<String> = Vec::new();
        let mut stack: Vec<String> = wf_def_texts.keys()
            .filter(|d| all_text.contains(&format!("{}Wf", d)))
            .cloned().collect();
        // keys() order varies per process; wf_needed's order (and with
        // it emitted wf-def order) must not.
        stack.sort();
        while let Some(d) = stack.pop() {
            if wf_needed.contains(&d) {
                continue;
            }
            for dep in wf_deps.get(&d).cloned().unwrap_or_default() {
                if !wf_needed.contains(&dep) {
                    stack.push(dep);
                }
            }
            wf_needed.push(d);
        }
        // Dependencies-first order: repeatedly emit defs whose deps are
        // done. Cross-datatype cycles (mutual inductive families, e.g.
        // RawExp/RawArmList/RawList) emit as a `mutual … end` block with
        // per-def `termination_by structural` (probe36 shape).
        let mut emitted: std::collections::HashSet<String> = Default::default();
        while emitted.len() < wf_needed.len() {
            let mut progressed = false;
            for d in &wf_needed {
                if emitted.contains(d) {
                    continue;
                }
                if wf_deps[d].iter().all(|x| emitted.contains(x) || !wf_needed.contains(x)) {
                    cmds.push(Command::Raw(format!("{}\n", wf_def_texts[d])));
                    emitted.insert(d.clone());
                    progressed = true;
                }
            }
            if !progressed {
                // Stuck ⇒ a cycle among the remaining. Extract the SCC of
                // an arbitrary remaining dt: reachable ∩ reaching, within
                // the remaining set.
                let remaining: Vec<String> = wf_needed
                    .iter()
                    .filter(|d| !emitted.contains(*d))
                    .cloned()
                    .collect();
                let reach = |from: &str, back: bool| -> std::collections::HashSet<String> {
                    let mut seen: std::collections::HashSet<String> = Default::default();
                    let mut stack = vec![from.to_string()];
                    while let Some(x) = stack.pop() {
                        if !seen.insert(x.clone()) {
                            continue;
                        }
                        for y in &remaining {
                            let edge = if back {
                                wf_deps.get(y).map(|ds| ds.contains(&x)).unwrap_or(false)
                            } else {
                                wf_deps.get(&x).map(|ds| ds.contains(y)).unwrap_or(false)
                            };
                            if edge && !seen.contains(y) {
                                stack.push(y.clone());
                            }
                        }
                    }
                    seen
                };
                // Try every remaining dt as seed — the stuck set mixes
                // genuine cycle members with dts merely WAITING on the
                // cycle (singleton SCCs); only a real, dep-ready cycle
                // unblocks progress.
                let mut found: Option<Vec<String>> = None;
                for seed in &remaining {
                    let fwd = reach(seed, false);
                    let bwd = reach(seed, true);
                    let mut scc: Vec<String> = remaining
                        .iter()
                        .filter(|d| fwd.contains(*d) && bwd.contains(*d))
                        .cloned()
                        .collect();
                    scc.sort();
                    let deps_ok = scc.iter().all(|d| {
                        wf_deps[d].iter().all(|x| {
                            scc.contains(x) || emitted.contains(x) || !wf_needed.contains(x)
                        })
                    });
                    if scc.len() >= 2 && deps_ok {
                        found = Some(scc);
                        break;
                    }
                }
                let scc = found.unwrap_or_default();
                if scc.len() < 2 {
                    cmds.push(Command::Raw(
                        "-- wf defs: unresolvable dependency order — SKIPPED\n".to_string(),
                    ));
                    break;
                }
                let mut block = String::from("mutual\n");
                for d in &scc {
                    let mut t = wf_def_texts[d].clone();
                    // Mutual members recurse even when only cross-dt:
                    // every member needs the structural clause.
                    if !t.contains("termination_by") {
                        t.push_str("termination_by structural x\n");
                    }
                    block.push_str(&t);
                    block.push('\n');
                }
                block.push_str("end\n");
                cmds.push(Command::Raw(block));
                for d in scc {
                    emitted.insert(d);
                }
            }
        }
        for c in &wf_census {
            cmds.push(Command::Raw(format!("-- wf lemma not synthesized: {}\n", c)));
        }
        for text in &wf_lemma_texts {
            cmds.push(Command::Raw(format!("{}\n", text)));
        }
        for (_, text, _) in &closed_texts {
            cmds.push(Command::Raw(format!("{}\n", text)));
        }
        cmds.push(Command::Raw(format!("end {}\n", ns)));
        for (dotted, _, _) in &closed_texts {
            cmds.push(Command::Raw(format!(
                "#tactus_check_axioms {}_closed [{}]\n",
                dotted, boundary_list
            )));
        }
    }
    let mut kind_counts: std::collections::BTreeMap<&'static str, usize> = Default::default();
    for (_, _, k) in &closed_texts {
        *kind_counts.entry(k).or_default() += 1;
    }
    let mut reason_counts: std::collections::BTreeMap<&str, usize> = Default::default();
    for r in pending.values() {
        *reason_counts.entry(r.as_str()).or_default() += 1;
    }
    let detail = format!(
        "{}{}",
        kind_counts
            .iter()
            .map(|(k, n)| format!("{} {}", n, k))
            .collect::<Vec<_>>()
            .join(" + "),
        if pending.is_empty() {
            String::new()
        } else {
            format!(
                "; pending: {}",
                reason_counts
                    .iter()
                    .map(|(r, n)| if *n > 1 {
                        format!("{}x {}", n, r)
                    } else {
                        r.to_string()
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
    );
    DISCHARGE_CLOSED.store(closed_texts.len(), std::sync::atomic::Ordering::Relaxed);
    DISCHARGE_PENDING.store(pending.len(), std::sync::atomic::Ordering::Relaxed);
    *DISCHARGE_DETAIL
        .get_or_init(Default::default)
        .lock()
        .unwrap_or_else(|p| p.into_inner()) = detail;
    let rendered = pp_commands(&cmds);
    let path = lean_out_root().join(sanitize(crate_name)).join("pkg")
        .join(format!("{}.lean", link_module_name(defs)));
    // Tracked: identical bytes → no rewrite (mtime churn poisoned
    // downstream freshness checks every run). The gate still
    // elaborates the Link each run — that's the sorry backstop.
    write_lean_file_tracked(&path, &rendered.text).map(|_| ())
}

/// The raw text a theorem's tactic elaborates — the scan surface for
/// helper references. `Named` bodies (`tactus_auto`, `omega`) can't
/// reference user lemmas, but scanning the name is harmless and keeps
/// this total.
fn tactic_scan_text(t: &crate::lean_ast::Tactic) -> &str {
    match t {
        crate::lean_ast::Tactic::Raw(s) => s,
        crate::lean_ast::Tactic::Named(s) => s,
    }
}

/// Bridge Option B tactic references onto package binders: replace each
/// helper's fully-qualified dotted name (`lib.runtime.lemma_fcf_end` —
/// what ISLAND texts must cite, since islands declare helpers as global
/// dotted theorems) with its short name (`lemma_fcf_end` — the only
/// name a local hypothesis binder can carry). Word-boundary-aware so
/// `lib.runtime.lemma_fcf_end2` survives. The island path embeds the
/// user's text verbatim; only machine-generated package modules get the
/// rewrite, so one source text serves both routes.
fn bridge_qualified_helper_refs(text: &str, deps: &[&FunctionX]) -> String {
    let mut out = text.to_string();
    for f in deps {
        let qualified = lean_name(&f.name.path);
        let short = short_name(&f.name.path);
        if qualified == short || !out.contains(&qualified) {
            continue;
        }
        let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
        let mut res = String::with_capacity(out.len());
        let mut rest: &str = &out;
        while let Some(i) = rest.find(&qualified) {
            let before_ok = i == 0 || {
                let b = rest.as_bytes()[i - 1];
                !is_ident(b) && b != b'.'
            };
            let end = i + qualified.len();
            let after_ok = end >= rest.len() || {
                let b = rest.as_bytes()[end];
                !is_ident(b) && b != b'.'
            };
            res.push_str(&rest[..i]);
            if before_ok && after_ok {
                res.push_str(short);
            } else {
                res.push_str(&qualified);
            }
            rest = &rest[end..];
        }
        res.push_str(rest);
        out = res;
    }
    out
}

/// Package-mode emission for one EXEC fn (DESIGN-exec-packages.md
/// M6.2). Same architecture as `emit_package_proof_fn`, with two
/// differences: an exec fn carries N obligation theorems (not one),
/// and its helper set is PRECISE — the obligations' tactic texts are
/// available here (from the SST), so no ExecFn over-approximation.
///
/// Artifacts:
/// - own stmt module `TactusStmts_<scope>__<fn>` in `defs.dir`: one
///   `@[reducible] def <thm>_stmt : Prop` per obligation (statement
///   defs for M6.3 Link composition; the import list doubles as the
///   dependency manifest).
/// - pkg module `pkg/<fn>.lean`: imports defs + own stmt + helper stmt
///   modules; each obligation theorem gets the helpers ITS tactic text
///   references as hypothesis binders (named by short name, typed by
///   the helper's stmt def — the island's global theorem becomes a
///   local hypothesis and the tactic body elaborates unchanged).
///
/// Exec fns are never in tactic-level mutual SCCs (obligation theorems
/// don't reference each other), so the outcome is always
/// `PkgEmitOutcome::Single`.
/// L1 Link-discharge sidecar writer (DESIGN-link-discharge.md §3.1).
/// One JSON file per pkg module (`<leaf>.spine.json`), one record per
/// emitted VC: the ordered spine descriptors the Link generator needs
/// to build a positional discharge term. Slice (a): write-only.
fn write_spine_sidecar(
    pkg_lean_path: &std::path::Path,
    leaf: &str,
    records: &[(String, Option<crate::lean_ast::GoalShape>)],
) -> std::io::Result<()> {
    use crate::lean_ast::{GoalSpine, HypProvenance, SpineArgTag};
    fn esc(s: &str) -> String {
        let mut out = String::with_capacity(s.len() + 2);
        for c in s.chars() {
            match c {
                '"' => out.push_str("\\\""),
                '\\' => out.push_str("\\\\"),
                '\n' => out.push_str("\\n"),
                '\t' => out.push_str("\\t"),
                c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
                c => out.push(c),
            }
        }
        out
    }
    let mut j = String::new();
    j.push_str(&format!("{{\"fn\":\"{}\",\"vcs\":[", esc(leaf)));
    for (i, (name, shape)) in records.iter().enumerate() {
        if i > 0 { j.push(','); }
        j.push_str(&format!("{{\"name\":\"{}\",", esc(name)));
        match shape {
            None => j.push_str("\"spine\":null}"),
            Some(sh) => {
                j.push_str(&format!("\"leaf\":\"{}\",", esc(&crate::lean_pp::pp_expr(&sh.leaf))));
                j.push_str("\"spine\":[");
                for (k, node) in sh.spine.iter().enumerate() {
                    if k > 0 { j.push(','); }
                    match node {
                        GoalSpine::All(b, prov) => {
                            j.push_str(&format!(
                                "{{\"k\":\"all\",\"name\":\"{}\",\"ty\":\"{}\"",
                                esc(b.name.as_ref().map(|n| n.as_str()).unwrap_or("_")),
                                esc(&crate::lean_pp::pp_expr(&b.ty)),
                            ));
                            // Absorbed-hyp provenance: same fields as the
                            // corresponding Imp so the discharge generator
                            // treats this binder as the premise it is.
                            match prov {
                                None | Some(HypProvenance::Other) if prov.is_none() => {}
                                Some(HypProvenance::CallFact(info)) => {
                                    j.push_str(&format!(
                                        ",\"p\":\"call\",\"callee\":\"{}\",\"self\":{},\"args\":[",
                                        esc(&info.callee), info.is_self));
                                    for (a, arg) in info.args.iter().enumerate() {
                                        if a > 0 { j.push(','); }
                                        let tag = match &arg.tag {
                                            SpineArgTag::CallerParam(n) => format!("param:{}", n),
                                            SpineArgTag::Literal => "lit".to_string(),
                                            SpineArgTag::Expr => "expr".to_string(),
                                        };
                                        j.push_str(&format!(
                                            "{{\"text\":\"{}\",\"tag\":\"{}\"}}",
                                            esc(&arg.text), esc(&tag)));
                                    }
                                    j.push(']');
                                j.push_str(",\"ens\":[");
                                for (k, s) in info.ensures_summary.iter().enumerate() {
                                    if k > 0 { j.push(','); }
                                    j.push_str(&format!("\"{}\"", match s {
                                        crate::lean_ast::EnsuresShape::LenEq => "leneq",
                                        crate::lean_ast::EnsuresShape::ForallPointwise => "pointwise",
                                        crate::lean_ast::EnsuresShape::OtherEq => "eq",
                                        crate::lean_ast::EnsuresShape::Other => "other",
                                    }));
                                }
                                j.push(']');
                                }
                                Some(HypProvenance::Branch(None)) =>
                                    j.push_str(",\"p\":\"branch\""),
                                Some(HypProvenance::Branch(Some(t))) => j.push_str(&format!(
                                    ",\"p\":\"branch\",\"scrut\":\"{}\",\"dt\":\"{}\",\"variant\":\"{}\",\"pos\":{}",
                                    esc(&t.scrutinee), esc(&t.datatype), esc(&t.variant), t.positive)),
                                Some(HypProvenance::HeightFact) =>
                                    j.push_str(",\"p\":\"height\""),
                                Some(HypProvenance::Requires { index }) =>
                                    j.push_str(&format!(",\"p\":\"requires\",\"i\":{}", index)),
                                Some(HypProvenance::HoistEq { binder }) => {
                                    j.push_str(&format!(
                                        ",\"p\":\"hoist\",\"binder\":\"{}\"", esc(binder.as_str())));
                                    // Structured equation RHS (self-review
                                    // 2026-07-24, finding 2): the composer
                                    // needs `v` to replay `let binder := v;`
                                    // — emit it from the STRUCTURED LExpr
                                    // here (the writer holds the eq tree),
                                    // never re-parsed from the pp'd `ty`
                                    // text. A non-eq / mismatched-lhs shape
                                    // omits the field and the parser keeps
                                    // the fn pending (loud).
                                    if let crate::lean_ast::ExprNode::BinOp {
                                        op: crate::lean_ast::BinOp::Eq, lhs, rhs,
                                    } = &b.ty.node
                                    {
                                        if matches!(&lhs.node,
                                            crate::lean_ast::ExprNode::Var(n)
                                                if n.as_str() == binder.as_str())
                                        {
                                            j.push_str(&format!(
                                                ",\"v\":\"{}\"",
                                                esc(&crate::lean_pp::pp_expr(rhs))));
                                        }
                                    }
                                }
                                Some(HypProvenance::CtorEq { scrutinee, variant, .. }) =>
                                    j.push_str(&format!(
                                        ",\"p\":\"ctor\",\"scrut\":\"{}\",\"variant\":\"{}\"",
                                        esc(scrutinee.as_str()), esc(variant))),
                                Some(HypProvenance::LoopInv { index, at }) =>
                                    j.push_str(&format!(
                                        ",\"p\":\"loopinv\",\"i\":{},\"at\":\"{}\"",
                                        index,
                                        match at {
                                            crate::lean_ast::LoopPhase::Maintain => "maintain",
                                            crate::lean_ast::LoopPhase::Exit => "exit",
                                        })),
                                Some(HypProvenance::AssertFact) =>
                                    j.push_str(",\"p\":\"assert\""),
                                Some(HypProvenance::AssumeFact) =>
                                    j.push_str(",\"p\":\"assume\""),
                                Some(HypProvenance::Other) =>
                                    j.push_str(",\"p\":\"other\""),
                                None => {}
                            }
                            j.push('}');
                        }
                        GoalSpine::Let(n, v) => j.push_str(&format!(
                            "{{\"k\":\"let\",\"name\":\"{}\",\"v\":\"{}\"}}",
                            esc(n.as_str()), esc(&crate::lean_pp::pp_expr(v)))),
                        GoalSpine::Imp(_, prov) => match prov {
                            HypProvenance::Branch(None) =>
                                j.push_str("{\"k\":\"imp\",\"p\":\"branch\"}"),
                            HypProvenance::Branch(Some(t)) => j.push_str(&format!(
                                "{{\"k\":\"imp\",\"p\":\"branch\",\"scrut\":\"{}\",\"dt\":\"{}\",\"variant\":\"{}\",\"pos\":{}}}",
                                esc(&t.scrutinee), esc(&t.datatype), esc(&t.variant), t.positive)),
                            HypProvenance::HeightFact =>
                                j.push_str("{\"k\":\"imp\",\"p\":\"height\"}"),
                            HypProvenance::Requires { index } =>
                                j.push_str(&format!("{{\"k\":\"imp\",\"p\":\"requires\",\"i\":{}}}", index)),
                            HypProvenance::HoistEq { binder } =>
                                j.push_str(&format!(
                                    "{{\"k\":\"imp\",\"p\":\"hoist\",\"binder\":\"{}\"}}", esc(binder.as_str()))),
                            HypProvenance::CtorEq { scrutinee, variant, .. } =>
                                j.push_str(&format!(
                                    "{{\"k\":\"imp\",\"p\":\"ctor\",\"scrut\":\"{}\",\"variant\":\"{}\"}}",
                                    esc(scrutinee.as_str()), esc(variant))),
                            HypProvenance::LoopInv { index, at } =>
                                j.push_str(&format!(
                                    "{{\"k\":\"imp\",\"p\":\"loopinv\",\"i\":{},\"at\":\"{}\"}}",
                                    index,
                                    match at {
                                        crate::lean_ast::LoopPhase::Maintain => "maintain",
                                        crate::lean_ast::LoopPhase::Exit => "exit",
                                    })),
                            HypProvenance::AssertFact =>
                                j.push_str("{\"k\":\"imp\",\"p\":\"assert\"}"),
                            HypProvenance::AssumeFact =>
                                j.push_str("{\"k\":\"imp\",\"p\":\"assume\"}"),
                            HypProvenance::Other =>
                                j.push_str("{\"k\":\"imp\",\"p\":\"other\"}"),
                            HypProvenance::CallFact(info) => {
                                j.push_str(&format!(
                                    "{{\"k\":\"imp\",\"p\":\"call\",\"callee\":\"{}\",\"self\":{},\"args\":[",
                                    esc(&info.callee), info.is_self));
                                for (a, arg) in info.args.iter().enumerate() {
                                    if a > 0 { j.push(','); }
                                    let tag = match &arg.tag {
                                        SpineArgTag::CallerParam(n) => format!("param:{}", n),
                                        SpineArgTag::Literal => "lit".to_string(),
                                        SpineArgTag::Expr => "expr".to_string(),
                                    };
                                    j.push_str(&format!(
                                        "{{\"text\":\"{}\",\"tag\":\"{}\"}}",
                                        esc(&arg.text), esc(&tag)));
                                }
                                j.push_str("],\"ens\":[");
                                for (k, s) in info.ensures_summary.iter().enumerate() {
                                    if k > 0 { j.push(','); }
                                    j.push_str(&format!("\"{}\"", match s {
                                        crate::lean_ast::EnsuresShape::LenEq => "leneq",
                                        crate::lean_ast::EnsuresShape::ForallPointwise => "pointwise",
                                        crate::lean_ast::EnsuresShape::OtherEq => "eq",
                                        crate::lean_ast::EnsuresShape::Other => "other",
                                    }));
                                }
                                j.push_str("]}");
                            }
                        },
                    }
                }
                j.push_str("]}");
            }
        }
    }
    j.push_str("]}\n");
    std::fs::write(pkg_lean_path.with_extension("spine.json"), j)
}

fn emit_package_exec_fn(
    krate: &KrateX,
    vir_fn: &FunctionX,
    fn_sst: &FunctionSst,
    check: &FuncCheckSst,
    imports: &[String],
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
    defs: &crate::crate_defs::CrateDefs,
) -> Result<PkgEmitOutcome, String> {
    install_emit_tables(krate, crate_name);
    // Same front half as `emit_exec_fn` (inline pass + broadcast
    // resolution + WP theorems); duplicated because the island path
    // remains the graceful-degradation fallback and must stay
    // self-contained. Divergence risk is bounded: both feed
    // `exec_fn_theorems_to_ast`, the single source of obligation
    // shape.
    let inlined_krate = crate::inline_spec::inline_marked_in_krate(krate);
    let vir_fn = inlined_krate.functions.iter()
        .find(|f| f.x.name == vir_fn.name).map(|f| &f.x)
        .ok_or("root exec fn absent from inlined krate")?;
    let krate = &inlined_krate;
    let broadcast_lemmas = sst_to_lean::collect_broadcast_lemma_funs(krate, check, crate_name);
    let sst_to_lean::ExecFnObligations { theorems, goal_shapes } =
        sst_to_lean::exec_fn_theorems_to_ast(krate, fn_sst, check, &broadcast_lemmas)
            .map_err(|reason| format!("tactus_auto rejected this fn: {}", reason))?;
    // Bootstrap N3 snapshot: serialize the fn's SST literal (inputs) plus
    // the production GoalList (N3b, from the just-built obligation spines).
    // `check` is `&`-borrowed by `exec_fn_theorems_to_ast`, so capturing
    // here — right after the call — reads the SAME snapshot (the single
    // source of obligation shape). No-op unless `--tactus-emit-cert`;
    // never perturbs verification.
    crate::sst_serialize::emit_cert(krate, fn_sst, check, crate_name, &theorems, &goal_shapes);
    // L1 Link-discharge: capture (name, shape) pairs for the spine
    // sidecar before `theorems` is consumed below.
    let spine_records: Vec<(String, Option<crate::lean_ast::GoalShape>)> = theorems
        .iter()
        .map(|t| t.name.clone())
        .zip(goal_shapes.iter().cloned())
        .collect();

    let stmts = stmt_partition_for(krate, crate_name, tactic_bodies, defs)
        .ok_or("Stmts partition unavailable")?;
    let ectx = crate::emit_ctx::EmitCtx::build(krate, tactic_bodies);
    let _ = &ectx;

    // Precise per-obligation helper scan (the same textual mechanism
    // as `direct_helper_deps`, over each obligation's tactic text).
    let candidates: Vec<(&FunctionX, &str)> = krate.functions.iter()
        .map(|f| &f.x)
        .filter(|f| is_emittable_tactic_proof_fn(f, tactic_bodies))
        .map(|f| (f, short_name(&f.name.path)))
        .collect();
    let per_thm_deps: Vec<Vec<&FunctionX>> = theorems.iter()
        .map(|thm| {
            let code = strip_lean_line_comments(tactic_scan_text(&thm.tactic));
            candidates.iter()
                .filter(|(_, name)| ident_appears(&code, name))
                .map(|(f, _)| *f)
                .collect()
        })
        .collect();
    let deps: Vec<&FunctionX> = {
        let mut seen = std::collections::HashSet::new();
        per_thm_deps.iter().flatten()
            .filter(|f| seen.insert(&f.name))
            .copied()
            .collect()
    };

    // Own stmt module: per-obligation statement defs. Same file head
    // as the proof-fn stmt partition (package preamble over empty
    // roots), written tracked into the defs dir so
    // `ensure_stmt_olean` covers it unchanged.
    let own_stmt_name = stmt_fn_module_name(defs, &vir_fn.name);
    let own_changed = {
        // Pass the fn's theorems so their `requires_preamble`
        // fragments (e.g. the #130 BitVec Int instances) are
        // aggregated at file top — the stmt defs re-render the same
        // obligation exprs and need the same instances (below-gate
        // shape surfaced when the defs size gate was removed).
        let (mut cmds, _ns) = krate_preamble(
            krate, &[], crate_name, &[], PreambleConfig::ExecFnPackage, &theorems,
            tactic_bodies, &[], Some(defs),
        );
        for thm in &theorems {
            cmds.push(to_lean_fn::exec_obligation_stmt_cmd(thm));
        }
        let rendered = pp_commands(&cmds);
        let path = defs.dir.join(format!("{}.lean", own_stmt_name));
        write_lean_file_tracked(&path, &rendered.text)?
    };

    // Import manifest: own stmt module first, then helpers' (M5d-2).
    let mut stmt_modules: Vec<(String, bool)> = vec![(own_stmt_name, own_changed)];
    stmt_modules.extend(deps.iter()
        .filter_map(|f| stmts.get(&f.name).map(|(n, _, ch)| (n.clone(), *ch))));
    let mut file_imports: Vec<String> = imports.to_vec();
    file_imports.extend(stmt_modules.iter().map(|(n, _)| n.clone()));

    // Binder names are SHORT names — two helpers sharing one short
    // name would collide as hypotheses and make the qualified-ref
    // bridge ambiguous. Bail to the island path (which has no such
    // constraint: its helpers are global dotted theorems).
    {
        let mut shorts = std::collections::HashSet::new();
        for f in &deps {
            if !shorts.insert(short_name(&f.name.path)) {
                return Ok(PkgEmitOutcome::UnsupportedScc(format!(
                    "helpers share the short name `{}` — hypothesis binders \
                     cannot disambiguate", short_name(&f.name.path))));
            }
        }
    }
    let (mut cmds, ns) = krate_preamble(
        krate, &file_imports, crate_name, &[vir_fn],
        PreambleConfig::ExecFnPackage, &theorems, tactic_bodies,
        &broadcast_lemmas, Some(defs),
    );
    let _ = ns;
    let thm_names: Vec<String> = theorems.iter().map(|t| t.name.clone()).collect();
    for (thm, thm_deps) in theorems.into_iter().zip(per_thm_deps.iter()) {
        let mut thm = thm;
        if !thm_deps.is_empty() {
            if let crate::lean_ast::Tactic::Raw(body) = &thm.tactic {
                thm.tactic = crate::lean_ast::Tactic::Raw(
                    bridge_qualified_helper_refs(body, thm_deps));
            }
        }
        let hyps: Vec<crate::lean_ast::Binder> = thm_deps.iter()
            .map(|f| to_lean_fn::helper_hyp_binder(&f.name.path))
            .collect();
        thm.binders.splice(0..0, hyps);
        cmds.push(Command::Theorem(thm));
    }

    #[cfg(debug_assertions)]
    {
        let concat: Vec<Command> = defs.cmds.iter()
            .chain(deps.iter()
                .filter_map(|f| stmts.get(&f.name))
                .flat_map(|(_, c, _)| c.iter()))
            .chain(cmds.iter())
            .cloned().collect();
        debug_check(&concat)?;
    }
    #[cfg(not(debug_assertions))]
    let _ = &stmts;

    let rendered = pp_commands(&cmds);
    let source_map = LeanSourceMap::ExecFn {
        fn_name: short_name(&vir_fn.name.path).to_string(),
        span_marks: rendered.landmarks.span_marks.clone(),
    };
    let leaf = lean_name(&vir_fn.name.path).replace('.', "__");
    let path = lean_out_root().join(sanitize(crate_name)).join("pkg")
        .join(format!("{}.lean", leaf));
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }
    let changed = write_lean_file_tracked(&path, &rendered.text)?;
    // L1 Link-discharge sidecar (DESIGN-link-discharge.md §3.1): persist
    // each VC's spine descriptors next to the pkg module so the Link
    // builder can generate discharge terms even on cache-skipped runs.
    // Slice (a): write-only — nothing consumes it yet. Best-effort: a
    // sidecar failure must not fail verification.
    if let Err(e) = write_spine_sidecar(&path, &leaf, &spine_records) {
        eprintln!("tactus: spine sidecar write failed for {leaf}: {e}");
    }
    record_exec_link_entry(&defs.scope, ExecLinkEntry {
        leaf: leaf.clone(),
        obligations: thm_names.into_iter()
            .zip(per_thm_deps.iter())
            .map(|(n, ds)| (n, ds.iter().map(|f| f.name.path.clone()).collect()))
            .collect(),
        fn_name: lean_name(&vir_fn.name.path),
        is_proof: matches!(vir_fn.mode, vir::ast::Mode::Proof),
    });
    Ok(PkgEmitOutcome::Single { leaf, path, source_map, stmt_modules, changed })
}

/// Verify an exec fn via its package module (M6.2). `None` = the
/// route can't run (defs unavailable, defs don't cover exec, or the
/// emission is package-inexpressible) — the caller falls through to
/// the island path, which remains fully self-contained.
///
/// Sorry is FATAL here, exactly as on the exec island path: exec
/// closed forms don't join the Link composition until M6.3, so there
/// is no sorryAx backstop behind this route yet — which is also why
/// the built olean is NOT registered with `record_pkg_olean_built`
/// (the M4 gate would try to compose it into the Link closure).
fn check_exec_fn_via_package(
    krate: &KrateX,
    vir_fn: &FunctionX,
    fn_sst: &FunctionSst,
    check: &FuncCheckSst,
    imports: &[String],
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> Option<CheckResult> {
    install_emit_tables(krate, crate_name);
    let defs = match crate::crate_defs::for_crate(
        krate, crate_name, tactic_bodies, true, crate::crate_defs::ScopeKind::Exec,
    ) {
        Some(d) if d.covers_exec => d,
        // Silent fallback (see check_proof_fn_via_package): below-gate
        // crates and failed ladders verify via islands, as pre-M6.5.
        _ => return None,
    };
    let prelude_dir = match crate::prelude::ensure_prelude_olean() {
        Ok(d) => d,
        Err(e) => return Some(CheckResult::Error(e)),
    };
    let base_path = format!("{}:{}", prelude_dir.display(), defs.dir.display());
    // Consume the prime pass's stashed emission if there is one (see
    // PRIME_OUTCOMES: re-emitting would corrupt the changed flags).
    let emitted = take_prime_outcome(&vir_fn.name).unwrap_or_else(|| {
        emit_package_exec_fn(
            krate, vir_fn, fn_sst, check, imports, crate_name, tactic_bodies, &defs,
        )
    });
    match emitted {
        Ok(PkgEmitOutcome::Single { leaf, path, source_map, stmt_modules, changed }) => {
            let olean = path.with_extension("olean");
            let cacheable = !changed
                && stmt_modules.iter().all(|(_, ch)| !ch)
                && !defs.breaking
                && olean.exists();
            if cacheable {
                record_pkg_olean_built(&path);
                PKG_CACHED_VERDICTS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                return Some(CheckResult::Success { warnings: vec![] });
            }
            for (m, ch) in &stmt_modules {
                let may_skip = !ch && !defs.breaking;
                if let Err(e) = ensure_stmt_olean(m, &defs, &prelude_dir, may_skip) {
                    return Some(CheckResult::Error(e));
                }
            }
            let pkg_dir = path.parent().expect("pkg file has a parent").to_path_buf();
            let result = run_lean_json(&pkg_dir, &leaf, true, &base_path);
            // Sorry parity with the proof-fn package path (C-2/M6.3):
            // warning at fn level; the Link gate's #tactus_check_axioms
            // closure is the fatal backstop — exec closed forms are in
            // it now. (A gate skipped by an UNRELATED fn error still
            // fails the run via that error, so no green run can carry
            // an ungated sorry.)
            if matches!(&result, Ok(r) if r.success) {
                record_pkg_olean_built(&path);
            }
            // assume(P)-site warnings: same collection as the island
            // path (`emit_exec_fn`) — the pkg route previously dropped
            // them (surfaced when the defs size gate was removed).
            let assume_warnings: Vec<String> = vir_fn.body.as_ref()
                .map(|body| sst_to_lean::collect_assume_sites(body))
                .unwrap_or_default()
                .iter()
                .map(|span| format!(
                    "{} at {}: backed by an unverified hypothesis (`assume(P)`                      enters the spec as fact without a proof). Replace with a proven                      `assert(P) by {{ ... }}` before relying on this in production.",
                    vir::tactus_messages::ASSUME_WARNING_TAG,
                    sst_to_lean::format_span_loc(span),
                ))
                .collect();
            Some(match format_lean_check_result(result, vir_fn, &path, &source_map) {
                CheckResult::Success { mut warnings } => {
                    warnings.extend(assume_warnings);
                    CheckResult::Success { warnings }
                }
                other => other,
            })
        }
        Ok(other) => {
            let reason = match other {
                PkgEmitOutcome::UnsupportedScc(r) => r,
                _ => "unexpected mutual outcome for exec fn".to_string(),
            };
            eprintln!(
                "tactus: package-check: `{}` not package-expressible ({}); island check",
                short_name(&vir_fn.name.path), reason
            );
            None
        }
        Err(e) => {
            eprintln!(
                "tactus: package-check: exec package emission failed for `{}` ({}); island check",
                short_name(&vir_fn.name.path), e
            );
            None
        }
    }
}

pub fn emit_exec_fn(
    krate: &KrateX,
    vir_fn: &FunctionX,
    fn_sst: &FunctionSst,
    check: &FuncCheckSst,
    imports: &[String],
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> Result<EmitOutput, CheckResult> {
    install_emit_tables(krate, crate_name);
    // Pre-inline krate for the shared-defs lookup below (`for_crate`
    // applies its own inline pass; the lookup happens after
    // `broadcast_lemmas` resolves, by which point `krate` is shadowed).
    let pre_inline_krate = krate;
    // Layer 7 — inline `#[verifier::inline]` spec fns on the VIR-AST so the
    // broadcast-lemma clauses krate_preamble emits agree with Verus's
    // SST-inlined exec goal. The exec goal itself already arrives inlined (via
    // the SST in `check`); this brings the VIR-AST side into agreement. The
    // root is re-fetched from the inlined krate so dep-walk roots don't
    // reference the dropped inline-fn defs. See `inline_spec`.
    let inlined_krate = crate::inline_spec::inline_marked_in_krate(krate);
    let vir_fn = inlined_krate.functions.iter()
        .find(|f| f.x.name == vir_fn.name).map(|f| &f.x)
        .expect("root exec fn present in inlined krate (exec fns are never #[inline])");
    let krate = &inlined_krate;

    // Collect `assume(P)` sites first so warnings surface even when
    // the rest of the codegen rejects the fn. Each `assume` is a
    // soundness escape hatch — `assume(P)` enters its expression
    // as a hypothesis without a backing proof obligation, so users
    // need a visible reminder per site. Walks the VIR-AST body
    // (`vir_fn.body`) rather than the SST so synthetic
    // `StmX::Assume` injected by Verus's later passes (overflow,
    // call-ensures) doesn't produce false positives.
    let warnings: Vec<String> = vir_fn.body.as_ref()
        .map(|body| sst_to_lean::collect_assume_sites(body))
        .unwrap_or_default()
        .iter()
        .map(|span| format!(
            "{} at {}: backed by an unverified hypothesis (`assume(P)` \
             enters the spec as fact without a proof). Replace with a proven \
             `assert(P) by {{ ... }}` before relying on this in production.",
            vir::tactus_messages::ASSUME_WARNING_TAG,
            sst_to_lean::format_span_loc(span),
        ))
        .collect();

    // Cross-crate broadcast lemmas this fn opts into via
    // `broadcast use <group>;` (#122). Resolved once here and fed to
    // both `exec_fn_theorems_to_ast` (which injects `have`-bindings)
    // and `krate_preamble` (which emits the lemma axioms + walks their
    // spec-fn deps).
    let broadcast_lemmas = sst_to_lean::collect_broadcast_lemma_funs(krate, check, crate_name);

    let (theorems, goal_shapes) = match sst_to_lean::exec_fn_theorems_to_ast(krate, fn_sst, check, &broadcast_lemmas) {
        Ok(r) => (r.theorems, r.goal_shapes),
        Err(reason) => return Err(CheckResult::Failed {
            errors: vec![TactusDiag {
                message: format!(
                    "tactus_auto rejected this fn: {} \
                     (see DESIGN.md \"Known deferrals, rejected cases, and untested edges\" \
                     for the full catalogue of unsupported SST shapes)",
                    reason,
                ),
                location: DiagLocation::Unknown,
                help: None,
            }],
            warnings,
        }),
    };

    // Bootstrap N3 snapshot: serialize the fn's SST literal (inputs) plus
    // the production GoalList (N3b), from the SAME `&`-borrowed `check`
    // the call above read. No-op unless `--tactus-emit-cert`; never
    // perturbs verification.
    crate::sst_serialize::emit_cert(krate, fn_sst, check, crate_name, &theorems, &goal_shapes);

    // Exec fns lower matches to if-chains over `IsVariant` and
    // `Field`, which the SST renderer routes to the synthesised
    // accessor fns — so the preamble must include them. The
    // preamble also aggregates each theorem's `requires_preamble`
    // (e.g., the BitVec instances #130 needs) and emits them once at
    // file top, deduped.
    // Broadcast lemmas no longer disable shared-defs (CRATEDEFS 1c
    // fix c): the defs module carries the UNION of emittable broadcast
    // axioms, and any per-fn collected set is a subset by construction
    // — so the import supplies what local emission used to. This is
    // what unlocks defs sharing for real crates at all: vstd's
    // default-on-import broadcast groups make `broadcast_lemmas`
    // non-empty for EVERY fn in a vstd-importing crate.
    // `covers_exec: false` = the defs module was rebuilt from proof
    // roots only (its full-roots attempt failed in Lean) — EXEC
    // closures may be absent, so true exec fns emit standalone; WP-
    // style PROOF fns (Verus proof bodies routed through this same WP
    // path) are covered by the proof roots and keep the import.
    let defs = crate::crate_defs::for_crate(pre_inline_krate, crate_name, tactic_bodies, false, crate::crate_defs::ScopeKind::Exec)
        .filter(|d| d.covers_exec || matches!(vir_fn.mode, vir::ast::Mode::Proof));
    let (mut cmds, ns) = krate_preamble(
        krate, imports, crate_name, &[vir_fn],
        PreambleConfig::ExecFn,
        &theorems,
        tactic_bodies,
        &broadcast_lemmas,
        defs.as_deref(),
    );

    for theorem in theorems {
        cmds.push(Command::Theorem(theorem));
    }
    let _ = ns;

    // Pretty-print and write the .lean file BEFORE the sanity check
    // so the artifact is always available for inspection — even when
    // sanity rejects, users can `cat` the .lean path mentioned in the
    // error to see what was emitted.
    let rendered = pp_commands(&cmds);

    // Exec fns map errors via `span_marks` populated by the pp's
    // `SpanMark` walker (#51 source mapping) — Rust source
    // location for each obligation emitted by `walk_obligations`.
    // Built here (in the emit half) since it depends only on
    // `rendered.landmarks`, available before the Lean run.
    let source_map = LeanSourceMap::ExecFn {
        fn_name: short_name(&vir_fn.name.path).to_string(),
        span_marks: rendered.landmarks.span_marks.clone(),
    };

    let file_path = lean_file_path(crate_name, &vir_fn.name.path);
    let changed = match write_lean_file_tracked(&file_path, &rendered.text) {
        Ok(c) => c,
        Err(e) => return Err(CheckResult::Error(e)),
    };

    let cmds_for_sanity: Vec<Command> = match &defs {
        // Sanity resolves identifiers over the command stream; in defs
        // mode the spec world arrives via import, so check against the
        // concatenation — exactly what Lean sees.
        Some(d) => d.cmds.iter().cloned().chain(cmds.iter().cloned()).collect(),
        None => cmds.clone(),
    };
    if let Err(reason) = debug_check(&cmds_for_sanity) {
        return Err(CheckResult::Failed {
            errors: vec![TactusDiag {
                message: reason,
                location: DiagLocation::Unknown,
                help: Some(format!("{} {}",
                    vir::tactus_messages::LEAN_FILE_HELP_PREFIX, file_path.display())),
            }],
            warnings,
        });
    }

    Ok(EmitOutput {
        file_path, source_map, warnings, changed,
        first_theorem_line: rendered.landmarks.theorem_heads.first().copied(),
    })
}

/// Verify an exec fn: emit its `.lean` (via `emit_exec_fn`), then run Lean.
pub fn check_exec_fn(
    krate: &KrateX,
    vir_fn: &FunctionX,
    fn_sst: &FunctionSst,
    check: &FuncCheckSst,
    imports: &[String],
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> CheckResult {
    // Package-check route (M6.2): exec fns verify via their PACKAGE
    // module when the exec defs cover them. `None` = fall through to
    // the island path below (graceful degradation, same as proof fns).
    if package_check_enabled() {
        if let Some(result) = check_exec_fn_via_package(
            krate, vir_fn, fn_sst, check, imports, crate_name, tactic_bodies,
        ) {
            return result;
        }
    }
    // Same defs-before-emit ordering as `check_proof_fn` (see there).
    let defs = crate::crate_defs::for_crate(krate, crate_name, tactic_bodies, true, crate::crate_defs::ScopeKind::Exec);
    let EmitOutput { file_path, source_map, warnings, first_theorem_line, changed } =
        match emit_exec_fn(krate, vir_fn, fn_sst, check, imports, crate_name, tactic_bodies) {
            Ok(o) => o,
            Err(cr) => return cr,
        };
    let marker = file_path.with_extension("verified");
    if island_cache_ok(&marker, changed, &defs) {
        // Emission warnings are recomputed each run (emit always
        // runs); lean-side success warnings are the sorry-filtered
        // set, empty by construction on this path.
        return CheckResult::Success { warnings };
    }
    let _ = std::fs::remove_file(&marker);

    let dir = project::default_project_dir();
    let lake_dir = if project::project_ready(&dir) { Some(dir.as_path()) } else { None };
    let prelude_dir = match crate::prelude::ensure_prelude_olean() {
        Ok(d) => d,
        Err(e) => return CheckResult::Error(e),
    };
    let mut extra_paths: Vec<&std::path::Path> = vec![&prelude_dir];
    if let Some(d) = &defs {
        extra_paths.push(&d.dir);
    }
    let result = lean_process::check_lean_file(&file_path, lake_dir, &extra_paths);

    match result {
        Ok(r) if r.success => {
            if let Some(fail) = island_sorry_failure(
                &r, first_theorem_line, &vir_fn.name.path, &file_path, &source_map)
            {
                return fail;
            }
            let _ = std::fs::write(&marker, crate::project::toolchain_fingerprint());
            CheckResult::Success { warnings }
        }
        Ok(r) => {
            let fn_short = short_name(&vir_fn.name.path);
            let header = format!("Lean tactus_auto failed for {}", fn_short);
            let help = Some(format!("{} {}",
                vir::tactus_messages::LEAN_FILE_HELP_PREFIX, file_path.display()));
            let errors: Vec<TactusDiag> = r.diagnostics.iter()
                .filter(|d| d.severity == "error")
                .map(|d| {
                    let formatted = lean_process::format_error(d, &source_map);
                    TactusDiag {
                        message: format!("{}:\n\n{}", header, formatted.message),
                        location: formatted.location,
                        help: help.clone(),
                    }
                })
                .collect();
            let errors = if errors.is_empty() {
                vec![TactusDiag {
                    message: format!("{}: {}", header,
                        vir::tactus_messages::NO_ERROR_DIAGNOSTICS_BODY),
                    location: DiagLocation::Unknown,
                    help,
                }]
            } else {
                errors
            };
            CheckResult::Failed { errors, warnings }
        }
        Err(e) => CheckResult::Error(e),
    }
}

/// Collect the datatypes that need Lean declarations emitted: the ones
/// directly referenced by the proof/exec fns plus their transitive
/// closure over field-type references.
///
/// `dep_order::collect_references` walks fn parameter / return / require /
/// ensure / body types and collects datatype names — but it doesn't
/// recurse into datatype variant fields. So a fn that references `Tree`
/// only via `(t: Tree) → ...` wouldn't surface `Forest` even when `Tree`'s
/// variant has a `Box<Forest>` field. Without that, mutually recursive
/// datatypes (#109) would emit only one half of the SCC and Lean would
/// reject the missing half.
///
/// Output is in original `krate.datatypes` order so emission is stable
/// across runs. Filters out tuples (no decl needed) and Verus-synthesized
/// `anonymous_closure%`-prefixed types (#93).
fn collect_referenced_datatypes<'a>(
    krate: &'a vir::ast::KrateX,
    refs: &dep_order::References<'_>,
    // Extra root paths beyond `refs.datatypes` — datatypes referenced
    // only by emitted instance heads (see caller, #122 RC3). Seeded into
    // the worklist alongside the fn-body refs so their (transitive)
    // declarations emit.
    extra_seed: &std::collections::HashSet<&'a vir::ast::Path>,
) -> Vec<&'a vir::ast::DatatypeX> {
    use std::collections::{HashMap, HashSet};
    let path_to_dt: HashMap<&'a vir::ast::Path, &'a vir::ast::DatatypeX> =
        krate.datatypes.iter()
            .filter_map(|dt| match &dt.x.name {
                Dt::Path(p) => {
                    let short = short_name(p);
                    if short.starts_with("anonymous_closure") { None }
                    else { Some((p, &dt.x)) }
                }
                Dt::Tuple(_) => None,
            })
            .collect();

    let mut seen: HashSet<&'a vir::ast::Path> = HashSet::new();
    let mut worklist: Vec<&'a vir::ast::Path> = path_to_dt.keys()
        .filter(|p| refs.datatypes.contains(short_name(p)) || extra_seed.contains(*p))
        .copied()
        .collect();
    while let Some(p) = worklist.pop() {
        if !seen.insert(p) { continue; }
        let Some(dt) = path_to_dt.get(p) else { continue };
        for variant in dt.variants.iter() {
            for field in variant.fields.iter() {
                dep_order::walk_typ_paths(&field.a.0, &mut |q| {
                    if path_to_dt.contains_key(q) && !seen.contains(q) {
                        worklist.push(q);
                    }
                });
            }
        }
    }

    // Preserve original krate.datatypes order.
    krate.datatypes.iter()
        .filter_map(|dt| match &dt.x.name {
            Dt::Path(p) if seen.contains(p) => Some(&dt.x),
            _ => None,
        })
        .collect()
}

/// In debug builds, verify the command stream is internally consistent —
/// every `Var` in a theorem goal / def body / instance method body is
/// either a local binder, an earlier top-level definition, or a known
/// Lean/Mathlib built-in. A violation means we lost track of a
/// dependency and Lean would reject the file; returning a formatted
/// error here points at the exact identifier instead of forcing the
/// user to decode a Lean unknown-identifier error.
///
/// Returns `Err` listing each unresolved reference and its context.
/// Callers convert this to `CheckResult::Failed` so the rejection
/// flows through Verus's normal error path (instead of a panic that
/// kills the test process).
///
/// Compiled out of release builds (returns `Ok(())` unconditionally).
/// Codegen sanity: unconditional in ALL build profiles (2026-07-11,
/// Danielle: "same behavior in release builds"). Users run release
/// binaries; the checks that guard USER input (the reserved-binder
/// rule) and emitted-reference resolution must not be debug-only —
/// a violation surfacing as a clear codegen diagnostic beats the same
/// bug surfacing as a baffling lake-time resolution error. Cost is an
/// AST walk per emitted fn — negligible next to the Lean run.
pub(crate) fn debug_check(_cmds: &[Command]) -> Result<(), String> {
    {
        let violations = sanity::check_references(_cmds);
        if !violations.is_empty() {
            let lines: Vec<String> = violations.iter()
                .map(|v| format!("  in `{}`: unresolved `{}`", v.context, v.name))
                .collect();
            return Err(format!(
                "Tactus codegen produced unresolved references:\n{}\n\nThis usually means \
                 `dep_order` missed a fn while walking VIR (check `walk_expr` / `walk_place` \
                 coverage for any new ExprX/PlaceX variants), or a callee's body is `None` \
                 (uninterp spec fn / external_body fn) and isn't yet emitted as an opaque/axiom \
                 — see DESIGN.md \"Cross-crate spec fn availability\".",
                lines.join("\n")
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
#[path = "tests/generate.rs"]
mod tests;

