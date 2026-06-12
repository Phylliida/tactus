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
    if let Ok(dir) = std::env::var("TACTUS_LEAN_OUT") {
        return PathBuf::from(dir);
    }
    if let Ok(dir) = std::env::var("CARGO_TARGET_DIR") {
        return PathBuf::from(dir).join("tactus-lean");
    }
    PathBuf::from("target").join("tactus-lean")
}

/// Compute the on-disk artifact path for a given function.
/// Structure: `{root}/{crate}/{fn_lean_name_with_underscores}.lean`.
/// Dots in Lean names (module separators) become `__` so the file name stays flat.
fn lean_file_path(crate_name: &str, fn_path: &vir::ast::Path) -> PathBuf {
    let ns = sanitize(crate_name);
    let leaf = lean_name(fn_path).replace('.', "__");
    lean_out_root().join(ns).join(format!("{}.lean", leaf))
}

/// On-disk path for the `--emit-lean` sidecar: `{root}/{crate}/sourcemap.json`,
/// alongside the crate's generated `.lean` files (so the Tactus server finds
/// the map next to the artifacts it indexes).
pub fn sourcemap_path(crate_name: &str) -> PathBuf {
    lean_out_root().join(sanitize(crate_name)).join("sourcemap.json")
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
    /// Proof fns: native match rendering (no accessor fns).
    /// Emitting accessors for types with non-Inhabited fields
    /// breaks Lean elaboration even when unused, so the proof-fn
    /// path keeps them off.
    ProofFn,
    /// Exec fns: emit accessor fns for desugared match (via
    /// `IsVariant` / `Field`).
    ExecFn,
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
    let is_emittable_helper = |f: &&FunctionX| {
        matches!(f.mode, vir::ast::Mode::Proof)
            && !matches!(
                f.kind,
                FunctionKind::TraitMethodDecl { .. } | FunctionKind::TraitMethodImpl { .. }
            )
            && tactic_bodies.contains_key(&f.name)
    };
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
            cmds.push(Command::Raw(crate::prelude::TACTUS_PRELUDE_IMPORT.to_string()));
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
    cmds.push(Command::NamespaceOpen(ns.clone()));
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
        cmds.extend(spec_world_cmds(krate, &ectx, &dep_walk_roots, emit_accessors, &bc_lemma_funcs, false));
    } else {
        debug_assert!(bc_lemma_funcs.is_empty(),
            "broadcast-using fns fall back to standalone emission");
    }
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
pub(crate) fn spec_world_cmds(
    krate: &KrateX,
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
    let push_lenient = |cmds: &mut Vec<Command>, what: &str, f: &mut dyn FnMut() -> Vec<Command>| {
        if !lenient {
            cmds.extend(f());
            return;
        }
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f())) {
            Ok(v) => cmds.extend(v),
            Err(payload) => {
                let msg = payload.downcast_ref::<&str>().map(|s| s.to_string())
                    .or_else(|| payload.downcast_ref::<String>().cloned())
                    .unwrap_or_else(|| "<non-string panic payload>".to_string());
                eprintln!("tactus: skipped un-renderable {} in shared defs: {}", what, msg);
            }
        }
    };
    let mut cmds: Vec<Command> = Vec::new();
    let all_fns: Vec<&FunctionX> = krate.functions.iter().map(|f| &f.x).collect();
    let spec_fn_map = dep_order::build_spec_fn_map(&all_fns);
    let mut refs = dep_order::collect_references(&spec_fn_map, &ectx.fn_map, dep_walk_roots);

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
    let traits_with_emitted_impl: std::collections::HashSet<&str> = instances_to_emit.iter()
        .map(|(ti, _)| short_name(&ti.x.trait_path))
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
    let nonempty_needs = crate::nonempty::compute_nonempty_needs(&all_fns);
    let add_nonempty = |f: vir::ast::FunctionX, name: &Fun| -> vir::ast::FunctionX {
        match nonempty_needs.get(name) {
            Some(idx) => crate::nonempty::add_fn_nonempty_bounds(f, idx),
            None => f,
        }
    };
    let augment = |f: &vir::ast::FunctionX| -> vir::ast::FunctionX {
        let augmented = if matches!(f.kind, FunctionKind::TraitMethodImpl { .. }) {
            crate::impl_subst::maybe_augment_impl_method(f, &impl_substs)
        } else {
            crate::impl_subst::maybe_augment_standalone_fn(f, &ectx.trait_outparams)
        };
        add_nonempty(augmented, &f.name)
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
        let ne_bounds = crate::nonempty::instance_nonempty_bounds(
            &nonempty_needs, method_impls, &ti.x.typ_params);
        cmds.push(Command::Instance(
            to_lean_fn::trait_impl_to_ast(&ti.x, method_impls, &assoc_types, subst, &ne_bounds, ectx)
        ));
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

    // No spec-fn groups at all: proof classes have nothing to wait on.
    if last_group_pos.is_none() {
        push_lenient(&mut cmds, "proof-method trait classes", &mut || {
            let mut tmp = Vec::new();
            emit_proof_classes(&mut tmp);
            tmp
        });
    }
    for (pos, step) in order.iter().enumerate() {
        match step {
            dep_order::EmitStep::Group(i) => match &groups[*i] {
                FnGroup::Single(f) => {
                    push_lenient(&mut cmds, "spec fn", &mut || {
                        let augmented = augment(f);
                        vec![to_lean_fn::spec_fn_to_ast(&augmented, ectx)]
                    });
                }
                FnGroup::Mutual(fns) => {
                    push_lenient(&mut cmds, "mutual spec fns", &mut || {
                        let inner: Vec<Command> = fns.iter()
                            .map(|f| {
                                let augmented = augment(f);
                                to_lean_fn::spec_fn_to_ast(&augmented, ectx)
                            })
                            .collect();
                        vec![Command::Mutual(inner)]
                    });
                }
            },
            dep_order::EmitStep::Instance(j) =>
                push_lenient(&mut cmds, "trait instance", &mut || {
                    let mut tmp = Vec::new();
                    emit_instance(&mut tmp, *j);
                    tmp
                }),
        }
        if Some(pos) == last_group_pos {
            push_lenient(&mut cmds, "proof-method trait classes", &mut || {
                let mut tmp = Vec::new();
                emit_proof_classes(&mut tmp);
                tmp
            });
        }
    }
    // Cross-crate broadcast lemmas (#122), emitted as Lean axioms
    // LAST in the preamble — they're leaves (only the fn's obligation
    // theorems reference them, via the injected `have _tactus_bc_i := …`),
    // and their require/ensure reference spec fns + datatypes already
    // emitted above (brought in via the `dep_walk_roots` extension).
    // Sound by the same argument as cross-crate axiomatized ensures:
    // vstd verified the lemma (`vargo build` → 1530/0); we stipulate
    // it. The user opted in explicitly with `broadcast use <group>;`.
    for &f in bc_lemma_funcs {
        // Lift assoc-type projections in the lemma's ensure/require (e.g.
        // `axiom_hashmap_deepview_borrow`'s `<K as DeepView>::V`) — same
        // generalized projection-lifting as standalone spec fns. No-op for
        // projection-free lemmas (the common case).
        let augmented = crate::impl_subst::maybe_augment_standalone_fn(f, &ectx.trait_outparams);
        // A lemma whose facts dispatch to a `choose`-using fn (e.g.
        // `axiom_hashmap_deepview_borrow` → `deep_view` → the epsilon in
        // `hash_map_deep_view_impl`) needs `[Nonempty T]` too.
        let augmented = add_nonempty(augmented, &f.name);
        cmds.push(to_lean_fn::broadcast_lemma_axiom_cmd(&augmented, ectx));
    }
    cmds
}

/// Ambient thread-local tables every render path needs installed
/// first. Wrapped so `crate_defs` (which renders outside the per-fn
/// emit entry points) installs exactly what `emit_proof_fn` /
/// `emit_exec_fn` install.
pub(crate) fn install_emit_tables(krate: &KrateX) {
    install_inherent_method_renames(krate);
    install_datatype_field_bounds(krate);
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
}

pub fn emit_proof_fn(
    krate: &KrateX,
    proof_fn: &FunctionX,
    tactic_body: &str,
    imports: &[String],
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> Result<EmitOutput, CheckResult> {
    install_inherent_method_renames(krate);
    install_datatype_field_bounds(krate);
    // Shared-defs lookup (CRATEDEFS.md step 1a). Memo-consistent with
    // the `check_proof_fn` build: in check mode the defs were already
    // built (or poisoned to None) before this runs; in `--emit-lean`
    // mode this writes the defs source without building. Takes the
    // pre-inline krate — `for_crate` applies its own inline pass.
    let defs = crate::crate_defs::for_crate(krate, crate_name, tactic_bodies, false);
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
    cmds.push(Command::NamespaceClose(ns));

    // Pretty-print and write the .lean file BEFORE the sanity check.
    // The artifact is always written when codegen produces a command
    // stream, even if sanity rejects — so error messages can name
    // the .lean path for inspection and `cat`-style debugging works
    // regardless of which step fails.
    let rendered = pp_commands(&cmds);
    let source_map = LeanSourceMap::ProofFn {
        fn_name: short_name(&proof_fn.name.path).to_string(),
        // One proof fn per file → exactly one `Tactic::Raw` emission.
        tactic_start_line: rendered.landmarks.tactic_starts.first().copied().unwrap_or(0),
        tactic_line_count: tactic_body.lines().count().max(1),
    };

    let file_path = lean_file_path(crate_name, &proof_fn.name.path);
    if let Err(e) = write_lean_file(&file_path, &rendered.text) {
        return Err(CheckResult::Error(e));
    }

    #[cfg(debug_assertions)]
    let cmds_for_sanity: Vec<Command> = match &defs {
        // Sanity resolves identifiers over the command stream; in defs
        // mode the spec world arrives via import, so check against the
        // concatenation — exactly what Lean sees.
        Some(d) => d.cmds.iter().cloned().chain(cmds.iter().cloned()).collect(),
        None => cmds.clone(),
    };
    #[cfg(not(debug_assertions))]
    let cmds_for_sanity = &cmds;
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

    Ok(EmitOutput { file_path, source_map, warnings: vec![] })
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
    // Build (or fetch) the shared defs module FIRST: `emit_proof_fn`'s
    // internal lookup is a memo hit on whatever this call cached, so
    // the emitted import and the built artifact can't disagree. A
    // build failure caches `None` → standalone emission, today's path.
    let defs = crate::crate_defs::for_crate(krate, crate_name, tactic_bodies, true);
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
    let EmitOutput { file_path, source_map, .. } =
        match emit_proof_fn(krate, proof_fn, tactic_body, imports, crate_name, tactic_bodies) {
            Ok(o) => o,
            Err(cr) => return cr,
        };

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
        Ok(r) if r.success => CheckResult::Success { warnings: vec![] },
        Ok(r) => {
            let fn_short = short_name(&proof_fn.name.path);
            let header = format!("Lean tactic failed for {}", fn_short);
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
            CheckResult::Failed { errors, warnings: vec![] }
        }
        Err(e) => CheckResult::Error(e),
    }
}

/// Codegen-only half of `check_exec_fn`: inline pass → SST→WP theorems →
/// preamble → pretty-print → write `.lean` → sanity check. Stops before the
/// Lean run. `Err(CheckResult)` carries a rejection / write error / sanity
/// failure (each already carrying any collected warnings).
pub fn emit_exec_fn(
    krate: &KrateX,
    vir_fn: &FunctionX,
    fn_sst: &FunctionSst,
    check: &FuncCheckSst,
    imports: &[String],
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> Result<EmitOutput, CheckResult> {
    install_inherent_method_renames(krate);
    install_datatype_field_bounds(krate);
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

    let theorems = match sst_to_lean::exec_fn_theorems_to_ast(krate, fn_sst, check, &broadcast_lemmas) {
        Ok(r) => r,
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

    // Exec fns lower matches to if-chains over `IsVariant` and
    // `Field`, which the SST renderer routes to the synthesised
    // accessor fns — so the preamble must include them. The
    // preamble also aggregates each theorem's `requires_preamble`
    // (e.g., the BitVec instances #130 needs) and emits them once at
    // file top, deduped.
    // Shared-defs mode is incompatible with `broadcast use` — the
    // lemma axioms extend the dep walk per-fn, which a once-per-crate
    // defs build can't anticipate. Such fns emit standalone.
    let defs = if broadcast_lemmas.is_empty() {
        crate::crate_defs::for_crate(pre_inline_krate, crate_name, tactic_bodies, false)
    } else {
        None
    };
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
    cmds.push(Command::NamespaceClose(ns));

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
    if let Err(e) = write_lean_file(&file_path, &rendered.text) {
        return Err(CheckResult::Error(e));
    }

    #[cfg(debug_assertions)]
    let cmds_for_sanity: Vec<Command> = match &defs {
        // Sanity resolves identifiers over the command stream; in defs
        // mode the spec world arrives via import, so check against the
        // concatenation — exactly what Lean sees.
        Some(d) => d.cmds.iter().cloned().chain(cmds.iter().cloned()).collect(),
        None => cmds.clone(),
    };
    #[cfg(not(debug_assertions))]
    let cmds_for_sanity = &cmds;
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

    Ok(EmitOutput { file_path, source_map, warnings })
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
    // Same defs-before-emit ordering as `check_proof_fn` (see there).
    let defs = crate::crate_defs::for_crate(krate, crate_name, tactic_bodies, true);
    let EmitOutput { file_path, source_map, warnings } =
        match emit_exec_fn(krate, vir_fn, fn_sst, check, imports, crate_name, tactic_bodies) {
            Ok(o) => o,
            Err(cr) => return cr,
        };

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
        Ok(r) if r.success => CheckResult::Success { warnings },
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
pub(crate) fn debug_check(_cmds: &[Command]) -> Result<(), String> {
    #[cfg(debug_assertions)]
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

