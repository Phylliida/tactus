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
use crate::prelude::TACTUS_PRELUDE;
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
fn lean_out_root() -> PathBuf {
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
) -> (Vec<Command>, String) {
    let emit_accessors = config.emit_accessors();

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
    for imp in imports {
        cmds.push(Command::Import(imp.clone()));
    }
    // Theorem-required Imports go before the prelude — Lean's
    // `import` statements must precede any other commands at file top.
    for frag in &ordered_fragments {
        if let crate::lean_ast::PreambleFragment::Import(s) = frag {
            cmds.push(Command::Import(s.clone()));
        }
    }
    cmds.push(Command::Raw(TACTUS_PRELUDE.to_string()));
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

    let all_fns: Vec<&FunctionX> = krate.functions.iter().map(|f| &f.x).collect();
    let spec_fn_map = dep_order::build_spec_fn_map(&all_fns);
    // `method_lookup` is the all-fn map (spec + proof + exec, no
    // filtering). Shared with `collect_references` so the dep walk
    // can resolve TraitMethodImpl→method redirects and walk into
    // exec-callee specs via the `call_inlining` abstraction.
    let method_lookup: std::collections::HashMap<&Fun, &FunctionX> = all_fns.iter()
        .map(|f| (&f.name, *f))
        .collect();

    // Compute helpers_to_emit: proof fns the root might invoke as
    // lemmas from `proof { have _ := lemma args }` blocks. Skip
    // root_fns themselves (the fn being checked emits as the file's
    // main content), proof fns without a tactic body in
    // `tactic_bodies` (uninterp trait method decls etc.), and
    // `TraitMethodDecl` / `TraitMethodImpl` (those live inside
    // class/instance declarations, not as standalone theorems).
    //
    // These helpers' dep-walk roots feed into the spec-fn dep walk
    // alongside `root_fns`, so any spec fn / datatype / trait the
    // helpers transitively reference also lands in the preamble.
    // See BUG-no-helper-proof-fn-call-from-exec.md.
    let root_fn_set: std::collections::HashSet<&Fun> =
        root_fns.iter().map(|f| &f.name).collect();
    let helpers_to_emit: Vec<&FunctionX> = krate.functions.iter()
        .map(|f| &f.x)
        .filter(|f| matches!(f.mode, vir::ast::Mode::Proof))
        .filter(|f| !root_fn_set.contains(&f.name))
        .filter(|f| !matches!(
            f.kind,
            FunctionKind::TraitMethodDecl { .. } | FunctionKind::TraitMethodImpl { .. }
        ))
        .filter(|f| tactic_bodies.contains_key(&f.name))
        .collect();
    // Extended root set for dep walking: root_fns + helpers. The dep
    // walk will pick up all transitive spec-fn / datatype refs from
    // both, so helpers can be emitted alongside spec fns without
    // unresolved-reference errors.
    let dep_walk_roots: Vec<&FunctionX> = root_fns.iter().copied()
        .chain(helpers_to_emit.iter().copied())
        .collect();

    let mut refs = dep_order::collect_references(&spec_fn_map, &method_lookup, &dep_walk_roots);

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
    let groups = dep_order::order_spec_fns(&spec_fn_map, &method_lookup, &all_fns, &dep_walk_roots);
    let instances_to_emit: Vec<(&TraitImpl, Vec<&FunctionX>)> = krate.trait_impls.iter()
        .filter_map(|ti| {
            let trait_short = short_name(&ti.x.trait_path);
            if !refs.traits.contains(trait_short) { return None; }
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
    // Path → &TraitX lookup for `ImplSubst::build` so it can
    // enumerate each bound trait's assoc types and fill outParam
    // slots that no projection covers. See `impl_subst::ImplSubst::build`
    // for the two-source rationale.
    let trait_lookup: std::collections::HashMap<vir::ast::Path, &vir::ast::TraitX> =
        krate.traits.iter().map(|tr| (tr.x.name.clone(), &tr.x)).collect();

    // Compute per-impl natural-name prefix `[Self, Trait]` for impl
    // method standalone defs. Count duplicates across impls — when
    // two impls produce the same prefix (e.g., `impl Foo<int> for
    // Bar` and `impl Foo<bool> for Bar`), neither gets renamed; both
    // fall back to `impl__N.method`. The natural name flows through
    // `impl_subst::set_method_context` → `augment_function` →
    // `spec_fn_to_ast` so the standalone def's emitted name is
    // `Bar.Foo.method`. Sibling-call rewrites use the same renamed
    // Fun via `method_redirects`. See HANDOFF.md "rename" plan and
    // DESIGN.md "Known UX limitation" for the rationale.
    let impl_name_prefixes: std::collections::HashMap<vir::ast::Path, Vec<vir::ast::Ident>> = {
        use std::collections::HashMap;
        // Naming scheme: `<SelfShortName>.<method>`. We DROP the
        // trait segment from the middle because using the trait
        // name there (e.g., `Wrap.View.view`) creates a namespace
        // conflict — inside `def Wrap.View.view`'s body, Lean
        // searches the def's namespace path first and resolves a
        // bare `View.view` reference to the def itself (recursive
        // self-ref) instead of to the class method. Without the
        // trait segment, `Wrap.view`'s body's `View.view` resolves
        // to the class method as intended.
        //
        // Cost: two trait impls on the same Self with same-named
        // methods (e.g., `Self: Foo` with `Foo::view` AND `Self:
        // Bar` with `Bar::view`) would collide on `Self.view`.
        // Counted below; collisions fall back to `impl__N.method`.
        // Collect each impl method's (Self, method_short) pair to
        // detect collisions across impls.
        let mut per_method: HashMap<(Vec<vir::ast::Ident>, String), usize> = HashMap::new();
        let mut tentative_per_impl: HashMap<vir::ast::Path, Vec<vir::ast::Ident>> = HashMap::new();
        for (ti, method_impls) in &instances_to_emit {
            let Some(self_typ) = ti.x.trait_typ_args.first() else { continue; };
            let Some(self_short) = crate::to_lean_type::type_short_name(self_typ) else { continue; };
            let prefix = vec![std::sync::Arc::new(self_short)];
            for f in method_impls {
                if let Some(method_short) = f.name.path.segments.last().map(|s| s.to_string()) {
                    *per_method.entry((prefix.clone(), method_short)).or_insert(0) += 1;
                }
            }
            tentative_per_impl.insert(ti.x.impl_path.clone(), prefix);
        }
        // Per-impl: only rename when NONE of its method names
        // collide with another impl's (same Self + same method
        // short name).
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
                &trait_lookup,
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
            method_lookup.get(m)
                .map(|f| matches!(f.mode, vir::ast::Mode::Proof))
                .unwrap_or(false)
        })
    };
    for tr in &krate.traits {
        let n = short_name(&tr.x.name);
        if !trait_has_proof_method(&tr.x)
            && (refs.traits.contains(n) || traits_with_emitted_impl.contains(n))
        {
            cmds.push(Command::Class(to_lean_fn::trait_to_ast(&tr.x, &method_lookup, tactic_bodies)));
        }
    }

    // Filter datatypes to those referenced by the proof/exec fns and
    // not synthesized closure types (#93), then transitively close over
    // field-type references and group into SCCs so mutually recursive
    // datatypes (#109) emit as `mutual ... end` blocks.
    let referenced_dts = collect_referenced_datatypes(krate, &refs);
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
        cmds.extend(to_lean_fn::datatype_group_to_cmds(&group, emit_accessors, &external_body_paths));
    }

    // Build fn_map once for the nat-coercion pre-pass (BUG-as-nat-cast.md)
    // applied inside spec_fn_to_ast / trait emission / proof_fn_to_ast.
    let fn_map: crate::sst_to_lean::FnMap =
        krate.functions.iter().map(|f| (&f.x.name, &f.x)).collect();
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
    for group in &groups {
        match group {
            FnGroup::Single(f) => {
                let augmented = crate::impl_subst::maybe_augment_impl_method(f, &impl_substs);
                cmds.push(to_lean_fn::spec_fn_to_ast(&augmented, &fn_map));
            }
            FnGroup::Mutual(fns) => {
                let inner: Vec<Command> = fns.iter()
                    .map(|f| {
                        let augmented = crate::impl_subst::maybe_augment_impl_method(f, &impl_substs);
                        to_lean_fn::spec_fn_to_ast(&augmented, &fn_map)
                    })
                    .collect();
                cmds.push(Command::Mutual(inner));
            }
        }
    }

    // Classes WITH proof-fn methods emit AFTER spec fns (their
    // Prop-typed class fields reference the spec fns in scope).
    for tr in &krate.traits {
        let n = short_name(&tr.x.name);
        if trait_has_proof_method(&tr.x)
            && (refs.traits.contains(n) || traits_with_emitted_impl.contains(n))
        {
            cmds.push(Command::Class(to_lean_fn::trait_to_ast(&tr.x, &method_lookup, tactic_bodies)));
        }
    }

    // Emit the Instance commands chosen above (after spec_fns so
    // standalone defs that instance method bodies might reference
    // are already declared).
    for (ti, method_impls) in &instances_to_emit {
        let assoc_types: Vec<&AssocTypeImplX> = krate.assoc_type_impls.iter()
            .filter(|a| a.x.impl_path == ti.x.impl_path)
            .map(|a| &a.x)
            .collect();
        let empty_subst = crate::impl_subst::ImplSubst::default();
        let subst = impl_substs.get(&ti.x.impl_path).unwrap_or(&empty_subst);
        cmds.push(Command::Instance(
            to_lean_fn::trait_impl_to_ast(&ti.x, method_impls, &assoc_types, tactic_bodies, subst)
        ));
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
    // Ordering: source order works in the common case (user defines
    // helpers before callers). True forward-refs between proof fns
    // would need topological sort; deferred until a case surfaces.
    for f in &helpers_to_emit {
        let tactic_body = tactic_bodies.get(&f.name)
            .expect("helpers_to_emit is built from tactic_bodies — \
                     every entry has a tactic body");
        cmds.push(Command::Theorem(to_lean_fn::proof_fn_to_ast(
            f, tactic_body, &fn_map,
        )));
    }

    (cmds, ns)
}

// ── Check results ──────────────────────────────────────────────────────

#[must_use]
pub enum CheckResult {
    /// Lean verified the proof successfully. `warnings` carries
    /// non-fatal diagnostics — currently used for `assume(P)` site
    /// notifications (each `assume` is a soundness escape hatch
    /// backed by `sorry`).
    Success { warnings: Vec<String> },
    /// Lean rejected the proof. The string is a formatted error
    /// message. `warnings` carries non-fatal diagnostics from the
    /// same crate (assume sites, etc.) that are worth surfacing
    /// even when verification itself fails.
    Failed { error: String, warnings: Vec<String> },
    /// Lean could not be invoked (not installed, project missing, etc.)
    Error(String),
}

// ── Entry points ───────────────────────────────────────────────────────

/// Check a tactic proof fn.
pub fn check_proof_fn(
    krate: &KrateX,
    proof_fn: &FunctionX,
    tactic_body: &str,
    imports: &[String],
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> CheckResult {
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
    );
    // Build fn_map for nat-coercion insertion (BUG-as-nat-cast.md).
    // The pass at fn entry rewrites Call args so Int → Nat parameter
    // mismatches get an explicit `Int.toNat`. Built locally here (vs.
    // threading through krate_preamble) since proof_fn_to_ast is called
    // outside the preamble.
    let fn_map: sst_to_lean::FnMap =
        krate.functions.iter().map(|f| (&f.x.name, &f.x)).collect();
    cmds.push(Command::Theorem(to_lean_fn::proof_fn_to_ast(proof_fn, tactic_body, &fn_map)));
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
        return CheckResult::Error(e);
    }

    if let Err(reason) = debug_check(&cmds) {
        return CheckResult::Failed { error: reason, warnings: vec![] };
    }

    let dir = project::default_project_dir();
    let lake_dir = if project::project_ready(&dir) { Some(dir.as_path()) } else { None };
    let result = lean_process::check_lean_file(&file_path, lake_dir);

    match result {
        Ok(r) if r.success => CheckResult::Success { warnings: vec![] },
        Ok(r) => {
            let errors: Vec<_> = r.diagnostics.iter()
                .filter(|d| d.severity == "error")
                .map(|d| lean_process::format_error(d, &source_map))
                .collect();
            let fn_short = short_name(&proof_fn.name.path);
            CheckResult::Failed {
                error: format!("Lean tactic failed for {}:\n\n{}", fn_short, errors.join("\n")),
                warnings: vec![],
            }
        }
        Err(e) => CheckResult::Error(e),
    }
}

/// Check an exec fn via SST → WP → Lean.
pub fn check_exec_fn(
    krate: &KrateX,
    vir_fn: &FunctionX,
    fn_sst: &FunctionSst,
    check: &FuncCheckSst,
    imports: &[String],
    crate_name: &str,
    tactic_bodies: &std::collections::HashMap<Fun, String>,
) -> CheckResult {
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

    let theorems = match sst_to_lean::exec_fn_theorems_to_ast(krate, fn_sst, check) {
        Ok(r) => r,
        Err(reason) => return CheckResult::Failed {
            error: format!(
                "tactus_auto rejected this fn: {} \
                 (see DESIGN.md \"Known deferrals, rejected cases, and untested edges\" \
                 for the full catalogue of unsupported SST shapes)",
                reason,
            ),
            warnings,
        },
    };

    // Exec fns lower matches to if-chains over `IsVariant` and
    // `Field`, which the SST renderer routes to the synthesised
    // accessor fns — so the preamble must include them. The
    // preamble also aggregates each theorem's `requires_preamble`
    // (e.g., the BitVec instances #130 needs) and emits them once at
    // file top, deduped.
    let (mut cmds, ns) = krate_preamble(
        krate, imports, crate_name, &[vir_fn],
        PreambleConfig::ExecFn,
        &theorems,
        tactic_bodies,
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

    let file_path = lean_file_path(crate_name, &vir_fn.name.path);
    if let Err(e) = write_lean_file(&file_path, &rendered.text) {
        return CheckResult::Error(e);
    }

    if let Err(reason) = debug_check(&cmds) {
        return CheckResult::Failed { error: reason, warnings };
    }

    let dir = project::default_project_dir();
    let lake_dir = if project::project_ready(&dir) { Some(dir.as_path()) } else { None };
    let result = lean_process::check_lean_file(&file_path, lake_dir);

    // Exec fns map errors via `span_marks` populated by the pp's
    // `SpanMark` walker (#51 source mapping) — Rust source
    // location for each obligation emitted by `walk_obligations`.
    let source_map = LeanSourceMap::ExecFn {
        fn_name: short_name(&vir_fn.name.path).to_string(),
        span_marks: rendered.landmarks.span_marks.clone(),
    };

    match result {
        Ok(r) if r.success => CheckResult::Success { warnings },
        Ok(r) => {
            let errors: Vec<_> = r.diagnostics.iter()
                .filter(|d| d.severity == "error")
                .map(|d| lean_process::format_error(d, &source_map))
                .collect();
            CheckResult::Failed {
                error: format!(
                    "Lean tactus_auto failed for {}:\n\n{}\n\n\
                     (generated .lean file: {})",
                    short_name(&vir_fn.name.path),
                    errors.join("\n"),
                    file_path.display(),
                ),
                warnings,
            }
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
        .filter(|p| refs.datatypes.contains(short_name(p)))
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
fn debug_check(_cmds: &[Command]) -> Result<(), String> {
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
mod tests {
    use super::*;
    use crate::lean_ast::{Expr as LExpr, PreambleFragment, Tactic, Theorem};
    use crate::test_fixtures::empty_krate;

    /// Build a stub Theorem with the given preamble fragments.
    /// Other fields take placeholder values — these tests are only
    /// about how `krate_preamble` aggregates fragments, not about
    /// theorem content.
    fn stub_theorem(name: &str, requires_preamble: Vec<PreambleFragment>) -> Theorem {
        Theorem {
            name: name.to_string(),
            binders: Vec::new(),
            goal: LExpr::lit_bool(true),
            tactic: Tactic::Named("tactus_auto".to_string()),
            requires_preamble,
            heartbeats: None,
            termination_by: Vec::new(),
        }
    }

    /// Right-way #4: with no theorems, no per-fn preamble fragments
    /// are emitted. The default Tactus preamble is still present
    /// (TACTUS_PRELUDE) but no extra Imports / PreludeAddendums leak
    /// in. Pins the "files that don't request anything pay nothing"
    /// contract.
    #[test]
    fn krate_preamble_with_no_theorems_emits_no_extra_fragments() {
        let krate = empty_krate();
        let (cmds, _ns) = krate_preamble(
            &krate, &[], "test_crate", &[], PreambleConfig::ProofFn, &[],
            &std::collections::HashMap::new(),
        );

        // The default preamble has exactly one Import-class chunk
        // (the `imports` parameter, here empty) and one Raw block
        // (TACTUS_PRELUDE). No extra Imports or Raws should appear
        // before the Namespace open from per-fn aggregation.
        let import_count = cmds.iter()
            .filter(|c| matches!(c, Command::Import(_)))
            .count();
        assert_eq!(import_count, 0,
            "no theorems → no aggregated imports; got cmds: {:?}",
            cmds.iter().map(|c| std::mem::discriminant(c)).collect::<Vec<_>>());

        // No Raw command should contain bitvec instance definitions
        // (substring check on `instance : HXor` skips comments in
        // the prelude that mention the type name — only executable
        // instance lines would matter).
        let bitvec_raw_count = cmds.iter()
            .filter_map(|c| if let Command::Raw(s) = c { Some(s) } else { None })
            .filter(|s| s.contains("instance : HXor Int Int Int"))
            .count();
        assert_eq!(bitvec_raw_count, 0,
            "no theorems → no aggregated PreludeAddendums");
    }

    /// Right-way #4: a theorem requesting an Import fragment causes
    /// `krate_preamble` to emit that Import (in the import section,
    /// before TACTUS_PRELUDE).
    #[test]
    fn krate_preamble_aggregates_import_fragments_from_theorems() {
        let krate = empty_krate();
        let theorems = vec![stub_theorem(
            "test_thm",
            vec![PreambleFragment::Import("Mathlib.Tactic.Polyrith".to_string())],
        )];
        let (cmds, _ns) = krate_preamble(
            &krate, &[], "test_crate", &[], PreambleConfig::ExecFn, &theorems,
            &std::collections::HashMap::new(),
        );

        let imports: Vec<&str> = cmds.iter()
            .filter_map(|c| if let Command::Import(s) = c { Some(s.as_str()) } else { None })
            .collect();
        assert!(imports.contains(&"Mathlib.Tactic.Polyrith"),
            "theorem-required Import should appear in preamble; got: {:?}", imports);

        // Sanity check: the Import appears BEFORE the prelude (Lean
        // requires all imports at file top).
        let import_idx = cmds.iter().position(|c| matches!(c, Command::Import(s) if s == "Mathlib.Tactic.Polyrith"));
        let prelude_idx = cmds.iter().position(|c| matches!(c, Command::Raw(s) if s.contains("set_option")));
        assert!(import_idx < prelude_idx,
            "imports must come before TACTUS_PRELUDE");
    }

    /// Right-way #4: a theorem requesting a PreludeAddendum fragment
    /// causes `krate_preamble` to emit that Raw block AFTER the
    /// prelude (instances typically depend on the prelude's defs).
    #[test]
    fn krate_preamble_aggregates_prelude_addendums_after_prelude() {
        let krate = empty_krate();
        let addendum = "instance : MyClass Foo := ⟨...⟩\n";
        let theorems = vec![stub_theorem(
            "test_thm",
            vec![PreambleFragment::PreludeAddendum(addendum.to_string())],
        )];
        let (cmds, _ns) = krate_preamble(
            &krate, &[], "test_crate", &[], PreambleConfig::ExecFn, &theorems,
            &std::collections::HashMap::new(),
        );

        // Find the addendum Raw and confirm it's AFTER the prelude Raw.
        let addendum_idx = cmds.iter().position(|c|
            matches!(c, Command::Raw(s) if s.contains("MyClass Foo")));
        let prelude_idx = cmds.iter().position(|c|
            matches!(c, Command::Raw(s) if s.contains("set_option")));
        assert!(addendum_idx.is_some(), "addendum should appear");
        assert!(addendum_idx > prelude_idx,
            "PreludeAddendums must come after TACTUS_PRELUDE");
    }

    /// Right-way #4: when multiple theorems request the same fragment,
    /// `krate_preamble` emits it once (dedup). Important because the
    /// common case is N exec-fn theorems all needing the same BitVec
    /// preamble.
    #[test]
    fn krate_preamble_dedups_repeated_fragments() {
        let krate = empty_krate();
        let frag = PreambleFragment::Import("Mathlib.Data.BitVec".to_string());
        let theorems = vec![
            stub_theorem("thm1", vec![frag.clone()]),
            stub_theorem("thm2", vec![frag.clone()]),
            stub_theorem("thm3", vec![frag.clone()]),
        ];
        let (cmds, _ns) = krate_preamble(
            &krate, &[], "test_crate", &[], PreambleConfig::ExecFn, &theorems,
            &std::collections::HashMap::new(),
        );

        let bitvec_imports: Vec<&str> = cmds.iter()
            .filter_map(|c| if let Command::Import(s) = c { Some(s.as_str()) } else { None })
            .filter(|s| *s == "Mathlib.Data.BitVec")
            .collect();
        assert_eq!(bitvec_imports.len(), 1,
            "duplicate fragments should emit once; got {} copies", bitvec_imports.len());
    }

    /// REVIEW lens 4/1: shape-drift guard for the `anonymous_closure`
    /// path prefix used by Verus to name synthesized closure types.
    /// `collect_referenced_datatypes` filters these out via
    /// `short.starts_with("anonymous_closure")` because:
    ///
    /// * `Wp::LetRaw` binds the closure as a first-class Lean lambda
    ///   (#93 slice B), not as an inductive datatype.
    /// * The synthesized closure datatypes have zero variants — Lean's
    ///   `deriving Inhabited` rejects zero-variant inductives.
    ///
    /// If Verus changes the prefix (e.g., to `closure_anon%` or some
    /// other shape), our filter silently misses, the synthesized
    /// types reach `datatype_to_cmds`, and Lean elaboration fails on
    /// the `deriving Inhabited` synthesis. The error surface (via
    /// e2e) would be obscure — this test points at the fix site
    /// directly.
    ///
    /// Verus exposes `vir::def::prefix_closure_type(i)` which we use
    /// as the canonical source of truth.
    #[test]
    fn anonymous_closure_prefix_pinned() {
        let path = vir::def::prefix_closure_type(0);
        let segment = path.segments[0].as_str();
        assert!(
            segment.starts_with("anonymous_closure"),
            "Verus closure-type prefix drift detected. Tactus's \
             `collect_referenced_datatypes` filter (in generate.rs) \
             expects synthesized closure paths to start with \
             `anonymous_closure`; Verus is now producing `{}`. \
             Update the filter substring to match.",
            segment,
        );
    }
}

