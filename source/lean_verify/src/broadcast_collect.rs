//! Cross-crate broadcast-lemma collection (#122).
//!
//! Resolves which broadcast lemmas are in scope for a fn — from
//! default-on-import groups and explicit `broadcast use` — and returns
//! the leaf lemma `Fun`s to emit as Lean axioms + inject as
//! `have`-hypotheses. See `collect_broadcast_lemma_funs` for the full
//! resolution rules.

use std::collections::{HashMap, HashSet};

use vir::ast::{CallTarget, ExprX, Fun, FunctionX, KrateX};
use vir::sst::{FuncCheckSst, Stm, StmX};

/// Walk the SST body collecting the target `Fun` of every
/// `StmX::Fuel(f, _)`. `broadcast use G;` lowers (via
/// `ExprX::Fuel(group_fun, _, is_broadcast_use=true)`) to
/// `StmX::Fuel(group_fun, _)`; plain `reveal(f)` also lowers to
/// `StmX::Fuel(f, _)`. We collect both here and let
/// `collect_broadcast_lemma_funs` discriminate group / broadcast-fn /
/// plain-reveal at resolution time.
///
/// Exhaustive `StmX` match (no `_ =>`) mirroring
/// `collect_borrow_mut_links` — a future Verus-side Stm variant
/// carrying nested statements compile-errors here, forcing a decision
/// about whether `broadcast use` can appear inside it.
fn collect_fuel_targets<'a>(stm: &'a Stm, out: &mut Vec<&'a Fun>) {
    match &stm.x {
        StmX::Fuel(f, _) => out.push(f),
        StmX::Block(stmts) => {
            for s in stmts.iter() {
                collect_fuel_targets(s, out);
            }
        }
        StmX::If(_, then_branch, else_branch) => {
            collect_fuel_targets(then_branch, out);
            if let Some(e) = else_branch {
                collect_fuel_targets(e, out);
            }
        }
        StmX::Loop { body, .. } => collect_fuel_targets(body, out),
        StmX::DeadEnd(s) | StmX::OpenInvariant(s) => collect_fuel_targets(s, out),
        StmX::AssertQuery { body, .. } => collect_fuel_targets(body, out),
        StmX::ClosureInner { body, .. } => collect_fuel_targets(body, out),
        // Leaf statements — no nested `Stm`.
        StmX::Call { .. }
        | StmX::Assign { .. }
        | StmX::Assert(_, _, _)
        | StmX::AssertBitVector { .. }
        | StmX::AssertCompute(_, _, _)
        | StmX::Assume(_)
        | StmX::RevealString(_)
        | StmX::Return { .. }
        | StmX::BreakOrContinue { .. }
        | StmX::Air(_) => {}
    }
}

/// Resolve which cross-crate broadcast lemmas are in scope for a fn
/// (#122). Returns the leaf lemma `Fun`s (deduped, source-order-stable)
/// to emit as Lean axioms and inject as `have`-hypotheses. Two sources:
///
/// **(1) Default-on-import groups** — a `pub broadcast group` marked
/// `broadcast_use_by_default_when_this_crate_is_imported(c)` is ambient
/// for every fn of any crate that imports `c` (`crate_name != c`). This
/// is the drop-in case: vstd's `group_vstd_default` makes Seq/Set/Map
/// semantic lemmas available with NO explicit `broadcast use`, matching
/// Verus-Z3.
///
/// **(2) Explicit `broadcast use <group/lemma>;`** in the fn body,
/// lowered to `StmX::Fuel(f, _)`. Covers non-default groups and
/// user-defined broadcast groups.
///
/// Each target (a default-group name or a `StmX::Fuel` target) is then
/// expanded:
/// * a **reveal group** (`f` matches a `RevealGroupX.name`) — expand
///   its `members` recursively (members may be subgroups or leaf fns);
/// * a **broadcast lemma fn** directly (`broadcast use single_lemma;`)
///   — `f` is in `fn_map` with `attrs.broadcast_forall` — include it;
/// * a **plain `reveal(f)`** of an opaque spec fn — `f` is a non-
///   broadcast spec fn — skip (Tactus models spec opacity via
///   `@[irreducible]`, not fuel; not a #122 concern).
///
/// **Scope simplification**: Verus scopes explicit `broadcast use`
/// lexically to the enclosing block, but we treat any `broadcast use`
/// anywhere in the body as fn-scoped (all collected lemmas available to
/// every obligation). Sound — the lemmas are true everywhere — and
/// matches the common top-of-fn usage. Module-level `broadcast use`
/// (`ModuleX.reveals`, distinct from default-on-import) is not yet
/// handled; deferred.
/// Krate-level union: every broadcast lemma in the krate that can be
/// emitted as a Lean axiom — same emit-safety filters as the per-fn
/// collection below (un-emittable trait bounds, BuiltinSpecFun in the
/// require/ensure). The shared-defs module (CRATEDEFS 1c) emits this
/// union so per-fn files can IMPORT the axioms instead of re-emitting
/// them; any per-fn collected set is a subset by construction (it
/// resolves through the same krate fn_map with the same filters).
pub fn all_emittable_broadcast_lemmas<'a>(krate: &'a KrateX) -> Vec<&'a FunctionX> {
    let fn_map: HashMap<&Fun, &FunctionX> =
        krate.functions.iter().map(|f| (&f.x.name, &f.x)).collect();
    let unemittable_traits = crate::expr_shared::unemittable_traits(krate, &fn_map);
    krate.functions.iter().map(|f| &f.x)
        .filter(|func| {
            func.attrs.broadcast_forall
                && !func.typ_bounds.iter().any(|b| match &**b {
                    vir::ast::GenericBoundX::Trait(vir::ast::TraitId::Path(p), _) =>
                        unemittable_traits.contains(p),
                    _ => false,
                })
                && !module_references_builtin_spec_fun(func)
        })
        .collect()
}

/// Module-scope twin of the collector's nested filter (same slots:
/// require + ensure.0).
fn module_references_builtin_spec_fun(func: &FunctionX) -> bool {
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
    for clause in func.require.iter().chain(func.ensure.0.iter()) {
        if found.get() { break; }
        vir::ast_visitor::expr_visitor_walk(clause, &mut visit);
    }
    found.get()
}

pub fn collect_broadcast_lemma_funs<'a>(
    krate: &'a KrateX,
    check: &'a FuncCheckSst,
    crate_name: &str,
) -> Vec<&'a Fun> {
    let group_members: HashMap<&Fun, &Vec<Fun>> = krate
        .reveal_groups
        .iter()
        .map(|g| (&g.x.name, &*g.x.members))
        .collect();
    let fn_map: HashMap<&Fun, &FunctionX> =
        krate.functions.iter().map(|f| (&f.x.name, &f.x)).collect();

    // Traits we can't emit a Lean `class` for: cross-crate traits whose
    // method decls weren't all merged into the function list (Verus's
    // `export_crate` strips them). `trait_to_ast` *panics* on a method
    // not in `method_lookup` ("this is a Tactus bug"). A broadcast
    // lemma with a bound on such a trait (e.g. vstd's
    // `full_set_properties<A: FiniteFull>` in `group_set_lib_default`,
    // pulled in by default-on-import) would render `[FiniteFull A]`,
    // drag `FiniteFull` into emission, and hit that panic. We skip such
    // lemmas at collection so they never reach the dep walk or emission
    // — the lemma's fact is unavailable (graceful: cross-crate Set/laws
    // reasoning isn't supported yet), but the verifier doesn't crash.
    // The clean seq/map/set *axiom* lemmas are unbounded (`<A>`, no
    // trait bound), so they're unaffected.
    let unemittable_traits = crate::expr_shared::unemittable_traits(krate, &fn_map);

    let mut targets: Vec<&Fun> = Vec::new();
    // (1) Default-on-import groups: a `pub broadcast group` marked
    // `broadcast_use_by_default_when_this_crate_is_imported(c)` is
    // ambient for every fn of any crate that imports `c` (Verus's
    // `context.rs` adds the crate→group edge when `crate_name != c`).
    // vstd's `group_vstd_default` (which contains `group_seq_axioms`,
    // `group_map_axioms`, ...) is the canonical case: importing vstd
    // makes the Seq/Set/Map semantic lemmas ambient with NO explicit
    // `broadcast use` — so this is what makes Tactus drop-in for
    // vstd-using spec code (matches Verus-Z3, which also doesn't
    // require an explicit `broadcast use` for these). `merge_krates`
    // prunes the group's transitive members to what the crate actually
    // references, so the leaf set stays small (≈7 seq lemmas for a
    // Seq-only crate, not all of vstd).
    for g in krate.reveal_groups.iter() {
        if let Some(c) = &g.x.broadcast_use_by_default_when_this_crate_is_imported {
            if c.to_string() != crate_name {
                targets.push(&g.x.name);
            }
        }
    }
    // (2) Explicit `broadcast use <group/lemma>;` in the fn body
    // (lowered to `StmX::Fuel`). Covers non-default groups (e.g.
    // `group_seq_lemmas_expensive`) and user-defined broadcast groups.
    collect_fuel_targets(&check.body, &mut targets);

    let mut seen: HashSet<&Fun> = HashSet::new();
    let mut out: Vec<&Fun> = Vec::new();
    // Recursively expand a target into leaf broadcast-lemma funs.
    // Does any require/ensure clause of `func` call a `BuiltinSpecFun`
    // (closure `call_requires` / `call_ensures` etc.)? The VIR-AST
    // renderer emits those as an unresolved literal `builtinSpecFun`
    // (no faithful, fixed-arity Lean form), so a broadcast lemma that
    // mentions one can't be emitted cleanly.
    fn references_builtin_spec_fun(func: &FunctionX) -> bool {
        use std::cell::Cell;
        use vir::visitor::VisitorControlFlow;
        let found = Cell::new(false);
        // Read-only DFS that stops at the first BuiltinSpecFun — no tree
        // clone (unlike `map_expr_visitor`, which rebuilds every node) and
        // short-circuits on first hit. Scans exactly `require` + `ensure.0`,
        // the slots `proof_fn_signature` emits for a broadcast lemma
        // (`ensure.1`, the trait-default ensures, is never rendered).
        let mut visit = |e: &vir::ast::Expr| {
            if let ExprX::Call(CallTarget::BuiltinSpecFun(..), ..) = &e.x {
                found.set(true);
                VisitorControlFlow::Stop(())
            } else {
                VisitorControlFlow::Recurse
            }
        };
        for clause in func.require.iter().chain(func.ensure.0.iter()) {
            if found.get() { break; }
            vir::ast_visitor::expr_visitor_walk(clause, &mut visit);
        }
        found.get()
    }
    fn expand<'a>(
        f: &'a Fun,
        group_members: &HashMap<&'a Fun, &'a Vec<Fun>>,
        fn_map: &HashMap<&'a Fun, &'a FunctionX>,
        unemittable_traits: &HashSet<vir::ast::Path>,
        seen: &mut HashSet<&'a Fun>,
        out: &mut Vec<&'a Fun>,
    ) {
        if !seen.insert(f) {
            return; // already expanded (cycle-safe + dedup)
        }
        if let Some(members) = group_members.get(f) {
            for m in members.iter() {
                expand(m, group_members, fn_map, unemittable_traits, seen, out);
            }
        } else if let Some(func) = fn_map.get(f) {
            // Skip a broadcast lemma whose bound references an
            // un-emittable cross-crate trait (would panic in trait
            // emission — see `unemittable_traits` above).
            let bad_bound = func.typ_bounds.iter().any(|b| match &**b {
                vir::ast::GenericBoundX::Trait(vir::ast::TraitId::Path(p), _) =>
                    unemittable_traits.contains(p),
                _ => false,
            });
            // Also skip a lemma whose require/ensure references a
            // `BuiltinSpecFun` (closure `call_requires`/`call_ensures`):
            // the VIR-AST renderer has no faithful Lean form for it (it's
            // variadic), so it would emit an unresolved `builtinSpecFun`.
            // e.g. vstd's `axiom_fn_mut_call_requires`/`_ensures`, pulled
            // in by default-on-import broadcast but irrelevant to most
            // code. Same graceful-skip family as the un-emittable-trait
            // bound above (#122).
            if func.attrs.broadcast_forall && !bad_bound
                && !references_builtin_spec_fun(func)
            {
                out.push(f);
            }
            // else: plain reveal of a non-broadcast spec fn, or a lemma
            // we can't emit cleanly — skip.
        }
        // else: f neither a known group nor in fn_map (cross-crate
        // group not merged?) — nothing to emit.
    }
    for t in targets {
        expand(t, &group_members, &fn_map, &unemittable_traits, &mut seen, &mut out);
    }
    out
}
