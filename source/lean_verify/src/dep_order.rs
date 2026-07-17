//! Dependency analysis and topological ordering for Lean output.
//!
//! Given a set of VIR functions and a "root" proof fn, this module:
//! 1. Collects all referenced entities (spec fns, datatypes, traits)
//! 2. Topologically sorts spec fns (callees before callers)
//! 3. Groups mutually recursive functions into `mutual ... end` blocks
//!
//! Uses a lifetime-preserving expression walker (`walk_expr`) instead of
//! VIR's `expr_visitor_walk`, so all references borrow from the krate — no
//! Arc clones or String allocations.

use std::collections::{HashMap, HashSet};
use vir::ast::*;
use crate::to_lean_type::{short_name, walk_typ};

/// A group of functions that should be emitted together.
pub enum FnGroup<'a> {
    Single(&'a FunctionX),
    Mutual(Vec<&'a FunctionX>),
}

/// A group of datatypes that should be emitted together.
///
/// `Mutual(group)` for SCCs with size > 1 — the inductives reference
/// each other, so Lean requires a `mutual ... end` block for both
/// the type declarations and the height fns. `Single(dt)` for
/// non-mutual datatypes (the common case, including self-recursive
/// types — those handle recursion structurally without needing a
/// `mutual` block).
pub enum DatatypeGroup<'a> {
    Single(&'a DatatypeX),
    Mutual(Vec<&'a DatatypeX>),
}

/// All entity names referenced by the proof fns (transitively through spec fns).
/// Borrows `&str` from VIR's `Arc<String>` — zero allocations.
pub struct References<'a> {
    pub datatypes: HashSet<&'a str>,
    pub traits: HashSet<&'a str>,
}

/// Collect all referenced datatype/trait names from proof fns and their
/// transitive spec fn dependencies.
///
/// `all_fn_map` covers spec, proof, and exec fns alike — used to
/// walk into exec/proof callees' inlined specs (the clauses the
/// emission path will substitute in via `walk_call`). Without that
/// walk, the dep walk would miss spec-fn references that appear
/// only inside an exec callee's `ensures` — see the 2026-05-12
/// "predicate is unresolved" regression. The shared abstraction in
/// `call_inlining::collect_inlined_at_call` defines what counts as
/// "inlined."
pub fn collect_references<'a>(
    spec_fn_map: &HashMap<&Fun, &'a FunctionX>,
    all_fn_map: &HashMap<&Fun, &'a FunctionX>,
    all_fns: &[&'a FunctionX],
    proof_fns: &[&'a FunctionX],
) -> References<'a> {
    let mut refs = References { datatypes: HashSet::new(), traits: HashSet::new() };

    for pf in proof_fns {
        collect_from_fn(pf, &mut refs);
    }

    let mut visited: HashSet<&Fun> = HashSet::new();
    let mut worklist: Vec<&'a Fun> = Vec::new();
    seed_worklist(proof_fns, &mut worklist);
    seed_impl_proof_method_bodies(all_fns, all_fn_map, &mut worklist);
    while let Some(fun) = worklist.pop() {
        if visited.contains(fun) { continue; }
        visited.insert(fun);
        if let Some(f) = spec_fn_map.get(fun) {
            // Spec fn: body gets transparently unfolded at call sites,
            // so walk its body + decreases + signature.
            collect_from_fn(f, &mut refs);
            if let Some(body) = &f.body { collect_fun_refs(body, &mut worklist); }
            for d in f.decrease.iter() { collect_fun_refs(d, &mut worklist); }
        } else if let Some(f) = all_fn_map.get(fun) {
            // Exec/proof callee (also: body-less spec fns and
            // TraitMethodDecls — both excluded from spec_fn_map but
            // present in all_fn_map). Their `require` + `ensure`
            // clauses get inlined at call sites by `walk_call`, so
            // refs in those clauses must land in the preamble.
            // Body NOT walked — it's not inlined, only the specs are.
            collect_from_fn(f, &mut refs);
            let spec_callee = crate::call_inlining::spec_source(f, all_fn_map)
                .unwrap_or(f);
            let inlined = crate::call_inlining::collect_inlined_at_call(f, spec_callee);
            for clause in inlined.requires.iter().chain(inlined.ensures.iter()) {
                collect_fun_refs(clause, &mut worklist);
            }
            // TraitMethodDecl with a default body: the body becomes
            // a class default, which Lean inlines via typeclass
            // dispatch. Refs inside the default body need the same
            // treatment as spec-fn bodies — they're effectively
            // inlined at use sites. Without this walk, a default
            // body referencing another trait spec method (Case A
            // from the design discussion) would leave that ref
            // unresolved in the class declaration.
            if matches!(f.kind, FunctionKind::TraitMethodDecl { has_default: true, .. }) {
                if let Some(body) = &f.body {
                    collect_fun_refs(body, &mut worklist);
                }
            }
        }
    }

    refs
}

/// Collect datatype/trait references from a function's types and expressions.
fn collect_from_fn<'a>(f: &'a FunctionX, refs: &mut References<'a>) {
    for bound in f.typ_bounds.iter() {
        match &**bound {
            GenericBoundX::Trait(TraitId::Path(path), _) => {
                refs.traits.insert(short_name(path));
            }
            GenericBoundX::TypEquality(path, _, _, _) => {
                refs.traits.insert(short_name(path));
            }
            _ => {}
        }
    }

    let mut collect_dt = |typ: &'a TypX| {
        if let TypX::Datatype(Dt::Path(path), _, _) = typ {
            refs.datatypes.insert(short_name(path));
        }
    };
    for p in f.params.iter() { walk_typ(&p.x.typ, &mut collect_dt); }
    walk_typ(&f.ret.x.typ, &mut collect_dt);

    let mut scan_expr = |expr: &'a Expr| {
        walk_expr(expr, &mut |e| {
            walk_typ(&e.typ, &mut |typ| {
                if let TypX::Datatype(Dt::Path(path), _, _) = typ {
                    refs.datatypes.insert(short_name(path));
                }
            });
            match &e.x {
                ExprX::Ctor(Dt::Path(path), _, _, _) => {
                    refs.datatypes.insert(short_name(path));
                }
                ExprX::Call(CallTarget::Fun(CallTargetKind::Dynamic, fun, _, _, _, _), _, _) => {
                    let segs = &fun.path.segments;
                    if segs.len() >= 2 { refs.traits.insert(segs[segs.len() - 2].as_str()); }
                }
                _ => {}
            }
        });
    };
    for r in f.require.iter() { scan_expr(r); }
    for e in f.ensure.0.iter() { scan_expr(e); }
    if let Some(body) = &f.body { scan_expr(body); }
}

/// Build the spec fn lookup map (shared between collect_references and order_spec_fns).
///
/// Includes body=None spec fns (uninterp / external_body / cross-crate-stripped).
/// They're emitted as `Command::Axiom` rather than `Command::Def` by
/// `to_lean_fn::spec_fn_to_ast` — their bodies don't need walking
/// (collect_references / order_spec_fns gate body iteration on
/// `f.body.is_some()` themselves), but skipping them here would drop
/// the name from the preamble entirely and produce an "unresolved"
/// sanity-check rejection at the call site.
///
/// Excludes `FunctionKind::TraitMethodDecl`: those live inside the
/// `class` declaration produced by `trait_to_ast`, not as standalone
/// top-level defs. The pre-2026-05-12 `body.is_some()` filter
/// excluded them as a side effect (trait method decls without default
/// bodies are body=None). With body-less emission, we make the
/// exclusion explicit on the structural property (`FunctionKind`)
/// rather than via the implicit body-presence proxy. A trait method
/// decl with `has_default: true` (body=Some) is also excluded — its
/// default body is emitted separately via Verus's
/// `<trait>%default%<method>` wrapper, a `Static` fn that DOES pass.
pub fn build_spec_fn_map<'a>(all_fns: &'a [&'a FunctionX]) -> HashMap<&'a Fun, &'a FunctionX> {
    all_fns.iter()
        .filter(|f| matches!(f.mode, Mode::Spec))
        .filter(|f| !matches!(f.kind, FunctionKind::TraitMethodDecl { .. }))
        .map(|f| (&f.name, *f))
        .collect()
}

/// Given spec fn map and proof fns, return spec fns in dependency order.
///
/// `all_fn_map` provides the same exec/proof-callee-spec-walking that
/// `collect_references` does: when an exec/proof callee is reached
/// via the worklist, its inlined `require`/`ensure` clauses (per the
/// shared `call_inlining::collect_inlined_at_call` abstraction) are
/// scanned for spec-fn refs. Without this, spec fns referenced only
/// inside an exec callee's specs would never enter `needed`, their
/// standalone defs would never emit, and the rendered theorem would
/// have unresolved references at the call site.
pub fn order_spec_fns<'a>(
    spec_fn_map: &HashMap<&Fun, &'a FunctionX>,
    all_fn_map: &HashMap<&Fun, &'a FunctionX>,
    all_fns: &'a [&'a FunctionX],
    proof_fns: &[&'a FunctionX],
) -> Vec<FnGroup<'a>> {
    let mut needed: HashSet<&Fun> = HashSet::new();
    // Edge lists are Vec (insertion order = deterministic AST-walk
    // order), NOT HashSet: Tarjan's DFS follows neighbor order, and
    // hash-set iteration order varies per process (RandomState), which
    // shuffled SCC output — and with it emitted defs order — across
    // otherwise-identical runs.
    let mut edges: HashMap<&'a Fun, Vec<&'a Fun>> = HashMap::new();
    let mut worklist: Vec<&'a Fun> = Vec::new();

    seed_worklist(proof_fns, &mut worklist);
    seed_impl_proof_method_bodies(all_fns, all_fn_map, &mut worklist);

    while let Some(fun) = worklist.pop() {
        if needed.contains(fun) { continue; }
        needed.insert(fun);

        if let Some(f) = spec_fn_map.get(fun) {
            // Spec fn: body and decreases get walked for transitive refs.
            let mut callees = Vec::new();
            if let Some(body) = &f.body { collect_fun_refs(body, &mut callees); }
            for d in f.decrease.iter() { collect_fun_refs(d, &mut callees); }

            for c in &callees {
                if !needed.contains(c) { worklist.push(c); }
            }
            // Dedup preserving first-occurrence order (the HashSet this
            // replaced deduped too, but with unstable iteration order).
            let mut seen_callees: HashSet<&Fun> = HashSet::new();
            edges.insert(fun, callees.into_iter()
                .filter(|c| spec_fn_map.contains_key(c) && seen_callees.insert(*c))
                .collect());
        } else if let Some(f) = all_fn_map.get(fun) {
            // Exec/proof callee: walk inlined require/ensure clauses
            // for spec-fn refs. Mirrors `collect_references`'s branch;
            // both go through `call_inlining::collect_inlined_at_call`
            // so emission and ordering can't drift.
            let spec_callee = crate::call_inlining::spec_source(f, all_fn_map)
                .unwrap_or(f);
            let inlined = crate::call_inlining::collect_inlined_at_call(f, spec_callee);
            for clause in inlined.requires.iter().chain(inlined.ensures.iter()) {
                collect_fun_refs(clause, &mut worklist);
            }
            // TraitMethodDecl with default body: walk it so refs in
            // the class default land in `needed`. Mirrors the
            // identical branch in `collect_references`.
            if matches!(f.kind, FunctionKind::TraitMethodDecl { has_default: true, .. }) {
                if let Some(body) = &f.body {
                    collect_fun_refs(body, &mut worklist);
                }
            }
        }
    }

    // Include body=None spec fns: they emit as `Command::Axiom` from
    // `to_lean_fn::spec_fn_to_ast`. Filtering them here would drop the
    // declaration entirely and downstream references would fail the
    // sanity check.
    //
    // Exclude `TraitMethodDecl` (see `build_spec_fn_map` rationale).
    // `needed_fns` is built from `all_fns` directly (not via
    // `spec_fn_map`), so the map-side filter doesn't propagate here;
    // we re-apply the structural exclusion.
    let needed_fns: Vec<&'a FunctionX> = all_fns.iter()
        .filter(|f| needed.contains(&f.name)
            && matches!(f.mode, Mode::Spec)
            && !matches!(f.kind, FunctionKind::TraitMethodDecl { .. }))
        .copied()
        .collect();

    let sccs = tarjan_scc(&needed_fns, &edges);

    let fn_lookup: HashMap<&Fun, &'a FunctionX> = needed_fns.iter()
        .map(|f| (&f.name, *f))
        .collect();

    sccs.into_iter().map(|scc| {
        if scc.len() == 1 {
            FnGroup::Single(fn_lookup[scc[0]])
        } else {
            FnGroup::Mutual(scc.iter().map(|name| fn_lookup[name]).collect())
        }
    }).collect()
}

/// One node in the emission order: a spec-fn `Group` (index into the
/// caller's `groups`) or a trait `Instance` (index into the caller's
/// instance list). Returning indices avoids cloning `FnGroup`.
pub enum EmitStep {
    Group(usize),
    Instance(usize),
}

/// Topologically order spec-fn groups together with trait instances, so
/// the spec-fn↔instance dependency DAG is respected in one pass:
///
/// * a spec-fn BODY that dispatches to an instance (e.g.
///   `hash_map_deep_view_impl`'s `m@` → `View (HashMap …)`) must follow
///   that instance — Lean instance resolution only sees earlier decls;
/// * an instance whose body references a spec-fn def (or dispatches to
///   another instance) must follow it.
///
/// Build the dependency graph, then Kahn's algorithm with an
/// original-position tiebreak: among ready nodes, emit the lowest id,
/// where groups own ids `0..n` (their `order_spec_fns` order) and
/// instances own `n..n+m`. So groups stay in their existing order and an
/// instance only moves out of the trailing position when an edge forces
/// it — zero drift for instances nothing dispatches to. The group-order
/// chain (`i` after `i-1`) pins the spec-fn sequence `order_spec_fns`
/// already validated; instances slot into the gaps the edges open.
///
/// `instances[j] = (impl_path, method_impl_fns)`, index-aligned with the
/// caller's instance list.
pub fn order_emission<'a>(
    groups: &[FnGroup<'a>],
    instances: &[(&'a Path, Vec<&'a FunctionX>)],
) -> Vec<EmitStep> {
    let n = groups.len();
    let m = instances.len();
    let total = n + m;

    // fn -> its group node; impl_path -> its instance node.
    let mut fn_node: HashMap<&Fun, usize> = HashMap::new();
    for (i, g) in groups.iter().enumerate() {
        match g {
            FnGroup::Single(f) => { fn_node.insert(&f.name, i); }
            FnGroup::Mutual(fs) => { for f in fs { fn_node.insert(&f.name, i); } }
        }
    }
    let mut impl_node: HashMap<&Path, usize> = HashMap::new();
    for (j, (ip, _)) in instances.iter().enumerate() {
        impl_node.insert(*ip, n + j);
    }

    // A trait-method call (`Dynamic` / `DynamicResolved`) carries, in the
    // `CallTarget::Fun` *call's* `ImplPaths` (4th field — the dispatch
    // "dictionary"), the impl it resolves through. Map those whose impl is
    // an emitted instance to that instance node. (NB: the separate
    // `DynamicResolved.impl_paths` field is the resolved fn's own bound
    // dictionary and is typically empty here — the call-level field is the
    // one naming the receiver's instance.)
    let dispatched_instances = |f: &'a FunctionX, out: &mut HashSet<usize>| {
        if let Some(body) = &f.body {
            walk_expr(body, &mut |e| {
                if let ExprX::Call(CallTarget::Fun(kind, _, _, impl_paths, _, _), _, _) = &e.x {
                    if matches!(kind,
                        CallTargetKind::Dynamic | CallTargetKind::DynamicResolved { .. })
                    {
                        for ip in impl_paths.iter() {
                            if let ImplPath::TraitImplPath(p) = ip {
                                if let Some(&node) = impl_node.get(p) { out.insert(node); }
                            }
                        }
                    }
                }
            });
        }
    };

    // prereqs[a] = nodes that must be emitted before a.
    let mut prereqs: Vec<HashSet<usize>> = vec![HashSet::new(); total];

    // Pin the spec-fn group sequence.
    for i in 1..n { prereqs[i].insert(i - 1); }

    // A group follows every instance it dispatches to.
    for (i, g) in groups.iter().enumerate() {
        match g {
            FnGroup::Single(f) => dispatched_instances(f, &mut prereqs[i]),
            FnGroup::Mutual(fs) => { for f in fs { dispatched_instances(f, &mut prereqs[i]); } }
        }
    }

    // An instance follows its method-def groups (its emitted body calls
    // the standalone defs + whatever those reference) and any instance
    // it dispatches to.
    for (j, (_, methods)) in instances.iter().enumerate() {
        let inst = n + j;
        for mth in methods {
            if let Some(&g) = fn_node.get(&mth.name) { prereqs[inst].insert(g); }
            if let Some(body) = &mth.body {
                let mut refs = Vec::new();
                collect_fun_refs(body, &mut refs);
                for r in &refs {
                    if let Some(&g) = fn_node.get(r) { prereqs[inst].insert(g); }
                }
            }
            dispatched_instances(mth, &mut prereqs[inst]);
        }
        prereqs[inst].remove(&inst); // never self-depend
    }

    kahn_emit(prereqs, n)
}

/// Kahn's topological sort over a node graph where node ids `0..n_groups`
/// are spec-fn groups and `n_groups..` are instances. `prereqs[a]` is the
/// set of nodes that must precede `a`. Ready nodes are emitted
/// lowest-id-first (the original-position tiebreak), so groups keep their
/// order and instances stay trailing unless an edge pulls them earlier.
/// Cycle remnants (no well-formed krate produces them) are appended in id
/// order so nothing is silently dropped. Pure over the graph — unit-tested
/// directly without fabricating `FunctionX`.
fn kahn_emit(prereqs: Vec<HashSet<usize>>, n_groups: usize) -> Vec<EmitStep> {
    let total = prereqs.len();
    let mut indeg: Vec<usize> = prereqs.iter().map(|p| p.len()).collect();
    let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); total];
    for (a, ps) in prereqs.iter().enumerate() {
        for &p in ps { dependents[p].push(a); }
    }
    let mut emitted = vec![false; total];
    let mut result = Vec::with_capacity(total);
    let step = |v: usize| if v < n_groups { EmitStep::Group(v) } else { EmitStep::Instance(v - n_groups) };
    for _ in 0..total {
        match (0..total).find(|&x| !emitted[x] && indeg[x] == 0) {
            Some(v) => {
                emitted[v] = true;
                result.push(step(v));
                for &d in &dependents[v] { indeg[d] -= 1; }
            }
            None => break, // cycle (shouldn't happen for well-formed krates)
        }
    }
    // Append any cycle remnants in id order so nothing is silently dropped.
    for v in 0..total {
        if !emitted[v] { result.push(step(v)); }
    }
    result
}

/// Seed a worklist from proof fn requires/ensures.
fn seed_worklist<'a>(proof_fns: &[&'a FunctionX], worklist: &mut Vec<&'a Fun>) {
    for pf in proof_fns {
        for e in pf.require.iter() { collect_fun_refs(e, worklist); }
        for e in pf.ensure.0.iter() { collect_fun_refs(e, worklist); }
        for e in pf.ensure.1.iter() { collect_fun_refs(e, worklist); }
        // Body-level spec fn calls (e.g., inside `assert(spec_fn(x) == ...)`
        // in an exec fn body, or via Verus's pre-injected `Assume(ens)`
        // before `StmX::AssertBitVector`) need to be added to the
        // worklist too. Without this, the spec fn def never lands in
        // the preamble and the sanity check panics with "unresolved"
        // (#147). For exec fns this matters because most spec fn
        // references live in body assertions; for proof fns the body
        // is a tactic block (text) so collect_fun_refs naturally finds
        // nothing there.
        if let Some(body) = &pf.body { collect_fun_refs(body, worklist); }
    }
}

/// Seed the worklist with references from impl proof-fn methods'
/// ensures + bodies. For these, Tactus's `trait_impl_to_ast` renders
/// content that may reference spec methods (the impl's own siblings,
/// or trait-method calls in ensures), and those references must be
/// in scope as standalone defs at instance-emission time.
///
/// Two reference paths matter:
/// 1. **Ensures (always walked).** The proof fn's ensures appears
///    inside the class field's type AND, via Verus's
///    auto-postcondition checking, in proof obligations that need
///    the referenced spec fns visible. Example: `proof fn val_nonneg
///    ensures self.val() >= 0` — `val` must emit so the user's
///    tactic body `simp [val]` resolves.
/// 2. **Body (only for non-unit return).** For non-unit-return
///    proof fns, the impl's body is the witness expression in the
///    instance's subtype value `⟨body, proof⟩`. Body references
///    (e.g., `self.target()` calling sibling spec method) need
///    standalone defs in scope.
///
/// Pre-seeded unconditionally — we don't try to predict which trait
/// impls will emit (that decision happens later in `generate.rs`).
/// Over-emitting spec fn defs is harmless: they're inert dead code
/// in the preamble if nothing else references them.
fn seed_impl_proof_method_bodies<'a>(
    all_fns: &[&'a FunctionX],
    all_fn_map: &HashMap<&Fun, &'a FunctionX>,
    worklist: &mut Vec<&'a Fun>,
) {
    // Iterate the slice, not `all_fn_map`: map iteration order varies
    // per process and would leak into worklist order. (Downstream
    // consumers re-order deterministically today, but a deterministic
    // seed keeps that from being load-bearing.)
    let _ = all_fn_map;
    for f in all_fns {
        if !matches!(f.kind, FunctionKind::TraitMethodImpl { .. }) { continue; }
        if !matches!(f.mode, Mode::Proof) { continue; }
        // Always walk ensures — these reach into the class field
        // type AND into the tactic body's auto-postcondition scope.
        for e in f.ensure.0.iter() { collect_fun_refs(e, worklist); }
        for e in f.ensure.1.iter() { collect_fun_refs(e, worklist); }
        // Body only for non-unit return — that's where the body
        // becomes the witness. Shared with `to_lean_fn`'s emission
        // dispatch via `is_unit_typ` so the two stay aligned.
        if !crate::to_lean_type::is_unit_typ(&f.ret.x.typ) {
            if let Some(body) = &f.body {
                collect_fun_refs(body, worklist);
            }
        }
    }
}

/// Order datatypes for emission, grouping mutually-recursive SCCs.
///
/// For each datatype in `referenced_datatypes` (subset of `krate.datatypes`
/// the proof/exec fns transitively touch), build a graph where A → B if
/// A's variants have a field whose peeled type is `Datatype(B, …)`. Run
/// Tarjan's SCC. Returns a topologically-ordered list of groups — Single
/// for self-contained datatypes (including self-recursive ones, which
/// don't need a `mutual` block), Mutual for SCCs of size > 1.
///
/// Used by `generate.rs` to wrap mutually-recursive datatype declarations
/// (and their height fns) in Lean `mutual ... end` blocks (#109).
pub fn order_datatypes<'a>(
    referenced_datatypes: &[&'a DatatypeX],
) -> Vec<DatatypeGroup<'a>> {
    // Build a path → DatatypeX lookup. Filter Dt::Tuple — they don't
    // have declarations to emit; references to them in field types
    // are skipped during edge collection. Keys are `&Path` (= `&Arc<PathX>`)
    // so PartialEq/Hash delegate to PathX content.
    let dt_by_path: HashMap<&'a Path, &'a DatatypeX> = referenced_datatypes
        .iter()
        .filter_map(|dt| match &dt.name {
            Dt::Path(p) => Some((p, *dt)),
            Dt::Tuple(_) => None,
        })
        .collect();

    // Build edges: A → B for every B referenced in A's field types
    // (including self). Edge lists are Vec in deterministic walk order,
    // deduped via a side set — Tarjan follows neighbor order, and
    // hash-set iteration order varies per process (see the fn-graph
    // twin above).
    let mut edges: HashMap<&'a Path, Vec<&'a Path>> = HashMap::new();
    for dt in referenced_datatypes.iter() {
        let a_path = match &dt.name {
            Dt::Path(p) => p,
            Dt::Tuple(_) => continue,
        };
        let mut deps: Vec<&'a Path> = Vec::new();
        let mut seen: HashSet<&'a Path> = HashSet::new();
        for variant in dt.variants.iter() {
            for field in variant.fields.iter() {
                walk_typ_paths(&field.a.0, &mut |p: &'a Path| {
                    if dt_by_path.contains_key(p) && seen.insert(p) {
                        deps.push(p);
                    }
                });
            }
        }
        edges.insert(a_path, deps);
    }

    // Order datatypes deterministically by their position in the input.
    // Tarjan's output preserves processing order, so this gives stable
    // output across runs.
    let ordered_paths: Vec<&'a Path> = referenced_datatypes
        .iter()
        .filter_map(|dt| match &dt.name {
            Dt::Path(p) => Some(p),
            Dt::Tuple(_) => None,
        })
        .collect();

    let sccs = tarjan_scc_path(&ordered_paths, &edges);

    sccs.into_iter().map(|scc| {
        if scc.len() == 1 {
            DatatypeGroup::Single(dt_by_path[scc[0]])
        } else {
            DatatypeGroup::Mutual(scc.iter().map(|p| dt_by_path[p]).collect())
        }
    }).collect()
}

/// Walk a `Typ` and call `f` on each `Path` reached through
/// `TypX::Datatype(Dt::Path, …)`. Recurses through every nested
/// `TypX` (`Boxed`, `Decorate`, `SpecFn`, datatype args, etc.) via
/// the shared `to_lean_type::walk_typ` helper, then filters on
/// `Datatype(Path)` — wrapper nodes (Box / Decorate) and tuples
/// produce no path to call `f` on.
pub fn walk_typ_paths<'a>(typ: &'a Typ, f: &mut impl FnMut(&'a Path)) {
    crate::to_lean_type::walk_typ(typ, &mut |t| {
        if let TypX::Datatype(Dt::Path(p), _, _) = t {
            f(p);
        }
    });
}

// ── Coverage instrumentation ───────────────────────────────────────────
//
// When `$TACTUS_COVERAGE_FILE` is set, every ExprX / PlaceX variant
// visited by the walkers is appended to that file (one line per visit).
// The test binary `tactus_coverage` sets this path, runs a battery of
// targeted snippets, and asserts the expected variant set was hit.
//
// Off by default — zero cost in normal runs (one `OnceLock` lookup).

use std::path::PathBuf;
use std::sync::OnceLock;

static COVERAGE_PATH: OnceLock<Option<PathBuf>> = OnceLock::new();

fn coverage_path() -> Option<&'static PathBuf> {
    COVERAGE_PATH.get_or_init(|| {
        std::env::var_os("TACTUS_COVERAGE_FILE").map(PathBuf::from)
    }).as_ref()
}

/// Append `kind` to the coverage file if one is configured. Best-effort:
/// failures are swallowed since we're in a diagnostic-only path.
fn record(kind: &str) {
    if let Some(path) = coverage_path() {
        use std::io::Write;
        if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
            let _ = writeln!(f, "{}", kind);
        }
    }
}

// ── Expression walker ───────────────────────────────────────────────────

/// Walk all sub-expressions, preserving the krate lifetime `'a`.
///
/// Unlike VIR's `expr_visitor_walk`, this gives the callback `&'a Expr`
/// (not a short-lived `&Expr`), so callers can borrow data from the AST
/// without Arc clones.
///
/// # Invariant
///
/// **Every `Expr` and every `Place` embedded in an `ExprX` variant must be
/// recursed into.** Missing a field here silently drops the subtree — which
/// for dep_order means any spec-fn reference inside never surfaces, and the
/// callee ends up missing from the generated Lean preamble. That was the
/// bug behind the tuple regression: `ReadPlace(Place::Field(…, Temporary(
/// Call(pair, …))))` hid the call inside a `Place`, and this walker used
/// to treat `ReadPlace` as a leaf.
///
/// When adding a new `ExprX` variant: the match below is exhaustive, so
/// the compiler will force you to handle it. When doing so, walk **every**
/// sub-`Expr` and call `walk_place` for every sub-`Place`.
pub(crate) fn walk_expr<'a>(expr: &'a Expr, visit: &mut impl FnMut(&'a Expr)) {
    visit(expr);
    record(expr_variant_name(&expr.x));
    match &expr.x {
        ExprX::Unary(_, e) | ExprX::UnaryOpr(_, e) | ExprX::Loc(e)
        | ExprX::Ghost { expr: e, .. } | ExprX::ProofInSpec(e) | ExprX::NeverToAny(e)
        | ExprX::AssertCompute(e, _) => walk_expr(e, visit),

        ExprX::Binary(_, a, b) | ExprX::BinaryOpr(_, a, b)
        | ExprX::Assign { lhs: a, rhs: b, .. } => {
            walk_expr(a, visit); walk_expr(b, visit);
        }

        ExprX::Call(target, args, pre) => {
            if let CallTarget::FnSpec(e) = target { walk_expr(e, visit); }
            for a in args.iter() { walk_expr(a, visit); }
            if let Some(p) = pre { walk_expr(p, visit); }
        }
        ExprX::Ctor(_, _, fields, _) => {
            for f in fields.iter() { walk_expr(&f.a, visit); }
        }
        ExprX::If(c, t, e) => {
            walk_expr(c, visit); walk_expr(t, visit);
            if let Some(e) = e { walk_expr(e, visit); }
        }
        ExprX::Block(stmts, final_e) => {
            for s in stmts.iter() {
                match &s.x {
                    StmtX::Expr(e) => walk_expr(e, visit),
                    // `let p = e;` — the initializer is a `Place` that may
                    // hide a `Ctor` / `Call` / `Match` inside its `Temporary`
                    // arm. Previously we missed these entirely, so any exec
                    // fn whose only Ctor ref was in a let-RHS (e.g.,
                    // `let p = Point { x: 1, y: 2 };`) would have its
                    // datatype dropped from the Lean preamble, producing
                    // unresolved `Point.mk` references. Walk the place.
                    StmtX::Decl { init: Some(init), .. } => walk_place(&init.x, visit),
                    StmtX::Decl { init: None, .. } => {}
                }
            }
            if let Some(e) = final_e { walk_expr(e, visit); }
        }
        ExprX::Multi(_, es) | ExprX::ArrayLiteral(es) => {
            for e in es.iter() { walk_expr(e, visit); }
        }
        ExprX::Quant(_, _, body) | ExprX::Closure(_, body)
        | ExprX::WithTriggers { body, .. } => walk_expr(body, visit),
        ExprX::Choose { cond, body, .. } => {
            walk_expr(cond, visit); walk_expr(body, visit);
        }
        ExprX::Match(place, arms) => {
            walk_place(&place.x, visit);
            for arm in arms.iter() { walk_expr(&arm.x.body, visit); }
        }
        ExprX::AssertAssume { expr: e, .. }
        | ExprX::AssertAssumeUserDefinedTypeInvariant { expr: e, .. } => walk_expr(e, visit),
        ExprX::AssertBy { require, ensure, proof, .. } => {
            walk_expr(require, visit); walk_expr(ensure, visit); walk_expr(proof, visit);
        }
        ExprX::Return(e) => { if let Some(e) = e { walk_expr(e, visit); } }
        ExprX::AssignToPlace { place, rhs, .. } => {
            walk_place(&place.x, visit);
            walk_expr(rhs, visit);
        }
        ExprX::OpenInvariant(a, _, b, _) => { walk_expr(a, visit); walk_expr(b, visit); }
        ExprX::NonSpecClosure { body, requires, ensures, external_spec, .. } => {
            walk_expr(body, visit);
            for r in requires.iter() { walk_expr(r, visit); }
            for e in ensures.iter() { walk_expr(e, visit); }
            if let Some((_, e)) = external_spec { walk_expr(e, visit); }
        }
        ExprX::Loop { cond, body, invs, decrease, .. } => {
            if let Some(c) = cond { walk_expr(c, visit); }
            walk_expr(body, visit);
            for d in decrease.iter() { walk_expr(d, visit); }
            for inv in invs.iter() { walk_expr(&inv.inv, visit); }
        }
        ExprX::AssertQuery { requires, ensures, proof, .. } => {
            for r in requires.iter() { walk_expr(r, visit); }
            for e in ensures.iter() { walk_expr(e, visit); }
            walk_expr(proof, visit);
        }

        // Place-containing variants: recurse through `walk_place` to find
        // any Exprs buried inside Temporary / Index / WithExpr.
        ExprX::ReadPlace(place, _)
        | ExprX::BorrowMut(place)
        | ExprX::TwoPhaseBorrowMut(place)
        | ExprX::BorrowMutTracked(place) => walk_place(&place.x, visit),
        ExprX::ImplicitReborrowOrSpecRead(place, _, _) => walk_place(&place.x, visit),

        // Leaf nodes (no sub-expressions)
        ExprX::Const(_) | ExprX::Var(_) | ExprX::ConstVar(..) | ExprX::StaticVar(_)
        | ExprX::VarLoc(_) | ExprX::ExecFnByName(_) | ExprX::Fuel(..)
        | ExprX::NullaryOpr(_) | ExprX::Header(_) | ExprX::AirStmt(_)
        | ExprX::RevealString(_) | ExprX::Nondeterministic
        | ExprX::BreakOrContinue { .. }
        | ExprX::VarAt(..)
        | ExprX::EvalAndResolve(..) | ExprX::Old(_) => {}
    }
}

/// Walk a `PlaceX`, visiting any `Expr` nodes embedded in its variants.
/// Without this, spec-fn calls buried inside a `Temporary(...)` place (e.g.
/// `pair(x).0` reached via `ReadPlace(Field("0", Temporary(Call(pair, x))))`)
/// never hit the Expr visitor and wouldn't be pulled into `dep_order`.
fn walk_place<'a>(place: &'a PlaceX, visit: &mut impl FnMut(&'a Expr)) {
    record(&format!("Place::{}", place_variant_name(place)));
    match place {
        PlaceX::Local(_) => {}
        PlaceX::Field(_, p)
        | PlaceX::DerefMut(p)
        | PlaceX::ModeUnwrap(p, _)
        | PlaceX::UserDefinedTypInvariantObligation(p, _) => walk_place(&p.x, visit),
        PlaceX::Temporary(e) => walk_expr(e, visit),
        PlaceX::WithExpr(e, p) => { walk_expr(e, visit); walk_place(&p.x, visit); }
        PlaceX::Index(p, e, _, _) => { walk_place(&p.x, visit); walk_expr(e, visit); }
    }
}

/// Stable short name for an `ExprX` variant. Used only by the coverage
/// instrumentation — not for diagnostics. If you add a new variant, add
/// it here and (ideally) to the expected set in `tactus_coverage`.
fn expr_variant_name(e: &ExprX) -> &'static str {
    match e {
        ExprX::Const(_) => "Const", ExprX::Var(_) => "Var",
        ExprX::ConstVar(..) => "ConstVar", ExprX::StaticVar(_) => "StaticVar",
        ExprX::VarLoc(_) => "VarLoc", ExprX::VarAt(..) => "VarAt",
        ExprX::Loc(_) => "Loc", ExprX::ReadPlace(..) => "ReadPlace",
        ExprX::ExecFnByName(_) => "ExecFnByName", ExprX::NullaryOpr(_) => "NullaryOpr",
        ExprX::Unary(..) => "Unary", ExprX::UnaryOpr(..) => "UnaryOpr",
        ExprX::Binary(..) => "Binary", ExprX::BinaryOpr(..) => "BinaryOpr",
        ExprX::Call(..) => "Call", ExprX::Ctor(..) => "Ctor",
        ExprX::If(..) => "If", ExprX::Match(..) => "Match",
        ExprX::Block(..) => "Block", ExprX::Closure(..) => "Closure",
        ExprX::NonSpecClosure { .. } => "NonSpecClosure",
        ExprX::Quant(..) => "Quant", ExprX::Choose { .. } => "Choose",
        ExprX::WithTriggers { .. } => "WithTriggers",
        ExprX::Multi(..) => "Multi", ExprX::ArrayLiteral(_) => "ArrayLiteral",
        ExprX::Assign { .. } => "Assign", ExprX::AssignToPlace { .. } => "AssignToPlace",
        ExprX::Loop { .. } => "Loop", ExprX::Return(_) => "Return",
        ExprX::AssertAssume { .. } => "AssertAssume",
        ExprX::AssertAssumeUserDefinedTypeInvariant { .. } => "AssertAssumeUDTI",
        ExprX::AssertBy { .. } => "AssertBy", ExprX::AssertQuery { .. } => "AssertQuery",
        ExprX::AssertCompute(..) => "AssertCompute",
        ExprX::OpenInvariant(..) => "OpenInvariant",
        ExprX::Fuel(..) => "Fuel", ExprX::Header(_) => "Header",
        ExprX::RevealString(_) => "RevealString", ExprX::AirStmt(_) => "AirStmt",
        ExprX::Nondeterministic => "Nondeterministic",
        ExprX::BreakOrContinue { .. } => "BreakOrContinue",
        ExprX::Ghost { .. } => "Ghost", ExprX::ProofInSpec(_) => "ProofInSpec",
        ExprX::NeverToAny(_) => "NeverToAny",
        ExprX::BorrowMut(_) => "BorrowMut", ExprX::TwoPhaseBorrowMut(_) => "TwoPhaseBorrowMut",
        ExprX::BorrowMutTracked(_) => "BorrowMutTracked",
        ExprX::ImplicitReborrowOrSpecRead(..) => "ImplicitReborrowOrSpecRead",
        ExprX::EvalAndResolve(..) => "EvalAndResolve",
        ExprX::Old(_) => "Old",
    }
}

/// Stable short name for a `PlaceX` variant.
fn place_variant_name(p: &PlaceX) -> &'static str {
    match p {
        PlaceX::Local(_) => "Local",
        PlaceX::Field(..) => "Field",
        PlaceX::DerefMut(_) => "DerefMut",
        PlaceX::ModeUnwrap(..) => "ModeUnwrap",
        PlaceX::Temporary(_) => "Temporary",
        PlaceX::WithExpr(..) => "WithExpr",
        PlaceX::Index(..) => "Index",
        PlaceX::UserDefinedTypInvariantObligation(..) => "UDTI",
    }
}

/// Collect all `&Fun` references from an expression. Zero Arc clones.
pub(crate) fn collect_fun_refs<'a>(expr: &'a Expr, out: &mut Vec<&'a Fun>) {
    walk_expr(expr, &mut |e| {
        match &e.x {
            ExprX::Call(target, _, _) => match target {
                CallTarget::Fun(kind, fun, _, _, _, _) => {
                    out.push(fun);
                    if let CallTargetKind::DynamicResolved { resolved, .. } = kind {
                        out.push(resolved);
                    }
                }
                _ => {}
            }
            ExprX::ConstVar(fun, _) | ExprX::StaticVar(fun)
            | ExprX::ExecFnByName(fun) | ExprX::Fuel(fun, _, _) => out.push(fun),
            ExprX::AssertAssumeUserDefinedTypeInvariant { fun, .. } => out.push(fun),
            _ => {}
        }
    });
}

// ── Tarjan's SCC ────────────────────────────────────────────────────────

/// Tarjan's SCC algorithm specialized to `&Path` keys (datatypes).
/// Same shape as the `&Fun` version below — duplicated rather than
/// genericized because the Tarjan impl uses `HashMap`/`HashSet`
/// keyed on the node type, and Rust's iter-borrow rules around
/// generic Eq+Hash keys with lifetime params get unwieldy fast for
/// a 60-line algorithm.
fn tarjan_scc_path<'a>(
    nodes: &[&'a Path],
    edges: &HashMap<&'a Path, Vec<&'a Path>>,
) -> Vec<Vec<&'a Path>> {
    struct State<'a> {
        counter: usize,
        stack: Vec<&'a Path>,
        on_stack: HashSet<&'a Path>,
        index: HashMap<&'a Path, usize>,
        lowlink: HashMap<&'a Path, usize>,
        result: Vec<Vec<&'a Path>>,
    }

    fn visit<'a>(
        v: &'a Path,
        edges: &HashMap<&'a Path, Vec<&'a Path>>,
        s: &mut State<'a>,
    ) {
        s.index.insert(v, s.counter);
        s.lowlink.insert(v, s.counter);
        s.counter += 1;
        s.stack.push(v);
        s.on_stack.insert(v);

        if let Some(neighbors) = edges.get(v) {
            for w in neighbors {
                if !s.index.contains_key(w) {
                    visit(w, edges, s);
                    let wl = s.lowlink[w];
                    let vl = s.lowlink.get_mut(v).unwrap();
                    *vl = (*vl).min(wl);
                } else if s.on_stack.contains(w) {
                    let wi = s.index[w];
                    let vl = s.lowlink.get_mut(v).unwrap();
                    *vl = (*vl).min(wi);
                }
            }
        }

        if s.lowlink[v] == s.index[v] {
            let mut scc = Vec::new();
            loop {
                let w = s.stack.pop().unwrap();
                s.on_stack.remove(w);
                let done = std::ptr::eq(w, v);
                scc.push(w);
                if done { break; }
            }
            scc.reverse();
            s.result.push(scc);
        }
    }

    let mut s = State {
        counter: 0, stack: Vec::new(), on_stack: HashSet::new(),
        index: HashMap::new(), lowlink: HashMap::new(), result: Vec::new(),
    };
    for n in nodes {
        if !s.index.contains_key(n) { visit(n, edges, &mut s); }
    }
    s.result
}

/// Tarjan's SCC algorithm using borrowed `&Fun` references. Zero Arc clones.
fn tarjan_scc<'a>(
    fns: &[&'a FunctionX],
    edges: &HashMap<&'a Fun, Vec<&'a Fun>>,
) -> Vec<Vec<&'a Fun>> {
    struct State<'a> {
        counter: usize,
        stack: Vec<&'a Fun>,
        on_stack: HashSet<&'a Fun>,
        index: HashMap<&'a Fun, usize>,
        lowlink: HashMap<&'a Fun, usize>,
        result: Vec<Vec<&'a Fun>>,
    }

    fn visit<'a>(
        v: &'a Fun,
        edges: &HashMap<&'a Fun, Vec<&'a Fun>>,
        s: &mut State<'a>,
    ) {
        s.index.insert(v, s.counter);
        s.lowlink.insert(v, s.counter);
        s.counter += 1;
        s.stack.push(v);
        s.on_stack.insert(v);

        if let Some(neighbors) = edges.get(v) {
            for w in neighbors {
                if !s.index.contains_key(w) {
                    visit(w, edges, s);
                    let wl = s.lowlink[w];
                    let vl = s.lowlink.get_mut(v).unwrap();
                    *vl = (*vl).min(wl);
                } else if s.on_stack.contains(w) {
                    let wi = s.index[w];
                    let vl = s.lowlink.get_mut(v).unwrap();
                    *vl = (*vl).min(wi);
                }
            }
        }

        if s.lowlink[v] == s.index[v] {
            let mut scc = Vec::new();
            loop {
                let w = s.stack.pop().unwrap();
                s.on_stack.remove(w);
                let done = std::ptr::eq(w, v);
                scc.push(w);
                if done { break; }
            }
            scc.reverse();
            s.result.push(scc);
        }
    }

    let mut s = State {
        counter: 0, stack: Vec::new(), on_stack: HashSet::new(),
        index: HashMap::new(), lowlink: HashMap::new(), result: Vec::new(),
    };
    for f in fns {
        if !s.index.contains_key(&f.name) { visit(&f.name, edges, &mut s); }
    }
    s.result
}

#[cfg(test)]
#[path = "tests/dep_order.rs"]
mod tests;
