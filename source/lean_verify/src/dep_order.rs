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
///
/// `needed_fns` is the set of spec-fn `Fun`s reached by the worklist walk
/// (the same set `order_spec_fns` re-derives internally as `needed`).
/// Exposed here so `generate.rs`'s trait_impls loop can gate Instance
/// emission on whether any of an impl's method_impls is reachable —
/// the structural rule documented at the trait_impls call site.
pub struct References<'a> {
    pub datatypes: HashSet<&'a str>,
    pub traits: HashSet<&'a str>,
    pub needed_fns: HashSet<&'a Fun>,
}

/// Collect all referenced datatype/trait names from proof fns and their
/// transitive spec fn dependencies.
pub fn collect_references<'a>(
    spec_fn_map: &HashMap<&Fun, &'a FunctionX>,
    proof_fns: &[&'a FunctionX],
) -> References<'a> {
    let mut refs = References {
        datatypes: HashSet::new(),
        traits: HashSet::new(),
        needed_fns: HashSet::new(),
    };

    for pf in proof_fns {
        collect_from_fn(pf, &mut refs);
    }

    let mut worklist: Vec<&'a Fun> = Vec::new();
    seed_worklist(proof_fns, &mut worklist);
    while let Some(fun) = worklist.pop() {
        if refs.needed_fns.contains(fun) { continue; }
        refs.needed_fns.insert(fun);
        if let Some(f) = spec_fn_map.get(fun) {
            collect_from_fn(f, &mut refs);
            if let Some(body) = &f.body { collect_fun_refs(body, &mut worklist); }
            for d in f.decrease.iter() { collect_fun_refs(d, &mut worklist); }
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
pub fn order_spec_fns<'a>(
    spec_fn_map: &HashMap<&Fun, &'a FunctionX>,
    all_fns: &'a [&'a FunctionX],
    proof_fns: &[&'a FunctionX],
) -> Vec<FnGroup<'a>> {
    let mut needed: HashSet<&Fun> = HashSet::new();
    let mut edges: HashMap<&'a Fun, HashSet<&'a Fun>> = HashMap::new();
    let mut worklist: Vec<&'a Fun> = Vec::new();

    seed_worklist(proof_fns, &mut worklist);

    while let Some(fun) = worklist.pop() {
        if needed.contains(fun) { continue; }
        needed.insert(fun);

        if let Some(f) = spec_fn_map.get(fun) {
            let mut callees = Vec::new();
            if let Some(body) = &f.body { collect_fun_refs(body, &mut callees); }
            for d in f.decrease.iter() { collect_fun_refs(d, &mut callees); }

            for c in &callees {
                if !needed.contains(c) { worklist.push(c); }
            }
            edges.insert(fun, callees.into_iter()
                .filter(|c| spec_fn_map.contains_key(c))
                .collect());
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
    // (including self).
    let mut edges: HashMap<&'a Path, HashSet<&'a Path>> = HashMap::new();
    for (a_path, dt) in &dt_by_path {
        let mut deps: HashSet<&'a Path> = HashSet::new();
        for variant in dt.variants.iter() {
            for field in variant.fields.iter() {
                walk_typ_paths(&field.a.0, &mut |p: &'a Path| {
                    if dt_by_path.contains_key(p) {
                        deps.insert(p);
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
fn walk_expr<'a>(expr: &'a Expr, visit: &mut impl FnMut(&'a Expr)) {
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
fn collect_fun_refs<'a>(expr: &'a Expr, out: &mut Vec<&'a Fun>) {
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
    edges: &HashMap<&'a Path, HashSet<&'a Path>>,
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
        edges: &HashMap<&'a Path, HashSet<&'a Path>>,
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
    edges: &HashMap<&'a Fun, HashSet<&'a Fun>>,
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
        edges: &HashMap<&'a Fun, HashSet<&'a Fun>>,
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
mod tests {
    use super::*;
    use crate::test_fixtures::{mk_path, typ_datatype, typ_int};
    use air::ast::BinderX;
    use std::sync::Arc;

    /// Build a minimal `DatatypeX` with the given name and one
    /// variant containing `field_types` as positional fields. All
    /// boilerplate fields (proxy / owning_module / visibility /
    /// transparency / typ_params / ext_equal / etc.) take "default"
    /// values that don't affect SCC graph construction.
    fn mk_datatype(name: &str, field_types: Vec<Typ>) -> DatatypeX {
        let path = mk_path(name);
        let fields: Fields = Arc::new(field_types.into_iter().enumerate().map(|(i, t)| {
            Arc::new(BinderX {
                name: Arc::new(format!("{}", i)),
                a: (t, Mode::Exec, Visibility { restricted_to: None }),
            })
        }).collect());
        let variant = Variant {
            name: Arc::new(format!("{}_variant", name)),
            fields,
            ctor_style: CtorPrintStyle::Parens,
        };
        DatatypeX {
            name: Dt::Path(path),
            proxy: None,
            owning_module: None,
            visibility: Visibility { restricted_to: None },
            transparency: DatatypeTransparency::WhenVisible(Visibility { restricted_to: None }),
            typ_params: Arc::new(vec![]),
            typ_bounds: Arc::new(vec![]),
            variants: Arc::new(vec![variant]),
            mode: Mode::Exec,
            ext_equal: false,
            user_defined_invariant_fn: None,
            sized_constraint: None,
            destructor: false,
        }
    }

    /// Helper: returns the first segment of the datatype's path
    /// (e.g., "Tree" for a Datatype named `Dt::Path("Tree")`).
    fn dt_short_name(dt: &DatatypeX) -> &str {
        match &dt.name {
            Dt::Path(p) => p.segments[0].as_str(),
            Dt::Tuple(_) => panic!("test fixture should not produce Dt::Tuple"),
        }
    }

    /// REVIEW lens 3/8: a non-recursive datatype produces a Single
    /// group. Just one inductive declaration; no `mutual` block needed.
    #[test]
    fn order_datatypes_non_recursive_is_single() {
        let a = mk_datatype("A", vec![typ_int()]);
        let groups = order_datatypes(&[&a]);
        assert_eq!(groups.len(), 1);
        match &groups[0] {
            DatatypeGroup::Single(dt) => assert_eq!(dt_short_name(dt), "A"),
            DatatypeGroup::Mutual(_) => panic!("non-recursive datatype should be Single"),
        }
    }

    /// REVIEW lens 3/8: a self-recursive datatype (Stack referencing
    /// Stack in its own field) produces a Single group — Lean's
    /// equation compiler handles structural self-recursion without a
    /// `mutual` block. Documented invariant in the docstring of
    /// `DatatypeGroup`.
    #[test]
    fn order_datatypes_self_recursive_is_single() {
        let stack = mk_datatype("Stack", vec![typ_datatype("Stack")]);
        let groups = order_datatypes(&[&stack]);
        assert_eq!(groups.len(), 1);
        match &groups[0] {
            DatatypeGroup::Single(dt) => assert_eq!(dt_short_name(dt), "Stack"),
            DatatypeGroup::Mutual(_) => panic!("self-recursive should be Single, not Mutual"),
        }
    }

    /// REVIEW lens 3/8: Tree ↔ Forest mutual recursion produces a
    /// 2-element Mutual group. Pinned by e2e
    /// (`test_exec_mutually_recursive_datatypes`); this direct unit
    /// test isolates the SCC algorithm without going through Verus.
    #[test]
    fn order_datatypes_tree_forest_scc_is_mutual() {
        let tree = mk_datatype("Tree", vec![typ_datatype("Forest")]);
        let forest = mk_datatype("Forest", vec![typ_datatype("Tree")]);
        let groups = order_datatypes(&[&tree, &forest]);
        assert_eq!(groups.len(), 1);
        match &groups[0] {
            DatatypeGroup::Mutual(dts) => {
                assert_eq!(dts.len(), 2);
                let names: Vec<&str> = dts.iter().map(|d| dt_short_name(d)).collect();
                assert!(names.contains(&"Tree") && names.contains(&"Forest"),
                    "Mutual group should contain both Tree and Forest; got {:?}", names);
            }
            DatatypeGroup::Single(_) => panic!("Tree ↔ Forest should produce a Mutual group"),
        }
    }

    /// REVIEW lens 3/8: 3-element SCC (A → B → C → A). Pinpoints
    /// the algorithm scales beyond the 2-element case.
    #[test]
    fn order_datatypes_three_element_scc_is_mutual() {
        let a = mk_datatype("A", vec![typ_datatype("B")]);
        let b = mk_datatype("B", vec![typ_datatype("C")]);
        let c = mk_datatype("C", vec![typ_datatype("A")]);
        let groups = order_datatypes(&[&a, &b, &c]);
        assert_eq!(groups.len(), 1);
        match &groups[0] {
            DatatypeGroup::Mutual(dts) => assert_eq!(dts.len(), 3),
            DatatypeGroup::Single(_) => panic!("3-cycle should be Mutual, got Single"),
        }
    }

    /// REVIEW lens 3/8: SCC + standalone — a 2-element Mutual group
    /// (Tree ↔ Forest) alongside a non-recursive Single (Pair).
    /// Verifies that order_datatypes correctly partitions the input
    /// rather than collapsing everything into one group.
    #[test]
    fn order_datatypes_scc_plus_standalone() {
        let tree = mk_datatype("Tree", vec![typ_datatype("Forest")]);
        let forest = mk_datatype("Forest", vec![typ_datatype("Tree")]);
        let pair = mk_datatype("Pair", vec![typ_int()]);
        let groups = order_datatypes(&[&tree, &forest, &pair]);
        assert_eq!(groups.len(), 2);

        let mutual_count = groups.iter()
            .filter(|g| matches!(g, DatatypeGroup::Mutual(_)))
            .count();
        let single_count = groups.iter()
            .filter(|g| matches!(g, DatatypeGroup::Single(_)))
            .count();
        assert_eq!(mutual_count, 1, "expected one Mutual group (Tree ↔ Forest)");
        assert_eq!(single_count, 1, "expected one Single group (Pair)");

        // Verify the Single is Pair specifically.
        for g in &groups {
            if let DatatypeGroup::Single(dt) = g {
                assert_eq!(dt_short_name(dt), "Pair");
            }
        }
    }

    /// REVIEW lens 3/8: empty input produces an empty result. Edge
    /// case — would be silly to fail but good to pin against a
    /// future refactor that assumes non-empty input.
    #[test]
    fn order_datatypes_empty_input_returns_empty() {
        let groups = order_datatypes(&[]);
        assert!(groups.is_empty(), "empty input should produce empty output");
    }
}
