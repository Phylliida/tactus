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

/// All entity names referenced by the proof fns (transitively through spec fns).
/// Borrows `&str` from VIR's `Arc<String>` — zero allocations.
pub struct References<'a> {
    pub datatypes: HashSet<&'a str>,
    pub traits: HashSet<&'a str>,
}

/// Collect all referenced datatype/trait names from proof fns and their
/// transitive spec fn dependencies.
pub fn collect_references<'a>(
    spec_fn_map: &HashMap<&Fun, &'a FunctionX>,
    proof_fns: &[&'a FunctionX],
) -> References<'a> {
    let mut refs = References { datatypes: HashSet::new(), traits: HashSet::new() };

    for pf in proof_fns {
        collect_from_fn(pf, &mut refs);
    }

    let mut visited: HashSet<&Fun> = HashSet::new();
    let mut worklist: Vec<&'a Fun> = Vec::new();
    seed_worklist(proof_fns, &mut worklist);
    while let Some(fun) = worklist.pop() {
        if visited.contains(fun) { continue; }
        visited.insert(fun);
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
pub fn build_spec_fn_map<'a>(all_fns: &'a [&'a FunctionX]) -> HashMap<&'a Fun, &'a FunctionX> {
    all_fns.iter()
        .filter(|f| matches!(f.mode, Mode::Spec) && f.body.is_some())
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

    let needed_fns: Vec<&'a FunctionX> = all_fns.iter()
        .filter(|f| needed.contains(&f.name) && matches!(f.mode, Mode::Spec) && f.body.is_some())
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
    }
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
