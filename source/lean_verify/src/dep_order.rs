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

/// Collect all referenced datatype/trait names and return spec fns in dependency order.
pub fn collect_references<'a>(
    all_fns: &'a [&'a FunctionX],
    proof_fns: &[&'a FunctionX],  // needs 'a for worklist Fun refs
) -> References<'a> {
    let mut refs = References { datatypes: HashSet::new(), traits: HashSet::new() };

    for pf in proof_fns {
        collect_from_fn(pf, &mut refs);
    }

    // Transitive closure: scan spec fns reachable from proof fns
    let spec_fn_map: HashMap<&Fun, &'a FunctionX> = all_fns.iter()
        .filter(|f| matches!(f.mode, Mode::Spec) && f.body.is_some())
        .map(|f| (&f.name, *f))
        .collect();

    let mut visited: HashSet<&Fun> = HashSet::new();
    let mut worklist: Vec<&'a Fun> = Vec::new();
    for pf in proof_fns {
        for e in pf.require.iter() { collect_fun_refs(e, &mut worklist); }
        for e in pf.ensure.0.iter() { collect_fun_refs(e, &mut worklist); }
        for e in pf.ensure.1.iter() { collect_fun_refs(e, &mut worklist); }
    }
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
        if let GenericBoundX::Trait(TraitId::Path(path), _) = &**bound {
            refs.traits.insert(short_name(path));
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

/// Given all VIR functions and proof fns, return spec fns in dependency order.
pub fn order_spec_fns<'a>(
    all_fns: &'a [&'a FunctionX],
    proof_fns: &[&'a FunctionX],
) -> Vec<FnGroup<'a>> {
    let spec_fn_map: HashMap<&Fun, &'a FunctionX> = all_fns.iter()
        .filter(|f| matches!(f.mode, Mode::Spec) && f.body.is_some())
        .map(|f| (&f.name, *f))
        .collect();

    let mut needed: HashSet<&Fun> = HashSet::new();
    let mut edges: HashMap<&'a Fun, HashSet<&'a Fun>> = HashMap::new();
    let mut worklist: Vec<&'a Fun> = Vec::new();

    for pf in proof_fns {
        for e in pf.require.iter() { collect_fun_refs(e, &mut worklist); }
        for e in pf.ensure.0.iter() { collect_fun_refs(e, &mut worklist); }
        for e in pf.ensure.1.iter() { collect_fun_refs(e, &mut worklist); }
    }

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

// ── Expression walker ───────────────────────────────────────────────────

/// Walk all sub-expressions, preserving the krate lifetime `'a`.
///
/// Unlike VIR's `expr_visitor_walk`, this gives the callback `&'a Expr`
/// (not a short-lived `&Expr`), so callers can borrow data from the AST
/// without Arc clones.
fn walk_expr<'a>(expr: &'a Expr, visit: &mut impl FnMut(&'a Expr)) {
    visit(expr);
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
            for s in stmts.iter() { if let StmtX::Expr(e) = &s.x { walk_expr(e, visit); } }
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
        ExprX::Match(_, arms) => {
            for arm in arms.iter() { walk_expr(&arm.x.body, visit); }
        }
        ExprX::AssertAssume { expr: e, .. }
        | ExprX::AssertAssumeUserDefinedTypeInvariant { expr: e, .. } => walk_expr(e, visit),
        ExprX::AssertBy { require, ensure, proof, .. } => {
            walk_expr(require, visit); walk_expr(ensure, visit); walk_expr(proof, visit);
        }
        ExprX::Return(e) => { if let Some(e) = e { walk_expr(e, visit); } }
        ExprX::AssignToPlace { rhs, .. } => walk_expr(rhs, visit),
        ExprX::OpenInvariant(a, _, b, _) => { walk_expr(a, visit); walk_expr(b, visit); }

        // Leaf nodes
        _ => {}
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
