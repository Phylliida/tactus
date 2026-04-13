//! Dependency analysis and topological ordering for Lean output.
//!
//! Given a set of VIR functions and a "root" proof fn, this module:
//! 1. Collects the spec fns transitively referenced by the proof fn
//! 2. Topologically sorts them (callees before callers)
//! 3. Groups mutually recursive functions into `mutual ... end` blocks

use std::collections::{HashMap, HashSet};
use vir::ast::*;

/// A group of functions that should be emitted together.
/// Single functions are emitted normally; mutual groups use `mutual ... end`.
pub enum FnGroup<'a> {
    Single(&'a FunctionX),
    Mutual(Vec<&'a FunctionX>),
}

/// Given all VIR functions and a set of proof fns, return the spec fns
/// needed for Lean output, in dependency order, grouped by mutual recursion.
pub fn order_spec_fns<'a>(
    all_fns: &'a [&'a FunctionX],
    proof_fns: &[&FunctionX],
) -> Vec<FnGroup<'a>> {
    // Build name → function map for spec fns
    let spec_fn_map: HashMap<&Fun, &'a FunctionX> = all_fns.iter()
        .filter(|f| matches!(f.mode, Mode::Spec) && f.body.is_some())
        .map(|f| (&f.name, *f))
        .collect();

    // Collect all function names referenced transitively from proof fns
    let mut needed: HashSet<Fun> = HashSet::new();
    let mut worklist: Vec<Fun> = Vec::new();

    // Seed from proof fn requires, ensures, and spec fn bodies
    for pf in proof_fns {
        collect_fun_refs_from_exprs(&pf.require, &mut worklist);
        collect_fun_refs_from_exprs(&pf.ensure.0, &mut worklist);
        collect_fun_refs_from_exprs(&pf.ensure.1, &mut worklist);
    }

    // Transitive closure
    while let Some(fun) = worklist.pop() {
        if needed.contains(&fun) {
            continue;
        }
        needed.insert(fun.clone());
        if let Some(f) = spec_fn_map.get(&fun) {
            // Collect references from this spec fn's body and decrease clauses
            if let Some(body) = &f.body {
                collect_fun_refs_from_expr(body, &mut worklist);
            }
            collect_fun_refs_from_exprs(&f.decrease, &mut worklist);
        }
    }

    // Build adjacency list for the needed spec fns
    let needed_fns: Vec<&'a FunctionX> = all_fns.iter()
        .filter(|f| needed.contains(&f.name) && matches!(f.mode, Mode::Spec) && f.body.is_some())
        .copied()
        .collect();

    // Build call graph edges (caller → callees)
    let mut edges: HashMap<Fun, HashSet<Fun>> = HashMap::new();
    for f in &needed_fns {
        let mut callees = Vec::new();
        if let Some(body) = &f.body {
            collect_fun_refs_from_expr(body, &mut callees);
        }
        let callee_set: HashSet<Fun> = callees.into_iter()
            .filter(|c| needed.contains(c))
            .collect();
        edges.insert(f.name.clone(), callee_set);
    }

    // Tarjan's SCC to find mutual recursion groups, then topological sort
    let sccs = tarjan_scc(&needed_fns, &edges);

    // Convert SCCs to FnGroups (already in reverse topological order from Tarjan's)
    let fn_map: HashMap<&Fun, &'a FunctionX> = needed_fns.iter()
        .map(|f| (&f.name, *f))
        .collect();

    sccs.into_iter().map(|scc| {
        if scc.len() == 1 {
            FnGroup::Single(fn_map[&scc[0]])
        } else {
            FnGroup::Mutual(scc.iter().map(|name| fn_map[name]).collect())
        }
    }).collect()
}

/// Tarjan's strongly connected components algorithm.
/// Returns SCCs in reverse topological order (dependencies first).
fn tarjan_scc(fns: &[&FunctionX], edges: &HashMap<Fun, HashSet<Fun>>) -> Vec<Vec<Fun>> {
    let mut index_counter: usize = 0;
    let mut stack: Vec<Fun> = Vec::new();
    let mut on_stack: HashSet<Fun> = HashSet::new();
    let mut index: HashMap<Fun, usize> = HashMap::new();
    let mut lowlink: HashMap<Fun, usize> = HashMap::new();
    let mut result: Vec<Vec<Fun>> = Vec::new();

    fn strongconnect(
        v: &Fun,
        edges: &HashMap<Fun, HashSet<Fun>>,
        index_counter: &mut usize,
        stack: &mut Vec<Fun>,
        on_stack: &mut HashSet<Fun>,
        index: &mut HashMap<Fun, usize>,
        lowlink: &mut HashMap<Fun, usize>,
        result: &mut Vec<Vec<Fun>>,
    ) {
        index.insert(v.clone(), *index_counter);
        lowlink.insert(v.clone(), *index_counter);
        *index_counter += 1;
        stack.push(v.clone());
        on_stack.insert(v.clone());

        if let Some(neighbors) = edges.get(v) {
            for w in neighbors {
                if !index.contains_key(w) {
                    strongconnect(w, edges, index_counter, stack, on_stack, index, lowlink, result);
                    let wl = lowlink[w];
                    let vl = lowlink.get_mut(v).unwrap();
                    if wl < *vl {
                        *vl = wl;
                    }
                } else if on_stack.contains(w) {
                    let wi = index[w];
                    let vl = lowlink.get_mut(v).unwrap();
                    if wi < *vl {
                        *vl = wi;
                    }
                }
            }
        }

        if lowlink[v] == index[v] {
            let mut scc = Vec::new();
            loop {
                let w = stack.pop().unwrap();
                on_stack.remove(&w);
                scc.push(w.clone());
                if &w == v {
                    break;
                }
            }
            scc.reverse();
            result.push(scc);
        }
    }

    for f in fns {
        if !index.contains_key(&f.name) {
            strongconnect(
                &f.name, edges, &mut index_counter, &mut stack, &mut on_stack,
                &mut index, &mut lowlink, &mut result,
            );
        }
    }

    result
}

/// Collect all Fun references from an expression tree.
fn collect_fun_refs_from_expr(expr: &Expr, out: &mut Vec<Fun>) {
    collect_fun_refs_from_exprx(&expr.x, out);
}

fn collect_fun_refs_from_exprs(exprs: &[Expr], out: &mut Vec<Fun>) {
    for e in exprs {
        collect_fun_refs_from_expr(e, out);
    }
}

fn collect_fun_refs_from_exprx(expr: &ExprX, out: &mut Vec<Fun>) {
    match expr {
        ExprX::Call(target, args, _) => {
            if let CallTarget::Fun(_, fun, _, _, _, _) = target {
                out.push(fun.clone());
            }
            for arg in args.iter() {
                collect_fun_refs_from_expr(arg, out);
            }
        }
        ExprX::ConstVar(fun, _) => {
            out.push(fun.clone());
        }
        // Recurse into subexpressions
        ExprX::Unary(_, e) | ExprX::UnaryOpr(_, e) | ExprX::Loc(e) => {
            collect_fun_refs_from_expr(e, out);
        }
        ExprX::Binary(_, a, b) | ExprX::BinaryOpr(_, a, b) => {
            collect_fun_refs_from_expr(a, out);
            collect_fun_refs_from_expr(b, out);
        }
        ExprX::If(c, t, e) => {
            collect_fun_refs_from_expr(c, out);
            collect_fun_refs_from_expr(t, out);
            if let Some(e) = e {
                collect_fun_refs_from_expr(e, out);
            }
        }
        ExprX::Quant(_, _, body) | ExprX::Closure(_, body) => {
            collect_fun_refs_from_expr(body, out);
        }
        ExprX::Choose { cond, body, .. } => {
            collect_fun_refs_from_expr(cond, out);
            collect_fun_refs_from_expr(body, out);
        }
        ExprX::WithTriggers { body, .. } => {
            collect_fun_refs_from_expr(body, out);
        }
        ExprX::Block(stmts, final_expr) => {
            for stmt in stmts.iter() {
                match &stmt.x {
                    StmtX::Expr(e) => collect_fun_refs_from_expr(e, out),
                    StmtX::Decl { .. } => {} // TODO: handle decl init exprs
                }
            }
            if let Some(e) = final_expr {
                collect_fun_refs_from_expr(e, out);
            }
        }
        ExprX::ReadPlace(place, _) => {
            collect_fun_refs_from_place(place, out);
        }
        ExprX::Ghost { expr, .. } | ExprX::ProofInSpec(expr) => {
            collect_fun_refs_from_expr(expr, out);
        }
        ExprX::Multi(_, exprs) => {
            for e in exprs.iter() {
                collect_fun_refs_from_expr(e, out);
            }
        }
        // Leaf nodes with no function references
        ExprX::Const(_) | ExprX::Var(_) | ExprX::VarLoc(_) | ExprX::VarAt(..)
        | ExprX::NullaryOpr(_) | ExprX::Header(_) | ExprX::Nondeterministic => {}
        // Other expressions — conservatively skip (no function refs in most)
        _ => {}
    }
}

fn collect_fun_refs_from_place(place: &Place, out: &mut Vec<Fun>) {
    match &place.x {
        PlaceX::Local(_) => {}
        PlaceX::Field(_, base) | PlaceX::DerefMut(base) | PlaceX::ModeUnwrap(base, _) => {
            collect_fun_refs_from_place(base, out);
        }
        PlaceX::Index(base, idx, _, _) => {
            collect_fun_refs_from_place(base, out);
            collect_fun_refs_from_expr(idx, out);
        }
        PlaceX::Temporary(e) => {
            collect_fun_refs_from_expr(e, out);
        }
        _ => {}
    }
}
