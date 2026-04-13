//! Dependency analysis and topological ordering for Lean output.
//!
//! Given a set of VIR functions and a "root" proof fn, this module:
//! 1. Collects the spec fns transitively referenced by the proof fn
//! 2. Topologically sorts them (callees before callers)
//! 3. Groups mutually recursive functions into `mutual ... end` blocks

use std::collections::{HashMap, HashSet};
use vir::ast::*;
use vir::ast_visitor::expr_visitor_walk;
use vir::visitor::VisitorControlFlow;

/// A group of functions that should be emitted together.
/// Single functions are emitted normally; mutual groups use `mutual ... end`.
///
/// A self-recursive function (e.g., `factorial`) forms a single-element SCC.
/// It does NOT need `mutual ... end` — Lean handles single recursion with `termination_by`.
/// Only functions that call each other (2+ element SCC) need `mutual ... end`.
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
    let spec_fn_map: HashMap<&Fun, &'a FunctionX> = all_fns.iter()
        .filter(|f| matches!(f.mode, Mode::Spec) && f.body.is_some())
        .map(|f| (&f.name, *f))
        .collect();

    // Single pass: transitive closure + edge building.
    let mut needed: HashSet<Fun> = HashSet::new();
    let mut edges: HashMap<Fun, HashSet<Fun>> = HashMap::new();
    let mut worklist: Vec<Fun> = Vec::new();

    // Seed from proof fn requires/ensures
    for pf in proof_fns {
        for e in pf.require.iter() { collect_fun_refs(e, &mut worklist); }
        for e in pf.ensure.0.iter() { collect_fun_refs(e, &mut worklist); }
        for e in pf.ensure.1.iter() { collect_fun_refs(e, &mut worklist); }
    }

    while let Some(fun) = worklist.pop() {
        if needed.contains(&fun) { continue; }
        needed.insert(fun.clone());

        if let Some(f) = spec_fn_map.get(&fun) {
            let mut callees = Vec::new();
            if let Some(body) = &f.body { collect_fun_refs(body, &mut callees); }
            for d in f.decrease.iter() { collect_fun_refs(d, &mut callees); }

            for c in &callees {
                if !needed.contains(c) { worklist.push(c.clone()); }
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

/// Collect all Fun references from an expression using VIR's built-in walker.
fn collect_fun_refs(expr: &Expr, out: &mut Vec<Fun>) {
    expr_visitor_walk(expr, &mut |e| {
        match &e.x {
            ExprX::Call(target, _, _) => {
                match target {
                    CallTarget::Fun(_, fun, _, _, _, _) => out.push(fun.clone()),
                    CallTarget::FnSpec(inner) => collect_fun_refs(inner, out),
                    CallTarget::BuiltinSpecFun(_, _, _) => {}
                }
            }
            ExprX::ConstVar(fun, _) | ExprX::StaticVar(fun)
            | ExprX::ExecFnByName(fun) | ExprX::Fuel(fun, _, _) => {
                out.push(fun.clone());
            }
            ExprX::AssertAssumeUserDefinedTypeInvariant { fun, .. } => {
                out.push(fun.clone());
            }
            _ => {}
        }
        VisitorControlFlow::Recurse
    });
}

/// Tarjan's SCC algorithm. Returns SCCs in reverse topological order (deps first).
fn tarjan_scc(fns: &[&FunctionX], edges: &HashMap<Fun, HashSet<Fun>>) -> Vec<Vec<Fun>> {
    struct State {
        counter: usize,
        stack: Vec<Fun>,
        on_stack: HashSet<Fun>,
        index: HashMap<Fun, usize>,
        lowlink: HashMap<Fun, usize>,
        result: Vec<Vec<Fun>>,
    }

    fn visit(v: &Fun, edges: &HashMap<Fun, HashSet<Fun>>, s: &mut State) {
        s.index.insert(v.clone(), s.counter);
        s.lowlink.insert(v.clone(), s.counter);
        s.counter += 1;
        s.stack.push(v.clone());
        s.on_stack.insert(v.clone());

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
                s.on_stack.remove(&w);
                let done = &w == v;
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
