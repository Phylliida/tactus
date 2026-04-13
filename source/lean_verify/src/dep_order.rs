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
///
/// Note: a self-recursive function (e.g., `factorial`) forms a single-element SCC.
/// It does NOT need `mutual ... end` — Lean handles single recursion with `termination_by`.
/// Only functions that call EACH OTHER (2+ element SCC) need `mutual ... end`.
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

    // Single pass: collect transitive closure AND build edge map simultaneously.
    // For each needed spec fn, we store its direct callees (within the spec fn set).
    let mut needed: HashSet<Fun> = HashSet::new();
    let mut edges: HashMap<Fun, HashSet<Fun>> = HashMap::new();
    let mut worklist: Vec<Fun> = Vec::new();

    // Seed from proof fn requires/ensures
    for pf in proof_fns {
        collect_fun_refs_from_exprs(&pf.require, &mut worklist);
        collect_fun_refs_from_exprs(&pf.ensure.0, &mut worklist);
        collect_fun_refs_from_exprs(&pf.ensure.1, &mut worklist);
    }

    // Transitive closure: for each new function, collect its callees
    while let Some(fun) = worklist.pop() {
        if needed.contains(&fun) {
            continue;
        }
        needed.insert(fun.clone());
        if let Some(f) = spec_fn_map.get(&fun) {
            let mut callees = Vec::new();
            if let Some(body) = &f.body {
                collect_fun_refs_from_expr(body, &mut callees);
            }
            collect_fun_refs_from_exprs(&f.decrease, &mut callees);

            // Add unvisited callees to worklist
            for c in &callees {
                if !needed.contains(c) {
                    worklist.push(c.clone());
                }
            }

            // Store edges (only to other needed spec fns)
            let callee_set: HashSet<Fun> = callees.into_iter()
                .filter(|c| spec_fn_map.contains_key(c))
                .collect();
            edges.insert(fun, callee_set);
        }
    }

    // Collect the needed spec fns in their original order (for determinism)
    let needed_fns: Vec<&'a FunctionX> = all_fns.iter()
        .filter(|f| needed.contains(&f.name) && matches!(f.mode, Mode::Spec) && f.body.is_some())
        .copied()
        .collect();

    // Tarjan's SCC: find mutual recursion groups + topological order
    let sccs = tarjan_scc(&needed_fns, &edges);

    // Convert SCCs to FnGroups
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
///
/// Uses `Fun` references internally to avoid cloning `Arc`s where possible.
/// The `Fun` type is `Arc<FunX>`, so clones are just refcount bumps.
fn tarjan_scc(fns: &[&FunctionX], edges: &HashMap<Fun, HashSet<Fun>>) -> Vec<Vec<Fun>> {
    struct State {
        index_counter: usize,
        stack: Vec<Fun>,
        on_stack: HashSet<Fun>,
        index: HashMap<Fun, usize>,
        lowlink: HashMap<Fun, usize>,
        result: Vec<Vec<Fun>>,
    }

    fn strongconnect(v: &Fun, edges: &HashMap<Fun, HashSet<Fun>>, s: &mut State) {
        s.index.insert(v.clone(), s.index_counter);
        s.lowlink.insert(v.clone(), s.index_counter);
        s.index_counter += 1;
        s.stack.push(v.clone());
        s.on_stack.insert(v.clone());

        if let Some(neighbors) = edges.get(v) {
            for w in neighbors {
                if !s.index.contains_key(w) {
                    strongconnect(w, edges, s);
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

    let mut state = State {
        index_counter: 0,
        stack: Vec::new(),
        on_stack: HashSet::new(),
        index: HashMap::new(),
        lowlink: HashMap::new(),
        result: Vec::new(),
    };

    for f in fns {
        if !state.index.contains_key(&f.name) {
            strongconnect(&f.name, edges, &mut state);
        }
    }

    state.result
}

// ── Expression walking ──────────────────────────────────────────────────────

/// Collect all Fun references from an expression.
fn collect_fun_refs_from_expr(expr: &Expr, out: &mut Vec<Fun>) {
    walk_expr(&expr.x, out);
}

fn collect_fun_refs_from_exprs(exprs: &[Expr], out: &mut Vec<Fun>) {
    for e in exprs { walk_expr(&e.x, out); }
}

/// Walk an ExprX, collecting all function references.
/// Handles ALL ExprX variants explicitly — no silent catch-all.
fn walk_expr(expr: &ExprX, out: &mut Vec<Fun>) {
    match expr {
        // Function references
        ExprX::Call(target, args, extra) => {
            walk_call_target(target, out);
            for arg in args.iter() { walk_expr(&arg.x, out); }
            if let Some(e) = extra { walk_expr(&e.x, out); }
        }
        ExprX::ConstVar(fun, _) | ExprX::StaticVar(fun) | ExprX::ExecFnByName(fun) => {
            out.push(fun.clone());
        }
        ExprX::Fuel(fun, _, _) => {
            out.push(fun.clone());
        }

        // Unary
        ExprX::Unary(_, e) | ExprX::UnaryOpr(_, e) | ExprX::Loc(e) => {
            walk_expr(&e.x, out);
        }

        // Binary
        ExprX::Binary(_, a, b) | ExprX::BinaryOpr(_, a, b) => {
            walk_expr(&a.x, out);
            walk_expr(&b.x, out);
        }

        // Control flow
        ExprX::If(c, t, e) => {
            walk_expr(&c.x, out);
            walk_expr(&t.x, out);
            if let Some(e) = e { walk_expr(&e.x, out); }
        }
        ExprX::Match(place, arms) => {
            walk_place(&place.x, out);
            for arm in arms.iter() {
                walk_expr(&arm.x.guard.x, out);
                walk_expr(&arm.x.body.x, out);
            }
        }
        ExprX::Loop { cond, body, invs, decrease, .. } => {
            if let Some(c) = cond { walk_expr(&c.x, out); }
            walk_expr(&body.x, out);
            for inv in invs.iter() { walk_expr(&inv.inv.x, out); }
            for d in decrease.iter() { walk_expr(&d.x, out); }
        }

        // Quantifiers / closures
        ExprX::Quant(_, _, body) | ExprX::Closure(_, body) => {
            walk_expr(&body.x, out);
        }
        ExprX::NonSpecClosure { body, requires, ensures, external_spec, .. } => {
            walk_expr(&body.x, out);
            for r in requires.iter() { walk_expr(&r.x, out); }
            for e in ensures.iter() { walk_expr(&e.x, out); }
            if let Some(spec) = external_spec { walk_expr(&spec.1.x, out); }
        }

        // Choose / triggers
        ExprX::Choose { cond, body, .. } => {
            walk_expr(&cond.x, out);
            walk_expr(&body.x, out);
        }
        ExprX::WithTriggers { triggers, body } => {
            for trig in triggers.iter() {
                for e in trig.iter() { walk_expr(&e.x, out); }
            }
            walk_expr(&body.x, out);
        }

        // Blocks
        ExprX::Block(stmts, final_expr) => {
            for stmt in stmts.iter() {
                match &stmt.x {
                    StmtX::Expr(e) => walk_expr(&e.x, out),
                    StmtX::Decl { init, els, .. } => {
                        if let Some(place) = init { walk_place(&place.x, out); }
                        if let Some(e) = els { walk_expr(&e.x, out); }
                    }
                }
            }
            if let Some(e) = final_expr { walk_expr(&e.x, out); }
        }

        // Constructors
        ExprX::Ctor(_, _, binders, update_tail) => {
            for b in binders.iter() { walk_expr(&b.a.x, out); }
            if let Some(tail) = update_tail { walk_place(&tail.place.x, out); }
        }
        ExprX::ArrayLiteral(exprs) | ExprX::Multi(_, exprs) => {
            for e in exprs.iter() { walk_expr(&e.x, out); }
        }

        // Assertions
        ExprX::AssertAssume { expr, .. } | ExprX::AssertCompute(expr, _) => {
            walk_expr(&expr.x, out);
        }
        ExprX::AssertAssumeUserDefinedTypeInvariant { expr, fun, .. } => {
            walk_expr(&expr.x, out);
            out.push(fun.clone());
        }
        ExprX::AssertBy { require, ensure, proof, .. } => {
            walk_expr(&require.x, out);
            walk_expr(&ensure.x, out);
            walk_expr(&proof.x, out);
        }
        ExprX::AssertQuery { requires, ensures, proof, .. } => {
            for r in requires.iter() { walk_expr(&r.x, out); }
            for e in ensures.iter() { walk_expr(&e.x, out); }
            walk_expr(&proof.x, out);
        }

        // Assignments
        ExprX::Assign { lhs, rhs, .. } => {
            walk_expr(&lhs.x, out);
            walk_expr(&rhs.x, out);
        }
        ExprX::AssignToPlace { place, rhs, .. } => {
            walk_place(&place.x, out);
            walk_expr(&rhs.x, out);
        }

        // Ghost / mode wrappers
        ExprX::Ghost { expr, .. } | ExprX::ProofInSpec(expr)
        | ExprX::NeverToAny(expr) | ExprX::Old(expr) | ExprX::Return(Some(expr)) => {
            walk_expr(&expr.x, out);
        }

        // Places
        ExprX::ReadPlace(place, _) | ExprX::BorrowMut(place)
        | ExprX::TwoPhaseBorrowMut(place) | ExprX::BorrowMutTracked(place) => {
            walk_place(&place.x, out);
        }
        ExprX::ImplicitReborrowOrSpecRead(place, _, _) => {
            walk_place(&place.x, out);
        }
        ExprX::EvalAndResolve(a, b) => {
            walk_expr(&a.x, out);
            walk_expr(&b.x, out);
        }
        ExprX::OpenInvariant(e1, _, e2, _) => {
            walk_expr(&e1.x, out);
            walk_expr(&e2.x, out);
        }

        // Leaf nodes — no function references
        ExprX::Const(_) | ExprX::Var(_) | ExprX::VarLoc(_) | ExprX::VarAt(..)
        | ExprX::NullaryOpr(_) | ExprX::Header(_) | ExprX::Nondeterministic
        | ExprX::BreakOrContinue { .. } | ExprX::Return(None)
        | ExprX::RevealString(_) | ExprX::AirStmt(_) => {}
    }
}

/// Extract function references from a CallTarget.
fn walk_call_target(target: &CallTarget, out: &mut Vec<Fun>) {
    match target {
        CallTarget::Fun(_, fun, _, _, _, _) => out.push(fun.clone()),
        CallTarget::FnSpec(expr) => walk_expr(&expr.x, out),
        // BuiltinSpecFun references built-in operations (e.g., Seq.len),
        // not user-defined functions. No Fun to collect.
        CallTarget::BuiltinSpecFun(_, _, _) => {}
    }
}

/// Walk a PlaceX, collecting function references from any sub-expressions.
fn walk_place(place: &PlaceX, out: &mut Vec<Fun>) {
    match place {
        PlaceX::Local(_) => {}
        PlaceX::Field(_, base) | PlaceX::DerefMut(base) | PlaceX::ModeUnwrap(base, _) => {
            walk_place(&base.x, out);
        }
        PlaceX::Index(base, idx, _, _) => {
            walk_place(&base.x, out);
            walk_expr(&idx.x, out);
        }
        PlaceX::Temporary(e) => walk_expr(&e.x, out),
        PlaceX::WithExpr(e, place) => {
            walk_expr(&e.x, out);
            walk_place(&place.x, out);
        }
        PlaceX::UserDefinedTypInvariantObligation(place, fun) => {
            walk_place(&place.x, out);
            out.push(fun.clone());
        }
    }
}
