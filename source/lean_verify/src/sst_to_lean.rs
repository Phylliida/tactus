//! Weakest-precondition VC generation from SST → Lean AST.
//!
//! Takes an exec fn's `FuncCheckSst` (from `FunctionSst::exec_proof_check`)
//! and produces a `Theorem` AST node whose goal is the WP of the body and
//! whose tactic body is `tactus_auto`.
//!
//! # First-slice scope
//!
//! Handles straight-line code only: a body that is a (possibly nested)
//! `StmX::Block` of
//!
//!   * `StmX::Assign`    — simple `let x := e` bindings
//!   * `StmX::Assert`    — obligations, conjoined into the goal
//!   * `StmX::Assume`    — hypotheses, threaded into the goal as implications
//!   * `StmX::Return`    — the final returned expression (at most one)
//!   * `StmX::Air`, `StmX::Fuel`, `StmX::RevealString` — transparent
//!
//! Not yet supported: if/else, mutation/SSA, loops, fixed-width overflow as
//! a separate obligation, pattern matching, closures, mutable references.
//!
//! # Semantic model (weakest-precondition, in body order)
//!
//! We walk statements in source order and nest each one into the goal:
//!
//! * `let x = e` becomes `let x := e; <rest>`.
//! * `assume(P)` becomes `(P) → <rest>`.
//! * `assert(P)` becomes `(P) ∧ (<rest>)`. `P` must be provable without
//!   using assumes that appear *after* it — this is the property that
//!   separates us from a naive "conjoin everything" scheme.
//! * `return e` ends the body; if the ensures references the return name,
//!   we wrap the ensures in `let <ret_name> := e; <ensures_conj>`.
//!
//! The AST pretty-printer handles precedence, so constructors just build
//! `BinOp::And` / `BinOp::Implies` / `Let` without worrying about parens.

use vir::sst::{BndX, CallFun, Dest, Exp, ExpX, FuncCheckSst, FunctionSst, Stm, StmX};
use vir::ast::{BinaryOp, UnaryOp};
use crate::lean_ast::{
    and_all, BinOp as L, Binder as LBinder, BinderKind, Expr as LExpr, ExprNode, Tactic, Theorem,
};
use crate::to_lean_sst_expr::sst_exp_to_ast;
use crate::to_lean_type::{lean_name, sanitize, typ_to_expr};

// ── Support check ──────────────────────────────────────────────────────
//
// Before building any AST, we walk the whole `FuncCheckSst` and confirm
// every statement and every expression is something we know how to emit.

/// Confirm the function's body, requires, and ensures only use SST forms
/// that the first slice supports.
pub fn supported_body(check: &FuncCheckSst) -> Result<(), String> {
    check_stm(&check.body)?;
    for req in check.reqs.iter() {
        check_exp(req)?;
    }
    for ens in check.post_condition.ens_exps.iter() {
        check_exp(ens)?;
    }
    Ok(())
}

fn check_stm(stm: &Stm) -> Result<(), String> {
    match &stm.x {
        StmX::Block(stms) => {
            for s in stms.iter() { check_stm(s)?; }
            Ok(())
        }
        StmX::Assign { lhs: Dest { dest, .. }, rhs } => {
            check_exp(dest)?;
            check_exp(rhs)?;
            Ok(())
        }
        StmX::Return { ret_exp: Some(e), inside_body: false, .. } => check_exp(e),
        StmX::Return { ret_exp: None, inside_body: false, .. } => Ok(()),
        StmX::Return { inside_body: true, .. } => Err(
            "early returns from within a block are not yet supported".to_string()
        ),
        StmX::Assert(_, _, e) | StmX::Assume(e) => check_exp(e),
        StmX::AssertCompute(_, e, _) => check_exp(e),
        StmX::Air(_) | StmX::Fuel(..) | StmX::RevealString(_) => Ok(()),
        StmX::If(..) => Err("if/else in exec fn body not yet supported".to_string()),
        StmX::Loop { .. } => Err("loops in exec fn body not yet supported".to_string()),
        StmX::Call { .. } => Err("function calls in exec fn body not yet supported".to_string()),
        StmX::BreakOrContinue { .. } => Err("break/continue not yet supported".to_string()),
        StmX::AssertBitVector { .. } => Err("assert by(bit_vector) not yet supported".to_string()),
        StmX::AssertQuery { .. } => Err("assert by(...) queries not yet supported".to_string()),
        StmX::DeadEnd(_) => Err("DeadEnd not yet supported".to_string()),
        StmX::OpenInvariant(_) => Err("OpenInvariant not yet supported".to_string()),
        StmX::ClosureInner { .. } => Err("exec closures not yet supported".to_string()),
    }
}

fn check_exp(e: &Exp) -> Result<(), String> {
    match &e.x {
        ExpX::Const(_) | ExpX::Var(_) | ExpX::VarLoc(_) | ExpX::VarAt(..)
        | ExpX::StaticVar(_) | ExpX::ExecFnByName(_) | ExpX::NullaryOpr(_) => Ok(()),
        ExpX::Unary(op, inner) => match op {
            UnaryOp::Not
            | UnaryOp::Clip { .. }
            | UnaryOp::CoerceMode { .. }
            | UnaryOp::Trigger(_) => check_exp(inner),
            other => Err(format!("unsupported unary op: {:?}", other)),
        },
        ExpX::UnaryOpr(_, inner) => check_exp(inner),
        ExpX::Binary(op, l, r) => match op {
            BinaryOp::HeightCompare { .. }
            | BinaryOp::Index(_, _)
            | BinaryOp::StrGetChar
            | BinaryOp::IeeeFloat(_) => Err(format!("unsupported binary op: {:?}", op)),
            _ => { check_exp(l)?; check_exp(r) }
        },
        ExpX::BinaryOpr(_, l, r) => { check_exp(l)?; check_exp(r) }
        ExpX::If(c, t, e) => { check_exp(c)?; check_exp(t)?; check_exp(e) }
        ExpX::Call(target, _, args) => {
            if matches!(target, CallFun::InternalFun(_)) {
                return Err("internal function calls not yet supported".to_string());
            }
            for a in args.iter() { check_exp(a)?; }
            Ok(())
        }
        ExpX::Bind(bnd, body) => {
            match &bnd.x {
                BndX::Let(binders) => for b in binders.iter() { check_exp(&b.a)?; },
                BndX::Quant(..) | BndX::Lambda(..) => {}
                BndX::Choose(_, _, cond) => check_exp(cond)?,
            }
            check_exp(body)
        }
        ExpX::WithTriggers(_, inner) | ExpX::Loc(inner) => check_exp(inner),
        ExpX::Ctor(..) => Err("datatype constructors not yet supported in exec fns".to_string()),
        ExpX::CallLambda(..) => Err("closure calls not yet supported in exec fns".to_string()),
        ExpX::ArrayLiteral(_) => Err("array literals not yet supported in exec fns".to_string()),
        ExpX::Old(..) => Err("`old(...)` not yet supported in exec fns".to_string()),
        ExpX::Interp(_) => Err(
            "Interp nodes should never escape the interpreter (internal bug)".to_string()
        ),
        ExpX::FuelConst(_) => Err("FuelConst not yet supported".to_string()),
    }
}

// ── Theorem builder ────────────────────────────────────────────────────

/// Build a Lean `Theorem` AST node for an exec fn body check.
///
/// Precondition: `supported_body(check)` returned `Ok(())`. Name follows
/// the reserved `_tactus_body_` prefix so it can't collide with a user
/// identifier (Rust doesn't emit names starting with `_tactus_`).
pub fn exec_fn_theorem_to_ast(fn_sst: &FunctionSst, check: &FuncCheckSst) -> Theorem {
    let mut binders: Vec<LBinder> = Vec::new();

    // Function params. Skip Verus-synthetic dummy params (names containing
    // `%`, e.g., `no%param` injected for zero-arg functions).
    for p in fn_sst.x.pars.iter() {
        if p.x.name.0.contains('%') { continue; }
        binders.push(LBinder {
            name: Some(sanitize(&p.x.name.0)),
            ty: typ_to_expr(&p.x.typ),
            kind: BinderKind::Explicit,
        });
    }

    // Requires → hypothesis params.
    for (i, req) in check.reqs.iter().enumerate() {
        binders.push(LBinder {
            name: Some(format!("h_req{}", i)),
            ty: sst_exp_to_ast(req),
            kind: BinderKind::Explicit,
        });
    }

    let (items, return_expr) = collect_body_items(&check.body);

    let goal = build_goal(
        &items,
        0,
        return_expr,
        check.post_condition.dest.as_ref().map(|v| v.0.as_str()),
        &check.post_condition.ens_exps,
    );

    Theorem {
        name: format!("_tactus_body_{}", lean_name(&fn_sst.x.name.path)),
        binders,
        goal,
        tactic: Tactic::Named("tactus_auto".to_string()),
    }
}

// ── Goal builder ───────────────────────────────────────────────────────

/// Construct the theorem goal by folding body items in source order. See
/// the module doc for the WP rules — each item wraps the goal built from
/// the remainder of the body.
fn build_goal(
    items: &[BodyItem<'_>],
    i: usize,
    return_expr: Option<&Exp>,
    ret_name: Option<&str>,
    ensures: &[Exp],
) -> LExpr {
    if i >= items.len() {
        return final_goal(return_expr, ret_name, ensures);
    }
    match &items[i] {
        BodyItem::Let(name, rhs) => LExpr::new(ExprNode::Let {
            name: sanitize(name),
            value: Box::new(sst_exp_to_ast(rhs)),
            body: Box::new(build_goal(items, i + 1, return_expr, ret_name, ensures)),
        }),
        BodyItem::Assume(e) => LExpr::new(ExprNode::BinOp {
            op: L::Implies,
            lhs: Box::new(sst_exp_to_ast(e)),
            rhs: Box::new(build_goal(items, i + 1, return_expr, ret_name, ensures)),
        }),
        BodyItem::Assert(e) => LExpr::new(ExprNode::BinOp {
            op: L::And,
            lhs: Box::new(sst_exp_to_ast(e)),
            rhs: Box::new(build_goal(items, i + 1, return_expr, ret_name, ensures)),
        }),
    }
}

/// Innermost goal: optional `let <ret> := <ret_expr>; <ensures_conj>`,
/// else just the ensures conjunction. Empty ensures → `True`.
fn final_goal(
    return_expr: Option<&Exp>,
    ret_name: Option<&str>,
    ensures: &[Exp],
) -> LExpr {
    let ens_conj = and_all(ensures.iter().map(|e| sst_exp_to_ast(e)).collect());
    match (return_expr, ret_name) {
        (Some(re), Some(name)) => LExpr::new(ExprNode::Let {
            name: sanitize(name),
            value: Box::new(sst_exp_to_ast(re)),
            body: Box::new(ens_conj),
        }),
        _ => ens_conj,
    }
}

// ── Body walk ──────────────────────────────────────────────────────────

enum BodyItem<'a> {
    Let(&'a str, &'a Exp),
    Assert(&'a Exp),
    Assume(&'a Exp),
}

fn collect_body_items<'a>(body: &'a Stm) -> (Vec<BodyItem<'a>>, Option<&'a Exp>) {
    let mut items = Vec::new();
    let mut ret = None;
    walk(body, &mut items, &mut ret);
    (items, ret)
}

fn walk<'a>(
    stm: &'a Stm,
    items: &mut Vec<BodyItem<'a>>,
    ret: &mut Option<&'a Exp>,
) {
    match &stm.x {
        StmX::Block(stms) => for s in stms.iter() { walk(s, items, ret); },
        StmX::Assign { lhs: Dest { dest, .. }, rhs } => {
            if let Some(name) = extract_simple_var(dest) {
                items.push(BodyItem::Let(name, rhs));
            }
        }
        StmX::Assert(_, _, e) | StmX::AssertCompute(_, e, _) => items.push(BodyItem::Assert(e)),
        StmX::Assume(e) => items.push(BodyItem::Assume(e)),
        StmX::Return { ret_exp: Some(e), .. } => { *ret = Some(e); }
        _ => {}
    }
}

fn extract_simple_var<'a>(e: &'a Exp) -> Option<&'a str> {
    match &e.x {
        ExpX::Var(ident) | ExpX::VarLoc(ident) => Some(ident.0.as_str()),
        ExpX::Loc(inner) => extract_simple_var(inner),
        _ => None,
    }
}
