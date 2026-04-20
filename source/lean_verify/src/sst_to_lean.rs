//! Weakest-precondition VC generation from SST → Lean AST.
//!
//! Takes an exec fn's `FuncCheckSst` (from `FunctionSst::exec_proof_check`)
//! and produces a `Theorem` AST node whose goal is the WP of the body and
//! whose tactic body is `tactus_auto`.
//!
//! # Current scope
//!
//! Handles bodies built from:
//!
//!   * `StmX::Block`     — nested/sequential composition
//!   * `StmX::Assign`    — simple-LHS `let x := e` bindings; non-simple
//!                         LHS (field writes, etc.) is rejected upfront
//!   * `StmX::Assert`    — obligations, conjoined into the goal
//!   * `StmX::Assume`    — hypotheses, threaded into the goal as implications
//!   * `StmX::If`        — branching; WP splits across `cond` / `¬cond`
//!   * `StmX::Return`    — terminator (works at top level and inside a
//!                         branch; `inside_body: true` is rejected)
//!   * `StmX::Air`, `StmX::Fuel`, `StmX::RevealString` — transparent
//!
//! Not yet supported: loops, pattern matching, closures, mutable
//! references (`&mut`). Fixed-width arithmetic overflow IS checked,
//! but via `HasType` assertions folded into the body WP — not via
//! separate per-op theorems.
//!
//! # Mutation
//!
//! Simple mutation (`let mut x = …; x = …;`) needs no rename pass:
//! `StmX::Assign { is_init: false }` emits `let x := e` just like an
//! init, and Lean's let-shadowing gives us SSA semantics naturally.
//! This also works across if-branches — an inner branch's `let x := …`
//! only shadows within its implication, so the outer `x` remains in
//! scope for the other branch and the code after the if. Loops break
//! this trick because the loop body's mutations can't tunnel out
//! through shadowing; they'll need a real rename pass when we get
//! there.
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
//! * `if c { s₁ } else { s₂ }` becomes
//!   `(c → wp(s₁; <rest>)) ∧ (¬c → wp(s₂; <rest>))`. Both branches share
//!   the same continuation; we duplicate `<rest>` syntactically rather
//!   than let-binding a shared goal.
//! * `return e` is a terminator: it wraps the ensures as `let <ret> :=
//!   e; <ensures>` and any items after it in the same sequence are
//!   unreachable and dropped. Works for both tail returns and for
//!   early returns inside an `if` branch (the branch's continuation
//!   ends at the return; the outer `rest` never gets appended past it).
//!
//! The AST pretty-printer handles precedence, so constructors just build
//! `BinOp::And` / `BinOp::Implies` / `UnOp::Not` / `Let` without worrying
//! about parens.

use vir::sst::{BndX, CallFun, Dest, Exp, ExpX, FuncCheckSst, FunctionSst, Par, Stm, StmX};
use vir::ast::{BinaryOp, UnaryOp};
use crate::lean_ast::{
    and_all, BinOp as L, Binder as LBinder, BinderKind, Expr as LExpr, ExprNode, Tactic, Theorem,
    UnOp as LU,
};
use crate::to_lean_sst_expr::{sst_exp_to_ast, type_bound_predicate};
use crate::to_lean_type::{lean_name, sanitize, typ_to_expr};

// ── Support check ──────────────────────────────────────────────────────
//
// Before building any AST, we walk the whole `FuncCheckSst` and confirm
// every statement and every expression is something we know how to emit.

/// Confirm the function's body, requires, and ensures only use SST forms
/// that `sst_to_lean` currently knows how to emit.
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
            // `walk` can only turn simple-var LHS assignments into
            // `let` bindings; anything fancier (field writes, index
            // writes, tuple destructure) would be silently dropped,
            // which is a soundness hazard. Reject upfront so the
            // user sees a clear "not yet supported" instead of a
            // spurious pass.
            if extract_simple_var(dest).is_none() {
                return Err(format!(
                    "assignment with non-simple LHS (got {:?}) is not yet supported",
                    dest.x
                ));
            }
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
        StmX::If(cond, then_stm, else_stm) => {
            check_exp(cond)?;
            check_stm(then_stm)?;
            if let Some(e) = else_stm { check_stm(e)?; }
            Ok(())
        }
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

    // Each real param contributes one binder — `(name : T)` — and, for
    // fixed-width integer types, one hypothesis binder right after —
    // `(h_<name>_bound : <predicate>)`. Interleaving is fine because
    // each hypothesis only references its own immediately preceding
    // param.
    for p in fn_sst.x.pars.iter().filter(|p| !is_synthetic_param(p)) {
        let name = sanitize(&p.x.name.0);
        binders.push(LBinder {
            name: Some(name.clone()),
            ty: typ_to_expr(&p.x.typ),
            kind: BinderKind::Explicit,
        });
        if let Some(pred) = type_bound_predicate(
            &LExpr::new(ExprNode::Var(name.clone())),
            &p.x.typ,
        ) {
            binders.push(LBinder {
                name: Some(format!("h_{}_bound", name)),
                ty: pred,
                kind: BinderKind::Explicit,
            });
        }
    }

    // Requires → hypothesis params.
    for (i, req) in check.reqs.iter().enumerate() {
        binders.push(LBinder {
            name: Some(format!("h_req{}", i)),
            ty: sst_exp_to_ast(req),
            kind: BinderKind::Explicit,
        });
    }

    let items = collect_body_items(&check.body);

    let goal = build_goal(
        &items,
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
/// the remainder of the body. `Return` terminates: items after it are
/// dropped because they're unreachable.
fn build_goal(
    items: &[BodyItem<'_>],
    ret_name: Option<&str>,
    ensures: &[Exp],
) -> LExpr {
    let Some((head, rest)) = items.split_first() else {
        return final_goal(None, ret_name, ensures);
    };
    match head {
        BodyItem::Let(name, rhs) => LExpr::new(ExprNode::Let {
            name: sanitize(name),
            value: Box::new(sst_exp_to_ast(rhs)),
            body: Box::new(build_goal(rest, ret_name, ensures)),
        }),
        BodyItem::Assume(e) => LExpr::new(ExprNode::BinOp {
            op: L::Implies,
            lhs: Box::new(sst_exp_to_ast(e)),
            rhs: Box::new(build_goal(rest, ret_name, ensures)),
        }),
        BodyItem::Assert(e) => LExpr::new(ExprNode::BinOp {
            op: L::And,
            lhs: Box::new(sst_exp_to_ast(e)),
            rhs: Box::new(build_goal(rest, ret_name, ensures)),
        }),
        BodyItem::Return(e) => final_goal(Some(e), ret_name, ensures),
        BodyItem::IfThenElse { cond, then_items, else_items } => {
            // WP: (c → wp(then ++ rest)) ∧ (¬c → wp(else ++ rest)).
            // `rest` duplicates syntactically — we don't share goals via
            // a named let-binding. Exponential in nesting depth (see
            // DESIGN.md "Known codegen-complexity trade-offs"), but Lean
            // / Z3 see the same logical goal either way. If either branch
            // ends with `Return`, its continuation naturally terminates
            // there and `rest` is appended but ignored.
            let then_all: Vec<BodyItem<'_>> =
                then_items.iter().chain(rest.iter()).cloned().collect();
            let else_all: Vec<BodyItem<'_>> =
                else_items.iter().chain(rest.iter()).cloned().collect();
            let cond_ast = sst_exp_to_ast(cond);
            let not_cond = LExpr::new(ExprNode::UnOp {
                op: LU::Not,
                arg: Box::new(cond_ast.clone()),
            });
            let then_goal = build_goal(&then_all, ret_name, ensures);
            let else_goal = build_goal(&else_all, ret_name, ensures);
            let then_branch = LExpr::new(ExprNode::BinOp {
                op: L::Implies,
                lhs: Box::new(cond_ast),
                rhs: Box::new(then_goal),
            });
            let else_branch = LExpr::new(ExprNode::BinOp {
                op: L::Implies,
                lhs: Box::new(not_cond),
                rhs: Box::new(else_goal),
            });
            LExpr::new(ExprNode::BinOp {
                op: L::And,
                lhs: Box::new(then_branch),
                rhs: Box::new(else_branch),
            })
        }
    }
}

/// Innermost goal: the ensures conjunction, optionally preceded by a
/// `let <ret> := <ret_expr>;` binding so the ensures can reference the
/// returned value by name. Empty ensures → `True`.
///
/// The four `(return_expr, ret_name)` cases:
///
///   * `(Some(re), Some(name))` — non-unit fn with a reachable `Return`:
///     bind then check ensures. This is the common shape.
///   * `(None, Some(name))` — the return value was bound earlier via an
///     `Assign` (typical "fn foo() -> T { let r := e; r }" pattern); the
///     name is already in scope.
///   * `(None, None)` — unit-returning fn (or one without ensures
///     referencing a return).
///   * `(Some(re), None)` — a `return` carrying a value but no named
///     destination. This happens when Rust desugars `return;` to
///     `return ()` in a unit-returning fn. `re` is unit in that case;
///     dropping it is correct since there's no name to bind it to.
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
        (None, Some(_)) | (None, None) | (Some(_), None) => ens_conj,
    }
}

// ── Body walk ──────────────────────────────────────────────────────────

#[derive(Clone)]
enum BodyItem<'a> {
    Let(&'a str, &'a Exp),
    Assert(&'a Exp),
    Assume(&'a Exp),
    /// Terminator: wraps the ensures as `let <ret> := e; <ensures>` and
    /// discards any subsequent items in the same sequence. Populated
    /// from `StmX::Return { ret_exp: Some(_), inside_body: false }`.
    Return(&'a Exp),
    /// `if <cond> { <then_items> } else { <else_items> }` — both branches
    /// are already flattened into `BodyItem` sequences. Either branch
    /// may end with a `Return` (handled by `build_goal`).
    IfThenElse {
        cond: &'a Exp,
        then_items: Vec<BodyItem<'a>>,
        else_items: Vec<BodyItem<'a>>,
    },
}

fn collect_body_items<'a>(body: &'a Stm) -> Vec<BodyItem<'a>> {
    let mut items = Vec::new();
    walk(body, &mut items);
    items
}

fn walk<'a>(stm: &'a Stm, items: &mut Vec<BodyItem<'a>>) {
    match &stm.x {
        StmX::Block(stms) => for s in stms.iter() { walk(s, items); },
        StmX::Assign { lhs: Dest { dest, .. }, rhs } => {
            if let Some(name) = extract_simple_var(dest) {
                items.push(BodyItem::Let(name, rhs));
            }
        }
        StmX::Assert(_, _, e) | StmX::AssertCompute(_, e, _) => items.push(BodyItem::Assert(e)),
        StmX::Assume(e) => items.push(BodyItem::Assume(e)),
        // `Return { ret_exp: Some, inside_body: false }` is the normal
        // case — a tail return either at top level or ending a branch.
        // `ret_exp: None` is a unit return with no value to bind; skip.
        StmX::Return { ret_exp: Some(e), .. } => items.push(BodyItem::Return(e)),
        StmX::Return { ret_exp: None, .. } => {}
        StmX::If(cond, then_stm, else_stm) => {
            let mut then_items = Vec::new();
            walk(then_stm, &mut then_items);
            let mut else_items = Vec::new();
            if let Some(e) = else_stm {
                walk(e, &mut else_items);
            }
            items.push(BodyItem::IfThenElse { cond, then_items, else_items });
        }
        // Transparent in SST: contribute nothing to the WP goal.
        StmX::Air(_) | StmX::Fuel(..) | StmX::RevealString(_) => {}
        // These all fail `check_stm`. Reaching them here means the
        // support-check and the walker fell out of sync.
        StmX::Call { .. }
        | StmX::BreakOrContinue { .. }
        | StmX::AssertBitVector { .. }
        | StmX::AssertQuery { .. }
        | StmX::DeadEnd(_)
        | StmX::OpenInvariant(_)
        | StmX::ClosureInner { .. }
        | StmX::Loop { .. } => {
            unreachable!(
                "sst_to_lean::walk: {:?} should have been rejected by supported_body",
                stm.x
            )
        }
    }
}

fn extract_simple_var<'a>(e: &'a Exp) -> Option<&'a str> {
    match &e.x {
        ExpX::Var(ident) | ExpX::VarLoc(ident) => Some(ident.0.as_str()),
        ExpX::Loc(inner) => extract_simple_var(inner),
        _ => None,
    }
}

/// Verus injects synthetic params (`no%param`, etc.) with `%` in the
/// name for zero-arg functions and a few internal cases. They have no
/// user-visible semantics and must be dropped from the theorem binders.
fn is_synthetic_param(p: &Par) -> bool {
    p.x.name.0.contains('%')
}
