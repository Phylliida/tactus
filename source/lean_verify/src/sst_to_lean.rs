//! Weakest-precondition VC generation from SST → Lean.
//!
//! Takes an exec fn's `FuncCheckSst` (from `FunctionSst::exec_proof_check`)
//! and emits a single Lean theorem checked with `by tactus_auto`.
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
//! Not yet supported: if/else (Slice 2), mutation/SSA (Slice 3), loops
//! (Slice 4), fixed-width overflow as a separate obligation (Slice 5),
//! pattern matching, closures, mutable references.
//!
//! # Semantic model (weakest-precondition, in body order)
//!
//! We walk statements in source order and nest each one into the goal:
//!
//! * `let x = e` becomes `let x := e; <rest>`, so later items see `x`.
//! * `assume(P)` becomes `(P) → <rest>`, so proofs of later obligations get
//!   `P` as a hypothesis.
//! * `assert(P)` becomes `(P) ∧ (<rest>)`. `P` must be provable *without*
//!   using assumes that appear *after* it — this is the crucial property
//!   that separates us from a naive "conjoin everything" scheme, which
//!   would let an `assume(P); assert(P)` (which Verus generates when you
//!   desugar a user `assert(P)`) trivially satisfy itself.
//! * `return e` ends the body; if the ensures references the return, we
//!   wrap the ensures in `let <ret_name> := e; <ensures_conj>`.
//!
//! So e.g. `let x = 5; assert(x > 0); return x` with ensures `r = 5` emits:
//!
//! ```lean
//! let x := 5
//! (x > 0) ∧ (let r := x; (r = 5))
//! ```
//!
//! Because ∧ binds tighter than →, the right-hand side of an Assert is
//! parenthesized. Let-bindings and implications don't need outer parens
//! thanks to right-associativity and Lean's let-binder grammar.

use vir::sst::{BndX, CallFun, Dest, Exp, ExpX, FuncCheckSst, FunctionSst, Stm, StmX};
use vir::ast::{BinaryOp, UnaryOp};
use crate::to_lean_sst_expr::write_sst_exp;
use crate::to_lean_type::{lean_name, write_typ};
use crate::to_lean_expr::write_name;

// ── Support check ──────────────────────────────────────────────────────
//
// Before generating any Lean text, we walk the whole `FuncCheckSst` and
// confirm every statement and every expression is something we know how to
// emit. If anything isn't, we return `Err(reason)` with a clear message —
// never panic mid-generation.

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
        // Transparent / internal
        StmX::Air(_) | StmX::Fuel(..) | StmX::RevealString(_) => Ok(()),
        // Known not-yet-supported forms with friendly names, rather than an
        // opaque "Discriminant(N)" that requires consulting sst.rs.
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

/// Walk an `Exp` recursively and reject forms that `write_sst_exp` would
/// panic on. Keeps generation-time in sync with support-check-time.
fn check_exp(e: &Exp) -> Result<(), String> {
    match &e.x {
        ExpX::Const(_) | ExpX::Var(_) | ExpX::VarLoc(_) | ExpX::VarAt(..)
        | ExpX::StaticVar(_) | ExpX::ExecFnByName(_) | ExpX::NullaryOpr(_) => Ok(()),

        ExpX::Unary(op, inner) => {
            match op {
                UnaryOp::Not
                | UnaryOp::Clip { .. }
                | UnaryOp::CoerceMode { .. }
                | UnaryOp::Trigger(_) => check_exp(inner),
                other => Err(format!("unsupported unary op: {:?}", other)),
            }
        }
        ExpX::UnaryOpr(_, inner) => check_exp(inner),

        ExpX::Binary(op, l, r) => {
            // Conservative whitelist: anything `binop_symbol` emits can
            // also be written, but some (HeightCompare, Index, IeeeFloat)
            // don't produce meaningful Lean. Reject those explicitly.
            match op {
                BinaryOp::HeightCompare { .. }
                | BinaryOp::Index(_, _)
                | BinaryOp::StrGetChar
                | BinaryOp::IeeeFloat(_) => {
                    Err(format!("unsupported binary op: {:?}", op))
                }
                _ => {
                    check_exp(l)?;
                    check_exp(r)
                }
            }
        }
        ExpX::BinaryOpr(_, l, r) => {
            check_exp(l)?;
            check_exp(r)
        }

        ExpX::If(c, t, e) => {
            check_exp(c)?;
            check_exp(t)?;
            check_exp(e)
        }

        ExpX::Call(target, _, args) => {
            if matches!(target, CallFun::InternalFun(_)) {
                return Err("internal function calls not yet supported".to_string());
            }
            for a in args.iter() { check_exp(a)?; }
            Ok(())
        }

        ExpX::Bind(bnd, body) => {
            match &bnd.x {
                BndX::Let(binders) => {
                    for b in binders.iter() { check_exp(&b.a)?; }
                }
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

// ── Theorem emission ───────────────────────────────────────────────────

/// Emit a `theorem _tactus_body_<fn_name> ... := by tactus_auto` for an exec fn.
///
/// Precondition: `supported_body(check)` returned `Ok(())`. Otherwise
/// `write_sst_exp` may panic on an unknown form; the support check exists
/// to catch those ahead of time.
///
/// The `_tactus_body_` prefix is reserved for Tactus use so it can't collide
/// with a user-defined name (Rust doesn't generate identifiers starting with
/// `_tactus_`).
pub fn write_exec_fn_theorem(
    out: &mut String,
    fn_sst: &FunctionSst,
    check: &FuncCheckSst,
) {
    out.push_str("theorem _tactus_body_");
    out.push_str(&lean_name(&fn_sst.x.name.path));

    // Function params. Skip Verus-synthetic dummy params (names containing `%`,
    // e.g., `no%param` injected for zero-arg functions) — they exist for SMT
    // reasons and have no place in the Lean theorem.
    for p in fn_sst.x.pars.iter() {
        if p.x.name.0.contains('%') { continue; }
        out.push_str(" (");
        write_name(out, &p.x.name.0);
        out.push_str(" : ");
        write_typ(out, &p.x.typ);
        out.push(')');
    }

    // Requires → hypothesis params
    for (i, req) in check.reqs.iter().enumerate() {
        out.push_str(" (h_req");
        write_subscript(out, i);
        out.push_str(" : ");
        write_sst_exp(out, req);
        out.push(')');
    }

    out.push_str(" :\n    ");

    let (items, return_expr) = collect_body_items(&check.body);

    emit_nested(
        out,
        &items,
        0,
        return_expr,
        check.post_condition.dest.as_ref().map(|v| v.0.as_str()),
        &check.post_condition.ens_exps,
    );

    out.push_str(" := by tactus_auto\n");

    // TODO: source mapping. Proof fns track the tactic's line number in the
    // generated Lean so diagnostics can point back at the user's `by { }`
    // block. Exec fns don't have a user-written tactic body, but when an
    // auto-obligation fails we should still be able to map Lean's error
    // position back to the Rust span that generated it. Requires emitting
    // Lean `show`-style breadcrumbs keyed to VIR spans.
}

// ── Goal emission (nested) ─────────────────────────────────────────────

/// Emit the theorem goal by nesting statement contributions in body order.
/// See the module doc for the WP rules.
fn emit_nested(
    out: &mut String,
    items: &[BodyItem<'_>],
    i: usize,
    return_expr: Option<&Exp>,
    ret_name: Option<&str>,
    ensures: &[Exp],
) {
    if i >= items.len() {
        emit_final_goal(out, return_expr, ret_name, ensures);
        return;
    }
    match &items[i] {
        BodyItem::Let(name, rhs) => {
            out.push_str("let ");
            write_name(out, name);
            out.push_str(" := ");
            write_sst_exp(out, rhs);
            out.push_str("\n    ");
            emit_nested(out, items, i + 1, return_expr, ret_name, ensures);
        }
        BodyItem::Assume(e) => {
            // `→` is right-associative and binds looser than `∧`, so no
            // outer parens are needed around the rest.
            out.push('(');
            write_sst_exp(out, e);
            out.push_str(") → ");
            emit_nested(out, items, i + 1, return_expr, ret_name, ensures);
        }
        BodyItem::Assert(e) => {
            // `∧` binds tighter than `→`, so wrap the rest in parens to
            // keep `P ∧ (Q → R)` from being misread as `(P ∧ Q) → R`.
            out.push('(');
            write_sst_exp(out, e);
            out.push_str(") ∧ (");
            emit_nested(out, items, i + 1, return_expr, ret_name, ensures);
            out.push(')');
        }
    }
}

/// Emit the innermost goal: `let <ret> := <ret_expr>; <ensures_conj>` if the
/// ensures references the return value; otherwise just the ensures.
fn emit_final_goal(
    out: &mut String,
    return_expr: Option<&Exp>,
    ret_name: Option<&str>,
    ensures: &[Exp],
) {
    if let (Some(ret_exp), Some(name)) = (return_expr, ret_name) {
        out.push_str("let ");
        write_name(out, name);
        out.push_str(" := ");
        write_sst_exp(out, ret_exp);
        out.push_str("\n    ");
    }
    if ensures.is_empty() {
        out.push_str("True");
        return;
    }
    for (i, e) in ensures.iter().enumerate() {
        if i > 0 { out.push_str(" ∧ "); }
        out.push('(');
        write_sst_exp(out, e);
        out.push(')');
    }
}

// ── Body walk ──────────────────────────────────────────────────────────

/// A single statement-level item contributing to the theorem goal.
enum BodyItem<'a> {
    /// Straight-line let binding from a `StmX::Assign` onto a simple variable.
    Let(&'a str, &'a Exp),
    /// User or auto-generated assertion; becomes an obligation in the goal.
    Assert(&'a Exp),
    /// User or auto-generated assumption; becomes an implication in the goal.
    Assume(&'a Exp),
}

/// Walk a straight-line body and split it into let/assert/assume items plus
/// the final return expression (at most one).
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
        StmX::Block(stms) => {
            for s in stms.iter() { walk(s, items, ret); }
        }
        StmX::Assign { lhs: Dest { dest, .. }, rhs } => {
            if let Some(name) = extract_simple_var(dest) {
                items.push(BodyItem::Let(name, rhs));
            }
            // Non-simple LHS (e.g., field assignments, index stores) aren't
            // in the first slice; `check_stm` already rejected them above.
        }
        StmX::Assert(_, _, e) | StmX::AssertCompute(_, e, _) => items.push(BodyItem::Assert(e)),
        StmX::Assume(e) => items.push(BodyItem::Assume(e)),
        StmX::Return { ret_exp: Some(e), .. } => { *ret = Some(e); }
        StmX::Return { ret_exp: None, .. } => {}
        _ => {}
    }
}

/// If `e` is a simple variable reference (`Var`, `VarLoc`, or `Loc(Var)`),
/// return its name. Otherwise `None`.
fn extract_simple_var<'a>(e: &'a Exp) -> Option<&'a str> {
    match &e.x {
        ExpX::Var(ident) | ExpX::VarLoc(ident) => Some(ident.0.as_str()),
        ExpX::Loc(inner) => extract_simple_var(inner),
        _ => None,
    }
}

// ── Small helpers ──────────────────────────────────────────────────────

/// Write a non-negative integer compactly, avoiding an allocation for the
/// common case of one-digit numbers.
fn write_subscript(out: &mut String, n: usize) {
    if n < 10 { out.push((b'0' + n as u8) as char); }
    else { out.push_str(&n.to_string()); }
}

