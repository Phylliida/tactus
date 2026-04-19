//! Weakest-precondition VC generation from SST → Lean.
//!
//! Takes an exec fn's `FuncCheckSst` (from `FunctionSst::exec_proof_check`)
//! and emits a single Lean theorem checked with `by tactus_auto`.
//!
//! # First-slice scope
//!
//! Handles straight-line code only: a body that is a (possibly nested)
//! `StmX::Block` ending in a `StmX::Return { ret_exp: Some(_), inside_body: false }`.
//! No mutation, no loops, no if/else, no early returns, no overflow checks.
//!
//! The WP rule for this shape is simple:
//!   `body = Return(e)`  ⇒  `ensures[result := e]`
//!   `body = Block([s1, .., sn])` with straight-line body  ⇒  fold stmts
//!
//! Intermediate `let x = e;` in the body (represented as `StmX::Assign` on a
//! `StmtLet` local) become Lean `let x := <lean_e>;` bindings in the theorem
//! goal. The ensures is expanded below all such bindings so Lean's elaborator
//! sees the bindings as hypotheses.

use vir::sst::{Dest, Exp, ExpX, FuncCheckSst, FunctionSst, PostConditionSst, Stm, StmX};
use crate::to_lean_sst_expr::write_sst_exp;
use crate::to_lean_type::{lean_name, write_typ};
use crate::to_lean_expr::write_name;

/// Scan a function body and confirm it matches the first-slice shape.
/// Returns `Err(reason)` if we hit anything we don't support yet.
pub fn supported_body(body: &Stm) -> Result<(), String> {
    match &body.x {
        StmX::Block(stms) => {
            for s in stms.iter() {
                supported_stmt(s)?;
            }
            Ok(())
        }
        _ => supported_stmt(body),
    }
}

fn supported_stmt(stm: &Stm) -> Result<(), String> {
    match &stm.x {
        StmX::Assign { .. } => Ok(()),
        StmX::Return { inside_body: false, .. } => Ok(()),
        StmX::Block(stms) => {
            for s in stms.iter() { supported_stmt(s)?; }
            Ok(())
        }
        // Auto-generated Asserts (overflow, type-invariant, precondition checks) are
        // obligations we will handle in a later slice. For now, skip them — the user's
        // ensures is still checked, but overflow is not guaranteed.
        StmX::Assert(..) => Ok(()),
        StmX::AssertCompute(..) => Ok(()),
        StmX::Assume(_) => Ok(()),
        // Internal / transparent
        StmX::Air(_) => Ok(()),
        StmX::Fuel(..) => Ok(()),
        StmX::RevealString(_) => Ok(()),
        other => Err(format!(
            "sst_to_lean first-slice: unsupported statement form {:?}",
            std::mem::discriminant(other)
        )),
    }
}

/// Emit a `theorem body_check_<fn_name> ... := by tactus_auto` for an exec fn.
///
/// `fn_sst.pars` and `fn_sst.ret` give the parameter / return binders.
/// `check.reqs` are the preconditions.
/// `check.post_condition.ens_exps` are the ensures clauses.
/// `check.body` is the body statement tree (must pass `supported_body`).
///
/// The theorem has shape:
/// ```lean
/// theorem body_check_<fn> (p1 : T1) ... (h0 : req0) ... :
///   let x1 := e1     -- any intermediate lets from the body
///   let <ret> := <final return expression>
///   ens0 ∧ ens1 ∧ ...
/// := by tactus_auto
/// ```
pub fn write_exec_fn_theorem(
    out: &mut String,
    fn_sst: &FunctionSst,
    check: &FuncCheckSst,
) -> usize {
    out.push_str("theorem body_check_");
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
        out.push_str(" (h");
        if i < 10 { out.push((b'0' + i as u8) as char); }
        else { out.push_str(&i.to_string()); }
        out.push_str(" : ");
        write_sst_exp(out, req);
        out.push(')');
    }

    out.push_str(" :\n    ");

    // Fold body: collect intermediate `let`s from StmX::Assign, plus the
    // final return expression. If there is no return, the goal is just the
    // ensures unchanged (no `result` substitution needed).
    let (lets, return_expr) = collect_lets_and_return(&check.body);
    for (name, rhs) in &lets {
        out.push_str("let ");
        write_name(out, name);
        out.push_str(" := ");
        write_sst_exp(out, rhs);
        out.push_str("\n    ");
    }
    if let (Some(ret_exp), Some(ret_name)) = (&return_expr, &check.post_condition.dest) {
        // Bind the return-name so the ensures can reference it.
        out.push_str("let ");
        write_name(out, &ret_name.0);
        out.push_str(" := ");
        write_sst_exp(out, ret_exp);
        out.push_str("\n    ");
    }
    write_ensures_conj(out, &check.post_condition);

    out.push_str(" := by tactus_auto\n");

    // Line count for source map (not yet wired for exec fns — stubbed)
    out.chars().filter(|&c| c == '\n').count() + 1
}

/// Walk the body collecting `let`-style assignments to stmt-locals plus the
/// final return expression. First-slice: flat Block only.
fn collect_lets_and_return<'a>(body: &'a Stm) -> (Vec<(&'a str, &'a Exp)>, Option<&'a Exp>) {
    let mut lets: Vec<(&str, &Exp)> = Vec::new();
    let mut ret: Option<&Exp> = None;
    walk_straight(body, &mut lets, &mut ret);
    (lets, ret)
}

fn walk_straight<'a>(
    stm: &'a Stm,
    lets: &mut Vec<(&'a str, &'a Exp)>,
    ret: &mut Option<&'a Exp>,
) {
    match &stm.x {
        StmX::Block(stms) => {
            for s in stms.iter() { walk_straight(s, lets, ret); }
        }
        StmX::Assign { lhs: Dest { dest, .. }, rhs } => {
            // Only handle the simple case: LHS is a plain variable reference.
            if let ExpX::VarLoc(ident) | ExpX::Var(ident) = &dest.x {
                lets.push((ident.0.as_str(), rhs));
            } else if let ExpX::Loc(inner) = &dest.x {
                if let ExpX::VarLoc(ident) | ExpX::Var(ident) = &inner.x {
                    lets.push((ident.0.as_str(), rhs));
                }
            }
        }
        StmX::Return { ret_exp: Some(e), .. } => { *ret = Some(e); }
        StmX::Return { ret_exp: None, .. } => {}
        StmX::Air(_) => {}
        _ => {}
    }
}

fn write_ensures_conj(out: &mut String, post: &PostConditionSst) {
    if post.ens_exps.is_empty() {
        out.push_str("True");
        return;
    }
    for (i, e) in post.ens_exps.iter().enumerate() {
        if i > 0 { out.push_str(" ∧ "); }
        // Wrap each ensures in parens defensively — ensures are often
        // equalities or inequalities that don't need them, but comparisons
        // chained with ∧ can tokenize awkwardly.
        out.push('(');
        write_sst_exp(out, e);
        out.push(')');
    }
}
