//! Nat-coercion insertion (BUG-as-nat-cast.md + BUG-ch5-pow-iter F2).
//!
//! At every `Call` site, insert `Clip { range: Nat }` around args whose
//! Lean type renders as `Int` but whose corresponding callee param
//! renders as `Nat`. Closes the bug where `f(i as nat)` for `i : u64`
//! lowered to `f i` in Lean (Int → Nat type mismatch) because Verus's
//! `fn_call_to_vir.rs` drops `U(_)/USize → Nat` casts as no-ops.
//!
//! The no-op is sound for Z3 (which sees both u_N and nat as `Int` with
//! refinements), but unsound for Lean (distinct types). We can't always-
//! emit Clip in Verus because 7 vstd bit-shift lemmas rely on Z3 silently
//! equating `x` and `clip(Nat, x)` for u-typed x — adding Clip globally
//! breaks their calc-style proofs. So we run a Tactus-side normalization
//! pass that operates only on Lean-bound code.
//!
//! **Pattern.** This is the fourth Tactus-side normalization (sibling
//! to the unified `rewrite_mut_ref_in_*` pass — the collapse of #94's
//! `rewrite_varat_for_mut_params` and #95's `normalize_mut_ref` —
//! plus #127's original_cond recovery in build_wp_loop): Verus's pipeline
//! produces a shape that's right for SMT but wrong for Lean, so we fix
//! it up at fn entry before rendering.
//!
//! **Cases (`needs_nat_coercion`):**
//!   * U(_)/I(_)/ISize/Int (renders as Lean Int) → Nat/USize/Char
//!     (renders as Lean Nat): insert Clip(Nat). This is the bug fix
//!     surface — primarily `u_N → nat`.
//!   * USize/Char/Nat (renders as Nat) → Nat: skip — both already
//!     render as Nat, no Lean-level coercion needed.
//!   * Same-side or non-Int types: skip.
//!
//! Cross-crate callees aren't in `fn_map`; we skip those (the call
//! would hit cross-crate rejection downstream regardless). Mismatched
//! arity also short-circuits — defensive against trait-method shapes
//! where Verus's resolution may produce arg/param count divergence.

use std::sync::Arc;

use vir::ast::{CallTarget, Expr, ExprX, IntRange, SpannedTyped, Typ, TypX, UnaryOp};
use vir::ast_visitor::map_expr_visitor;
use vir::sst::{CallFun, Exp, ExpX, Stm};

use crate::sst_to_lean::FnMap;
use crate::to_lean_sst_expr::renders_as_lean_int;

pub(crate) fn insert_nat_coercions_in_exp(exp: &Exp, fn_map: &FnMap) -> Exp {
    vir::sst_visitor::map_exp_visitor(exp, &mut |e: &Exp| {
        rewrite_one_call_for_coercions(e, fn_map)
    })
}

pub(crate) fn insert_nat_coercions_in_stm(stm: &Stm, fn_map: &FnMap) -> Stm {
    vir::sst_visitor::map_exps_in_stm_visitor(stm, &mut |e: &Exp| {
        rewrite_one_call_for_coercions(e, fn_map)
    })
}

/// SST leaf rewrite for the nat-coercion pass. At a Call node, look up
/// the callee in `fn_map` and wrap each arg that needs `Int.toNat`
/// coercion in a synthetic `Clip { range: Nat }` node.
fn rewrite_one_call_for_coercions(e: &Exp, fn_map: &FnMap) -> Exp {
    match &e.x {
        ExpX::Call(callfun, typs, args) => {
            // Only direct Fun calls (and self-recursion) have a Fun we can
            // look up in fn_map. InternalFun calls (CheckDecreaseHeight etc.)
            // don't apply.
            let fun = match callfun {
                CallFun::Fun(f, _) | CallFun::Recursive(f) => f,
                CallFun::InternalFun(_) => return e.clone(),
            };
            let Some(callee) = fn_map.get(fun) else {
                // Cross-crate or otherwise unknown callee.
                return e.clone();
            };
            if callee.params.len() != args.len() {
                // Arity mismatch — bail; the renderer will surface a real
                // mismatch as a Lean elaboration error if there is one.
                return e.clone();
            }
            let new_args: Vec<Exp> = args.iter().zip(callee.params.iter())
                .map(|(arg, param)| coerce_arg_to_nat_exp(arg, &param.x.typ))
                .collect();
            SpannedTyped::new(
                &e.span,
                &e.typ,
                ExpX::Call(callfun.clone(), typs.clone(), Arc::new(new_args)),
            )
        }
        // Consistent `as nat` materialization for arithmetic operands.
        // Verus keeps a nat-typed arith op's `IntRange` (`a * b : nat`)
        // even when it ELIDES the operands' `uN -> nat` casts (a bare
        // `x as nat` drops to `x : U(64)`, but the surrounding `Mul` stays
        // `IntRange Nat`). In Lean `U(_)` renders `Int` and `nat` renders
        // `Nat` — distinct types — so an Int-rendering operand under a
        // nat-typed op needs the `Int.toNat` the cast would have produced.
        // The op's own result type (`e.typ`) IS the operand type for arith
        // ops, so it's the coercion target. This makes `(x as nat) * pow(…)`
        // render `Int.toNat x * pow …` uniformly with the compound/call-arg
        // cases (which Verus already materializes as `Clip{Nat}`). Only
        // fires for nat-ranged ops (an `IntRange Int`/`U(_)` op no-ops via
        // `needs_nat_coercion`). See DECISION-cast-rendering.md.
        ExpX::Binary(op, lhs, rhs) if matches!(op, vir::ast::BinaryOp::Arith(_)) => {
            let new_lhs = coerce_arg_to_nat_exp(lhs, &e.typ);
            let new_rhs = coerce_arg_to_nat_exp(rhs, &e.typ);
            SpannedTyped::new(&e.span, &e.typ, ExpX::Binary(op.clone(), new_lhs, new_rhs))
        }
        _ => e.clone(),
    }
}

/// VIR-AST counterpart of `insert_nat_coercions_in_exp` — applies to
/// proof fn `require`/`ensure` and spec fn bodies that route through
/// the VIR-AST renderer (`vir_expr_to_ast`).
pub fn insert_nat_coercions_in_expr(expr: &Expr, fn_map: &FnMap) -> Expr {
    map_expr_visitor(expr, &|e: &Expr| {
        Ok(rewrite_one_call_for_coercions_expr(e, fn_map))
    })
    // Leaf only constructs valid Call/Clip nodes — cannot error.
    .expect("nat-coercion rewrite is structural")
}

fn rewrite_one_call_for_coercions_expr(e: &Expr, fn_map: &FnMap) -> Expr {
    match &e.x {
        ExprX::Call(target, args, extra) => {
            let CallTarget::Fun(_, fun, _, _, _, _) = target else { return e.clone() };
            let Some(callee) = fn_map.get(fun) else {
                return e.clone();
            };
            if callee.params.len() != args.len() {
                return e.clone();
            }
            let new_args: Vec<Expr> = args.iter().zip(callee.params.iter())
                .map(|(arg, param)| coerce_arg_to_nat_expr(arg, &param.x.typ))
                .collect();
            SpannedTyped::new(
                &e.span,
                &e.typ,
                ExprX::Call(target.clone(), Arc::new(new_args), extra.clone()),
            )
        }
        // Consistent `as nat` materialization for arithmetic operands —
        // VIR-AST twin of the SST arm in `rewrite_one_call_for_coercions`.
        // A nat-typed arith op gets any Int-rendering operand wrapped in
        // `Clip{Nat}`. See that arm's comment + DECISION-cast-rendering.md.
        ExprX::Binary(op, lhs, rhs) if matches!(op, vir::ast::BinaryOp::Arith(_)) => {
            let new_lhs = coerce_arg_to_nat_expr(lhs, &e.typ);
            let new_rhs = coerce_arg_to_nat_expr(rhs, &e.typ);
            SpannedTyped::new(&e.span, &e.typ, ExprX::Binary(op.clone(), new_lhs, new_rhs))
        }
        _ => e.clone(),
    }
}

/// True when `arg_typ` renders as Lean `Int` but `param_typ` renders as
/// Lean `Nat` — the case where Tactus needs to wrap the arg in a
/// `Clip { range: Nat }` node so the renderer emits `Int.toNat`.
///
/// Both types must be `TypX::Int(_)` after peeling transparent wrappers
/// (`Boxed`, `Decorate`); non-int types fall through (the renderer
/// handles them directly). Peeling matches what `typ_to_expr` does at
/// rendering time — so the predicate's view of "renders as Int/Nat" is
/// aligned with what the renderer would actually emit.
fn needs_nat_coercion(arg_typ: &Typ, param_typ: &Typ) -> bool {
    let arg_peeled = crate::to_lean_type::peel_typ_wrappers(arg_typ);
    let param_peeled = crate::to_lean_type::peel_typ_wrappers(param_typ);
    let TypX::Int(arg_range) = &**arg_peeled else { return false };
    let TypX::Int(param_range) = &**param_peeled else { return false };
    renders_as_lean_int(arg_range) && !renders_as_lean_int(param_range)
}

/// Build a synthetic `Clip { range: Nat }` node wrapping `arg`. Same
/// shape Verus's `mk_ty_clip` would have produced if `fn_call_to_vir.rs`
/// hadn't taken the no-op shortcut for U/USize → Nat casts.
fn wrap_in_nat_clip_exp(arg: &Exp) -> Exp {
    let clip_op = UnaryOp::Clip { range: IntRange::Nat, truncate: true };
    let nat_typ: Typ = Arc::new(TypX::Int(IntRange::Nat));
    SpannedTyped::new(&arg.span, &nat_typ, ExpX::Unary(clip_op, arg.clone()))
}

fn wrap_in_nat_clip_expr(arg: &Expr) -> Expr {
    let clip_op = UnaryOp::Clip { range: IntRange::Nat, truncate: true };
    let nat_typ: Typ = Arc::new(TypX::Int(IntRange::Nat));
    SpannedTyped::new(&arg.span, &nat_typ, ExprX::Unary(clip_op, arg.clone()))
}

/// Nat-coercion leaf: wrap `arg` in `Clip{Nat}` when it renders as Lean
/// `Int` but `target_typ` renders as `Nat`, else pass through unchanged.
fn coerce_arg_to_nat_exp(arg: &Exp, target_typ: &Typ) -> Exp {
    if needs_nat_coercion(&arg.typ, target_typ) {
        wrap_in_nat_clip_exp(arg)
    } else {
        arg.clone()
    }
}

/// VIR-AST twin of `coerce_arg_to_nat_exp`.
fn coerce_arg_to_nat_expr(arg: &Expr, target_typ: &Typ) -> Expr {
    if needs_nat_coercion(&arg.typ, target_typ) {
        wrap_in_nat_clip_expr(arg)
    } else {
        arg.clone()
    }
}
