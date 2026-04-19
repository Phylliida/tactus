//! Translate SST expressions (`sst::Exp`) to Lean 4 expression syntax.
//!
//! Parallel to `to_lean_expr.rs` which operates on VIR-AST `Expr`.
//! SST is a cleaned-up AST (no statements inside expressions), used as the
//! input to weakest-precondition generation for exec fns (`sst_to_lean.rs`).
//!
//! First-slice scope: constants, variables, arithmetic/comparison/bool
//! binary ops, Clip/Not unary ops, if-then-else, let bindings, and static
//! calls. Unsupported forms panic with a clear message so gaps are caught
//! during development rather than producing silent garbage.
//!
//! Shares type translation with the VIR writer via `to_lean_type`.

use vir::ast::*;
use vir::sst::{BndX, CallFun, Exp, ExpX};
use crate::to_lean_common::{
    binop_prec, binop_symbol, write_const,
    PREC_ATOM, PREC_CMP, PREC_MUL,
};
use crate::to_lean_expr::write_name;
use crate::to_lean_type::{write_typ, lean_name};

fn expx_prec(e: &ExpX) -> u8 {
    match e {
        ExpX::Const(_) | ExpX::Var(_) | ExpX::VarLoc(_) | ExpX::VarAt(..) => PREC_ATOM,
        ExpX::Call(_, _, args) => if args.is_empty() { PREC_ATOM } else { 0 },
        ExpX::Binary(op, _, _) => binop_prec(op),
        ExpX::Unary(..) => PREC_MUL + 1,
        _ => 0,
    }
}

/// Write an SST expression as Lean 4 syntax.
pub fn write_sst_exp(out: &mut String, e: &Exp) {
    match &e.x {
        ExpX::Const(c) => write_const(out, c),
        ExpX::Var(ident) | ExpX::VarLoc(ident) => write_name(out, &ident.0),
        ExpX::VarAt(ident, _) => write_name(out, &ident.0),

        ExpX::Unary(UnaryOp::Not, inner) => {
            out.push('¬');
            write_prec(out, inner, PREC_ATOM, true);
        }

        ExpX::Unary(UnaryOp::Clip { range, .. }, inner) => {
            // Int → Nat requires explicit toNat; all other clips are identity
            // in spec mode (Nat ↪ Int is implicit in Lean).
            let src_is_int = matches!(&*inner.typ, TypX::Int(
                IntRange::Int | IntRange::I(_) | IntRange::ISize
            ));
            let dst_is_nat = matches!(range,
                IntRange::Nat | IntRange::U(_) | IntRange::USize | IntRange::Char
            );
            if src_is_int && dst_is_nat {
                out.push_str("Int.toNat ");
                write_prec(out, inner, PREC_ATOM, true);
            } else {
                write_sst_exp(out, inner);
            }
        }

        // Transparent unary ops
        ExpX::Unary(UnaryOp::CoerceMode { .. }, inner)
        | ExpX::Unary(UnaryOp::Trigger(_), inner) => write_sst_exp(out, inner),

        ExpX::Unary(op, _) => {
            panic!("sst_to_lean: unsupported unary op in first slice: {:?}", op);
        }

        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner) => {
            write_sst_exp(out, inner);
        }
        ExpX::UnaryOpr(UnaryOpr::Field(field_opr), inner) => {
            write_prec(out, inner, PREC_ATOM, true);
            out.push('.');
            out.push_str(&field_opr.field);
        }
        // Type propositions (HasType, IntegerTypeBound at spec mode) become
        // `True` in Lean: the Verus integer type is already reflected in the
        // Lean parameter type, so the proposition is trivially true. Without
        // this case the previous fallthrough emitted the *argument* of the
        // wrapper, turning `HasType(x+1, U8)` into the arithmetic expression
        // `x+1` where a proposition was expected.
        ExpX::UnaryOpr(UnaryOpr::HasType(_), _)
        | ExpX::UnaryOpr(UnaryOpr::IntegerTypeBound(_, _), _) => {
            out.push_str("True");
        }
        // IsVariant, CustomErr and other per-datatype checks: keep the
        // transparent fallthrough (IsVariant is rendered explicitly via the
        // `ExpX::Unary(Clip…)` path in practice; CustomErr is informational).
        ExpX::UnaryOpr(_, inner) => write_sst_exp(out, inner),

        ExpX::Binary(op, lhs, rhs) => {
            let p = binop_prec(op);
            write_prec(out, lhs, p, true);
            out.push(' ');
            write_binop(out, op);
            out.push(' ');
            write_prec(out, rhs, p, false);
        }

        ExpX::BinaryOpr(BinaryOpr::ExtEq(_, _), lhs, rhs) => {
            write_prec(out, lhs, PREC_CMP, true);
            out.push_str(" = ");
            write_prec(out, rhs, PREC_CMP, false);
        }

        ExpX::If(cond, then_e, else_e) => {
            out.push_str("if ");
            write_sst_exp(out, cond);
            out.push_str(" then ");
            write_sst_exp(out, then_e);
            out.push_str(" else ");
            write_sst_exp(out, else_e);
        }

        ExpX::Call(CallFun::Fun(fun, _), typs, args)
        | ExpX::Call(CallFun::Recursive(fun), typs, args) => {
            out.push_str(&lean_name(&fun.path));
            for typ in typs.iter() {
                out.push_str(" (");
                write_typ(out, typ);
                out.push(')');
            }
            for arg in args.iter() {
                out.push(' ');
                write_prec(out, arg, PREC_ATOM, true);
            }
        }

        ExpX::Bind(bnd, body) => {
            match &bnd.x {
                BndX::Let(binders) => {
                    for b in binders.iter() {
                        out.push_str("let ");
                        write_name(out, &b.name.0);
                        out.push_str(" := ");
                        write_sst_exp(out, &b.a);
                        out.push_str("; ");
                    }
                    write_sst_exp(out, body);
                }
                BndX::Quant(quant, binders, _, _) => {
                    out.push_str(match quant.quant {
                        air::ast::Quant::Forall => "∀ ",
                        air::ast::Quant::Exists => "∃ ",
                    });
                    for (i, b) in binders.iter().enumerate() {
                        if i > 0 { out.push(' '); }
                        out.push('(');
                        write_name(out, &b.name.0);
                        out.push_str(" : ");
                        write_typ(out, &b.a);
                        out.push(')');
                    }
                    out.push_str(", ");
                    write_sst_exp(out, body);
                }
                BndX::Lambda(binders, _) => {
                    out.push_str("fun");
                    for b in binders.iter() {
                        out.push_str(" (");
                        write_name(out, &b.name.0);
                        out.push_str(" : ");
                        write_typ(out, &b.a);
                        out.push(')');
                    }
                    out.push_str(" => ");
                    write_sst_exp(out, body);
                }
                BndX::Choose(binders, _, cond) => {
                    out.push_str("Classical.epsilon (fun");
                    for b in binders.iter() {
                        out.push_str(" (");
                        write_name(out, &b.name.0);
                        out.push_str(" : ");
                        write_typ(out, &b.a);
                        out.push(')');
                    }
                    out.push_str(" => ");
                    write_sst_exp(out, cond);
                    out.push_str(" ∧ ");
                    write_sst_exp(out, body);
                    out.push(')');
                }
            }
        }

        ExpX::WithTriggers(_, inner) | ExpX::Loc(inner) => write_sst_exp(out, inner),

        ExpX::NullaryOpr(_) => out.push_str("True"),

        ExpX::ExecFnByName(fun) | ExpX::StaticVar(fun) => {
            out.push_str(&lean_name(&fun.path));
        }

        // First-slice: these shouldn't appear in straight-line exec fns.
        // Panic loudly so we know when we need to extend.
        ExpX::Ctor(..) => panic!("sst_to_lean: Ctor unsupported in first slice"),
        ExpX::CallLambda(..) => panic!("sst_to_lean: CallLambda unsupported in first slice"),
        ExpX::ArrayLiteral(_) => panic!("sst_to_lean: ArrayLiteral unsupported in first slice"),
        ExpX::Old(..) => panic!("sst_to_lean: Old unsupported in first slice"),
        ExpX::Call(CallFun::InternalFun(_), _, _) => {
            panic!("sst_to_lean: InternalFun calls unsupported in first slice")
        }
        ExpX::Interp(_) => panic!("sst_to_lean: Interp should never escape the interpreter"),
        ExpX::FuelConst(_) => panic!("sst_to_lean: FuelConst unsupported in first slice"),
    }
}

/// Parens added per precedence.
fn write_prec(out: &mut String, e: &Exp, parent_prec: u8, is_left: bool) {
    let child_prec = expx_prec(&e.x);
    let needs_parens = child_prec < parent_prec || (child_prec == parent_prec && !is_left);
    if needs_parens { out.push('('); }
    write_sst_exp(out, e);
    if needs_parens { out.push(')'); }
}

fn write_binop(out: &mut String, op: &BinaryOp) {
    out.push_str(binop_symbol(op));
}
