//! Translate SST expressions (`vir::sst::Exp`) to `lean_ast::Expr`.
//!
//! Mirrors `to_lean_expr` but operates on SST's `Exp` / `ExpX` instead of
//! VIR-AST's `Expr` / `ExprX`. SST is a cleaned-up AST used as the input
//! to WP generation for exec fns (`sst_to_lean`).
//!
//! `supported_body` in `sst_to_lean.rs` rejects expression forms that
//! would end up as `Raw` or panic here — so any form reaching this module
//! is one we've committed to rendering.

use vir::ast::*;
use vir::sst::{BndX, CallFun, Exp, ExpX};
use crate::lean_ast::{
    BinOp as L, Binder as LBinder, BinderKind, Expr as LExpr, ExprNode, UnOp as LUn,
};
use crate::lean_pp::pp_expr;
use crate::to_lean_type::{lean_name, sanitize, typ_to_expr};

/// Build a `lean_ast::Expr` from an SST expression.
pub fn sst_exp_to_ast(e: &Exp) -> LExpr {
    LExpr::new(exp_to_node(e))
}

/// Back-compat: write an SST expression as Lean text into `out`. Kept
/// while callers are migrated to the AST API.
pub fn write_sst_exp(out: &mut String, e: &Exp) {
    out.push_str(&pp_expr(&sst_exp_to_ast(e)));
}

fn var(s: impl Into<String>) -> LExpr {
    LExpr::new(ExprNode::Var(s.into()))
}

fn apply(head: LExpr, args: Vec<LExpr>) -> ExprNode {
    if args.is_empty() {
        head.node
    } else {
        ExprNode::App { head: Box::new(head), args }
    }
}

fn exp_to_node(e: &Exp) -> ExprNode {
    match &e.x {
        ExpX::Const(c) => const_to_node(c),
        ExpX::Var(ident) | ExpX::VarLoc(ident) | ExpX::VarAt(ident, _) => {
            ExprNode::Var(sanitize(&ident.0))
        }
        ExpX::StaticVar(fun) | ExpX::ExecFnByName(fun) => {
            ExprNode::Var(lean_name(&fun.path))
        }

        ExpX::Unary(UnaryOp::Not, inner) => ExprNode::UnOp {
            op: LUn::Not,
            arg: Box::new(sst_exp_to_ast(inner)),
        },
        ExpX::Unary(UnaryOp::Clip { range, .. }, inner) => {
            let src_is_int = matches!(&*inner.typ, TypX::Int(
                IntRange::Int | IntRange::I(_) | IntRange::ISize
            ));
            let dst_is_nat = matches!(range,
                IntRange::Nat | IntRange::U(_) | IntRange::USize | IntRange::Char
            );
            if src_is_int && dst_is_nat {
                apply(var("Int.toNat"), vec![sst_exp_to_ast(inner)])
            } else {
                exp_to_node(inner)
            }
        }
        ExpX::Unary(UnaryOp::CoerceMode { .. }, inner)
        | ExpX::Unary(UnaryOp::Trigger(_), inner) => exp_to_node(inner),
        ExpX::Unary(op, _) => panic!(
            "to_lean_sst_expr: unary op {:?} should have been rejected by supported_body",
            op
        ),

        // Box/Unbox: transparent. Field projection.
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner) => exp_to_node(inner),
        ExpX::UnaryOpr(UnaryOpr::Field(field_opr), inner) => ExprNode::FieldProj {
            expr: Box::new(sst_exp_to_ast(inner)),
            field: sanitize(&field_opr.field),
        },
        // Type propositions are trivially True in Lean — our parameter types
        // already reflect the VIR integer type, so `HasType(x, U8)` etc.
        // carries no additional information.
        ExpX::UnaryOpr(UnaryOpr::HasType(_), _)
        | ExpX::UnaryOpr(UnaryOpr::IntegerTypeBound(_, _), _) => ExprNode::LitBool(true),
        ExpX::UnaryOpr(_, inner) => exp_to_node(inner),

        ExpX::Binary(op, lhs, rhs) => match binop_to_ast(op) {
            Some(l_op) => ExprNode::BinOp {
                op: l_op,
                lhs: Box::new(sst_exp_to_ast(lhs)),
                rhs: Box::new(sst_exp_to_ast(rhs)),
            },
            // Non-structural: emit as `head lhs rhs` via App. HeightCompare
            // / Index / StrGetChar / IeeeFloat are rejected earlier by
            // `sst_to_lean::supported_body`; the only op that reaches here
            // is `Xor`, which renders as `xor lhs rhs`.
            None => ExprNode::App {
                head: Box::new(var("xor")),
                args: vec![sst_exp_to_ast(lhs), sst_exp_to_ast(rhs)],
            },
        },
        ExpX::BinaryOpr(BinaryOpr::ExtEq(_, _), lhs, rhs) => ExprNode::BinOp {
            op: L::Eq,
            lhs: Box::new(sst_exp_to_ast(lhs)),
            rhs: Box::new(sst_exp_to_ast(rhs)),
        },

        ExpX::If(cond, then_e, else_e) => ExprNode::If {
            cond: Box::new(sst_exp_to_ast(cond)),
            then_: Box::new(sst_exp_to_ast(then_e)),
            else_: Some(Box::new(sst_exp_to_ast(else_e))),
        },

        ExpX::Call(CallFun::Fun(fun, _), typs, args)
        | ExpX::Call(CallFun::Recursive(fun), typs, args) => {
            let base = var(&lean_name(&fun.path));
            let head = if typs.is_empty() {
                base
            } else {
                LExpr::new(ExprNode::App {
                    head: Box::new(base),
                    args: typs.iter().map(|t| typ_to_expr(t)).collect(),
                })
            };
            apply(head, args.iter().map(|a| sst_exp_to_ast(a)).collect())
        }
        ExpX::Call(CallFun::InternalFun(_), _, _) => panic!(
            "to_lean_sst_expr: InternalFun should have been rejected by supported_body"
        ),

        ExpX::Bind(bnd, body) => match &bnd.x {
            BndX::Let(binders) => {
                // Nest single-variable lets right-to-left so each binder is
                // in scope for the remainder.
                let mut out = sst_exp_to_ast(body);
                for b in binders.iter().rev() {
                    out = LExpr::new(ExprNode::Let {
                        name: sanitize(&b.name.0),
                        value: Box::new(sst_exp_to_ast(&b.a)),
                        body: Box::new(out),
                    });
                }
                out.node
            }
            BndX::Quant(quant, binders, _, _) => {
                let l_binders: Vec<LBinder> = binders.iter().map(|b| LBinder {
                    name: Some(sanitize(&b.name.0)),
                    ty: typ_to_expr(&b.a),
                    kind: BinderKind::Explicit,
                }).collect();
                let body = Box::new(sst_exp_to_ast(body));
                match quant.quant {
                    air::ast::Quant::Forall => ExprNode::Forall { binders: l_binders, body },
                    air::ast::Quant::Exists => ExprNode::Exists { binders: l_binders, body },
                }
            }
            BndX::Lambda(binders, _) => ExprNode::Lambda {
                binders: binders.iter().map(|b| LBinder {
                    name: Some(sanitize(&b.name.0)),
                    ty: typ_to_expr(&b.a),
                    kind: BinderKind::Explicit,
                }).collect(),
                body: Box::new(sst_exp_to_ast(body)),
            },
            BndX::Choose(binders, _, cond) => {
                // `Classical.epsilon (fun (x : T) => cond ∧ body)`
                let lambda_body = LExpr::new(ExprNode::BinOp {
                    op: L::And,
                    lhs: Box::new(sst_exp_to_ast(cond)),
                    rhs: Box::new(sst_exp_to_ast(body)),
                });
                let lambda = LExpr::new(ExprNode::Lambda {
                    binders: binders.iter().map(|b| LBinder {
                        name: Some(sanitize(&b.name.0)),
                        ty: typ_to_expr(&b.a),
                        kind: BinderKind::Explicit,
                    }).collect(),
                    body: Box::new(lambda_body),
                });
                ExprNode::App {
                    head: Box::new(var("Classical.epsilon")),
                    args: vec![lambda],
                }
            }
        },

        ExpX::WithTriggers(_, inner) | ExpX::Loc(inner) => exp_to_node(inner),

        ExpX::NullaryOpr(_) => ExprNode::LitBool(true),

        // Forms rejected by `supported_body`. If we reach them here, the
        // support check and this function got out of sync.
        ExpX::Ctor(..) => panic!("to_lean_sst_expr: Ctor should have been rejected"),
        ExpX::CallLambda(..) => panic!("to_lean_sst_expr: CallLambda should have been rejected"),
        ExpX::ArrayLiteral(_) => panic!("to_lean_sst_expr: ArrayLiteral should have been rejected"),
        ExpX::Old(..) => panic!("to_lean_sst_expr: Old should have been rejected"),
        ExpX::Interp(_) => panic!("to_lean_sst_expr: Interp must not escape the interpreter"),
        ExpX::FuelConst(_) => panic!("to_lean_sst_expr: FuelConst should have been rejected"),
    }
}

fn const_to_node(c: &Constant) -> ExprNode {
    match c {
        Constant::Bool(b) => ExprNode::LitBool(*b),
        Constant::Int(n) => ExprNode::Lit(n.to_string()),
        Constant::StrSlice(s) => ExprNode::LitStr(s.to_string()),
        Constant::Char(c) => ExprNode::LitChar(*c),
        Constant::Real(_) | Constant::Float32(_) | Constant::Float64(_) => panic!(
            "to_lean_sst_expr: constant {:?} should have been rejected by supported_body", c
        ),
    }
}

fn binop_to_ast(op: &BinaryOp) -> Option<L> {
    Some(match op {
        BinaryOp::And => L::And,
        BinaryOp::Or => L::Or,
        BinaryOp::Implies => L::Implies,
        BinaryOp::Eq(_) => L::Eq,
        BinaryOp::Ne => L::Ne,
        BinaryOp::Inequality(InequalityOp::Le) => L::Le,
        BinaryOp::Inequality(InequalityOp::Lt) => L::Lt,
        BinaryOp::Inequality(InequalityOp::Ge) => L::Ge,
        BinaryOp::Inequality(InequalityOp::Gt) => L::Gt,
        BinaryOp::Arith(ArithOp::Add(_)) => L::Add,
        BinaryOp::Arith(ArithOp::Sub(_)) => L::Sub,
        BinaryOp::Arith(ArithOp::Mul(_)) => L::Mul,
        BinaryOp::Arith(ArithOp::EuclideanDiv(_)) => L::Div,
        BinaryOp::Arith(ArithOp::EuclideanMod(_)) => L::Mod,
        BinaryOp::RealArith(RealArithOp::Add) => L::Add,
        BinaryOp::RealArith(RealArithOp::Sub) => L::Sub,
        BinaryOp::RealArith(RealArithOp::Mul) => L::Mul,
        BinaryOp::RealArith(RealArithOp::Div) => L::Div,
        BinaryOp::Bitwise(BitwiseOp::BitAnd, _) => L::BitAnd,
        BinaryOp::Bitwise(BitwiseOp::BitOr, _) => L::BitOr,
        BinaryOp::Bitwise(BitwiseOp::BitXor, _) => L::BitXor,
        BinaryOp::Bitwise(BitwiseOp::Shr(_), _) => L::Shr,
        BinaryOp::Bitwise(BitwiseOp::Shl(_, _), _) => L::Shl,
        BinaryOp::Xor
        | BinaryOp::HeightCompare { .. }
        | BinaryOp::StrGetChar
        | BinaryOp::Index(_, _)
        | BinaryOp::IeeeFloat(_) => return None,
    })
}
