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

/// `2^n` rendered as a decimal string. Supports 0 ≤ n ≤ 128 — VIR's
/// `U(n)` / `I(n)` only reach that range in practice (u8/u16/u32/u64/u128).
/// We compute it in `u128`; `n = 128` is the boundary, so we fall back to
/// a precomputed constant for that single case.
fn two_pow_str(n: u32) -> String {
    if n < 128 {
        (1u128 << n).to_string()
    } else if n == 128 {
        "340282366920938463463374607431768211456".to_string()
    } else {
        panic!("two_pow_str: bit width {} exceeds the u128 ceiling", n)
    }
}

fn two_pow_lit(n: u32) -> LExpr {
    LExpr::new(ExprNode::Lit(two_pow_str(n)))
}

/// If `e` is a constant non-negative integer that fits in `u32`, return
/// its value. Used to read the bit-width argument of `IntegerTypeBound`
/// from an SST `Exp`.
fn const_u32_from_sst(e: &Exp) -> Option<u32> {
    match &e.x {
        ExpX::Const(Constant::Int(n)) => n.to_string().parse().ok(),
        _ => None,
    }
}

/// VIR-AST counterpart of `const_u32_from_sst`.
fn const_u32_from_vir(e: &Expr) -> Option<u32> {
    match &e.x {
        ExprX::Const(Constant::Int(n)) => n.to_string().parse().ok(),
        _ => None,
    }
}

/// Shared helper: lower `IntegerTypeBound(kind, _) applied to <bit width>`.
/// Both the SST and VIR-AST paths end up here once they've extracted
/// `bits`. `ArchWordBits` panics — it needs prelude plumbing that isn't
/// wired through yet.
pub fn integer_type_bound_node(kind: &IntegerTypeBoundKind, bits: u32) -> ExprNode {
    if matches!(kind, IntegerTypeBoundKind::ArchWordBits) {
        panic!(
            "IntegerTypeBound::ArchWordBits requires arch_word_bits in the \
             Tactus prelude, which isn't wired through yet"
        );
    }
    integer_type_bound_lit(kind.clone(), bits).node
}

/// Entry point for the VIR-AST rendering path (`to_lean_expr.rs`).
pub fn integer_type_bound_from_vir(
    kind: &IntegerTypeBoundKind,
    inner: &Expr,
) -> LExpr {
    if matches!(kind, IntegerTypeBoundKind::ArchWordBits) {
        // Fall through to the shared helper's panic so the message
        // matches regardless of which pipeline tripped it.
        return LExpr::new(integer_type_bound_node(kind, 0));
    }
    let bits = const_u32_from_vir(inner).unwrap_or_else(|| panic!(
        "IntegerTypeBound({:?}): non-constant bit width is not supported \
         (VIR-AST inner = {:?})",
        kind, inner.x,
    ));
    LExpr::new(integer_type_bound_node(kind, bits))
}

/// The literal value of `IntegerTypeBound(kind, _)` at the given bit width.
///
/// Mirrors the AIR encoding in `sst_to_air::exp_to_expr`:
///   * `UnsignedMax` → `2^bits - 1`
///   * `SignedMin`   → `-2^(bits-1)`
///   * `SignedMax`   → `2^(bits-1) - 1`
///
/// `ArchWordBits` is handled by the caller (it needs prelude plumbing).
fn integer_type_bound_lit(kind: IntegerTypeBoundKind, bits: u32) -> LExpr {
    let s = match kind {
        IntegerTypeBoundKind::UnsignedMax => {
            // 2^bits - 1. At bits == 128 we hit u128::MAX; shift-by-128
            // is UB so branch around it.
            if bits == 128 {
                "340282366920938463463374607431768211455".to_string()
            } else if bits == 0 {
                "0".to_string()
            } else {
                ((1u128 << bits) - 1).to_string()
            }
        }
        IntegerTypeBoundKind::SignedMin => {
            assert!(bits >= 1, "SignedMin on 0-bit int");
            format!("-{}", two_pow_str(bits - 1))
        }
        IntegerTypeBoundKind::SignedMax => {
            assert!(bits >= 1, "SignedMax on 0-bit int");
            ((1u128 << (bits - 1)) - 1).to_string()
        }
        IntegerTypeBoundKind::ArchWordBits => unreachable!(
            "integer_type_bound_lit: ArchWordBits should be handled at the call site"
        ),
    };
    LExpr::new(ExprNode::Lit(s))
}

/// Build the Lean predicate expressing the type invariant on `e : ty`
/// (i.e., the refinement bounds Verus treats as `HasType(e, ty)`).
///
/// Returns `None` when the target type carries no additional constraint:
///   * `Nat`, `Int` — unbounded
///   * non-integer types — structural, no refinement
///   * `USize`, `ISize` — depend on `arch_word_bits`, not yet wired through
///     the prelude; treated as unbounded for now (accepted soundness gap,
///     same as stock Verus when compiling without `--target`)
///
/// Returns `Some(pred)` otherwise.
///
/// For `U(n)` (rendered as `Nat`): `e < 2^n`. The `0 ≤ e` half comes for
/// free from `Nat`.
///
/// For `I(n)` (rendered as `Int`): `-2^(n-1) ≤ e ∧ e < 2^(n-1)`. `e` is
/// duplicated in the predicate.
///
/// For `Char`: `e < 0x110000` (Unicode scalar range).
pub fn type_bound_predicate(e: &LExpr, ty: &Typ) -> Option<LExpr> {
    // Transparent: unbox before examining.
    if let TypX::Boxed(inner) = &**ty {
        return type_bound_predicate(e, inner);
    }
    let range = match &**ty {
        TypX::Int(r) => r,
        _ => return None,
    };
    match range {
        IntRange::U(n) => Some(LExpr::new(ExprNode::BinOp {
            op: L::Lt,
            lhs: Box::new(e.clone()),
            rhs: Box::new(two_pow_lit(*n)),
        })),
        IntRange::I(n) => {
            let hi = two_pow_lit(*n - 1);
            let lo = LExpr::new(ExprNode::UnOp {
                op: LUn::Neg,
                arg: Box::new(hi.clone()),
            });
            let lo_le = LExpr::new(ExprNode::BinOp {
                op: L::Le,
                lhs: Box::new(lo),
                rhs: Box::new(e.clone()),
            });
            let e_lt = LExpr::new(ExprNode::BinOp {
                op: L::Lt,
                lhs: Box::new(e.clone()),
                rhs: Box::new(hi),
            });
            Some(LExpr::new(ExprNode::BinOp {
                op: L::And,
                lhs: Box::new(lo_le),
                rhs: Box::new(e_lt),
            }))
        }
        // Unicode scalar range: 0 ≤ c ≤ U+10FFFF. We render as
        // `c < 0x110000`; `0 ≤` is free from `Nat`. (Surrogates
        // U+D800..U+DFFF are technically excluded from Unicode scalar
        // values, but Verus and Rust's `char` don't track that, and
        // omega's simpler with a single upper-bound literal.)
        IntRange::Char => Some(LExpr::new(ExprNode::BinOp {
            op: L::Lt,
            lhs: Box::new(e.clone()),
            rhs: Box::new(LExpr::new(ExprNode::Lit("0x110000".to_string()))),
        })),
        IntRange::Nat | IntRange::Int | IntRange::USize | IntRange::ISize => None,
    }
}

fn apply(head: LExpr, args: Vec<LExpr>) -> ExprNode {
    if args.is_empty() {
        head.node
    } else {
        ExprNode::App { head: Box::new(head), args }
    }
}

/// `true` iff VIR's `IntRange` renders as Lean `Int` (the signed side
/// plus unbounded `Int`). The complement renders as `Nat`. Keep in
/// sync with `to_lean_type::typ_to_expr`.
fn renders_as_lean_int(range: &IntRange) -> bool {
    matches!(range, IntRange::Int | IntRange::I(_) | IntRange::ISize)
}

/// Lower a `Clip { range: dst }` applied to an expression of type `src`.
///
/// Verus's Clip is a value-preserving coercion *if* the source value
/// actually fits in `dst` — overflow is guarded by a neighbouring
/// `HasType(inner, dst)` assertion. So our job is just to keep Lean's
/// types aligned:
///
///   * Int-rendered source, Nat-rendered dst → `Int.toNat`
///   * Nat-rendered source, Int-rendered dst → `Int.ofNat`
///   * Same-side → transparent (Lean accepts the value as-is)
///
/// Dropping the coercion in the mixed case (the old behaviour) caused a
/// soundness hole in exec-fn WP: `x as int - y as int` for `x, y : u8`
/// rendered as `x - y` on `Nat`, which truncates negatives to zero. The
/// `Int.ofNat` insertion forces subtraction to happen over `Int` so the
/// lower-bound refinement check (if present) can actually fire.
fn clip_to_node(src: &Typ, dst: &IntRange, inner: &Exp) -> ExprNode {
    let src_range = match &**src {
        TypX::Int(r) => r,
        // Boxed int? Peel the box; otherwise the inner isn't an int type
        // at all (shouldn't happen for Clip) and we pass through.
        TypX::Boxed(t) => if let TypX::Int(r) = &**t { r } else {
            return exp_to_node(inner);
        },
        _ => return exp_to_node(inner),
    };
    let rendered = sst_exp_to_ast(inner);
    match (renders_as_lean_int(src_range), renders_as_lean_int(dst)) {
        (true, false) => apply(var("Int.toNat"), vec![rendered]),
        (false, true) => apply(var("Int.ofNat"), vec![rendered]),
        _ => rendered.node,
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
            clip_to_node(&inner.typ, range, inner)
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
        // `HasType(e, t)` — the refinement constraint for `e` to inhabit
        // `t`. For fixed-width ints (u8, i32, …) this is the bounds check
        // Verus emits at every arithmetic site. For unbounded types (Nat,
        // Int, structs) it's vacuous; we emit `True` and let Lean simplify.
        ExpX::UnaryOpr(UnaryOpr::HasType(t), inner) => {
            let e_ast = sst_exp_to_ast(inner);
            match type_bound_predicate(&e_ast, t) {
                Some(pred) => pred.node,
                None => ExprNode::LitBool(true),
            }
        }
        // `IntegerTypeBound(kind, _)` returns the numeric bound of a
        // fixed-width int type. The inner expression is the bit width
        // (a literal like 8, 32, …) — we evaluate at codegen time and
        // emit the decimal literal directly.
        ExpX::UnaryOpr(UnaryOpr::IntegerTypeBound(kind, _), inner) => {
            if matches!(kind, IntegerTypeBoundKind::ArchWordBits) {
                return integer_type_bound_node(kind, 0);
            }
            let bits = const_u32_from_sst(inner).unwrap_or_else(|| panic!(
                "IntegerTypeBound({:?}): non-constant bit width is not supported \
                 (SST inner = {:?})",
                kind, inner.x,
            ));
            integer_type_bound_node(kind, bits)
        }
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
