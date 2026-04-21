//! Helpers shared between the VIR-AST renderer (`to_lean_expr.rs`) and
//! the SST renderer (`to_lean_sst_expr.rs`).
//!
//! ## Why two renderers, and why shared helpers instead of full unification
//!
//! VIR-AST and SST are genuinely different trees at different pipeline
//! stages. VIR-AST renders spec fn bodies, proof fn requires/ensures/
//! goals, and decreases clauses. SST renders exec fn bodies and the
//! `CheckDecreaseHeight` termination obligation. Many variants don't
//! cross: VIR-AST has `Block` / `Match` / `Ctor` / `Place`; SST has
//! `CheckDecreaseHeight` / `CallFun::InternalFun` / a flattened
//! statement sequence.
//!
//! A full trait-based unification (`trait ExprLike`) was investigated
//! and rejected — half the variants are asymmetric, so a shared trait
//! would still require per-impl case-splits for the asymmetric half,
//! netting boilerplate without eliminating it. Routing callee-spec
//! inlining through SST (so `to_lean_expr.rs` is purely for spec/proof
//! fns) was also rejected — `FuncCheckSst` is built per-fn during
//! verification rather than prebuilt in the krate, so accessing a
//! callee's SST would require invasive changes to Verus's compilation
//! pipeline. See DESIGN.md § "Two parallel expression renderers" for
//! the full reasoning.
//!
//! What remains: each helper here corresponds to a rule that BOTH
//! renderers must apply identically. The exec-fn WP path inlines
//! callee require/ensure via the VIR renderer while the callee's own
//! theorem renders via the SST renderer; divergence between the two
//! would produce a silent mismatch between the spec Tactus checks and
//! the spec the callee actually proved. Centralising each rule here
//! makes divergence a compile error rather than a runtime
//! disagreement.

use vir::ast::{ArithOp, BinaryOp, BitwiseOp, Constant, InequalityOp, RealArithOp};

use crate::lean_ast::{BinOp as L, Expr as LExpr, ExprNode};

/// Map a VIR/SST binary op to its structural Lean `BinOp` representation.
///
/// Returns `None` for ops that don't correspond to a Lean structural
/// binary operator — the caller emits those via
/// `App(non_binop_head(op), …)`. SST's exec-fn path rejects everything
/// except `Xor` before reaching the `None` branch; the VIR-AST path
/// accepts all variants for spec/proof fn rendering.
pub(crate) fn binop_to_ast(op: &BinaryOp) -> Option<L> {
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

/// Head identifier used when a VIR/SST binop is expressed as a 2-arg
/// function call rather than a structural `BinOp` — i.e., the `None`
/// return from [`binop_to_ast`]. These render as stand-ins; the exec-fn
/// SST path only reaches `Xor` because the other cases are rejected
/// upstream. The spec/proof VIR path reaches all cases.
pub(crate) fn non_binop_head(op: &BinaryOp) -> &'static str {
    match op {
        BinaryOp::Xor => "xor",
        BinaryOp::HeightCompare { .. } => "Tactus.heightLt",
        BinaryOp::StrGetChar => "String.get",
        BinaryOp::Index(_, _) => "Tactus.index",
        BinaryOp::IeeeFloat(_) => "Tactus.floatOp",
        _ => "?",
    }
}

/// Render the non-float arms of a `Constant`.
///
/// Returns `None` for `Real` / `Float32` / `Float64` so each caller
/// decides: the VIR-AST path emits a type-annotated literal (Verus
/// accepts floats in spec code); the SST path rejects them as
/// unsupported in exec-fn bodies.
pub(crate) fn const_to_node_common(c: &Constant) -> Option<ExprNode> {
    Some(match c {
        Constant::Bool(b) => ExprNode::LitBool(*b),
        Constant::Int(n) => ExprNode::Lit(n.to_string()),
        Constant::StrSlice(s) => ExprNode::LitStr(s.to_string()),
        Constant::Char(c) => ExprNode::LitChar(*c),
        Constant::Real(_) | Constant::Float32(_) | Constant::Float64(_) => return None,
    })
}

/// Resolve a `Clip` coercion to its Lean wrapper name, given whether
/// the source and destination types render as Lean `Int` (per
/// `to_lean_sst_expr::renders_as_lean_int`).
///
///   * `(Int, Nat)` → `Some("Int.toNat")`
///   * `(Nat, Int)` → `Some("Int.ofNat")`
///   * same-side    → `None` (passthrough)
///
/// Both renderers' Clip arms consult this table so the coercion rule
/// lives in one place. Dropping a coercion in the mixed case (the old
/// SST behaviour) caused a soundness hole: `x as int - y as int` for
/// `x, y : u8` rendered as `x - y` on `Nat`, which truncates negatives
/// to zero. Forcing subtraction to happen over `Int` — via
/// `Int.ofNat` — makes the lower-bound refinement check actually fire.
pub(crate) fn clip_coercion_head(src_int: bool, dst_int: bool) -> Option<&'static str> {
    match (src_int, dst_int) {
        (true, false) => Some("Int.toNat"),
        (false, true) => Some("Int.ofNat"),
        _ => None,
    }
}

/// Apply a clip coercion wrapper to an already-rendered `LExpr`, using
/// [`clip_coercion_head`] to pick the wrapper name. Passthrough
/// (same-side) returns the expression unchanged.
pub(crate) fn apply_clip_coercion(src_int: bool, dst_int: bool, inner: LExpr) -> LExpr {
    match clip_coercion_head(src_int, dst_int) {
        Some(head) => LExpr::app1(LExpr::var(head), inner),
        None => inner,
    }
}
