//! Helpers shared by both `to_lean_expr.rs` (VIR-AST) and
//! `to_lean_sst_expr.rs` (SST). These don't depend on which AST they came
//! from: an integer is an integer, `+` is `+`, precedence is precedence.
//!
//! Keeping them in one place means a new Lean syntax question (e.g., how to
//! print a `Real` constant) only needs to be answered once.

use vir::ast::*;

// ── Precedence ──────────────────────────────────────────────────────────
//
// Higher numbers bind tighter. `write_expr_prec`-style helpers use these to
// decide whether to wrap a subexpression in parens.

pub(crate) const PREC_IMPLIES: u8 = 25;
pub(crate) const PREC_OR: u8 = 30;
pub(crate) const PREC_AND: u8 = 35;
pub(crate) const PREC_CMP: u8 = 50;
pub(crate) const PREC_ADD: u8 = 65;
pub(crate) const PREC_MUL: u8 = 70;
pub(crate) const PREC_ATOM: u8 = 255;

/// Precedence of a Lean binary operator. Used by both writers.
pub(crate) fn binop_prec(op: &BinaryOp) -> u8 {
    match op {
        BinaryOp::Implies => PREC_IMPLIES,
        BinaryOp::Or => PREC_OR,
        BinaryOp::And => PREC_AND,
        BinaryOp::Eq(_) | BinaryOp::Ne | BinaryOp::Inequality(_) => PREC_CMP,
        BinaryOp::Arith(ArithOp::Add(_) | ArithOp::Sub(_)) => PREC_ADD,
        BinaryOp::Arith(ArithOp::Mul(_) | ArithOp::EuclideanDiv(_) | ArithOp::EuclideanMod(_)) => PREC_MUL,
        _ => PREC_CMP,
    }
}

/// Lean textual representation of a VIR/SST binary operator.
/// Caller is responsible for surrounding spaces.
pub(crate) fn binop_symbol(op: &BinaryOp) -> &'static str {
    match op {
        BinaryOp::And => "∧",
        BinaryOp::Or => "∨",
        BinaryOp::Xor => "xor",
        BinaryOp::Implies => "→",
        BinaryOp::Eq(_) => "=",
        BinaryOp::Ne => "≠",
        BinaryOp::Inequality(InequalityOp::Le) => "≤",
        BinaryOp::Inequality(InequalityOp::Lt) => "<",
        BinaryOp::Inequality(InequalityOp::Ge) => "≥",
        BinaryOp::Inequality(InequalityOp::Gt) => ">",
        BinaryOp::Arith(ArithOp::Add(_)) => "+",
        BinaryOp::Arith(ArithOp::Sub(_)) => "-",
        BinaryOp::Arith(ArithOp::Mul(_)) => "*",
        BinaryOp::Arith(ArithOp::EuclideanDiv(_)) => "/",
        BinaryOp::Arith(ArithOp::EuclideanMod(_)) => "%",
        BinaryOp::RealArith(RealArithOp::Add) => "+",
        BinaryOp::RealArith(RealArithOp::Sub) => "-",
        BinaryOp::RealArith(RealArithOp::Mul) => "*",
        BinaryOp::RealArith(RealArithOp::Div) => "/",
        BinaryOp::Bitwise(BitwiseOp::BitAnd, _) => "&&&",
        BinaryOp::Bitwise(BitwiseOp::BitOr, _) => "|||",
        BinaryOp::Bitwise(BitwiseOp::BitXor, _) => "^^^",
        BinaryOp::Bitwise(BitwiseOp::Shr(_), _) => ">>>",
        BinaryOp::Bitwise(BitwiseOp::Shl(_, _), _) => "<<<",
        BinaryOp::HeightCompare { .. } => "<",
        BinaryOp::StrGetChar => "String.get",
        BinaryOp::Index(_, _) => "!!",
        BinaryOp::IeeeFloat(_) => "+",
    }
}

/// Write a VIR `Constant` as Lean source. Used by both expression writers.
/// The SST writer previously panicked on Real/Float constants; the VIR writer
/// accepts them. We unify on "accept if we can reasonably render, reject
/// otherwise with a clear error-in-output" — Lean will fail to parse the
/// output rather than Tactus panicking mid-generation.
pub(crate) fn write_const(out: &mut String, c: &Constant) {
    match c {
        Constant::Bool(true) => out.push_str("True"),
        Constant::Bool(false) => out.push_str("False"),
        Constant::Int(n) => {
            let s = n.to_string();
            if s.starts_with('-') {
                out.push('(');
                out.push_str(&s);
                out.push(')');
            } else {
                out.push_str(&s);
            }
        }
        Constant::StrSlice(s) => {
            out.push('"');
            for c in s.chars() {
                match c {
                    '"' => out.push_str("\\\""),
                    '\\' => out.push_str("\\\\"),
                    '\n' => out.push_str("\\n"),
                    '\r' => out.push_str("\\r"),
                    '\t' => out.push_str("\\t"),
                    c => out.push(c),
                }
            }
            out.push('"');
        }
        Constant::Char(c) => {
            out.push('\'');
            out.push(*c);
            out.push('\'');
        }
        Constant::Real(s) => {
            out.push('(');
            out.push_str(s);
            out.push_str(" : Real)");
        }
        Constant::Float32(bits) => {
            out.push_str(&format!("({} : Float)", f32::from_bits(*bits)));
        }
        Constant::Float64(bits) => {
            out.push_str(&format!("({} : Float)", f64::from_bits(*bits)));
        }
    }
}
