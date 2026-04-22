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

use vir::ast::{
    ArithOp, BinaryOp, BitwiseOp, Constant, Dt, FieldOpr, Ident, InequalityOp, RealArithOp,
};

use crate::lean_ast::{BinOp as L, Expr as LExpr, ExprNode};
use crate::to_lean_type::{lean_name, sanitize, short_name};

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

/// Build a Lean constructor expression from an already-rendered
/// `Vec<LExpr>` of field values.
///
/// * `Dt::Path(path)` + variant → named ctor `TypeName.variant arg₁ arg₂ …`,
///   with the special case that a struct's sole variant (whose name
///   equals the type's short name) renders as `TypeName.mk` —
///   matching Lean's auto-generated `.mk` for single-field-group
///   inductives.
/// * `Dt::Tuple(_)` → Lean anonymous constructor `⟨a, b, c⟩`, which
///   elaborates against the tuple's product type.
///
/// Both expression renderers (VIR-AST and SST) use this so the ctor
/// naming convention can't drift between the proof-fn / spec-fn path
/// and the exec-fn WP path. Caller is responsible for rendering the
/// fields via their respective per-tree walker.
pub(crate) fn ctor_node(
    dt: &Dt,
    variant: &Ident,
    rendered_fields: Vec<LExpr>,
) -> ExprNode {
    match dt {
        Dt::Path(path) => {
            let type_name = lean_name(path);
            let variant_seg = if variant.as_str() == short_name(path) {
                "mk".to_string()
            } else {
                sanitize(variant)
            };
            let head = format!("{}.{}", type_name, variant_seg);
            if rendered_fields.is_empty() {
                ExprNode::Var(head)
            } else {
                ExprNode::App {
                    head: Box::new(LExpr::var(head)),
                    args: rendered_fields,
                }
            }
        }
        Dt::Tuple(_) => ExprNode::Anon(rendered_fields),
    }
}

/// Render the `is_<variant>` discriminator for a `UnaryOpr::IsVariant`
/// applied to an already-rendered receiver expression. Lean's inductive
/// derivation provides these accessors automatically: `x.isSome` for
/// `Option.Some`, `x.isOk` for `Result.Ok`, etc. Both renderers call
/// this so the naming convention stays consistent.
pub(crate) fn is_variant_node(variant: &Ident, inner: LExpr) -> ExprNode {
    LExpr::field_proj(inner, format!("is{}", variant)).node
}

/// Map a VIR field access to the Lean side's field name.
///
/// * Anonymous tuple (`Dt::Tuple`) uses 0-indexed numeric fields like
///   `"0"` / `"1"`; Lean's `Prod`-derived accessor is 1-indexed
///   (`.1`, `.2`), so `"0"` → `"1"`, `"1"` → `"2"`, etc.
/// * Single-variant struct (`Dt::Path` where the variant name equals
///   the type's short name) uses the structure-auto-derived accessor
///   names: numeric `"0"` → `"val0"`, named fields pass through
///   (after sanitization). Lean's `structure` auto-derives these.
/// * Multi-variant enum (`Dt::Path` where the variant name differs
///   from the type's short name) routes through the per-variant
///   accessor fns emitted by `datatype_to_cmds` — numeric field
///   becomes `"<Variant>_val<n>"`, named field becomes
///   `"<Variant>_<field>"`. Lean's `inductive` doesn't auto-derive
///   field accessors, so we synthesise `def Kind.Foo_val0 : Kind → …`
///   alongside the inductive declaration.
///
/// Shared between the VIR-AST and SST renderers so the naming rule
/// lives in one place. Divergence would make match-arm desugaring
/// (exec path) reference a field name that the accessor-fn emission
/// (preamble path) doesn't define — silent Lean "invalid field"
/// failure.
pub(crate) fn field_access_name(field_opr: &FieldOpr) -> String {
    let raw = field_opr.field.as_str();
    let numeric = raw.parse::<usize>().ok();
    match (&field_opr.datatype, numeric) {
        (Dt::Tuple(_), Some(n)) => (n + 1).to_string(),
        (Dt::Path(path), _) => {
            let type_short = short_name(path);
            let variant = field_opr.variant.as_str();
            let is_single_variant = variant == type_short;
            let field_seg = match numeric {
                Some(n) => format!("val{}", n),
                None => sanitize(raw),
            };
            if is_single_variant {
                field_seg
            } else {
                format!("{}_{}", sanitize(variant), field_seg)
            }
        }
        _ => sanitize(raw),
    }
}
