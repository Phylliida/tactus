//! Translate SST expressions (`vir::sst::Exp`) to `lean_ast::Expr`.
//!
//! Mirrors `to_lean_expr` but operates on SST's `Exp` / `ExpX` instead of
//! VIR-AST's `Expr` / `ExprX`. SST is a cleaned-up AST used as the input
//! to WP generation for exec fns (`sst_to_lean`).
//!
//! ## Fallible vs infallible entry points
//!
//! Validation and rendering share a single case analysis:
//!
//!   * [`sst_exp_to_ast_checked`] is the primary recursive impl — it
//!     validates every SST shape as it renders, returning `Err(…)` for
//!     forms we don't support. Use this at the boundary where unchecked
//!     SST enters the pipeline (walk, req/ens validation).
//!   * [`sst_exp_to_ast`] is a thin infallible wrapper that panics on
//!     `Err`. Use this in build_* paths where `walk` has already
//!     validated the stored `Exp` refs — the panic is documented as
//!     "codegen bug: caller should have validated."
//!
//! This replaces an earlier split where `check_exp` (in `sst_to_lean`)
//! and `sst_exp_to_ast` each had parallel case analyses that had to
//! stay in sync by hand.

use vir::ast::*;
use vir::sst::{BndX, CallFun, Exp, ExpX, InternalFun};
use crate::lean_ast::{
    substitute, BinOp as L, Binder as LBinder, BinderKind, Expr as LExpr, ExprNode,
};
use crate::lean_pp::pp_expr;
use crate::to_lean_type::{lean_name, sanitize, typ_to_expr};

/// Build a `lean_ast::Expr` from an SST expression, validating as we
/// go. Returns `Err(reason)` for any SST form we don't know how to
/// emit. This is the primary entry point — use it anywhere unchecked
/// SST enters (walk, req/ens validation).
pub fn sst_exp_to_ast_checked(e: &Exp) -> Result<LExpr, String> {
    exp_to_node_checked(e).map(LExpr::new)
}

/// Infallible wrapper around [`sst_exp_to_ast_checked`] — panics on
/// `Err` with a documented "caller should have validated" message.
/// Use in contexts where `walk` or an upstream `sst_exp_to_ast_checked`
/// call has already cleared validation.
pub fn sst_exp_to_ast(e: &Exp) -> LExpr {
    sst_exp_to_ast_checked(e).unwrap_or_else(|reason| panic!(
        "sst_exp_to_ast: {} — caller should have validated via \
         `sst_exp_to_ast_checked` or `walk` before reaching a build_* path",
        reason
    ))
}

/// Back-compat: write an SST expression as Lean text into `out`. Kept
/// while callers are migrated to the AST API.
pub fn write_sst_exp(out: &mut String, e: &Exp) {
    out.push_str(&pp_expr(&sst_exp_to_ast(e)));
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

fn two_pow_lit(n: u32) -> LExpr { LExpr::lit_int(two_pow_str(n)) }

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
/// `bits`. `ArchWordBits` is handled specially — it's a reference to
/// the prelude axiom rather than a computed literal.
pub fn integer_type_bound_node(kind: &IntegerTypeBoundKind, bits: u32) -> ExprNode {
    match kind {
        IntegerTypeBoundKind::ArchWordBits => {
            // `arch_word_bits : Nat` from TactusPrelude — an opaque axiom
            // whose value comes from the build target. Downstream tactics
            // only know `arch_word_bits = 32 ∨ arch_word_bits = 64`; that
            // disjunction is available as the `arch_word_bits_valid`
            // axiom if a proof needs to case-split.
            LExpr::var("arch_word_bits").node
        }
        _ => integer_type_bound_lit(kind.clone(), bits).node,
    }
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
///
/// Returns `Some(pred)` otherwise.
///
/// For `U(n)` (rendered as `Int`): `0 ≤ e ∧ e < 2^n`. Rendering u-types
/// as `Int` rather than `Nat` is what makes subtraction underflow
/// catchable — Lean's `Nat` silently truncates negatives, but `Int`
/// gives the true mathematical value so this refinement check can fire.
///
/// For `I(n)` (rendered as `Int`): `-2^(n-1) ≤ e ∧ e < 2^(n-1)`.
///
/// For `USize` (rendered as `Int`): `0 ≤ e ∧ e < usize_hi`, where
/// `usize_hi = 2^arch_word_bits` is a prelude-defined constant. For
/// `ISize`: `-isize_hi ≤ e ∧ e < isize_hi`, same idea. `tactus_auto`
/// generally can't discharge these symbolically (omega doesn't reason
/// about `2^n` for unknown `n`) — proofs often need an explicit
/// `cases arch_word_bits_valid` step. Emitting them anyway is the
/// soundness-preserving choice.
///
/// For `Char` (rendered as `Nat`): `e < 0x110000`. The `0 ≤` half comes
/// for free from `Nat`.
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
        IntRange::U(n) => Some(LExpr::and(
            LExpr::le(LExpr::lit_int("0"), e.clone()),
            LExpr::lt(e.clone(), two_pow_lit(*n)),
        )),
        IntRange::I(n) => {
            let hi = two_pow_lit(*n - 1);
            Some(LExpr::and(
                LExpr::le(LExpr::neg(hi.clone()), e.clone()),
                LExpr::lt(e.clone(), hi),
            ))
        }
        IntRange::USize => {
            let hi = LExpr::var("usize_hi");
            Some(LExpr::and(
                LExpr::le(LExpr::lit_int("0"), e.clone()),
                LExpr::lt(e.clone(), hi),
            ))
        }
        IntRange::ISize => {
            let hi = LExpr::var("isize_hi");
            Some(LExpr::and(
                LExpr::le(LExpr::neg(hi.clone()), e.clone()),
                LExpr::lt(e.clone(), hi),
            ))
        }
        // Unicode scalar range: 0 ≤ c ≤ U+10FFFF. `c < 0x110000` covers
        // the upper half; `0 ≤` is free from `Nat`. (Surrogates
        // U+D800..U+DFFF are technically excluded from Unicode scalar
        // values, but Verus and Rust's `char` don't track that, and
        // omega's simpler with a single upper-bound literal.)
        IntRange::Char => Some(LExpr::lt(e.clone(), LExpr::lit_int("0x110000"))),
        IntRange::Nat | IntRange::Int => None,
    }
}

/// `true` iff VIR's `IntRange` renders as Lean `Int` (the signed side
/// plus unbounded `Int`, and also fixed-width u-types — their spec-mode
/// subtraction is mathematical rather than truncating). The complement
/// — `Nat`, `USize`, `Char` — renders as `Nat`. Keep in sync with
/// `to_lean_type::typ_to_expr`.
///
/// Shared between the SST path (`clip_to_node` below) and the VIR-AST
/// path (`to_lean_expr.rs`) so Clip coercions stay consistent across
/// both renderers — relevant because exec-fn callees inline their
/// `require`/`ensure` via the VIR path while their own theorems render
/// via the SST path. Divergence would produce a different inlined
/// spec than the callee actually proved (silent soundness hole).
pub(crate) fn renders_as_lean_int(range: &IntRange) -> bool {
    matches!(
        range,
        IntRange::Int | IntRange::I(_) | IntRange::ISize | IntRange::U(_)
    )
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
fn clip_to_node_checked(src: &Typ, dst: &IntRange, inner: &Exp) -> Result<ExprNode, String> {
    let src_range = match &**src {
        TypX::Int(r) => r,
        // Boxed int? Peel the box; otherwise the inner isn't an int type
        // at all (shouldn't happen for Clip) and we pass through.
        TypX::Boxed(t) => if let TypX::Int(r) = &**t { r } else {
            return exp_to_node_checked(inner);
        },
        _ => return exp_to_node_checked(inner),
    };
    let rendered = sst_exp_to_ast_checked(inner)?;
    Ok(match (renders_as_lean_int(src_range), renders_as_lean_int(dst)) {
        (true, false) => LExpr::app1(LExpr::var("Int.toNat"), rendered).node,
        (false, true) => LExpr::app1(LExpr::var("Int.ofNat"), rendered).node,
        _ => rendered.node,
    })
}

/// Render a `CheckDecreaseHeight` arg with Verus's param-substitution
/// `Bind(Let)` wrapper zeta-reduced. The normal `Bind(Let)` rendering
/// emits `let x := v; body`, which defeats omega's let-handling when
/// the bound name shadows a caller-scope variable (common in self-
/// recursion: callee's decrease uses the callee's param names, which
/// equal the caller's when self == callee). Substituting directly at
/// the Lean AST level via `lean_ast::substitute` removes the shadow
/// and leaves omega-friendly arithmetic.
///
/// Only descends through top-level `Bind(Let)` wrappers; other shapes
/// render as-is via `sst_exp_to_ast`.
fn render_checked_decrease_arg(e: &Exp) -> Result<LExpr, String> {
    match &e.x {
        // Peel transparent SST wrappers — poly Box/Unbox (inserted
        // by Verus's Poly encoding for heterogeneous int types),
        // mode coercions, and trigger markers all render identically
        // to their inner expression. Peeling here lets us reach a
        // Bind(Let) that sits underneath.
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner)
        | ExpX::Unary(UnaryOp::CoerceMode { .. } | UnaryOp::Trigger(_), inner) => {
            render_checked_decrease_arg(inner)
        }
        ExpX::Bind(bnd, body) => match &bnd.x {
            BndX::Let(binders) => {
                let mut subst: std::collections::HashMap<String, LExpr> =
                    std::collections::HashMap::new();
                for b in binders.iter() {
                    subst.insert(
                        crate::to_lean_type::sanitize(&b.name.0),
                        sst_exp_to_ast_checked(&b.a)?,
                    );
                }
                let body_rendered = render_checked_decrease_arg(body)?;
                Ok(substitute(&body_rendered, &subst))
            }
            _ => sst_exp_to_ast_checked(e),
        },
        _ => sst_exp_to_ast_checked(e),
    }
}

fn exp_to_node_checked(e: &Exp) -> Result<ExprNode, String> {
    Ok(match &e.x {
        ExpX::Const(c) => const_to_node_checked(c)?,
        ExpX::Var(ident) | ExpX::VarLoc(ident) | ExpX::VarAt(ident, _) => {
            ExprNode::Var(sanitize(&ident.0))
        }
        ExpX::StaticVar(fun) | ExpX::ExecFnByName(fun) => {
            ExprNode::Var(lean_name(&fun.path))
        }

        ExpX::Unary(UnaryOp::Not, inner) => LExpr::not(sst_exp_to_ast_checked(inner)?).node,
        ExpX::Unary(UnaryOp::Clip { range, .. }, inner) => {
            clip_to_node_checked(&inner.typ, range, inner)?
        }
        ExpX::Unary(UnaryOp::CoerceMode { .. }, inner)
        | ExpX::Unary(UnaryOp::Trigger(_), inner) => exp_to_node_checked(inner)?,
        ExpX::Unary(op, _) => {
            return Err(format!("unsupported unary op: {:?}", op));
        }

        // Box/Unbox: transparent. Field projection.
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner) => {
            exp_to_node_checked(inner)?
        }
        ExpX::UnaryOpr(UnaryOpr::Field(field_opr), inner) => {
            LExpr::field_proj(sst_exp_to_ast_checked(inner)?, sanitize(&field_opr.field)).node
        }
        // `HasType(e, t)` — the refinement constraint for `e` to inhabit
        // `t`. For fixed-width ints (u8, i32, …) this is the bounds check
        // Verus emits at every arithmetic site. For unbounded types (Nat,
        // Int, structs) it's vacuous; we emit `True` and let Lean simplify.
        ExpX::UnaryOpr(UnaryOpr::HasType(t), inner) => {
            let e_ast = sst_exp_to_ast_checked(inner)?;
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
                return Ok(integer_type_bound_node(kind, 0));
            }
            let bits = const_u32_from_sst(inner).ok_or_else(|| format!(
                "IntegerTypeBound({:?}): non-constant bit width is not supported \
                 (SST inner = {:?})",
                kind, inner.x,
            ))?;
            integer_type_bound_node(kind, bits)
        }
        ExpX::UnaryOpr(_, inner) => exp_to_node_checked(inner)?,

        ExpX::Binary(op, lhs, rhs) => {
            match op {
                BinaryOp::HeightCompare { .. }
                | BinaryOp::Index(_, _)
                | BinaryOp::StrGetChar
                | BinaryOp::IeeeFloat(_) => {
                    return Err(format!("unsupported binary op: {:?}", op));
                }
                _ => {}
            }
            let (l, r) = (sst_exp_to_ast_checked(lhs)?, sst_exp_to_ast_checked(rhs)?);
            match binop_to_ast(op) {
                Some(l_op) => LExpr::binop(l_op, l, r).node,
                // Non-structural: emit as `head lhs rhs` via App. The
                // only reachable case is `Xor`, which renders as `xor
                // lhs rhs` (the rejected ops already early-exited above).
                None => LExpr::app(LExpr::var("xor"), vec![l, r]).node,
            }
        }
        ExpX::BinaryOpr(BinaryOpr::ExtEq(_, _), lhs, rhs) => {
            LExpr::eq(sst_exp_to_ast_checked(lhs)?, sst_exp_to_ast_checked(rhs)?).node
        }

        ExpX::If(cond, then_e, else_e) => ExprNode::If {
            cond: Box::new(sst_exp_to_ast_checked(cond)?),
            then_: Box::new(sst_exp_to_ast_checked(then_e)?),
            else_: Some(Box::new(sst_exp_to_ast_checked(else_e)?)),
        },

        ExpX::Call(CallFun::Fun(fun, _), typs, args)
        | ExpX::Call(CallFun::Recursive(fun), typs, args) => {
            let head = LExpr::app(
                LExpr::var(lean_name(&fun.path)),
                typs.iter().map(|t| typ_to_expr(t)).collect(),
            );
            let rendered_args: Result<Vec<_>, _> = args.iter()
                .map(|a| sst_exp_to_ast_checked(a))
                .collect();
            LExpr::app(head, rendered_args?).node
        }
        // `CheckDecreaseHeight(cur, prev, otherwise)` is the
        // termination obligation Verus inserts before each recursive
        // call (including mutual recursion across an SCC; see
        // `vir::recursion::check_decrease_call`). Per the prelude
        // axiom (`vir/src/prelude.rs:1019-1028`), its semantics is:
        //
        //   height_lt(height(cur), height(prev))
        //     ∨ (height(cur) = height(prev) ∧ otherwise)
        //
        // For int-typed decreases (`TypX::Int`), `height` is the
        // identity (modulo poly box/unbox), and the prelude also
        // axiomatises `height_lt(height(c), height(p)) ↔ 0 ≤ c ∧ c <
        // p` (`vir/src/prelude.rs:1030-1037`). So we can inline the
        // whole thing directly at the Lean level — no `height`
        // function needed, no axioms, completely transparent.
        //
        // For non-int (datatype) decreases, the `height` function is
        // non-trivial (encodes structural recursion on the datatype).
        // We don't support that yet; reject here if the decrease type
        // isn't int-like.
        ExpX::Call(CallFun::InternalFun(InternalFun::CheckDecreaseHeight), _, args) => {
            if args.len() != 3 {
                return Err(format!(
                    "CheckDecreaseHeight expects 3 args (cur, prev, otherwise), got {}",
                    args.len()
                ));
            }
            if !is_int_height(&args[0].typ) {
                return Err(format!(
                    "recursive call termination check with non-int decrease \
                     (type {:?}) not yet supported — only int decreases work today",
                    args[0].typ
                ));
            }
            // `cur` is shaped as `let params = args in decrease_expr`
            // (see `recursion::check_decrease_call`), i.e., Verus
            // encodes parameter substitution via a BndX::Let. Render
            // it with the let zeta-reduced so omega can see the
            // substituted expression directly.
            let cur = render_checked_decrease_arg(&args[0])?;
            let prev = render_checked_decrease_arg(&args[1])?;
            let otherwise = sst_exp_to_ast_checked(&args[2])?;
            // (0 ≤ cur ∧ cur < prev) ∨ (cur = prev ∧ otherwise)
            let lt_branch = LExpr::and(
                LExpr::le(LExpr::lit_int("0"), cur.clone()),
                LExpr::lt(cur.clone(), prev.clone()),
            );
            let eq_branch = LExpr::and(LExpr::eq(cur, prev), otherwise);
            LExpr::or(lt_branch, eq_branch).node
        }
        ExpX::Call(CallFun::InternalFun(_), _, _) => {
            return Err("internal function calls not yet supported".to_string());
        }

        ExpX::Bind(bnd, body) => match &bnd.x {
            BndX::Let(binders) => {
                // Validate + render binder values first. The closure
                // returns `Result<(String, LExpr), String>`; `collect`
                // flips it into `Result<Vec<_>, String>` which `?`
                // unwraps to a plain Vec for the fold.
                let rendered_binders = binders.iter()
                    .map(|b| sst_exp_to_ast_checked(&b.a)
                        .map(|val| (sanitize(&b.name.0), val)))
                    .collect::<Result<Vec<_>, _>>()?;
                let body_rendered = sst_exp_to_ast_checked(body)?;
                // Nest single-variable lets right-to-left so each binder is
                // in scope for the remainder.
                let out = rendered_binders.into_iter().rev().fold(body_rendered, |acc, (name, val)| {
                    LExpr::let_bind(name, val, acc)
                });
                out.node
            }
            BndX::Quant(quant, binders, _, _) => {
                let l_binders: Vec<LBinder> = binders.iter().map(|b| LBinder {
                    name: Some(sanitize(&b.name.0)),
                    ty: typ_to_expr(&b.a),
                    kind: BinderKind::Explicit,
                }).collect();
                let body = Box::new(sst_exp_to_ast_checked(body)?);
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
                body: Box::new(sst_exp_to_ast_checked(body)?),
            },
            BndX::Choose(binders, _, cond) => {
                // `Classical.epsilon (fun (x : T) => cond ∧ body)`
                let l_binders: Vec<LBinder> = binders.iter().map(|b| LBinder {
                    name: Some(sanitize(&b.name.0)),
                    ty: typ_to_expr(&b.a),
                    kind: BinderKind::Explicit,
                }).collect();
                let cond_ast = sst_exp_to_ast_checked(cond)?;
                let body_ast = sst_exp_to_ast_checked(body)?;
                let lambda = LExpr::new(ExprNode::Lambda {
                    binders: l_binders,
                    body: Box::new(LExpr::and(cond_ast, body_ast)),
                });
                LExpr::app1(LExpr::var("Classical.epsilon"), lambda).node
            }
        },

        ExpX::WithTriggers(_, inner) | ExpX::Loc(inner) => exp_to_node_checked(inner)?,

        ExpX::NullaryOpr(_) => ExprNode::LitBool(true),

        // Forms we don't know how to render.
        ExpX::Ctor(..) => return Err(
            "datatype constructors not yet supported in exec fns".to_string()
        ),
        ExpX::CallLambda(..) => return Err(
            "closure calls not yet supported in exec fns".to_string()
        ),
        ExpX::ArrayLiteral(_) => return Err(
            "array literals not yet supported in exec fns".to_string()
        ),
        ExpX::Old(..) => return Err(
            "`old(...)` not yet supported in exec fns".to_string()
        ),
        ExpX::Interp(_) => return Err(
            "Interp nodes should never escape the interpreter (internal bug)".to_string()
        ),
        ExpX::FuelConst(_) => return Err("FuelConst not yet supported".to_string()),
    })
}

/// Does this type bottom out at `TypX::Int(_)` once transparent
/// wrappers (`Boxed`, `Decorate`) are peeled? Mirrors
/// `vir::recursion::height_is_int`.
fn is_int_height(typ: &Typ) -> bool {
    match &**typ {
        TypX::Int(_) => true,
        TypX::Boxed(inner) | TypX::Decorate(_, _, inner) => is_int_height(inner),
        _ => false,
    }
}

fn const_to_node_checked(c: &Constant) -> Result<ExprNode, String> {
    Ok(match c {
        Constant::Bool(b) => ExprNode::LitBool(*b),
        Constant::Int(n) => ExprNode::Lit(n.to_string()),
        Constant::StrSlice(s) => ExprNode::LitStr(s.to_string()),
        Constant::Char(c) => ExprNode::LitChar(*c),
        Constant::Real(_) | Constant::Float32(_) | Constant::Float64(_) => {
            return Err(format!("unsupported constant: {:?}", c));
        }
    })
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
