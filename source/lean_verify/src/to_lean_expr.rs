//! Translate VIR-AST expressions to `lean_ast::Expr`.

use vir::ast::*;
use crate::lean_ast::{
    BinOp as L, Binder as LBinder, BinderKind, Expr as LExpr,
    ExprNode, MatchArm as LMatchArm, Pattern as LPattern,
};
use crate::to_lean_type::{lean_name, sanitize, short_name, typ_to_expr};

/// Build a `lean_ast::Expr` from a VIR-AST expression.
pub fn vir_expr_to_ast(expr: &Expr) -> LExpr {
    LExpr::new(expr_to_node(expr))
}

/// Build `VarBinders<Typ>` → AST binders for proof/spec fn parameters.
/// Each becomes an explicit `(name : Type)` binder.
pub(crate) fn vir_var_binders_to_ast(binders: &VarBinders<Typ>) -> Vec<LBinder> {
    binders.iter().map(|b| LBinder {
        name: Some(sanitize(b.name.0.as_str())),
        ty: typ_to_expr(&b.a),
        kind: BinderKind::Explicit,
    }).collect()
}

// ── Internal: build ExprNode ────────────────────────────────────────────

// Local aliases delegating to `LExpr`'s smart constructors. Keep the
// short names around — most call sites read better as `var("Real")` or
// `apply("Int.floor", …)` than as the longer chained form.
fn var(name: impl Into<String>) -> LExpr { LExpr::var(name) }

fn apply(head: &str, args: Vec<LExpr>) -> ExprNode {
    LExpr::app(LExpr::var(head), args).node
}

fn expr_to_node(expr: &Expr) -> ExprNode {
    match &expr.x {
        ExprX::Const(c) => const_to_node(c),
        ExprX::Var(ident) => ExprNode::Var(sanitize(&ident.0)),
        ExprX::VarAt(ident, _) => ExprNode::Var(sanitize(&ident.0)),
        ExprX::VarLoc(ident) => ExprNode::Var(sanitize(&ident.0)),
        ExprX::ConstVar(fun, _) => ExprNode::Var(lean_name(&fun.path)),
        ExprX::StaticVar(fun) | ExprX::ExecFnByName(fun) => ExprNode::Var(lean_name(&fun.path)),

        ExprX::Binary(op, lhs, rhs) => {
            let (l, r) = (vir_expr_to_ast(lhs), vir_expr_to_ast(rhs));
            match binop_to_ast(op) {
                Some(l_op) => LExpr::binop(l_op, l, r).node,
                // Non-structural: emit as `head lhs rhs` via App so the pp
                // layer handles precedence and spans flow through normally.
                None => LExpr::app(LExpr::var(non_binop_head(op)), vec![l, r]).node,
            }
        }

        ExprX::BinaryOpr(BinaryOpr::ExtEq(_, _), lhs, rhs) => {
            LExpr::eq(vir_expr_to_ast(lhs), vir_expr_to_ast(rhs)).node
        }

        ExprX::Unary(UnaryOp::Not, inner) => LExpr::not(vir_expr_to_ast(inner)).node,
        ExprX::Unary(UnaryOp::Clip { range, .. }, inner) => {
            // Keep in sync with `to_lean_sst_expr::clip_to_node`: the
            // set of ranges that render as Lean `Int` vs `Nat` has to
            // agree between the two paths.
            let renders_int = |r: &IntRange| matches!(
                r,
                IntRange::Int | IntRange::I(_) | IntRange::ISize | IntRange::U(_)
            );
            let src_int = matches!(&*inner.typ, TypX::Int(r) if renders_int(r));
            let dst_int = renders_int(range);
            match (src_int, dst_int) {
                (true, false) => apply("Int.toNat", vec![vir_expr_to_ast(inner)]),
                (false, true) => apply("Int.ofNat", vec![vir_expr_to_ast(inner)]),
                _ => expr_to_node(inner),
            }
        }
        ExprX::Unary(UnaryOp::CoerceMode { .. }, inner)
        | ExprX::Unary(UnaryOp::Trigger(_), inner) => expr_to_node(inner),

        ExprX::Unary(UnaryOp::BitNot(_), inner) => apply(
            "Complement.complement",
            vec![vir_expr_to_ast(inner)],
        ),
        ExprX::Unary(UnaryOp::IntToReal, inner) => {
            LExpr::type_annot(vir_expr_to_ast(inner), LExpr::var("Real")).node
        }
        ExprX::Unary(UnaryOp::RealToInt, inner) => apply(
            "Int.floor",
            vec![vir_expr_to_ast(inner)],
        ),
        ExprX::Unary(UnaryOp::FloatToBits, inner) => expr_to_node(inner),
        ExprX::Unary(UnaryOp::IeeeFloat(_), inner) => expr_to_node(inner),
        // Remaining unary ops: transparent annotations/markers/internal ops.
        ExprX::Unary(_, inner) => expr_to_node(inner),

        ExprX::Call(target, args, _) => call_to_node(target, args),

        ExprX::If(cond, then_e, else_e) => ExprNode::If {
            cond: Box::new(vir_expr_to_ast(cond)),
            then_: Box::new(vir_expr_to_ast(then_e)),
            else_: else_e.as_ref().map(|e| Box::new(vir_expr_to_ast(e))),
        },

        ExprX::Quant(quant, binders, body) => {
            let l_binders = vir_var_binders_to_ast(binders);
            let body = Box::new(vir_expr_to_ast(body));
            match quant.quant {
                air::ast::Quant::Forall => ExprNode::Forall { binders: l_binders, body },
                air::ast::Quant::Exists => ExprNode::Exists { binders: l_binders, body },
            }
        }

        ExprX::Choose { params, cond, body: _ } => {
            // `Classical.epsilon (fun (x : T) ... => P)` — the epsilon operator
            // returns *some* witness satisfying P if one exists. No existence
            // proof is required because `Classical.epsilon` is total.
            let lambda = LExpr::new(ExprNode::Lambda {
                binders: vir_var_binders_to_ast(params),
                body: Box::new(vir_expr_to_ast(cond)),
            });
            LExpr::app1(LExpr::var("Classical.epsilon"), lambda).node
        }

        ExprX::WithTriggers { body, .. } => expr_to_node(body),

        ExprX::Block(stmts, final_expr) => block_to_node(stmts, final_expr.as_ref()),

        ExprX::Closure(params, body) => ExprNode::Lambda {
            binders: vir_var_binders_to_ast(params),
            body: Box::new(vir_expr_to_ast(body)),
        },

        ExprX::Ctor(dt, variant, fields, update) => {
            if let Some(tail) = update {
                ExprNode::StructUpdate {
                    base: Box::new(place_to_expr(&tail.place.x)),
                    updates: fields.iter().map(|f|
                        (sanitize(&f.name), vir_expr_to_ast(&f.a))
                    ).collect(),
                }
            } else {
                ctor_to_node(dt, variant, fields)
            }
        }

        ExprX::Match(place, arms) => ExprNode::Match {
            scrutinee: Box::new(place_to_expr(&place.x)),
            arms: arms.iter().map(|arm| LMatchArm {
                pattern: pattern_to_ast(&arm.x.pattern.x),
                body: vir_expr_to_ast(&arm.x.body),
            }).collect(),
        },

        ExprX::Ghost { expr, .. } | ExprX::ProofInSpec(expr) => expr_to_node(expr),
        ExprX::Loc(expr) => expr_to_node(expr),

        ExprX::ReadPlace(place, _) => place_to_expr(&place.x).node,

        ExprX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner) => expr_to_node(inner),
        ExprX::UnaryOpr(UnaryOpr::Field(field_opr), inner) => {
            LExpr::field_proj(vir_expr_to_ast(inner), field_access_name(field_opr)).node
        }
        ExprX::UnaryOpr(UnaryOpr::IsVariant { variant, .. }, inner) => {
            LExpr::field_proj(vir_expr_to_ast(inner), format!("is{}", variant)).node
        }
        ExprX::UnaryOpr(UnaryOpr::HasType(t), inner) => {
            // Refinement invariant: `e < 2^n` for `U(n)`, `-2^(n-1) ≤ e ∧
            // e < 2^(n-1)` for `I(n)`, etc. Mirrors the `to_lean_sst_expr`
            // version — proof fns and exec fns must agree on what
            // `HasType` means.
            let e_ast = vir_expr_to_ast(inner);
            crate::to_lean_sst_expr::type_bound_predicate(&e_ast, t)
                .map(|pred| pred.node)
                .unwrap_or(ExprNode::LitBool(true))
        }
        ExprX::UnaryOpr(UnaryOpr::IntegerTypeBound(kind, _), inner) => {
            // Same handling as the SST path: evaluate the bit width at
            // codegen and emit the literal bound. Split out to a shared
            // helper so the two paths can't drift.
            crate::to_lean_sst_expr::integer_type_bound_from_vir(kind, inner).node
        }
        ExprX::UnaryOpr(UnaryOpr::CustomErr(_), inner) => expr_to_node(inner),
        ExprX::UnaryOpr(_, inner) => expr_to_node(inner),

        ExprX::NullaryOpr(NullaryOpr::ConstGeneric(typ)) => {
            // const generic parameter used as a value — the VIR typ is the
            // generic parameter's name/type (typically `TypParam(N)`), and we
            // emit it as an identifier expression. `(typ : typ)` would be
            // nonsense; just render the typ as an expression.
            typ_to_expr(typ).node
        }
        ExprX::NullaryOpr(_) => ExprNode::LitBool(true),

        ExprX::Multi(_, exprs) => {
            // VIR's Multi carries a list of operands (tuple construction,
            // chained conjunction, etc.). Render as Lean's anonymous
            // constructor `⟨a, b, c⟩` — correct for tuples, works for any
            // shape where the target type is inferred from context.
            LExpr::anon(exprs.iter().map(|e| vir_expr_to_ast(e)).collect()).node
        }
        ExprX::ArrayLiteral(exprs) => {
            ExprNode::ArrayLit(exprs.iter().map(|e| vir_expr_to_ast(e)).collect())
        }

        // `ExprX::Header` is a requires/ensures marker that VIR
        // simplification strips before spec fn bodies reach us. Reaching
        // it would mean the pipeline ordering got swapped.
        ExprX::Header(_) => panic!(
            "ExprX::Header in spec fn body — VIR should have stripped it \
             before translation"
        ),
        // `BreakOrContinue` is exec-mode only.
        ExprX::BreakOrContinue { .. } => panic!(
            "ExprX::BreakOrContinue in spec fn body — VIR mode checker bug"
        ),
        // Z3-specific markers that have no Lean analogue: fuel control,
        // hidden-string reveals, raw AIR statements. They're genuinely
        // effectless at our layer, so emit nothing.
        ExprX::Fuel(..) | ExprX::RevealString(_) | ExprX::AirStmt(_) => {
            ExprNode::Raw(String::new())
        }
        ExprX::Nondeterministic => {
            LExpr::app1(LExpr::var("Classical.arbitrary"), LExpr::var("_")).node
        }

        // Exec-mode forms — VIR mode checker guarantees these don't appear
        // inside spec fn bodies.
        ExprX::Assign { .. } | ExprX::AssignToPlace { .. }
        | ExprX::Loop { .. } | ExprX::Return(_) | ExprX::NonSpecClosure { .. } => {
            panic!("exec-mode expression in spec fn body — VIR mode checker bug");
        }

        ExprX::AssertAssume { expr: e, .. }
        | ExprX::AssertAssumeUserDefinedTypeInvariant { expr: e, .. }
        | ExprX::AssertCompute(e, _)
        | ExprX::NeverToAny(e) => expr_to_node(e),
        ExprX::AssertBy { ensure, .. } => expr_to_node(ensure),
        ExprX::AssertQuery { .. } => ExprNode::LitBool(true),
        ExprX::OpenInvariant(_, _, body, _) => expr_to_node(body),

        ExprX::Old(e) | ExprX::EvalAndResolve(_, e) => expr_to_node(e),
        ExprX::BorrowMut(_) | ExprX::TwoPhaseBorrowMut(_)
        | ExprX::BorrowMutTracked(_) => ExprNode::Var("()".into()),
        ExprX::ImplicitReborrowOrSpecRead(place, _, _) => place_to_expr(&place.x).node,
    }
}

// ── Helpers ─────────────────────────────────────────────────────────────

fn const_to_node(c: &Constant) -> ExprNode {
    match c {
        Constant::Bool(b) => ExprNode::LitBool(*b),
        Constant::Int(n) => ExprNode::Lit(n.to_string()),
        Constant::StrSlice(s) => ExprNode::LitStr(s.to_string()),
        Constant::Char(c) => ExprNode::LitChar(*c),
        Constant::Real(s) => ExprNode::TypeAnnot {
            expr: Box::new(LExpr::new(ExprNode::Lit(s.to_string()))),
            ty: Box::new(var("Real")),
        },
        Constant::Float32(bits) => ExprNode::TypeAnnot {
            expr: Box::new(LExpr::new(ExprNode::Lit(f32::from_bits(*bits).to_string()))),
            ty: Box::new(var("Float")),
        },
        Constant::Float64(bits) => ExprNode::TypeAnnot {
            expr: Box::new(LExpr::new(ExprNode::Lit(f64::from_bits(*bits).to_string()))),
            ty: Box::new(var("Float")),
        },
    }
}

/// Map VIR binary ops we model structurally. `None` means "emit via Raw".
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
        // These aren't real Lean binary operators; callers route them through
        // `App` with an explicit head name.
        BinaryOp::Xor
        | BinaryOp::HeightCompare { .. }
        | BinaryOp::StrGetChar
        | BinaryOp::Index(_, _)
        | BinaryOp::IeeeFloat(_) => return None,
    })
}

/// Head identifier used when a VIR binop is expressed as a 2-arg function
/// call rather than a structural `BinOp`. Kept narrow: these all render
/// harmlessly if the call ever gets executed — they're just stand-ins.
fn non_binop_head(op: &BinaryOp) -> &'static str {
    match op {
        BinaryOp::Xor => "xor",
        BinaryOp::HeightCompare { .. } => "Tactus.heightLt",
        BinaryOp::StrGetChar => "String.get",
        BinaryOp::Index(_, _) => "Tactus.index",
        BinaryOp::IeeeFloat(_) => "Tactus.floatOp",
        _ => "?",
    }
}

fn call_to_node(target: &CallTarget, args: &Exprs) -> ExprNode {
    let head = match target {
        CallTarget::Fun(kind, fun, typs, _, _, _) => {
            match kind {
                CallTargetKind::DynamicResolved { resolved, .. } => {
                    var(&lean_name(&resolved.path))
                }
                CallTargetKind::Dynamic => trait_method_ref(fun),
                _ => {
                    // Emit explicit type arguments for generic calls by
                    // building an intermediate App head: `fn T1 T2 …`.
                    let base = var(&lean_name(&fun.path));
                    if typs.is_empty() {
                        base
                    } else {
                        LExpr::new(ExprNode::App {
                            head: Box::new(base),
                            args: typs.iter().map(|t| typ_to_expr(t)).collect(),
                        })
                    }
                }
            }
        }
        CallTarget::FnSpec(inner) => vir_expr_to_ast(inner),
        CallTarget::BuiltinSpecFun(_, typs, _) => {
            let base = var("builtinSpecFun");
            if typs.is_empty() {
                base
            } else {
                LExpr::new(ExprNode::App {
                    head: Box::new(base),
                    args: typs.iter().map(|t| typ_to_expr(t)).collect(),
                })
            }
        }
    };
    if args.is_empty() {
        head.node
    } else {
        ExprNode::App {
            head: Box::new(head),
            args: args.iter().map(|a| vir_expr_to_ast(a)).collect(),
        }
    }
}

fn trait_method_ref(fun: &Fun) -> LExpr {
    let segs = &fun.path.segments;
    if segs.len() >= 2 {
        let t = sanitize(segs[segs.len() - 2].as_str());
        let m = sanitize(segs[segs.len() - 1].as_str());
        var(&format!("{}.{}", t, m))
    } else {
        var(&lean_name(&fun.path))
    }
}

/// Map a VIR field access name to the one the Lean side expects.
///
/// * Anonymous tuple (`Dt::Tuple`) uses 0-indexed numeric fields like `"0"`
///   and `"1"`; Lean's `Prod`-derived accessor is 1-indexed (`.1`, `.2`).
///   So `"0"` → `"1"`, `"1"` → `"2"`, etc.
/// * Tuple-struct variant (`Dt::Path` with numeric field names): our
///   datatype emitter renames the fields to `val0` / `val1` / … (see
///   `to_lean_fn::field_name`), so access must match.
/// * Named struct fields pass through unchanged (after identifier
///   sanitization).
fn field_access_name(field_opr: &FieldOpr) -> String {
    let raw = field_opr.field.as_str();
    let numeric = raw.parse::<usize>().ok();
    match (&field_opr.datatype, numeric) {
        (Dt::Tuple(_), Some(n)) => (n + 1).to_string(),
        (Dt::Path(_), Some(n)) => format!("val{}", n),
        _ => sanitize(raw),
    }
}

fn ctor_to_node(dt: &Dt, variant: &Ident, fields: &Binders<Expr>) -> ExprNode {
    match dt {
        Dt::Path(path) => {
            let type_name = lean_name(path);
            let variant_seg = if variant.as_str() == short_name(path) {
                "mk".to_string()
            } else {
                sanitize(variant)
            };
            let head = format!("{}.{}", type_name, variant_seg);
            if fields.is_empty() {
                ExprNode::Var(head)
            } else {
                ExprNode::App {
                    head: Box::new(var(&head)),
                    args: fields.iter().map(|f| vir_expr_to_ast(&f.a)).collect(),
                }
            }
        }
        // Anonymous tuple → Lean anonymous constructor `⟨a, b, c⟩`, which
        // elaborates against the tuple's product type.
        Dt::Tuple(_) => ExprNode::Anon(
            fields.iter().map(|f| vir_expr_to_ast(&f.a)).collect()
        ),
    }
}

/// Fold a VIR `Block` into nested Lean lets.
///
/// * `StmtX::Decl { pattern: Var(x), init: Some(e) }`  →  `let x := e; rest`
/// * `StmtX::Decl { pattern: <non-var>, init: Some(e) }`  →  `match e with | p => rest`
///   (Lean pattern-lets require `match` for non-variable LHS.)
/// * `StmtX::Expr(e)` with a following statement  →  `let _ := e; rest`
///   (drops the value like Rust's `;` does).
/// * Last stmt with no `final_expr` is the body.
fn block_to_node(stmts: &[Stmt], final_expr: Option<&Expr>) -> ExprNode {
    let body = match final_expr {
        Some(e) => vir_expr_to_ast(e),
        None if stmts.is_empty() => LExpr::new(ExprNode::Var("()".into())),
        // No final expression — the last stmt's value is the block's value.
        // In spec mode this is unusual; fall back to unit.
        None => LExpr::new(ExprNode::Var("()".into())),
    };

    let mut folded = body;
    for stmt in stmts.iter().rev() {
        folded = match &stmt.x {
            StmtX::Decl { pattern, init, .. } => {
                let value = match init {
                    Some(place) => place_to_expr(&place.x),
                    // No initializer (e.g., `let x;`) — give a placeholder.
                    None => LExpr::new(ExprNode::Var("_".into())),
                };
                match &pattern.x {
                    PatternX::Var(binding) => LExpr::new(ExprNode::Let {
                        name: sanitize(&binding.name.0),
                        value: Box::new(value),
                        body: Box::new(folded),
                    }),
                    other => LExpr::new(ExprNode::Match {
                        scrutinee: Box::new(value),
                        arms: vec![crate::lean_ast::MatchArm {
                            pattern: pattern_to_ast(other),
                            body: folded,
                        }],
                    }),
                }
            }
            StmtX::Expr(e) => LExpr::new(ExprNode::Let {
                name: "_".to_string(),
                value: Box::new(vir_expr_to_ast(e)),
                body: Box::new(folded),
            }),
        };
    }
    folded.node
}

// ── Patterns ────────────────────────────────────────────────────────────

pub(crate) fn pattern_to_ast(pat: &PatternX) -> LPattern {
    match pat {
        PatternX::Wildcard(_) => LPattern::Wildcard,
        PatternX::Var(binding) => LPattern::Var(sanitize(&binding.name.0)),
        PatternX::Constructor(dt, variant, pats) => {
            let name = match dt {
                Dt::Path(path) => {
                    let v = if variant.as_str() == short_name(path) {
                        "mk".to_string()
                    } else {
                        sanitize(variant)
                    };
                    format!("{}.{}", lean_name(path), v)
                }
                Dt::Tuple(_) => sanitize(variant),
            };
            LPattern::Ctor {
                name,
                args: pats.iter().map(|p| pattern_to_ast(&p.a.x)).collect(),
            }
        }
        PatternX::Or(l, r) => LPattern::Or(
            Box::new(pattern_to_ast(&l.x)),
            Box::new(pattern_to_ast(&r.x)),
        ),
        PatternX::Binding { binding, sub_pat } => LPattern::Binding {
            name: sanitize(&binding.name.0),
            sub: Box::new(pattern_to_ast(&sub_pat.x)),
        },
        PatternX::Expr(e) => LPattern::Lit(expr_to_node(e)),
        PatternX::Range(lo, _hi) => {
            // Lean doesn't have numeric range patterns; fall back to the low
            // bound (or wildcard if absent). Range patterns are rare in spec
            // mode (ast_simplify usually eliminates Match).
            match lo {
                Some(e) => LPattern::Lit(expr_to_node(e)),
                None => LPattern::Wildcard,
            }
        }
        PatternX::MutRef(inner) | PatternX::ImmutRef(inner) => pattern_to_ast(&inner.x),
    }
}

// ── Places ──────────────────────────────────────────────────────────────

fn place_to_expr(place: &PlaceX) -> LExpr {
    LExpr::new(match place {
        PlaceX::Local(ident) => ExprNode::Var(sanitize(&ident.0)),
        PlaceX::Field(field_opr, base) => ExprNode::FieldProj {
            expr: Box::new(place_to_expr(&base.x)),
            field: field_access_name(field_opr),
        },
        PlaceX::DerefMut(inner) | PlaceX::ModeUnwrap(inner, _) => {
            return place_to_expr(&inner.x);
        }
        PlaceX::Temporary(expr) => return vir_expr_to_ast(expr),
        PlaceX::WithExpr(_, place) => return place_to_expr(&place.x),
        PlaceX::Index(base, idx, _, _) => ExprNode::Index {
            base: Box::new(place_to_expr(&base.x)),
            idx: Box::new(vir_expr_to_ast(idx)),
        },
        PlaceX::UserDefinedTypInvariantObligation(inner, _) => {
            return place_to_expr(&inner.x);
        }
    })
}
