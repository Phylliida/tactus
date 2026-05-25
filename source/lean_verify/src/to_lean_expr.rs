//! Translate VIR-AST expressions to `lean_ast::Expr`.

use std::collections::HashMap;
use vir::ast::*;
use crate::expr_shared::{
    apply_clip_coercion, binop_to_ast, const_to_node_common, ctor_node, field_access_name,
    is_variant_node, non_binop_head,
};
use crate::lean_ast::{
    Binder as LBinder, BinderKind, Expr as LExpr,
    ExprNode, MatchArm as LMatchArm, Pattern as LPattern,
};
use crate::to_lean_type::{lean_name, sanitize, short_name, typ_to_expr};

/// Binder context: maps in-scope variable names to their declared types.
/// Threaded through the renderer so `Var(p)` can compare its tagged
/// `expr.typ` to `p`'s actual binder type — if they differ in reference
/// decorations (because Verus's `add_vir_ref_decoration` adjustment
/// decorated the Var's typ without changing the binder), the renderer
/// inserts explicit `Tactus.X.mk` wraps to bridge.
pub(crate) type BinderCtx = HashMap<VarIdent, Typ>;

/// Build a binder context from a function's params. Used by callers
/// (spec_fn_to_ast, proof_fn_to_ast, trait_impl_to_ast, trait_to_ast)
/// to seed the renderer with the fn's params as the initial in-scope
/// binders.
///
/// For params that will be body-shadowed (post-U2: `&mut`-style
/// mutation-encoding cases only, see `to_lean_fn::needs_param_deref`),
/// the recorded typ is stripped of one outer ref decoration to reflect
/// the post-shadow Lean-level reality. For non-shadowed params (`&`-only
/// references), the typ is recorded as-declared — the renderer's
/// bidirectional `apply_ref_coercion_if_needed` handles use-site
/// coercion against this wrapper-decorated typ.
pub(crate) fn binder_ctx_from_params(params: &Params) -> BinderCtx {
    let mut out = BinderCtx::new();
    for p in params.iter() {
        let typ = if crate::expr_shared::is_mut_ref_typ(&p.x.typ, p.x.is_mut) {
            strip_one_ref_decoration(&p.x.typ)
        } else {
            p.x.typ.clone()
        };
        out.insert(p.x.name.clone(), typ);
    }
    out
}

/// Strip exactly one outer reference decoration layer from a typ.
/// Mirrors what the body shadow `let p := p.deref;` does at the Lean
/// level. Returns the typ unchanged if there's no outer ref decoration.
pub(crate) fn strip_one_ref_decoration(typ: &Typ) -> Typ {
    match &**typ {
        TypX::Decorate(deco, _, inner) if decoration_wrapper(*deco).is_some() => {
            inner.clone()
        }
        TypX::MutRef(inner) => inner.clone(),
        _ => typ.clone(),
    }
}

/// Build a `lean_ast::Expr` from a VIR-AST expression with no enclosing
/// binders. Use `vir_expr_to_ast_with_binders` from inside a fn body to
/// pass the fn's params as initial context.
pub fn vir_expr_to_ast(expr: &Expr) -> LExpr {
    vir_expr_to_ast_with_binders(expr, &BinderCtx::new())
}

/// Variant for callee-spec inlining contexts. Suppresses the
/// `apply_ref_coercion_if_needed` lift at `ExprX::ReadPlace` sites
/// (returns None from `structural_typ` for ReadPlace via the
/// `READPLACE_LIFT_ENABLED` thread-local).
///
/// Why: standalone proof / spec / trait-impl-method bodies need the
/// lift to bridge from peeled-binder rendering to decorated-expr.typ
/// (the auto-`&` adjustment from a method call). But callee-spec
/// inlining substitutes the rendered form with a CALLER-provided arg
/// — and post-β refactor, that arg is already wrapper-typed. The
/// lift then over-wraps, requiring a downstream peel (see
/// `build_call_substitutions` / Piece 3 history).
///
/// Disabling the lift at the inlining-render site means the
/// substituted form matches the caller's wrapper-typed arg directly:
/// `Foo.predicate self` + `subst self → b` → `Foo.predicate b`
/// (where b : Tactus.Ref Bar matches the class signature's
/// `Tactus.Ref Self → Prop`).
pub fn vir_expr_to_ast_for_inlining(expr: &Expr) -> LExpr {
    READPLACE_LIFT_ENABLED.with(|cell| {
        let prior = cell.replace(false);
        let result = vir_expr_to_ast_with_binders(expr, &BinderCtx::new());
        cell.set(prior);
        result
    })
}

thread_local! {
    /// Controls whether `structural_typ` for `ExprX::ReadPlace`
    /// returns the place's peeled typ (default true → lift fires via
    /// apply_ref_coercion) or `None` (false → no lift). Toggled
    /// false during `vir_expr_to_ast_for_inlining` and restored on
    /// exit. The default is `true` so non-inlining callers keep
    /// pre-existing behaviour.
    static READPLACE_LIFT_ENABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(true) };
}

/// Build a `lean_ast::Expr` from a VIR-AST expression with the given
/// binder context. Inserts `Tactus.X.mk` wraps where:
/// * `expr.x` is `Const` / `Ctor` / `ArrayLiteral` (structurally
///   undecorated kinds) and `expr.typ` has reference decorations.
/// * `expr.x` is `Var(p)` / `VarLoc(p)` / `VarAt(p, _)` and `p`'s
///   binder typ has FEWER reference decorations than `expr.typ` (Verus's
///   auto-`&` adjustment on a Var leaves the binder untouched).
pub(crate) fn vir_expr_to_ast_with_binders(expr: &Expr, binders: &BinderCtx) -> LExpr {
    let rendered = LExpr::new(expr_to_node(expr, binders));
    apply_ref_coercion_if_needed(expr, rendered, binders)
}

/// Compute the "structural" type of an expression — the type its Lean
/// rendering naturally produces, ignoring Verus's adjustment-driven
/// decorations on `expr.typ`. Returns `None` for kinds where we trust
/// `expr.typ` (e.g., `Call`, `Binary`, `Unary` — Verus's typing for
/// these matches what the rendering produces).
///
/// Used to compute the delta between `expr.typ` and what the rendering
/// produces, so we can insert explicit `Tactus.X.mk` wraps to bridge.
fn structural_typ(expr: &Expr, binders: &BinderCtx) -> Option<Typ> {
    match &expr.x {
        // Constructors and literals produce undecorated values.
        ExprX::Const(_) | ExprX::Ctor(..) | ExprX::ArrayLiteral(_) => {
            // Use the un-decorated form of expr.typ as the structural typ.
            Some(strip_all_ref_decorations(&expr.typ.clone()))
        }
        // Variable references produce the binder's typ.
        ExprX::Var(v) | ExprX::VarLoc(v) | ExprX::VarAt(v, _) => {
            binders.get(v).cloned()
        }
        // ReadPlace's rendering drops the read kind, producing the
        // place's underlying value typ. (The read kind, e.g., ImmutBor
        // for auto-`&`, is what decorates expr.typ.)
        //
        // Binder-aware path (U2 refactor): when the inner Place is
        // `Local(v)`, return `binders.get(v)` — this reflects the
        // ACTUAL Lean-level typ of the rendered variable, accounting
        // for whether a body shadow was applied (BinderCtx records
        // post-shadow typs at construction time). For non-Local
        // places, fall back to `p.typ` (the SST place's typ).
        //
        // Inlining contexts (`vir_expr_to_ast_for_inlining`) flip
        // `READPLACE_LIFT_ENABLED` to false to suppress the lift —
        // the substituted-arg provides the correct wrapper-typed
        // value directly. See the doc on `vir_expr_to_ast_for_inlining`.
        ExprX::ReadPlace(p, _) => {
            if READPLACE_LIFT_ENABLED.with(|cell| cell.get()) {
                match &p.x {
                    PlaceX::Local(v) => binders.get(v).cloned().or_else(|| Some(p.typ.clone())),
                    _ => Some(p.typ.clone()),
                }
            } else {
                None
            }
        }
        // Pass-through expressions: natural typ is the inner's.
        ExprX::Loc(inner) | ExprX::Ghost { expr: inner, .. }
        | ExprX::ProofInSpec(inner) => structural_typ(inner, binders),
        _ => None,
    }
}

/// Strip every reference decoration layer from a typ (and `Boxed`/
/// `MutRef`). Returns the deepest non-decorated `Arc<TypX>`.
fn strip_all_ref_decorations(typ: &Typ) -> Typ {
    match &**typ {
        TypX::Decorate(deco, _, inner) if decoration_wrapper(*deco).is_some() => {
            strip_all_ref_decorations(inner)
        }
        TypX::Boxed(inner) => strip_all_ref_decorations(inner),
        TypX::MutRef(inner) => strip_all_ref_decorations(inner),
        _ => typ.clone(),
    }
}

// `decoration_wrapper` moved to `expr_shared` — shared between this
// renderer's coercion logic, the SST path, and the height-fn /
// body-shadow machinery.
use crate::expr_shared::decoration_wrapper;

/// Walk `typ` outermost-in, collecting Tactus wrapper names for each
/// reference-like `TypX::Decorate` layer. Peels `Boxed` (Verus's poly
/// encoding — Lean-transparent) and skips non-reference decorations.
/// Stops at the first non-Decorate-non-Boxed node.
fn collect_ref_wraps(typ: &TypX) -> Vec<&'static str> {
    let mut out = Vec::new();
    let mut cur = typ;
    loop {
        match cur {
            TypX::Decorate(deco, _, inner) => {
                if let Some(w) = decoration_wrapper(*deco) {
                    out.push(w);
                }
                cur = &**inner;
            }
            TypX::Boxed(inner) => cur = &**inner,
            TypX::MutRef(_) => {
                out.push("Tactus.MutRef");
                break;
            }
            _ => break,
        }
    }
    out
}

/// Apply wraps from innermost to outermost: `wraps[last]` is innermost.
fn apply_ref_wraps(mut e: LExpr, wraps: &[&'static str]) -> LExpr {
    for w in wraps.iter().rev() {
        e = LExpr::app1(LExpr::var_lit(&format!("{}.mk", w)), e);
    }
    e
}

// `count_ref_decorations` moved to `expr_shared`.
use crate::expr_shared::count_ref_decorations;

/// Count of wrapper layers (`Tactus.Ref`/`Box`/`Rc`/`Arc`/`MutRef`)
/// on the actual Lean-level rendering at this site. Used at
/// Field / IsVariant projection sites (both `ExprX` and `PlaceX`
/// arms) to know how many `.deref`s to insert before accessing the
/// inner type's fields/variants.
///
/// `var_id` is the VarIdent if the inner is var-shaped (`Var` /
/// `VarLoc` / `VarAt` for ExprX; `Local` for PlaceX); `None`
/// otherwise. When var-shaped, the actual Lean typ comes from
/// BinderCtx (which post-U2 records post-shadow types — wrapper
/// for &-only params, stripped-typ for &mut). Otherwise we fall
/// back to the spanned typ. Handles the spec-collapse case where
/// Verus's SST may strip decorations from the SST typ while the
/// rendered Lean value still has them.
fn lean_level_wrap_count(var_id: Option<&VarIdent>, spanned_typ: &Typ, binders: &BinderCtx) -> usize {
    let lean_typ = var_id
        .and_then(|v| binders.get(v).cloned())
        .unwrap_or_else(|| spanned_typ.clone());
    count_ref_decorations(&lean_typ)
}

/// Render `inner` and apply a `.deref` chain matching its actual
/// Lean-level wrapper depth. Used at Field / IsVariant projection
/// sites where the field/variant belongs to the inner type rather
/// than the wrapper.
fn render_expr_with_derefs(inner: &Expr, binders: &BinderCtx) -> LExpr {
    let rendered = vir_expr_to_ast_with_binders(inner, binders);
    let var_id = match &inner.x {
        ExprX::Var(v) | ExprX::VarLoc(v) | ExprX::VarAt(v, _) => Some(v),
        _ => None,
    };
    let n_derefs = lean_level_wrap_count(var_id, &inner.typ, binders);
    crate::expr_shared::apply_deref_chain(rendered, n_derefs)
}

/// Place-side analog of `render_expr_with_derefs`. Renders the
/// place's value and applies the matching `.deref` chain.
fn render_place_with_derefs(base: &Place, binders: &BinderCtx) -> LExpr {
    let rendered = place_to_expr(&base.x, binders);
    let var_id = match &base.x {
        PlaceX::Local(v) => Some(v),
        _ => None,
    };
    let n_derefs = lean_level_wrap_count(var_id, &base.typ, binders);
    crate::expr_shared::apply_deref_chain(rendered, n_derefs)
}

fn apply_ref_coercion_if_needed(
    expr: &Expr,
    rendered: LExpr,
    binders: &BinderCtx,
) -> LExpr {
    // Bidirectional coercion. Compute the "structural" typ — what the
    // rendering naturally produces — and compare to `expr.typ`:
    //
    // * `expr.typ` has MORE wrappers than structural → insert
    //   `Tactus.X.mk` for the extra layers (e.g., auto-`&` at a call
    //   site needs to wrap a bare value).
    // * `expr.typ` has FEWER wrappers than structural → insert
    //   `.deref` chain for the difference (e.g., Verus's spec-mode
    //   `**b` collapses to `Var(b)` with expr.typ = bare, but the
    //   binder is wrapper-typed — we need to project out the inner).
    //
    // The equal case renders verbatim.
    let Some(natural) = structural_typ(expr, binders) else {
        return rendered;
    };
    let natural_n = count_ref_decorations(&natural);
    let expr_n = count_ref_decorations(&*expr.typ);
    if expr_n > natural_n {
        let wraps = collect_ref_wraps(&expr.typ);
        // Take the outermost (expr_n - natural_n) wraps; the rest are
        // already accounted for by the structural typ.
        let extra = expr_n - natural_n;
        apply_ref_wraps(rendered, &wraps[..extra])
    } else if expr_n < natural_n {
        crate::expr_shared::apply_deref_chain(rendered, natural_n - expr_n)
    } else {
        rendered
    }
}

/// Build `VarBinders<Typ>` → AST binders for proof/spec fn parameters.
/// Each becomes an explicit `(name : Type)` binder.
pub(crate) fn vir_var_binders_to_ast(binders: &VarBinders<Typ>) -> Vec<LBinder> {
    binders.iter().map(|b| LBinder {
        name: Some(crate::lean_name::LeanName::from_var_ident(&b.name)),
        ty: typ_to_expr(&b.a),
        kind: BinderKind::Explicit,
    }).collect()
}

// ── Internal: build ExprNode ────────────────────────────────────────────

// Local aliases delegating to `LExpr`'s smart constructors. Keep the
// short names around — most call sites read better as `var("Real")` or
// `apply("Int.floor", …)` than as the longer chained form. These
// take `&str` and produce `lit`-typed `LeanName`s, since they're for
// hardcoded prelude / Mathlib references.
fn var(name: &str) -> LExpr { LExpr::var_lit(name) }

fn apply(head: &str, args: Vec<LExpr>) -> ExprNode {
    LExpr::app(LExpr::var_lit(head), args).node
}

fn expr_to_node(expr: &Expr, binders: &BinderCtx) -> ExprNode {
    match &expr.x {
        ExprX::Const(c) => const_to_node(c),
        ExprX::Var(ident) => ExprNode::Var(crate::lean_name::LeanName::from_var_ident(ident)),
        // `VarAt(x, Pre)` collapses to `Var(x)` for the general path
        // (non-mut params, loop ensures' at-entry refs, etc. — these
        // are correct because the AT-entry value equals the current
        // value at the relevant scope). For `&mut` callee-spec
        // inlining, `walk_call` pre-rewrites `VarAt(p, Pre)` to a
        // synthetic distinct name BEFORE this renderer runs, so the
        // substitution map can target pre- and post-state separately.
        // See `walk_call` and `varat_pre_name` for the full picture.
        ExprX::VarAt(ident, _) => ExprNode::Var(crate::lean_name::LeanName::from_var_ident(ident)),
        ExprX::VarLoc(ident) => ExprNode::Var(crate::lean_name::LeanName::from_var_ident(ident)),
        ExprX::ConstVar(fun, _) => ExprNode::Var(crate::lean_name::LeanName::from_path(&fun.path)),
        ExprX::StaticVar(fun) | ExprX::ExecFnByName(fun) => ExprNode::Var(crate::lean_name::LeanName::from_path(&fun.path)),

        ExprX::Binary(op, lhs, rhs) => {
            let (l, r) = (
                vir_expr_to_ast_with_binders(lhs, binders),
                vir_expr_to_ast_with_binders(rhs, binders),
            );
            match binop_to_ast(op) {
                Some(l_op) => LExpr::binop(l_op, l, r).node,
                // Non-structural: emit as `head lhs rhs` via App so the pp
                // layer handles precedence and spans flow through normally.
                // Non-structural heads (e.g., `Tactus.strGetChar`,
                // `Bool.xor`) expect inner-typed args — apply `.deref`
                // chains to bridge wrapper-typed operands. Mirrors the
                // β refactor's SST-side fix at the same arm.
                None => {
                    let l_peeled = crate::expr_shared::apply_deref_chain(
                        l, count_ref_decorations(&lhs.typ));
                    let r_peeled = crate::expr_shared::apply_deref_chain(
                        r, count_ref_decorations(&rhs.typ));
                    LExpr::app(LExpr::var_lit(non_binop_head(op)), vec![l_peeled, r_peeled]).node
                }
            }
        }

        ExprX::BinaryOpr(BinaryOpr::ExtEq(_, _), lhs, rhs) => {
            LExpr::eq(
                vir_expr_to_ast_with_binders(lhs, binders),
                vir_expr_to_ast_with_binders(rhs, binders),
            ).node
        }

        ExprX::Unary(UnaryOp::Not, inner) => LExpr::not(vir_expr_to_ast_with_binders(inner, binders)).node,
        ExprX::Unary(UnaryOp::Clip { range, .. }, inner) => {
            // Shared `renders_as_lean_int` classifier + `clip_coercion_head`
            // from `expr_shared` — the VIR-AST and SST paths must agree on
            // both which ranges render as Lean `Int` vs `Nat` AND which
            // coercion wrapper to emit at mixed-side boundaries. Exec-fn
            // callees inline their `require`/`ensure` via THIS path while
            // their own theorems render via the SST path; divergence here
            // would produce a different inlined spec than the callee
            // proved.
            use crate::to_lean_sst_expr::renders_as_lean_int;
            let src_int = matches!(&*inner.typ, TypX::Int(r) if renders_as_lean_int(r));
            let dst_int = renders_as_lean_int(range);
            apply_clip_coercion(src_int, dst_int, vir_expr_to_ast_with_binders(inner, binders)).node
        }
        ExprX::Unary(UnaryOp::CoerceMode { .. }, inner)
        | ExprX::Unary(UnaryOp::Trigger(_), inner) => expr_to_node(inner, binders),

        ExprX::Unary(UnaryOp::BitNot(_), inner) => apply(
            "Complement.complement",
            vec![vir_expr_to_ast_with_binders(inner, binders)],
        ),
        ExprX::Unary(UnaryOp::IntToReal, inner) => {
            LExpr::type_annot(vir_expr_to_ast_with_binders(inner, binders), LExpr::var_lit("Real")).node
        }
        ExprX::Unary(UnaryOp::RealToInt, inner) => apply(
            "Int.floor",
            vec![vir_expr_to_ast_with_binders(inner, binders)],
        ),
        ExprX::Unary(UnaryOp::FloatToBits, inner) => expr_to_node(inner, binders),
        ExprX::Unary(UnaryOp::IeeeFloat(_), inner) => expr_to_node(inner, binders),
        // Remaining unary ops: transparent annotations/markers/internal ops.
        ExprX::Unary(_, inner) => expr_to_node(inner, binders),

        ExprX::Call(target, args, _) => {
            // Class-method calls (Dynamic / DynamicResolved) use Lean's
            // typeclass-method auto-binding to infer class type params
            // from value args. For traits with extra type params beyond
            // Self (`Container<T>`-style generics) or generic impls
            // (`Wrapper for Box<int>`), auto-binding can't infer the
            // type params from value args alone; Lean defaults result-
            // type literals to `Nat` and fails to find the instance.
            // Two annotations together fix the inference:
            // (a) annotate each value arg with its known type, so
            //     inner generic Ctors (`Box.mk 42`) elaborate against
            //     the concrete `Box Int` rather than `Box Nat`;
            // (b) annotate the whole call with its return type, so
            //     the outer equality's RHS literal infers correctly.
            // For Self-only traits the annotations are harmless
            // redundancy; for generic traits / generic impls they are
            // load-bearing for Lean's instance synthesis.
            let is_class_method = matches!(target,
                CallTarget::Fun(CallTargetKind::DynamicResolved { .. }, _, _, _, _, _)
                | CallTarget::Fun(CallTargetKind::Dynamic, _, _, _, _, _));
            if is_class_method {
                let head = match target {
                    CallTarget::Fun(_, fun, _, _, _, _) => trait_method_ref(fun),
                    _ => unreachable!("guarded by is_class_method"),
                };
                // Annotate each arg only when its type is concrete (no
                // type-param refs); a TypParam-rooted arg type renders
                // as `Self%` / `T%` which fail the sanity check when
                // emitted at call sites that aren't inside a class
                // declaration. Concrete-typed args are where the
                // disambiguation matters anyway (literals inside
                // Ctors of generic types).
                let app_args: Vec<LExpr> = args.iter().map(|a| {
                    let arg_node = vir_expr_to_ast_with_binders(a, binders);
                    if typ_contains_param(&a.typ) {
                        arg_node
                    } else {
                        LExpr::new(ExprNode::TypeAnnot {
                            expr: Box::new(arg_node),
                            ty: Box::new(typ_to_expr(&a.typ)),
                        })
                    }
                }).collect();
                let app = if app_args.is_empty() {
                    head
                } else {
                    LExpr::new(ExprNode::App { head: Box::new(head), args: app_args })
                };
                if typ_contains_param(&expr.typ) {
                    app.node
                } else {
                    ExprNode::TypeAnnot {
                        expr: Box::new(app),
                        ty: Box::new(typ_to_expr(&expr.typ)),
                    }
                }
            } else {
                call_to_node(target, args, binders)
            }
        }

        ExprX::If(cond, then_e, else_e) => ExprNode::If {
            cond: Box::new(vir_expr_to_ast_with_binders(cond, binders)),
            then_: Box::new(vir_expr_to_ast_with_binders(then_e, binders)),
            else_: else_e.as_ref().map(|e| Box::new(vir_expr_to_ast_with_binders(e, binders))),
        },

        ExprX::Quant(quant, q_binders, body) => {
            let l_binders = vir_var_binders_to_ast(q_binders);
            let mut extended = binders.clone();
            for b in q_binders.iter() {
                extended.insert(b.name.clone(), b.a.clone());
            }
            let body = Box::new(vir_expr_to_ast_with_binders(body, &extended));
            match quant.quant {
                air::ast::Quant::Forall => ExprNode::Forall { binders: l_binders, body },
                air::ast::Quant::Exists => ExprNode::Exists { binders: l_binders, body },
            }
        }

        ExprX::Choose { params, cond, body: _ } => {
            // `Classical.epsilon (fun (x : T) ... => P)` — the epsilon operator
            // returns *some* witness satisfying P if one exists. No existence
            // proof is required because `Classical.epsilon` is total.
            let mut extended = binders.clone();
            for b in params.iter() {
                extended.insert(b.name.clone(), b.a.clone());
            }
            let lambda = LExpr::new(ExprNode::Lambda {
                binders: vir_var_binders_to_ast(params),
                body: Box::new(vir_expr_to_ast_with_binders(cond, &extended)),
            });
            LExpr::app1(LExpr::var_lit("Classical.epsilon"), lambda).node
        }

        ExprX::WithTriggers { body, .. } => expr_to_node(body, binders),

        ExprX::Block(stmts, final_expr) => block_to_node(stmts, final_expr.as_ref(), binders),

        ExprX::Closure(params, body) => {
            let mut extended = binders.clone();
            for b in params.iter() {
                extended.insert(b.name.clone(), b.a.clone());
            }
            ExprNode::Lambda {
                binders: vir_var_binders_to_ast(params),
                body: Box::new(vir_expr_to_ast_with_binders(body, &extended)),
            }
        }

        // Exec-mode closure: also a Lean lambda. The closure's
        // requires/ensures aren't part of the lambda VALUE — they
        // verify the body against its own contract (a separate scope
        // emitted from `StmX::ClosureInner`'s `body` Stm). Here we just
        // produce the function value. Reachable only from the SST-side
        // `StmX::ClosureInner`'s `ast_body` field; the proof-fn pipeline
        // doesn't see exec closures (its panic arm catches that).
        ExprX::NonSpecClosure { params, body, requires: _, ensures: _, .. } => {
            let mut extended = binders.clone();
            for b in params.iter() {
                extended.insert(b.name.clone(), b.a.clone());
            }
            ExprNode::Lambda {
                binders: vir_var_binders_to_ast(params),
                body: Box::new(vir_expr_to_ast_with_binders(body, &extended)),
            }
        }

        ExprX::Ctor(dt, variant, fields, update) => {
            if let Some(tail) = update {
                ExprNode::StructUpdate {
                    base: Box::new(place_to_expr(&tail.place.x, binders)),
                    updates: fields.iter().map(|f|
                        (sanitize(&f.name), vir_expr_to_ast_with_binders(&f.a, binders))
                    ).collect(),
                }
            } else {
                ctor_to_node(dt, variant, fields, binders)
            }
        }

        ExprX::Match(place, arms) => ExprNode::Match {
            scrutinee: Box::new(place_to_expr(&place.x, binders)),
            arms: arms.iter().map(|arm| LMatchArm {
                pattern: pattern_to_ast(&arm.x.pattern.x),
                body: vir_expr_to_ast_with_binders(&arm.x.body, binders),
            }).collect(),
        },

        ExprX::Ghost { expr, .. } | ExprX::ProofInSpec(expr) => expr_to_node(expr, binders),
        ExprX::Loc(expr) => expr_to_node(expr, binders),

        ExprX::ReadPlace(place, _) => place_to_expr(&place.x, binders).node,

        ExprX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner) => expr_to_node(inner, binders),
        ExprX::UnaryOpr(UnaryOpr::Field(field_opr), inner) => {
            // U2: fields belong to the INNER type, not the wrapper.
            // `render_expr_with_derefs` peels wrapper layers via
            // `.deref` chain based on the actual Lean-level depth
            // (binder-aware for Var-shaped inner). Mirrors the
            // SST-side fix at `to_lean_sst_expr::ExpX::UnaryOpr(Field, _)`.
            LExpr::field_proj(
                render_expr_with_derefs(inner, binders),
                field_access_name(field_opr),
            ).node
        }
        ExprX::UnaryOpr(UnaryOpr::IsVariant { variant, .. }, inner) => {
            // U2: discriminator checks operate on the inner inductive
            // type, not the wrapper — same `.deref` chain treatment as
            // Field.
            is_variant_node(variant, render_expr_with_derefs(inner, binders))
        }
        ExprX::UnaryOpr(UnaryOpr::HasType(t), inner) => {
            // Refinement invariant: `e < 2^n` for `U(n)`, `-2^(n-1) ≤ e ∧
            // e < 2^(n-1)` for `I(n)`, etc. Mirrors the `to_lean_sst_expr`
            // version — proof fns and exec fns must agree on what
            // `HasType` means.
            let e_ast = vir_expr_to_ast_with_binders(inner, binders);
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
        ExprX::UnaryOpr(UnaryOpr::CustomErr(_), inner) => expr_to_node(inner, binders),
        ExprX::UnaryOpr(_, inner) => expr_to_node(inner, binders),

        ExprX::NullaryOpr(NullaryOpr::ConstGeneric(typ)) => {
            // const generic parameter used as a value — the VIR typ is the
            // generic parameter's name/type (typically `TypParam(N)`), and we
            // emit it as an identifier expression. `(typ : typ)` would be
            // nonsense; just render the typ as an expression.
            typ_to_expr(typ).node
        }
        ExprX::NullaryOpr(_) => ExprNode::LitBool(true),

        ExprX::Multi(MultiOp::Chained(ops), exprs) => {
            // Chained comparison `a0 op0 a1 op1 a2 ...` (e.g.,
            // `0 <= x <= 10`) → `(a0 op0 a1) ∧ (a1 op1 a2) ∧ ...`.
            //
            // Verus's `ast_simplify` rewrites this shape into the same
            // conjunction for the SST path, but proof fns route through
            // the PRE-simplify krate (so we see Multi here verbatim) —
            // the renderer mirrors ast_simplify's logic. Pre-fix this
            // arm rendered as `⟨a, b, c⟩` (Lean anon-ctor / tuple),
            // which Lean's elaborator can't unify with the surrounding
            // Prop-typed context. Pinned by
            // `test_chained_compare_in_proof_fn`.
            assert!(
                exprs.len() == ops.len() + 1,
                "ExprX::Multi(Chained): expected {} operands for {} ops, got {}",
                ops.len() + 1, ops.len(), exprs.len(),
            );
            let rendered: Vec<LExpr> = exprs.iter().map(|e| vir_expr_to_ast_with_binders(e, binders)).collect();
            let pairs: Vec<LExpr> = ops.iter().enumerate().map(|(i, op)| {
                let l_op = match op {
                    ChainedOp::Inequality(InequalityOp::Le) => crate::lean_ast::BinOp::Le,
                    ChainedOp::Inequality(InequalityOp::Lt) => crate::lean_ast::BinOp::Lt,
                    ChainedOp::Inequality(InequalityOp::Ge) => crate::lean_ast::BinOp::Ge,
                    ChainedOp::Inequality(InequalityOp::Gt) => crate::lean_ast::BinOp::Gt,
                    ChainedOp::MultiEq => crate::lean_ast::BinOp::Eq,
                };
                LExpr::binop(l_op, rendered[i].clone(), rendered[i + 1].clone())
            }).collect();
            crate::lean_ast::and_all(pairs).node
        }
        ExprX::ArrayLiteral(exprs) => {
            ExprNode::ArrayLit(exprs.iter().map(|e| vir_expr_to_ast_with_binders(e, binders)).collect())
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
            LExpr::app1(LExpr::var_lit("Classical.arbitrary"), LExpr::var_lit("_")).node
        }

        // Exec-mode forms — VIR mode checker guarantees these don't appear
        // inside spec fn bodies. (`NonSpecClosure` is handled above as a
        // lambda value — reached via `StmX::ClosureInner.ast_body` for
        // exec-fn bodies.)
        ExprX::Assign { .. } | ExprX::AssignToPlace { .. }
        | ExprX::Loop { .. } | ExprX::Return(_) => {
            panic!("exec-mode expression in spec fn body — VIR mode checker bug");
        }

        ExprX::AssertAssume { expr: e, .. }
        | ExprX::AssertAssumeUserDefinedTypeInvariant { expr: e, .. }
        | ExprX::AssertCompute(e, _)
        | ExprX::NeverToAny(e) => expr_to_node(e, binders),
        ExprX::AssertBy { ensure, .. } => expr_to_node(ensure, binders),
        ExprX::AssertQuery { .. } => ExprNode::LitBool(true),
        ExprX::OpenInvariant(_, _, body, _) => expr_to_node(body, binders),

        // `ExprX::Old(e)` wraps the inner expression for well-
        // formedness checking ("ignored after these checks are
        // complete" per the AST docstring). The actual pre-state
        // reference uses `ExprX::VarAt(x, Pre)`, which we render
        // distinctly via `varat_pre_name` for &mut callee-spec
        // inlining (#55). For this arm: render the inner unchanged.
        ExprX::Old(e) | ExprX::EvalAndResolve(_, e) => expr_to_node(e, binders),
        ExprX::BorrowMut(_) | ExprX::TwoPhaseBorrowMut(_)
        | ExprX::BorrowMutTracked(_) => ExprNode::Var(crate::lean_name::LeanName::lit("()")),
        ExprX::ImplicitReborrowOrSpecRead(place, _, _) => place_to_expr(&place.x, binders).node,
    }
}

// ── Helpers ─────────────────────────────────────────────────────────────

/// Render a `Constant` — shared numeric/bool/string/char arms come from
/// `expr_shared::const_to_node_common`; floats (rejected by the SST path)
/// are handled locally with a type-annotated literal.
fn const_to_node(c: &Constant) -> ExprNode {
    if let Some(node) = const_to_node_common(c) {
        return node;
    }
    match c {
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
        // `const_to_node_common` returned `Some` for every non-float arm.
        _ => unreachable!("const_to_node_common covers all non-float constants"),
    }
}

/// True if `typ` contains a `TypX::TypParam` or `TypX::Projection`
/// anywhere in its structure (e.g., `Self%`, `T`, `<Self as Tr>::Out`).
/// Such types render as bare identifiers that the sanity check rejects
/// when emitted outside a class declaration body. Used to gate type-
/// annotation injection at class-method call sites — we annotate only
/// concrete types where the disambiguation matters anyway.
pub(crate) fn typ_contains_param(typ: &TypX) -> bool {
    let mut found = false;
    crate::to_lean_type::walk_typ(typ, &mut |t| {
        if matches!(t, TypX::TypParam(_) | TypX::Projection { .. }) {
            found = true;
        }
    });
    found
}

/// Render a call expression. Class-method calls (`Dynamic` /
/// `DynamicResolved`) are routed away from this helper by
/// `expr_to_node`'s `ExprX::Call` arm — those need TypeAnnot
/// wrapping for generic disambiguation (see `expr_to_node`). So
/// only Static (and FnSpec / BuiltinSpecFun) calls reach here.
fn call_to_node(target: &CallTarget, args: &Exprs, binders: &BinderCtx) -> ExprNode {
    let head = match target {
        CallTarget::Fun(_, fun, typs, _, _, _) => {
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
        CallTarget::FnSpec(inner) => vir_expr_to_ast_with_binders(inner, binders),
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
            args: args.iter().map(|a| vir_expr_to_ast_with_binders(a, binders)).collect(),
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


fn ctor_to_node(dt: &Dt, variant: &Ident, fields: &Binders<Expr>, binders: &BinderCtx) -> ExprNode {
    let rendered = fields.iter().map(|f| vir_expr_to_ast_with_binders(&f.a, binders)).collect();
    ctor_node(dt, variant, rendered)
}

/// Fold a VIR `Block` into nested Lean lets.
///
/// * `StmtX::Decl { pattern: Var(x), init: Some(e) }`  →  `let x := e; rest`
/// * `StmtX::Decl { pattern: <non-var>, init: Some(e) }`  →  `match e with | p => rest`
///   (Lean pattern-lets require `match` for non-variable LHS.)
/// * `StmtX::Expr(e)` with a following statement  →  `let _ := e; rest`
///   (drops the value like Rust's `;` does).
/// * Last stmt with no `final_expr` is the body.
fn block_to_node(stmts: &[Stmt], final_expr: Option<&Expr>, binders: &BinderCtx) -> ExprNode {
    let body = match final_expr {
        Some(e) => vir_expr_to_ast_with_binders(e, binders),
        None if stmts.is_empty() => LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit("()"))),
        // No final expression — the last stmt's value is the block's value.
        // In spec mode this is unusual; fall back to unit.
        None => LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit("()"))),
    };

    let mut folded = body;
    for stmt in stmts.iter().rev() {
        folded = match &stmt.x {
            StmtX::Decl { pattern, init, .. } => {
                let value = match init {
                    Some(place) => place_to_expr(&place.x, binders),
                    // No initializer (e.g., `let x;`) — give a placeholder.
                    None => LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit("_"))),
                };
                match &pattern.x {
                    PatternX::Var(binding) => LExpr::new(ExprNode::Let {
                        name: crate::lean_name::LeanName::from_var_ident(&binding.name),
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
                name: crate::lean_name::LeanName::lit("_"),
                value: Box::new(vir_expr_to_ast_with_binders(e, binders)),
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
        PatternX::Var(binding) => LPattern::Var(crate::lean_name::LeanName::from_var_ident(&binding.name)),
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
            name: crate::lean_name::LeanName::from_var_ident(&binding.name),
            sub: Box::new(pattern_to_ast(&sub_pat.x)),
        },
        PatternX::Expr(e) => LPattern::Lit(expr_to_node(e, &BinderCtx::new())),
        PatternX::Range(lo, _hi) => {
            // Lean doesn't have numeric range patterns; fall back to the low
            // bound (or wildcard if absent). Range patterns are rare in spec
            // mode (ast_simplify usually eliminates Match).
            match lo {
                Some(e) => LPattern::Lit(expr_to_node(e, &BinderCtx::new())),
                None => LPattern::Wildcard,
            }
        }
        PatternX::MutRef(inner) | PatternX::ImmutRef(inner) => pattern_to_ast(&inner.x),
    }
}

// ── Places ──────────────────────────────────────────────────────────────

fn place_to_expr(place: &PlaceX, binders: &BinderCtx) -> LExpr {
    LExpr::new(match place {
        PlaceX::Local(ident) => ExprNode::Var(crate::lean_name::LeanName::from_var_ident(ident)),
        PlaceX::Field(field_opr, base) => {
            // U2: fields belong to the inner type, not the wrapper —
            // `render_place_with_derefs` applies the .deref chain
            // (binder-aware for Local-rooted bases).
            ExprNode::FieldProj {
                expr: Box::new(render_place_with_derefs(base, binders)),
                field: field_access_name(field_opr),
            }
        }
        PlaceX::DerefMut(inner) | PlaceX::ModeUnwrap(inner, _) => {
            return place_to_expr(&inner.x, binders);
        }
        PlaceX::Temporary(expr) => return vir_expr_to_ast_with_binders(expr, binders),
        PlaceX::WithExpr(_, place) => return place_to_expr(&place.x, binders),
        PlaceX::Index(base, idx, _, _) => ExprNode::Index {
            base: Box::new(place_to_expr(&base.x, binders)),
            idx: Box::new(vir_expr_to_ast_with_binders(idx, binders)),
            // Place-position indexing in proof fns is rare and usually
            // sees the bounds proof in scope (legacy mut-ref code).
            // Keep the plain `[idx]` form here; add `!` only when we
            // identify a concrete shape that needs it.
            bang: false,
        },
        PlaceX::UserDefinedTypInvariantObligation(inner, _) => {
            return place_to_expr(&inner.x, binders);
        }
    })
}

// ── Tests ───────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr_shared::count_ref_decorations;
    use crate::test_fixtures::typ_int;
    use std::sync::Arc;
    use vir::ast::{Mode, ParamX, TypDecoration};
    use vir::def::Spanned;
    use vir::messages::Span;

    fn typ_ref(inner: Typ) -> Typ {
        Arc::new(TypX::Decorate(TypDecoration::Ref, None, inner))
    }

    fn typ_box(inner: Typ) -> Typ {
        Arc::new(TypX::Decorate(TypDecoration::Box, None, inner))
    }

    fn typ_boxed(inner: Typ) -> Typ {
        Arc::new(TypX::Boxed(inner))
    }

    fn typ_mut_ref(inner: Typ) -> Typ {
        Arc::new(TypX::MutRef(inner))
    }

    fn mk_var_ident(name: &str) -> VarIdent {
        VarIdent(Arc::new(name.to_string()), vir::ast::VarIdentDisambiguate::NoBodyParam)
    }

    fn mk_param(name: &str, typ: Typ, is_mut: bool) -> Param {
        Spanned::new(Span::dummy(), ParamX {
            name: mk_var_ident(name),
            typ,
            mode: Mode::Spec,
            user_mut: false,
            is_mut,
            unwrapped_info: None,
        })
    }

    // ── strip_one_ref_decoration ─────────────────────────────────────────

    #[test]
    fn strip_one_ref_decoration_strips_ref() {
        let int = typ_int();
        let r = typ_ref(int.clone());
        let stripped = strip_one_ref_decoration(&r);
        // Stripping `&Int` should give `Int` — count drops by 1.
        assert_eq!(count_ref_decorations(&stripped), 0);
    }

    #[test]
    fn strip_one_ref_decoration_strips_mut_ref() {
        // TypX::MutRef (new mode) is treated like a ref decoration
        // — strip the outer layer.
        let int = typ_int();
        let m = typ_mut_ref(int.clone());
        let stripped = strip_one_ref_decoration(&m);
        assert_eq!(count_ref_decorations(&stripped), 0);
    }

    #[test]
    fn strip_one_ref_decoration_strips_only_one_layer() {
        // `&Box<Int>` (count 2) → strip outermost ref → `Box<Int>` (count 1).
        // Only ONE decoration peeled per call, mirroring the shadow's
        // single `.deref` step.
        let int = typ_int();
        let bx = typ_box(int);
        let r_bx = typ_ref(bx);
        assert_eq!(count_ref_decorations(&r_bx), 2);
        let stripped = strip_one_ref_decoration(&r_bx);
        assert_eq!(count_ref_decorations(&stripped), 1);
    }

    #[test]
    fn strip_one_ref_decoration_passes_through_bare() {
        // No ref decoration → no change.
        let int = typ_int();
        let stripped = strip_one_ref_decoration(&int);
        assert_eq!(count_ref_decorations(&stripped), 0);
    }

    #[test]
    fn strip_one_ref_decoration_does_not_peel_boxed() {
        // `TypX::Boxed` is Verus's poly-encoding "transparent" marker
        // (NOT the `Box<T>` decoration). It's Lean-transparent and not
        // a wrapper. `strip_one_ref_decoration` only peels reference
        // decorations and MutRef.
        let int = typ_int();
        let boxed = typ_boxed(int);
        let stripped = strip_one_ref_decoration(&boxed);
        // `Boxed(Int)` returned as-is.
        assert!(matches!(&*stripped, TypX::Boxed(_)));
    }

    // ── binder_ctx_from_params ───────────────────────────────────────────

    #[test]
    fn binder_ctx_empty_params_empty_ctx() {
        let params: Params = Arc::new(vec![]);
        let ctx = binder_ctx_from_params(&params);
        assert!(ctx.is_empty());
    }

    #[test]
    fn binder_ctx_ref_only_param_keeps_wrapper() {
        // `&Int` param (`Decorate(Ref, _, Int)`, is_mut: false) is
        // NOT shadowed post-U2 — BinderCtx records the wrapper-
        // decorated typ as-declared.
        let int = typ_int();
        let r = typ_ref(int);
        let params: Params = Arc::new(vec![mk_param("p", r.clone(), false)]);
        let ctx = binder_ctx_from_params(&params);
        let recorded = ctx.get(&mk_var_ident("p")).expect("p should be in ctx");
        assert_eq!(count_ref_decorations(recorded), 1);
    }

    #[test]
    fn binder_ctx_legacy_mut_param_strips() {
        // Legacy `&mut x: Int` is `is_mut: true` with bare typ.
        // Lean renders the binder as `Tactus.MutRef Int` (via
        // param_binder_typ wrapping based on is_mut), and the body
        // shadow strips back to `Int`. BinderCtx records the
        // post-shadow `Int` (count 0).
        let int = typ_int();
        let params: Params = Arc::new(vec![mk_param("p", int, true)]);
        let ctx = binder_ctx_from_params(&params);
        let recorded = ctx.get(&mk_var_ident("p")).expect("p should be in ctx");
        assert_eq!(count_ref_decorations(recorded), 0);
    }

    #[test]
    fn binder_ctx_new_mode_mut_ref_param_strips_one() {
        // New-mode `&mut x: Int` arrives as `TypX::MutRef(Int)`,
        // `is_mut: false`. Lean renders as `Tactus.MutRef Int`;
        // shadow strips one layer → BinderCtx records `Int` (count 0).
        let int = typ_int();
        let m = typ_mut_ref(int);
        assert_eq!(count_ref_decorations(&m), 1);
        let params: Params = Arc::new(vec![mk_param("p", m, false)]);
        let ctx = binder_ctx_from_params(&params);
        let recorded = ctx.get(&mk_var_ident("p")).expect("p should be in ctx");
        assert_eq!(count_ref_decorations(recorded), 0);
    }

    #[test]
    fn binder_ctx_mixed_params_strips_only_mut() {
        // Three params: `&Int` (not shadowed), legacy `&mut Int`
        // (shadowed, bare typ → still bare), new-mode `MutRef<Int>`
        // (shadowed, MutRef → bare). Verify each is recorded
        // correctly.
        let int = typ_int();
        let r = typ_ref(int.clone());
        let m_new = typ_mut_ref(int.clone());
        let params: Params = Arc::new(vec![
            mk_param("a", r, false),                  // &-only
            mk_param("b", int.clone(), true),         // legacy &mut
            mk_param("c", m_new, false),              // new-mode MutRef
        ]);
        let ctx = binder_ctx_from_params(&params);
        assert_eq!(count_ref_decorations(ctx.get(&mk_var_ident("a")).unwrap()), 1);
        assert_eq!(count_ref_decorations(ctx.get(&mk_var_ident("b")).unwrap()), 0);
        assert_eq!(count_ref_decorations(ctx.get(&mk_var_ident("c")).unwrap()), 0);
    }

}
