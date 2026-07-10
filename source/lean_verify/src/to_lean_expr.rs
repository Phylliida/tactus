//! Translate VIR-AST expressions to `lean_ast::Expr`.

use std::collections::HashMap;
use vir::ast::*;
use crate::expr_shared::{
    apply_clip_coercion, binop_to_ast, const_to_node_common, ctor_node, field_proj_opr,
    is_variant_node, non_binop_head,
};
use crate::lean_ast::{
    Binder as LBinder, Expr as LExpr,
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
    expr_to_ast(expr, &crate::expr_shared::RenderCtx::empty())
}

/// Variant for callee-spec inlining contexts. Suppresses the
/// `apply_ref_coercion_if_needed` lift at `ExprX::ReadPlace` sites
/// (returns None from `structural_typ` for ReadPlace via the ctx's
/// `inlining` flag).
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
    vir_expr_to_ast_for_inlining_with_ctx(expr, &crate::expr_shared::RenderCtx::empty())
}

/// Variant of [`vir_expr_to_ast_for_inlining`] that takes a [`RenderCtx`]
/// for class-method-call coercion at trait dispatch sites. Use at codegen
/// entry points where the fn_map is available.
pub fn vir_expr_to_ast_for_inlining_with_ctx(expr: &Expr, ctx: &crate::expr_shared::RenderCtx) -> LExpr {
    expr_to_ast(expr, &ctx.for_inlining().without_binder_typs())
}

/// Build a `lean_ast::Expr` from a VIR-AST expression with the given
/// binder context. Inserts `Tactus.X.mk` wraps where:
/// * `expr.x` is `Const` / `Ctor` / `ArrayLiteral` (structurally
///   undecorated kinds) and `expr.typ` has reference decorations.
/// * `expr.x` is `Var(p)` / `VarLoc(p)` / `VarAt(p, _)` and `p`'s
///   binder typ has FEWER reference decorations than `expr.typ` (Verus's
///   auto-`&` adjustment on a Var leaves the binder untouched).
pub(crate) fn vir_expr_to_ast_with_binders(expr: &Expr, binders: &BinderCtx, ctx: &crate::expr_shared::RenderCtx) -> LExpr {
    // Attach the binder map to the ctx (overriding any caller-set
    // binder_typs — the explicit param wins) and render single-ctx
    // from here down. The map and the ctx's `binder_typs` field are
    // the same `HashMap<VarIdent, Typ>` shape; this entry is where
    // the two formerly-parallel threadings join.
    let ctx = ctx.with_binder_typs(binders);
    expr_to_ast(expr, &ctx)
}

/// Internal single-ctx renderer: the in-scope binder map rides on
/// `ctx.binder_typs` (extended at quantifier / choose / closure
/// binder sites via `with_binder_typs`).
fn expr_to_ast(expr: &Expr, ctx: &crate::expr_shared::RenderCtx) -> LExpr {
    let rendered = LExpr::new(expr_to_node(expr, ctx));
    apply_ref_coercion_if_needed(expr, rendered, ctx)
}

/// Compute the "structural" type of an expression — the type its Lean
/// rendering naturally produces, ignoring Verus's adjustment-driven
/// decorations on `expr.typ`. Returns `None` for kinds where we trust
/// `expr.typ` (e.g., `Call`, `Binary`, `Unary` — Verus's typing for
/// these matches what the rendering produces).
///
/// Used to compute the delta between `expr.typ` and what the rendering
/// produces, so we can insert explicit `Tactus.X.mk` wraps to bridge.
fn structural_typ(expr: &Expr, ctx: &crate::expr_shared::RenderCtx) -> Option<Typ> {
    match &expr.x {
        // Constructors and literals produce undecorated values.
        ExprX::Const(_) | ExprX::Ctor(..) | ExprX::ArrayLiteral(_) => {
            // Use the un-decorated form of expr.typ as the structural typ.
            Some(strip_all_ref_decorations(&expr.typ.clone()))
        }
        // Variable references produce the binder's typ OR — for
        // call-site inlining — the storage typ recorded in
        // `ctx.value_subst`. The latter handles mut-param refs in
        // the callee's specs: the substituted value is at the
        // local's Lean-level storage typ (e.g., `Tactus.MutRef T`),
        // not at Verus's AST claim, so `apply_ref_coercion_if_needed`
        // can bridge storage → expr.typ at the use site.
        ExprX::Var(v) | ExprX::VarLoc(v) | ExprX::VarAt(v, _) => {
            ctx.binder(v).cloned().or_else(|| {
                let lean_name = crate::lean_name::LeanName::from_var_ident(v);
                ctx.lookup_subst_typ(&lean_name)
            })
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
        // Inlining-substitution path: when the Local is in
        // `ctx.value_subst`, report the storage typ from there so
        // `apply_ref_coercion_if_needed` can bridge to expr.typ even
        // though the ReadPlace lift is otherwise suppressed for
        // inlining (`ctx.inlining`). The β refactor's suppression was
        // meant to skip the lift for substituted-non-mut args (whose
        // typ already matched the AST claim); mut-param substitution
        // genuinely needs the bridge, so the storage-typ hit wins.
        //
        // Inlining contexts (`vir_expr_to_ast_for_inlining`) set
        // `ctx.inlining` to suppress the lift — the substituted-arg
        // provides the correct wrapper-typed value directly. See the
        // doc on `vir_expr_to_ast_for_inlining`.
        ExprX::ReadPlace(p, _) => {
            let inlining_storage_typ = match &p.x {
                PlaceX::Local(v) => {
                    let lean_name = crate::lean_name::LeanName::from_var_ident(v);
                    ctx.lookup_subst_typ(&lean_name)
                }
                _ => None,
            };
            if let Some(t) = inlining_storage_typ {
                return Some(t);
            }
            // Inlining context: when value_subst is configured (i.e.,
            // we're rendering a callee's spec at a call site), the
            // outer ReadPlace's bridge needs to fire even for non-
            // Local Place shapes (DerefMut, Field, Temporary, etc.).
            // Returning `Some(p.typ.clone())` enables apply_ref_coercion
            // to bridge from the inner-rendered value typ (p.typ — what
            // the inner substituted Var's bridge brought it to) up to
            // the outer expr.typ (e.g., auto-borrow Ref T).
            //
            // For nested-Local shapes (DerefMut(Local(h))), the inner
            // value_subst hit happens inside place_to_expr; the outer
            // ReadPlace's bridge then wraps with Ref.mk to satisfy
            // expr.typ. Without this branch, the outer wrap was missing
            // and Lean rejected with a type mismatch (the
            // `claimed-typ-lies` case for nested Places).
            if ctx.value_subst.is_some() {
                return Some(p.typ.clone());
            }
            if ctx.inlining {
                None
            } else {
                match &p.x {
                    PlaceX::Local(v) => ctx.binder(v).cloned().or_else(|| Some(p.typ.clone())),
                    _ => Some(p.typ.clone()),
                }
            }
        }
        // A `Call` renders as a naked `head args` application — the
        // call renderer materializes NO wrapper decorations, so the
        // rendered value sits at the callee's (bare) return typ, not at
        // `expr.typ`. When `expr.typ` carries OUTER ref decorations (an
        // auto-`&` on a method receiver, e.g. `(self@[k]).deep_view()`
        // borrows the index result), those decorations are absent from
        // the rendered value — so report the stripped typ and let
        // `apply_ref_coercion_if_needed` bridge bare → `expr.typ` with a
        // `.mk` chain, exactly as it does for a `ReadPlace`/`Var` receiver.
        // For the common undecorated call (`expr.typ` already bare) the
        // strip is a no-op and the coercion no-ops too — zero change.
        // Relies on spec-fn returns being bare value typs; a decorated
        // return would over-strip and surface as a LOUD Lean type error.
        ExprX::Call(..) => Some(strip_all_ref_decorations(&expr.typ)),
        // Pass-through expressions: natural typ is the inner's.
        ExprX::Loc(inner) | ExprX::Ghost { expr: inner, .. }
        | ExprX::ProofInSpec(inner) => structural_typ(inner, ctx),
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

// `collect_ref_wraps`, `apply_wrap_chain` (formerly `apply_ref_wraps`),
// and `count_ref_decorations` all moved to `expr_shared` — shared with
// SST-side typed-composition machinery.
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
fn lean_level_wrap_count(var_id: Option<&VarIdent>, spanned_typ: &Typ, ctx: &crate::expr_shared::RenderCtx) -> usize {
    // Mirror `structural_typ`'s Var arm: binder typ if known, else the
    // inlined-call substitution's storage typ (records the caller
    // arg's actual wrapper depth), else the spanned AST typ. The
    // subst step fixes a Field access on a substituted immutable-ref
    // arg (`h.generator_images` where the callee's `h : &RuntimeHomData`
    // is substituted by the caller's `Tactus.Ref` value) whose spanned
    // typ is bare (Verus auto-derefs the `&self` base) — without it the
    // deref count is 0 and Lean gets `h.generator_images` (un-elaborable
    // → `sorry`; found via apply_hom_symbol_exec).
    let lean_typ = var_id
        .and_then(|v| {
            ctx.binder(v).cloned().or_else(|| {
                let lean_name = crate::lean_name::LeanName::from_var_ident(v);
                ctx.lookup_subst_typ(&lean_name)
            })
        })
        .unwrap_or_else(|| spanned_typ.clone());
    count_ref_decorations(&lean_typ)
}

/// Render `inner` and apply a `.deref` chain matching its actual
/// Lean-level wrapper depth. Used at Field / IsVariant projection
/// sites where the field/variant belongs to the inner type rather
/// than the wrapper.
fn render_expr_with_derefs(inner: &Expr, ctx: &crate::expr_shared::RenderCtx) -> LExpr {
    let rendered = expr_to_ast(inner, ctx);
    let var_id = match &inner.x {
        ExprX::Var(v) | ExprX::VarLoc(v) | ExprX::VarAt(v, _) => Some(v),
        _ => None,
    };
    let n_derefs = lean_level_wrap_count(var_id, &inner.typ, ctx);
    crate::expr_shared::apply_deref_chain(rendered, n_derefs)
}

/// Place-side analog of `render_expr_with_derefs`. Renders the
/// place's value and applies the matching `.deref` chain.
fn render_place_with_derefs(base: &Place, ctx: &crate::expr_shared::RenderCtx) -> LExpr {
    let rendered = place_to_expr(&base.x, ctx);
    let var_id = match &base.x {
        PlaceX::Local(v) => Some(v),
        _ => None,
    };
    let n_derefs = lean_level_wrap_count(var_id, &base.typ, ctx);
    crate::expr_shared::apply_deref_chain(rendered, n_derefs)
}

fn apply_ref_coercion_if_needed(
    expr: &Expr,
    rendered: LExpr,
    ctx: &crate::expr_shared::RenderCtx,
) -> LExpr {
    // Thin wrapper around `expr_shared::coerce_lexpr` — compute the
    // "structural" typ (what the rendering naturally produces, based
    // on binder ctx for var-shaped exprs) and bridge `expr.typ` →
    // structural via the shared bidirectional helper.
    //
    // * `expr.typ` has MORE wrappers than structural → `.mk` chain
    //   wraps (e.g., auto-`&` at a call site needs to wrap a bare value).
    // * `expr.typ` has FEWER wrappers than structural → `.deref`
    //   chain peels (e.g., Verus's spec-mode `**b` collapses to
    //   `Var(b)` with expr.typ = bare, but the binder is wrapper-typed).
    //
    // Equal renders verbatim.
    let Some(natural) = structural_typ(expr, ctx) else {
        return rendered;
    };
    // We're bridging from the binder-context's natural typ TO expr.typ
    // — the natural is the value's current type; expr.typ is what the
    // surrounding context expects.
    crate::expr_shared::coerce_lexpr(rendered, &natural, &expr.typ)
}

/// Build `VarBinders<Typ>` → AST binders for proof/spec fn parameters.
/// Each becomes an explicit `(name : Type)` binder.
pub(crate) fn vir_var_binders_to_ast(binders: &VarBinders<Typ>) -> Vec<LBinder> {
    binders.iter().map(|b| LBinder::explicit(
        crate::lean_name::LeanName::from_var_ident(&b.name),
        typ_to_expr(&b.a),
    )).collect()
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

fn expr_to_node(expr: &Expr, ctx: &crate::expr_shared::RenderCtx) -> ExprNode {
    // Render-time substitution: if ctx carries a value_subst map and
    // `ident` is in it, return the substituted value at its STORAGE
    // typ — without bridging. Downstream `apply_ref_coercion_if_needed`
    // bridges storage → expr.typ via `structural_typ` (which reports
    // the storage typ from `ctx.lookup_subst_typ`). This keeps the
    // substituted value's Lean reality (the storage typ) visible at
    // the surrounding lift sites, so they can compose with their own
    // coercions (e.g., the class-method-call arm's MutRef→Ref bridge).
    let try_subst = |ident: &VarIdent| -> Option<ExprNode> {
        let lean_name = crate::lean_name::LeanName::from_var_ident(ident);
        ctx.lookup_subst_raw(&lean_name).map(|e| e.node)
    };
    match &expr.x {
        ExprX::Const(c) => const_to_node(c),
        ExprX::Var(ident) => {
            if let Some(sub) = try_subst(ident) {
                return sub;
            }
            ExprNode::Var(crate::lean_name::LeanName::from_var_ident(ident))
        }
        // `VarAt(x, Pre)` collapses to `Var(x)` for the general path
        // (non-mut params, loop ensures' at-entry refs, etc. — these
        // are correct because the AT-entry value equals the current
        // value at the relevant scope). For `&mut` callee-spec
        // inlining, `walk_call` pre-rewrites `VarAt(p, Pre)` to a
        // synthetic distinct name BEFORE this renderer runs, so the
        // substitution map can target pre- and post-state separately.
        // See `walk_call` and `varat_pre_name` for the full picture.
        ExprX::VarAt(ident, _) => {
            if let Some(sub) = try_subst(ident) {
                return sub;
            }
            ExprNode::Var(crate::lean_name::LeanName::from_var_ident(ident))
        }
        ExprX::VarLoc(ident) => {
            if let Some(sub) = try_subst(ident) {
                return sub;
            }
            ExprNode::Var(crate::lean_name::LeanName::from_var_ident(ident))
        }
        ExprX::ConstVar(fun, _) => ExprNode::Var(crate::lean_name::LeanName::from_path(&fun.path)),
        ExprX::StaticVar(fun) | ExprX::ExecFnByName(fun) => ExprNode::Var(crate::lean_name::LeanName::from_path(&fun.path)),

        ExprX::Binary(op, lhs, rhs) => {
            let (l, r) = (
                expr_to_ast(lhs, ctx),
                expr_to_ast(rhs, ctx),
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
                expr_to_ast(lhs, ctx),
                expr_to_ast(rhs, ctx),
            ).node
        }

        ExprX::Unary(UnaryOp::Not, inner) => LExpr::not(expr_to_ast(inner, ctx)).node,
        ExprX::Unary(UnaryOp::Clip { range, .. }, inner) => {
            // Shared `renders_as_lean_int` classifier + `clip_coercion_head`
            // from `expr_shared` — the VIR-AST and SST paths must agree on
            // both which ranges render as Lean `Int` vs `Nat` AND which
            // coercion wrapper to emit at mixed-side boundaries. Exec-fn
            // callees inline their `require`/`ensure` via THIS path while
            // their own theorems render via the SST path; divergence here
            // would produce a different inlined spec than the callee
            // proved.
            use crate::expr_shared::renders_as_lean_int;
            let src_int = matches!(&*inner.typ, TypX::Int(r) if renders_as_lean_int(r));
            let dst_int = renders_as_lean_int(range);
            apply_clip_coercion(src_int, dst_int, expr_to_ast(inner, ctx)).node
        }
        ExprX::Unary(UnaryOp::CoerceMode { .. }, inner)
        | ExprX::Unary(UnaryOp::Trigger(_), inner) => expr_to_node(inner, ctx),

        ExprX::Unary(UnaryOp::BitNot(_), inner) => apply(
            "Complement.complement",
            vec![expr_to_ast(inner, ctx)],
        ),
        ExprX::Unary(UnaryOp::IntToReal, inner) => {
            LExpr::type_annot(expr_to_ast(inner, ctx), LExpr::var_lit("Real")).node
        }
        ExprX::Unary(UnaryOp::RealToInt, inner) => apply(
            "Int.floor",
            vec![expr_to_ast(inner, ctx)],
        ),
        ExprX::Unary(UnaryOp::FloatToBits, inner) => expr_to_node(inner, ctx),
        ExprX::Unary(UnaryOp::IeeeFloat(_), inner) => expr_to_node(inner, ctx),
        // Remaining unary ops: transparent annotations/markers/internal ops.
        ExprX::Unary(_, inner) => expr_to_node(inner, ctx),

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
                let (fun_for_lookup, typ_args) = match target {
                    CallTarget::Fun(_, fun, typs, _, _, _) => (fun, typs),
                    _ => unreachable!("guarded by is_class_method"),
                };
                let head = trait_method_ref(fun_for_lookup);
                // Wrapper-arch coercion (RenderCtx Option 1 Phase 1):
                // look up the trait method decl's declared param typs
                // via the RenderCtx fn_map. Coerce each arg to its
                // expected param typ via coerce_lexpr so receivers
                // wrap correctly (`Tactus.Ref.mk z` instead of bare
                // `z` for &self methods).
                //
                // When ctx.fn_param_typs returns None (empty ctx,
                // cross-crate fun), falls back to no-coerce + a.typ
                // annotation — same as the pre-RenderCtx behavior.
                // Inlining contexts where substitution produces a
                // typing-mismatched value benefit when ctx has fn_map;
                // non-inlining proof fns produce correct shapes either
                // way (binder_ctx + lift handles them).
                let expected_typs = ctx.fn_param_typs(fun_for_lookup, &typ_args[..]);
                // Wrapper coercion from a.typ to expected — handles
                // proof fn cases where binder_ctx + lift produces
                // arg matching a.typ. Inlining contexts (where
                // substitution has produced bare values) are NOT
                // correctly handled here — the substituted value's
                // actual Lean-level typ may differ from a.typ
                // (substituted-bare vs declared-wrapper). Closing
                // that case requires typed substitution (deferred
                // beyond Phase 1).
                let app_args: Vec<LExpr> = args.iter().enumerate().map(|(i, a)| {
                    let arg_node = expr_to_ast(a, ctx);
                    // Coerce from the arg's ACTUAL Lean typ, not the
                    // claimed `a.typ`. For a bare `Var` whose binder
                    // typ the ctx knows (a loop-modified local like
                    // `out : Vec`), VIR's `out@` auto-ref makes `a.typ`
                    // claim `&Vec` while the Lean binder is bare — so
                    // coercing from the claim is an identity where a
                    // `Tactus.Ref.mk` was needed. `binder_typs` carries
                    // the truth (BUG-call-arg-temp-claimed-typ.md).
                    // Falls back to `a.typ` when the arg isn't a
                    // ctx-known Var — unchanged for every other case.
                    let src_typ = match &a.x {
                        ExprX::Var(ident) => ctx.binder_typs
                            .and_then(|b| b.get(ident))
                            .cloned()
                            .unwrap_or_else(|| a.typ.clone()),
                        _ => a.typ.clone(),
                    };
                    let arg_coerced = match &expected_typs {
                        Some(typs) if i < typs.len() => {
                            crate::expr_shared::coerce_lexpr(arg_node, &src_typ, &typs[i])
                        }
                        _ => arg_node,
                    };
                    let annot_typ = match &expected_typs {
                        Some(typs) if i < typs.len() => typs[i].clone(),
                        _ => a.typ.clone(),
                    };
                    if typ_contains_param(&annot_typ) {
                        arg_coerced
                    } else {
                        LExpr::type_annot(arg_coerced, typ_to_expr(&annot_typ))
                    }
                }).collect();
                let app = if app_args.is_empty() {
                    head
                } else {
                    LExpr::app(head, app_args)
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
                call_to_node(target, args, ctx)
            }
        }

        ExprX::If(cond, then_e, else_e) => ExprNode::If {
            cond: Box::new(expr_to_ast(cond, ctx)),
            then_: Box::new(expr_to_ast(then_e, ctx)),
            else_: else_e.as_ref().map(|e| Box::new(expr_to_ast(e, ctx))),
        },

        ExprX::Quant(quant, q_binders, body) => {
            let l_binders = vir_var_binders_to_ast(q_binders);
            let mut extended = ctx.binder_typs.cloned().unwrap_or_default();
            for b in q_binders.iter() {
                extended.insert(b.name.clone(), b.a.clone());
            }
            let body = Box::new(expr_to_ast(body, &ctx.with_binder_typs(&extended)));
            match quant.quant {
                air::ast::Quant::Forall => ExprNode::Forall { binders: l_binders, body },
                air::ast::Quant::Exists => ExprNode::Exists { binders: l_binders, body },
            }
        }

        ExprX::Choose { params, cond, body: _ } => {
            // `Classical.epsilon (fun (x : T) ... => P)` — the epsilon operator
            // returns *some* witness satisfying P if one exists. No existence
            // proof is required because `Classical.epsilon` is total.
            let mut extended = ctx.binder_typs.cloned().unwrap_or_default();
            for b in params.iter() {
                extended.insert(b.name.clone(), b.a.clone());
            }
            let lambda = LExpr::lambda(
                vir_var_binders_to_ast(params),
                expr_to_ast(cond, &ctx.with_binder_typs(&extended)),
            );
            LExpr::app1(LExpr::var_lit("Classical.epsilon"), lambda).node
        }

        ExprX::WithTriggers { body, .. } => expr_to_node(body, ctx),

        ExprX::Block(stmts, final_expr) => block_to_node(stmts, final_expr.as_ref(), ctx),

        ExprX::Closure(params, body) => {
            let mut extended = ctx.binder_typs.cloned().unwrap_or_default();
            for b in params.iter() {
                extended.insert(b.name.clone(), b.a.clone());
            }
            ExprNode::Lambda {
                binders: vir_var_binders_to_ast(params),
                body: Box::new(expr_to_ast(body, &ctx.with_binder_typs(&extended))),
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
            let mut extended = ctx.binder_typs.cloned().unwrap_or_default();
            for b in params.iter() {
                extended.insert(b.name.clone(), b.a.clone());
            }
            ExprNode::Lambda {
                binders: vir_var_binders_to_ast(params),
                body: Box::new(expr_to_ast(body, &ctx.with_binder_typs(&extended))),
            }
        }

        ExprX::Ctor(dt, variant, fields, update) => {
            if let Some(tail) = update {
                ExprNode::StructUpdate {
                    base: Box::new(place_to_expr(&tail.place.x, ctx)),
                    updates: fields.iter().map(|f|
                        (sanitize(&f.name), expr_to_ast(&f.a, ctx))
                    ).collect(),
                }
            } else {
                ctor_to_node(dt, variant, fields, ctx)
            }
        }

        ExprX::Match(place, arms) => ExprNode::Match {
            scrutinee: Box::new(place_to_expr(&place.x, ctx)),
            arms: arms.iter().map(|arm| LMatchArm {
                pattern: pattern_to_ast(&arm.x.pattern.x),
                body: expr_to_ast(&arm.x.body, ctx),
            }).collect(),
        },

        ExprX::Ghost { expr, .. } | ExprX::ProofInSpec(expr) => expr_to_node(expr, ctx),
        ExprX::Loc(expr) => expr_to_node(expr, ctx),

        ExprX::ReadPlace(place, _) => {
            // Render-time substitution at `ReadPlace(Local(v), _)`
            // sites — same as the Var/VarAt arm above. Return the
            // value at its storage typ; the outer
            // `apply_ref_coercion_if_needed` bridges to expr.typ via
            // `structural_typ` which reports the storage typ from
            // `ctx.lookup_subst_typ` for this AST shape.
            //
            // For nested Place shapes (DerefMut/ModeUnwrap/Field/etc.
            // wrapping Local), the substitution happens inside
            // `place_to_expr`'s Local arm — same hit, same value,
            // different entry point.
            if let PlaceX::Local(ident) = &place.x {
                let lean_name = crate::lean_name::LeanName::from_var_ident(ident);
                if let Some(value) = ctx.lookup_subst_raw(&lean_name) {
                    return value.node;
                }
            }
            place_to_expr(&place.x, ctx).node
        }

        ExprX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner) => expr_to_node(inner, ctx),
        ExprX::UnaryOpr(UnaryOpr::Field(field_opr), inner) => {
            // U2: fields belong to the INNER type, not the wrapper.
            // `render_expr_with_derefs` peels wrapper layers via
            // `.deref` chain based on the actual Lean-level depth
            // (binder-aware for Var-shaped inner). Mirrors the
            // SST-side fix at `to_lean_sst_expr::ExpX::UnaryOpr(Field, _)`.
            field_proj_opr(
                render_expr_with_derefs(inner, ctx),
                field_opr,
            ).node
        }
        ExprX::UnaryOpr(UnaryOpr::IsVariant { datatype, variant }, inner) => {
            // A tuple has exactly one "variant" — its test is vacuously
            // true (the general path would emit the nonexistent
            // `.istuple%N`; cluster bug 6). Mirrors the SST arm.
            if matches!(datatype, Dt::Tuple(_)) {
                ExprNode::LitBool(true)
            } else {
                // U2: discriminator checks operate on the inner inductive
                // type, not the wrapper — same `.deref` chain treatment as
                // Field.
                is_variant_node(variant, render_expr_with_derefs(inner, ctx))
            }
        }
        ExprX::UnaryOpr(UnaryOpr::HasType(t), inner) => {
            // Refinement invariant: `e < 2^n` for `U(n)`, `-2^(n-1) ≤ e ∧
            // e < 2^(n-1)` for `I(n)`, etc. Mirrors the `to_lean_sst_expr`
            // version — proof fns and exec fns must agree on what
            // `HasType` means.
            let e_ast = expr_to_ast(inner, ctx);
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
        ExprX::UnaryOpr(UnaryOpr::CustomErr(_), inner) => expr_to_node(inner, ctx),
        // `has_resolved(x)` → uninterpreted Prop. The catch-all below
        // would render it as the bare argument (`has_resolved vec` →
        // `vec`), turning vstd's `axiom_vec_has_resolved` ensures
        // `has_resolved(vec) ==> ..` into `vec → ..` (a value in type
        // position — "type expected, got"). Tactus doesn't model
        // resolution, so leave it abstract. See `Tactus.hasResolved` in
        // the prelude. (#122)
        ExprX::UnaryOpr(UnaryOpr::HasResolved(_), inner) => apply(
            "Tactus.hasResolved",
            vec![expr_to_ast(inner, ctx)],
        ),
        ExprX::UnaryOpr(_, inner) => expr_to_node(inner, ctx),

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
            let rendered: Vec<LExpr> = exprs.iter().map(|e| expr_to_ast(e, ctx)).collect();
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
            ExprNode::ArrayLit(exprs.iter().map(|e| expr_to_ast(e, ctx)).collect())
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
        | ExprX::NeverToAny(e) => expr_to_node(e, ctx),
        ExprX::AssertBy { ensure, .. } => expr_to_node(ensure, ctx),
        ExprX::AssertQuery { .. } => ExprNode::LitBool(true),
        ExprX::OpenInvariant(_, _, body, _) => expr_to_node(body, ctx),

        // `ExprX::Old(e)` is Verus's marker for "evaluate `e` in the
        // pre-state context." Inside `Old`, references to a callee's
        // mut-param local resolve to the **pre-state** value (caller's
        // arg pre-call), NOT the post-state existential.
        //
        // We honor this by swapping `ctx.value_subst` with
        // `ctx.value_subst_pre` for the recursive descent: every Var
        // / ReadPlace+Local lookup against the active subst returns
        // the pre-state value. The structural_typ + apply_ref_coercion
        // machinery composes uniformly — the storage typs match
        // between post/pre maps (both at the local's wrapper typ),
        // only the value differs.
        //
        // When `ctx.value_subst_pre` is None (no pre-state map in
        // scope), `with_pre_state_subst` falls back to None for
        // value_subst — the inner expression renders as if no
        // substitution exists, which is the right behavior for
        // non-inlining contexts (proof-fn rendering of fn's own
        // body, where Old is upstream-stripped).
        ExprX::Old(e) => {
            let pre_ctx = ctx.with_pre_state_subst();
            return expr_to_ast(e, &pre_ctx).node;
        }
        ExprX::EvalAndResolve(_, e) => expr_to_node(e, ctx),
        ExprX::BorrowMut(_) | ExprX::TwoPhaseBorrowMut(_)
        | ExprX::BorrowMutTracked(_) => ExprNode::Var(crate::lean_name::LeanName::lit("()")),
        ExprX::ImplicitReborrowOrSpecRead(place, _, _) => place_to_expr(&place.x, ctx).node,
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
fn call_to_node(target: &CallTarget, args: &Exprs, ctx: &crate::expr_shared::RenderCtx) -> ExprNode {
    // Extract the callee Fun (for fn_param_typs lookup) when the target
    // is a CallTarget::Fun. FnSpec and BuiltinSpecFun don't have a Fun
    // in fn_map; args render without the bridge for those.
    let fun_for_lookup: Option<(&Fun, &Typs)> = match target {
        CallTarget::Fun(_, fun, typs, _, _, _) => Some((fun, typs)),
        _ => None,
    };
    let head = match target {
        CallTarget::Fun(_, fun, typs, _, _, _) => {
            // Emit explicit type arguments for generic calls by
            // building an intermediate App head: `fn T1 T2 …`.
            let base = var(&lean_name(&fun.path));
            if typs.is_empty() {
                base
            } else {
                LExpr::app(base, typs.iter().map(|t| typ_to_expr(t)).collect())
            }
        }
        CallTarget::FnSpec(inner) => {
            // The function value at this position must be at bare
            // `Int → Int`-style level so `App(head, args)` works at the
            // Lean level. Verus's spec semantics may decorate the
            // inner expr's typ with auto-borrow refs (`&spec_fn(...)`
            // at the call site), which causes `apply_ref_coercion_if_needed`
            // to wrap with `Tactus.Ref.mk` — producing the wrong
            // shape (`Tactus.Ref.mk f x` instead of `f x`). Peel back
            // those wrappers explicitly: render the inner, then strip
            // its declared wrapper depth via `.deref` chain.
            let rendered = expr_to_ast(inner, ctx);
            crate::expr_shared::apply_deref_chain(
                rendered,
                count_ref_decorations(&inner.typ),
            )
        }
        CallTarget::BuiltinSpecFun(_, typs, _) => {
            let base = var("builtinSpecFun");
            if typs.is_empty() {
                base
            } else {
                LExpr::app(base, typs.iter().map(|t| typ_to_expr(t)).collect())
            }
        }
    };
    if args.is_empty() {
        head.node
    } else {
        // Bridge each arg to the callee's expected param typ — the
        // auto-borrow analog. For inherent-method calls and regular
        // fn calls, the receiver / args may arrive at a different
        // wrapper depth than the callee declares (e.g., `self.view()`
        // passes a bare local where `view(&self)` expects
        // `Tactus.Ref T`). `coerce_lexpr` inserts `.mk` wraps or
        // `.deref` peels structurally. When fn_param_typs returns
        // None (cross-crate callee not in fn_map, or FnSpec/
        // BuiltinSpecFun target), falls back to no-coerce.
        let expected_typs = fun_for_lookup.and_then(|(f, typs)| ctx.fn_param_typs(f, &typs[..]));
        ExprNode::App {
            head: Box::new(head),
            args: args.iter().enumerate().map(|(i, a)| {
                let rendered = expr_to_ast(a, ctx);
                match &expected_typs {
                    Some(typs) if i < typs.len() => {
                        crate::expr_shared::coerce_lexpr(rendered, &a.typ, &typs[i])
                    }
                    _ => rendered,
                }
            }).collect(),
        }
    }
}

/// Render a trait-method call head (`Dynamic` / `DynamicResolved`) so it
/// matches the emitted class name. The class is `lean_name(&tr.name)` —
/// the trait's full module-qualified segment path (e.g. vstd's
/// `view::View` → `view.View`; the crate lives in `PathX::krate`, not in
/// `segments`, so it's never part of the name). The trait method decl's
/// `fun.path` extends that with the method segment, so `lean_name(&fun.path)`
/// yields `view.View.view` — exactly `<class>.<method>`.
///
/// An earlier version took only the last two path segments (`View.view`),
/// which coincided with `lean_name` for crate-root traits but dropped the
/// module segment for anything nested (`mymod::MyTrait::method` rendered
/// `MyTrait.method` while the class was `mymod.MyTrait`). Cross-crate vstd
/// traits live under a module (`view::View`), so last-2 emitted bare
/// `View.view` against a `view.View` class — unresolved (#122 B2).
fn trait_method_ref(fun: &Fun) -> LExpr {
    var(&lean_name(&fun.path))
}


fn ctor_to_node(dt: &Dt, variant: &Ident, fields: &Binders<Expr>, ctx: &crate::expr_shared::RenderCtx) -> ExprNode {
    let rendered = fields.iter().map(|f| expr_to_ast(&f.a, ctx)).collect();
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
fn block_to_node(stmts: &[Stmt], final_expr: Option<&Expr>, ctx: &crate::expr_shared::RenderCtx) -> ExprNode {
    let body = match final_expr {
        Some(e) => expr_to_ast(e, ctx),
        None if stmts.is_empty() => LExpr::var_lit("()"),
        // No final expression — the last stmt's value is the block's value.
        // In spec mode this is unusual; fall back to unit.
        None => LExpr::var_lit("()"),
    };

    let mut folded = body;
    for stmt in stmts.iter().rev() {
        folded = match &stmt.x {
            StmtX::Decl { pattern, init, .. } => {
                let value = match init {
                    Some(place) => place_to_expr(&place.x, ctx),
                    // No initializer (e.g., `let x;`) — give a placeholder.
                    None => LExpr::var_lit("_"),
                };
                match &pattern.x {
                    PatternX::Var(binding) => LExpr::let_bind(
                        crate::lean_name::LeanName::from_var_ident(&binding.name),
                        value,
                        folded,
                    ),
                    other => LExpr::match_expr(value, vec![crate::lean_ast::MatchArm {
                        pattern: pattern_to_ast(other),
                        body: folded,
                    }]),
                }
            }
            StmtX::Expr(e) => LExpr::let_bind(
                crate::lean_name::LeanName::lit("_"),
                expr_to_ast(e, ctx),
                folded,
            ),
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
                // Verus tuples render as Lean pair patterns, matching
                // the expr side (`ExprNode::Tuple`) — the tuple%N
                // constructor name has no Lean counterpart. 1-tuples
                // flatten to their element (the type renderer does the
                // same), so the sub-pattern stands alone.
                Dt::Tuple(1) => {
                    return pattern_to_ast(&pats[0].a.x);
                }
                Dt::Tuple(_) => {
                    return LPattern::Tuple(
                        pats.iter().map(|p| pattern_to_ast(&p.a.x)).collect(),
                    );
                }
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
        PatternX::Expr(e) => LPattern::Lit(expr_to_node(e, &crate::expr_shared::RenderCtx::empty())),
        PatternX::Range(lo, _hi) => {
            // Lean doesn't have numeric range patterns; fall back to the low
            // bound (or wildcard if absent). Range patterns are rare in spec
            // mode (ast_simplify usually eliminates Match).
            match lo {
                Some(e) => LPattern::Lit(expr_to_node(e, &crate::expr_shared::RenderCtx::empty())),
                None => LPattern::Wildcard,
            }
        }
        PatternX::MutRef(inner) | PatternX::ImmutRef(inner) => pattern_to_ast(&inner.x),
    }
}

// ── Places ──────────────────────────────────────────────────────────────

fn place_to_expr(place: &PlaceX, ctx: &crate::expr_shared::RenderCtx) -> LExpr {
    LExpr::new(match place {
        PlaceX::Local(ident) => {
            // Render-time substitution: same as the ExprX::Var arm.
            // Reached via place_to_expr when Local is nested inside
            // DerefMut/ModeUnwrap/Field/etc. — the ReadPlace+Local
            // early-return only handles the outer-Local case.
            // Without this, `*h` (ReadPlace(DerefMut(Local(h)))) renders
            // as bare `h` even when value_subst has an entry, because
            // DerefMut recurses through place_to_expr which previously
            // skipped the substitution.
            let lean_name = crate::lean_name::LeanName::from_var_ident(ident);
            if let Some(value) = ctx.lookup_subst_raw(&lean_name) {
                return value;
            }
            ExprNode::Var(lean_name)
        }
        PlaceX::Field(field_opr, base) => {
            // U2: fields belong to the inner type, not the wrapper —
            // `render_place_with_derefs` applies the .deref chain
            // (binder-aware for Local-rooted bases).
            field_proj_opr(render_place_with_derefs(base, ctx), field_opr).node
        }
        PlaceX::DerefMut(inner) | PlaceX::ModeUnwrap(inner, _) => {
            return place_to_expr(&inner.x, ctx);
        }
        PlaceX::Temporary(expr) => return expr_to_ast(expr, ctx),
        PlaceX::WithExpr(_, place) => return place_to_expr(&place.x, ctx),
        PlaceX::Index(base, idx, _, _) => ExprNode::Index {
            base: Box::new(place_to_expr(&base.x, ctx)),
            idx: Box::new(expr_to_ast(idx, ctx)),
            // Place-position indexing in proof fns is rare and usually
            // sees the bounds proof in scope (legacy mut-ref code).
            // Keep the plain `[idx]` form here; add `!` only when we
            // identify a concrete shape that needs it.
            bang: false,
        },
        PlaceX::UserDefinedTypInvariantObligation(inner, _) => {
            return place_to_expr(&inner.x, ctx);
        }
    })
}

// ── Tests ───────────────────────────────────────────────────────────────

#[cfg(test)]
#[path = "tests/to_lean_expr.rs"]
mod tests;
