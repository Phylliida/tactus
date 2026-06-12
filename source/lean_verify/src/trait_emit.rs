//! Trait → Lean `class` and trait-impl → Lean `instance` emission,
//! plus the trait-bound rendering machinery both share with fn binders.
//!
//! Carved out of `to_lean_fn.rs` as a pure code move (REFACTORING2
//! § 1.3) — the same playbook as the 2026-06-05 extractions. Items used
//! by the rest of the crate are re-exported from `to_lean_fn` so call
//! paths and the `use super::*` unit tests stayed put.

use std::collections::HashMap;
use vir::ast::*;
use crate::lean_ast::{
    and_all, Binder as LBinder, BinderKind, Class, ClassMethod, Expr as LExpr,
    ExprNode, Instance, InstanceMethod,
};
use crate::to_lean_expr::vir_expr_to_ast;
use crate::to_lean_type::{lean_name, sanitize, short_name, typ_to_expr};
use crate::to_lean_fn::{
    wrap_body_with_param_derefs, SUBTYPE_WITNESS_AUTO_PROOF, TACTIC_BODY_FALLBACK,
};

// ── Trait (Lean `class`) ───────────────────────────────────────────────

pub fn trait_to_ast(
    tr: &TraitX,
    ectx: &crate::emit_ctx::EmitCtx,
) -> Class {
    // A trait in the un-emittable set (a method decl stripped
    // cross-crate, e.g. `core::clone::Clone`) is emitted as a
    // method-less *marker shell* (drop the stripped methods, keep the
    // class header). The shell carries no methods and no laws, so it
    // asserts nothing — it can't make any obligation falsely provable
    // (same category as external-body-type opaque axioms). For a
    // NON-shell trait a missing method is a genuine same-crate bug, so
    // we still panic. The set also drops superclass bounds that
    // REFERENCE a shell trait (a contentless bound; see
    // `drop_unemittable_trait_bounds`) (#122).
    let shell = ectx.unemittable.contains(&tr.name);
    // Positional class binders: `(Self : Type) (T : Type) … (Item : outParam Type)`.
    let mut typ_params: Vec<LBinder> = Vec::new();
    typ_params.push(LBinder::explicit(crate::lean_name::LeanName::lit("Self"), LExpr::var_lit("Type")));
    for (tp, _) in tr.typ_params.iter() {
        typ_params.push(LBinder::typ_param(tp.as_str(), BinderKind::Explicit));
    }
    for assoc_name in tr.assoc_typs.iter() {
        typ_params.push(LBinder::typ_param(assoc_name.as_str(), BinderKind::OutParam));
    }
    // INHERITED out-params: a trait carries the (unpinned) out-params of its
    // superclasses as its own `outParam` binders, so the `extends` clause can
    // thread them into the parent's out-param slots (Lean can't leave an
    // out-param a hole at class-declaration time). `compute_trait_outparams`
    // gives the full ordered list (own + inherited); the own ones are already
    // emitted above, so add only the inherited tail.
    if let Some(all_outparams) = ectx.trait_outparams.get(&tr.name) {
        let own: std::collections::HashSet<&str> =
            tr.assoc_typs.iter().map(|a| a.as_str()).collect();
        for name in all_outparams.iter() {
            if own.contains(name.as_str()) { continue; }
            typ_params.push(LBinder::typ_param(name.as_str(), BinderKind::OutParam));
        }
    }

    // Superclasses render as Lean's native `extends P₁, P₂, …`, with each
    // parent's out-param slots threaded (see `class_extends_to_ast`). Lean's
    // `extends` handles superclass transitivity for us.
    let extends_parents = class_extends_to_ast(&tr.typ_bounds, &ectx.unemittable, &ectx.trait_outparams);

    // Pre-compute the set of sibling method names. Used by proof-fn
    // method-type rendering: ensures expressions that reference
    // sibling trait methods must render UNQUALIFIED (Lean rejects
    // `Class.method` inside the class declaration; see
    // `proof_fn_method_type` docstring).
    let trait_short_name = short_name(&tr.name).to_string();
    let sibling_methods: std::collections::HashSet<String> = tr.methods.iter()
        .filter_map(|m| m.path.segments.last().map(|s| s.to_string()))
        .collect();

    let methods: Vec<ClassMethod> = tr.methods.iter().filter_map(|method_fun| {
        let func = match ectx.fn_map.get(method_fun) {
            Some(f) => *f,
            // Shell trait: the method decl is stripped cross-crate. Drop
            // it — the marker shell keeps only its (emittable) header.
            None if shell => return None,
            // Non-shell trait with a missing method: genuine same-crate
            // bug (the whole-crate prune keeps every same-crate fn).
            None => panic!(
                "trait method {:?} not found in VIR function list — \
                 this is a Tactus bug, please report it",
                method_fun.path
            ),
        };
        let short = method_fun.path.segments.last()
            .map(|s| s.as_str()).unwrap_or("_");
        // Class-method default body, when the trait provides one.
        // Render strategy by mode:
        // * Spec methods: render the actual body via `vir_expr_to_ast`,
        //   wrapped in `fun (p₁ : _) (p₂ : _) … => body`. Lean unfolds
        //   class defaults during typeclass dispatch, so the body is
        //   load-bearing.
        // * Exec methods: render `default` placeholder wrapped in
        //   lambda. Rendering exec bodies via vir_expr_to_ast panics
        //   on Assign/Loop/Return; the body isn't load-bearing for
        //   verification (walk_call inlines specs, not bodies).
        // * Proof methods: render the tactic body verbatim as
        //   `by <tactic>` (via Raw escape hatch). Default body in
        //   the trait provides a proof that holds for any Self
        //   satisfying the class — Verus enforces this. Wrapped in
        //   lambda over the proof fn's params so the body's
        //   references to params (`self`, etc.) resolve correctly.
        //
        // Note for proof-fn class methods: the method's TYPE is a
        // Prop-valued `∀ params, ensures` (or subtype for non-unit
        // returns) — see `proof_fn_method_type`. So the default body
        // must produce a term of that type, which a tactic proof does.
        let default = func.body.as_ref().map(|b| {
            let body_binders = crate::to_lean_expr::binder_ctx_from_params(&func.params);
            let body_expr = match func.mode {
                vir::ast::Mode::Spec => wrap_body_with_param_derefs(
                    crate::to_lean_expr::vir_expr_to_ast_with_binders(b, &body_binders, &crate::expr_shared::RenderCtx::empty()),
                    &func.params),
                vir::ast::Mode::Exec => LExpr::var_lit("default"),
                vir::ast::Mode::Proof => {
                    // Class default for proof-fn method. Mirrors
                    // `trait_impl_to_ast`'s instance-side logic:
                    // unit return → `by <tactic>`; non-unit return
                    // → `⟨value, by first | rfl | simp_all⟩` built
                    // structurally via Anon + ByBlock.
                    if is_unit_typ(&func.ret.x.typ) {
                        let tac = ectx.tactic_bodies.get(&func.name)
                            .map(|s| s.as_str())
                            .unwrap_or(TACTIC_BODY_FALLBACK);
                        LExpr::by_block(tac)
                    } else {
                        let value = wrap_body_with_param_derefs(
                            crate::to_lean_expr::vir_expr_to_ast_with_binders(b, &body_binders, &crate::expr_shared::RenderCtx::empty()),
                            &func.params);
                        let proof = LExpr::by_block(SUBTYPE_WITNESS_AUTO_PROOF);
                        LExpr::anon(vec![value, proof])
                    }
                }
            };
            if func.params.is_empty() {
                body_expr
            } else {
                let binders: Vec<LBinder> = func.params.iter().map(|p| LBinder::explicit(
                    crate::lean_name::LeanName::synthetic(sanitize(p.x.name.0.as_str())),
                    LExpr::var_lit("_"),
                )).collect();
                LExpr::lambda(binders, body_expr)
            }
        });
        // Only spec-mode methods get termination clauses rendered.
        // Exec methods have placeholder bodies (no termination to
        // discharge). Proof methods have tactic bodies, but Lean
        // doesn't accept `termination_by` on class-method defaults
        // (it's for `def`/`theorem`); recursive proof-fn trait
        // methods are a documented deferral — see DESIGN.md TODO.
        let termination_by: Vec<LExpr> = if matches!(func.mode, vir::ast::Mode::Spec) {
            func.decrease.iter().map(|d| vir_expr_to_ast(d)).collect()
        } else {
            Vec::new()
        };
        // Method type: Prop-valued for proof fns, function-typed for
        // spec/exec. Proof-fn type captures the trait's full semantic
        // promise (the ensures is the class method type itself, with
        // sibling references stripped to unqualified form).
        let ty = if matches!(func.mode, vir::ast::Mode::Proof) {
            proof_fn_method_type(func, &trait_short_name, &sibling_methods)
        } else {
            method_type(func)
        };
        Some(ClassMethod {
            name: sanitize(short),
            ty,
            default,
            termination_by,
        })
    }).collect();

    Class {
        name: lean_name(&tr.name),
        typ_params,
        extends_parents,
        methods,
    }
}

/// Build the method type `<self_ty> → P₁ → … → Ret`. Inside a class,
/// associated types become unqualified identifiers (they're class type
/// params), and the trait's `Self%` type-param normalizes to the
/// class's outer `Self`. Reference-like decorations on the receiver
/// type (`&self`, `&mut self`, `Box<Self>`, etc.) survive as
/// `Tactus.Ref Self` etc. so that trait dispatch matches the impl
/// side.
fn method_type(func: &FunctionX) -> LExpr {
    let mut out = typ_maybe_projection_to_expr(&func.ret.x.typ);
    for p in func.params.iter().rev() {
        out = LExpr::implies(typ_maybe_projection_to_expr(&p.x.typ), out);
    }
    out
}

/// Inside a class definition:
/// - `Self::AssocType` projections render as the bare associated-type
///   name (a class type param).
/// - The trait's Self typ_param (`TypX::TypParam` with name
///   matching `vir::def::trait_self_type_param()`) renders as
///   the outer class's `Self` type variable.
/// - Everything else delegates to the standard type translator.
///
/// **Why the Self normalization.** Verus represents the trait's Self
/// as a typ_param with a canonical disambiguated name (literally
/// `"Self%"` per `vir::def::TRAIT_SELF_TYPE_PARAM`). The class
/// declaration's outer type variable is literally `Self` (no
/// disambiguator), so a method signature referencing the trait's
/// Self must normalize to match. Without this, e.g., a `proof fn
/// produce() -> (r: Self)` class field would render as
/// `produce : { _return : Self% // True }` — a dangling reference
/// the sanity check (correctly) rejects.
///
/// We match against `trait_self_type_param()` directly rather than
/// string-parsing the suffix, so a Verus-side rename of the constant
/// causes a compile error here rather than silent breakage.
fn typ_maybe_projection_to_expr(typ: &TypX) -> LExpr {
    use vir::ast::TypDecoration;
    use crate::lean_ast::BinOp;

    fn applied(name: &str, args: Vec<LExpr>) -> LExpr {
        if args.is_empty() {
            LExpr::var_lit(name)
        } else {
            LExpr::app(LExpr::var_lit(name), args)
        }
    }

    match typ {
        TypX::TypParam(name) if *name == vir::def::trait_self_type_param() => {
            LExpr::var_lit("Self")
        }
        TypX::Projection { name, .. } => {
            // Inside a class declaration, assoc-type projections render
            // as the bare name (a class type param).
            LExpr::var_synthetic(sanitize(name))
        }
        TypX::Decorate(deco, _, inner) => match deco {
            TypDecoration::Ref => applied("Tactus.Ref", vec![typ_maybe_projection_to_expr(inner)]),
            TypDecoration::MutRef => applied("Tactus.MutRef", vec![typ_maybe_projection_to_expr(inner)]),
            TypDecoration::Box => applied("Tactus.Box", vec![typ_maybe_projection_to_expr(inner)]),
            TypDecoration::Rc => applied("Tactus.Rc", vec![typ_maybe_projection_to_expr(inner)]),
            TypDecoration::Arc => applied("Tactus.Arc", vec![typ_maybe_projection_to_expr(inner)]),
            TypDecoration::Ghost | TypDecoration::Tracked
            | TypDecoration::Never | TypDecoration::ConstPtr =>
                typ_maybe_projection_to_expr(inner),
        },
        TypX::MutRef(inner) => applied("Tactus.MutRef", vec![typ_maybe_projection_to_expr(inner)]),
        TypX::Boxed(inner) => typ_maybe_projection_to_expr(inner),
        TypX::Datatype(dt, args, _) => match dt {
            vir::ast::Dt::Path(path) => {
                let head = crate::to_lean_type::lean_name(path);
                let mapped: Vec<LExpr> = args.iter()
                    .map(|a| typ_maybe_projection_to_expr(a)).collect();
                if mapped.is_empty() {
                    LExpr::var_lit(&head)
                } else {
                    LExpr::app(LExpr::var_lit(&head), mapped)
                }
            }
            vir::ast::Dt::Tuple(_) => match args.len() {
                0 => applied("Unit", Vec::new()),
                1 => typ_maybe_projection_to_expr(&args[0]),
                _ => {
                    let mut iter = args.iter().rev();
                    let mut acc = typ_maybe_projection_to_expr(iter.next().unwrap());
                    for a in iter {
                        acc = LExpr::binop(BinOp::Prod, typ_maybe_projection_to_expr(a), acc);
                    }
                    acc
                }
            },
        },
        TypX::SpecFn(params, ret) => {
            let mut out = typ_maybe_projection_to_expr(ret);
            for p in params.iter().rev() {
                out = LExpr::implies(typ_maybe_projection_to_expr(p), out);
            }
            out
        }
        TypX::Primitive(prim, args) => {
            let head = match prim {
                vir::ast::Primitive::Array => "Array",
                vir::ast::Primitive::Slice => "List",
                vir::ast::Primitive::StrSlice => "String",
                vir::ast::Primitive::Ptr => "USize",
                vir::ast::Primitive::Global => "Unit",
            };
            let type_args: Vec<_> = match prim {
                vir::ast::Primitive::Array | vir::ast::Primitive::Slice => {
                    args.iter().take(1).map(|a| typ_maybe_projection_to_expr(a)).collect()
                }
                _ => args.iter().map(|a| typ_maybe_projection_to_expr(a)).collect(),
            };
            applied(head, type_args)
        }
        // Everything else falls through to the standard renderer; these
        // shapes don't contain Self% or Projection (or if they do, the
        // standard renderer's emission is acceptable as-is).
        _ => typ_to_expr(typ),
    }
}

// `is_unit_typ` lives in `to_lean_type.rs` — shared with `dep_order`'s
// `seed_impl_proof_method_bodies`, which needs the same discrimination
// to decide whether an impl proof-fn body must be pre-seeded.
use crate::to_lean_type::is_unit_typ;

/// Build value-level parameter binders for a trait method's class-
/// method type. Distinct from `fn_binders` (which also emits
/// `(T : Type)` for typ_params and `[Trait T]` for trait bounds — both
/// of which are the OUTER class's responsibility when we're inside a
/// class declaration). Mathlib's class method type idiom binds only
/// value-level params.
///
/// For `self`-typed params, renders the type as `Self` (the class
/// type variable) rather than going through `typ_to_expr` which would
/// produce the trait's full path.
fn class_method_value_binders(func: &FunctionX) -> Vec<LBinder> {
    let mut out: Vec<LBinder> = Vec::new();
    for p in func.params.iter() {
        let name = crate::lean_name::LeanName::from_var_ident(&p.x.name);
        let ty = typ_maybe_projection_to_expr(&p.x.typ);
        out.push(LBinder::explicit(name.clone(), ty));
        if let Some(pred) = crate::to_lean_sst_expr::type_bound_predicate(
            &LExpr::var(name.clone()),
            &p.x.typ,
        ) {
            out.push(LBinder::explicit(crate::lean_name::LeanName::synthetic(format!("h_{}_bound", name.as_str())), pred));
        }
    }
    out
}

/// Build the class-method type for a proof-fn trait method.
///
/// Lean's idiom for "typeclass promises lemmas about its types" is
/// Prop-typed class fields (see Mathlib's `Group.mul_assoc`, etc.).
/// This helper builds `∀ (params...) (req_hyps...), <ensures>` for the
/// common unit-return case.
///
/// For non-unit return types, the goal becomes a subtype
/// `{ ret : RetTy // <ensures> }` so the instance must provide a
/// witnessing value together with a proof. The return name is bound
/// inside the ensures by Verus's named-return convention.
///
/// References to sibling trait methods inside the ensures must render
/// as UNQUALIFIED names. Lean rejects `ClassName.method` inside the
/// class declaration itself — the class isn't fully declared at that
/// point. Mathlib uniformly uses unqualified sibling references; we
/// post-process the rendered LExpr to strip the class qualifier from
/// known sibling method names.
fn proof_fn_method_type(
    func: &FunctionX,
    class_name: &str,
    sibling_methods: &std::collections::HashSet<String>,
) -> LExpr {
    // Class methods bind ONLY value-level params (and their refinement
    // bounds + requires hypotheses). The trait's `Self` is the class's
    // type variable (already in scope at the method's site); the
    // trait's bounds are imposed by the class extends mechanism, not
    // re-introduced on each method. Mathlib's `Semigroup` shows the
    // shape: `class Semigroup (G : Type u) extends Mul G where
    //   mul_assoc : ∀ a b c : G, ...` — no `(G : Type)` or `[Mul G]`
    // re-binders inside `mul_assoc`'s type.
    let mut binders = class_method_value_binders(func);
    let body_binders = crate::to_lean_expr::binder_ctx_from_params(&func.params);
    for (i, req) in func.require.iter().enumerate() {
        // Inside the class declaration, sibling refs can use bare
        // names (the class's own scope) — pass empty `impl_prefix`
        // to get the bare-name rewrite. Instance bodies use a
        // non-empty prefix to route to impl-specific standalones.
        let req_ty = strip_class_qualifier(
            crate::to_lean_expr::vir_expr_to_ast_with_binders(req, &body_binders, &crate::expr_shared::RenderCtx::empty()),
            class_name, "", sibling_methods,
        );
        // Requires render as named hypothesis binders following the
        // `_tactus_<role>_<id>` reserved-name convention (see
        // expr_shared.rs § "Reserved identifier conventions").
        // Anonymous binders aren't an option — Lean's ∀ chain
        // requires each binder to have a name, and our pp only
        // emits `(name : ty)` when name is Some.
        binders.push(LBinder::explicit(crate::lean_name::LeanName::synthetic(format!("_tactus_req_{}", i)), req_ty));
    }
    let ensures = and_all(func.ensure.0.iter()
        .map(|e| strip_class_qualifier(
            crate::to_lean_expr::vir_expr_to_ast_with_binders(e, &body_binders, &crate::expr_shared::RenderCtx::empty()),
            class_name, "", sibling_methods))
        .collect());

    let goal = if is_unit_typ(&func.ret.x.typ) {
        ensures
    } else {
        // Non-unit return: render as `{ ret : RetTy // <ensures> }`
        // via the structured Subtype AST node. The node owns its
        // type and predicate as LExprs — pp handles composition,
        // sanity check handles scoping (name is bound in pred),
        // substitute handles alpha-renaming.
        let ret_name = crate::lean_name::LeanName::synthetic(
            sanitize(func.ret.x.name.0.as_str())
        );
        let ret_ty = typ_maybe_projection_to_expr(&func.ret.x.typ);
        LExpr::subtype(ret_name, ret_ty, ensures)
    };

    if binders.is_empty() {
        goal
    } else {
        LExpr::forall(binders, goal)
    }
}

/// Walk `expr` and rewrite any `Var("<class_name>.<method>")` where
/// `method` is in `sibling_methods` to `Var("<method>")` (unqualified).
///
/// Inside a class declaration, sibling references to other methods of
/// the same class MUST be unqualified — see `proof_fn_method_type`'s
/// docstring for why. This helper applies the rewrite to a fully-
/// rendered LExpr, walking via the existing structural map_children
/// machinery so we don't have to enumerate every ExprNode variant.
/// Rewrite `Class.method` refs inside an instance body to the
/// disambiguated standalone-def name (`<impl_prefix>.method`).
/// Lean's `instance` construction can't forward-reference siblings
/// via class dispatch (the instance isn't available for synthesis
/// during its own definition — see Lean reference manual §
/// "Instance Declarations"). So sibling refs in impl method bodies
/// must go through the standalone defs that `spec_fn_to_ast` emits,
/// at their post-disambiguation names (per `lean_name`'s impl-
/// marker preservation, 2026-05-17 fix for
/// BUG-no-helper-proof-fn-call-from-exec.md).
///
/// `impl_prefix` is the dotted-path prefix shared by all siblings
/// of THIS impl (computed by dropping the last segment of any
/// impl method's `lean_name` rendering — e.g., for `MyInt::is_zero`
/// at full path `test_crate.impl__0.is_zero`, the prefix is
/// `test_crate.impl__0`). Passed in by `trait_impl_to_ast`.

fn strip_class_qualifier(
    expr: LExpr,
    class_name: &str,
    impl_prefix: &str,
    sibling_methods: &std::collections::HashSet<String>,
) -> LExpr {
    let class_prefix = format!("{}.", class_name);
    strip_class_qualifier_rec(expr, &class_prefix, impl_prefix, sibling_methods)
}

fn strip_class_qualifier_rec(
    expr: LExpr,
    class_prefix: &str,
    impl_prefix: &str,
    sibling_methods: &std::collections::HashSet<String>,
) -> LExpr {
    match &expr.node {
        ExprNode::Var(name) => {
            let s = name.as_str();
            if let Some(rest) = s.strip_prefix(class_prefix) {
                if sibling_methods.contains(rest) {
                    let disambiguated = if impl_prefix.is_empty() {
                        rest.to_string()
                    } else {
                        format!("{}.{}", impl_prefix, rest)
                    };
                    return LExpr::var_synthetic(disambiguated);
                }
            }
            expr
        }
        _ => {
            let node = crate::lean_ast::map_children(&expr.node, |c: &LExpr| {
                strip_class_qualifier_rec(c.clone(), class_prefix, impl_prefix, sibling_methods)
            });
            LExpr::new(node)
        }
    }
}

// ── Trait impl (Lean `instance`) ───────────────────────────────────────

/// Does `e` read the local variable named `self_name` (peeling
/// transparent unary wrappers / borrows)? Used to confirm a blanket
/// impl method's receiver arg is exactly the self param — `(**self)` —
/// and not a derived expression like `modified(**self)`.
fn recv_reads_local(e: &Expr, self_name: &str) -> bool {
    match &e.x {
        ExprX::ReadPlace(place, _) =>
            matches!(&place.x, PlaceX::Local(v) if v.0.as_str() == self_name),
        // Peel ONLY transparent wrappers — poly box/unbox, coerce-mode /
        // trigger markers, custom-err — never value-transforming ops
        // (Not / Clip / BitNot / Field / IsVariant / HasType / arithmetic
        // / …). A transform between `**self` and `.method()` means the
        // body is NOT a pure forward, so the synth must not fire (it would
        // silently drop the transform, emitting an unfaithful instance).
        // Mirrors the explicit-transparent-arms-then-reject structure of
        // `to_lean_expr::expr_to_node`'s unary handling, rather than a
        // wildcard `_` that would peel transforms too.
        ExprX::Unary(UnaryOp::CoerceMode { .. } | UnaryOp::Trigger(_), inner) =>
            recv_reads_local(inner, self_name),
        ExprX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_) | UnaryOpr::CustomErr(_), inner) =>
            recv_reads_local(inner, self_name),
        _ => false,
    }
}

/// If `func` is a forwarding blanket-impl method — Self is a single
/// reference wrapper over a bare type-param (`&A` / `Box<A>` / `Rc<A>`
/// / `Arc<A>`) and the body is exactly `(**self).method()` (a call to
/// the SAME trait method whose sole receiver arg reads the self
/// param) — synthesize the faithful instance body.
///
/// Verus reduces the `**self` deref for `&`/Box (so literal rendering
/// dispatches on the inner type correctly), but leaves the smart-
/// pointer spec deref opaque for Rc/Arc, so the literal render
/// dispatches `View.view` on `Rc A` = the instance under construction
/// (circular — "failed to synthesize"). The synth reproduces Rust's
/// `(**self).view()` directly: the Lean class field is `view : Ref
/// Self → V`, so the binder `self : Ref (Wrapper A)`; `self.deref`
/// peels the `&`, `.deref` peels the wrapper to the inner value, and
/// `Tactus.Ref.mk` re-borrows it so `Trait.method` dispatches the
/// inner's instance via the `[Trait A]` bound. Uniform and correct
/// for all four wrappers; the prelude wrappers' `.deref` reduces where
/// Verus's smart-pointer deref didn't.
///
/// Returns None for any other shape (non-forwarding bodies like
/// `(**self).view() + 1`, struct-field forwards like `self.0.view()`,
/// multi-param methods), so those fall through to faithful literal
/// rendering — the synth only fires when it provably reproduces the
/// source. (#122 B1)
fn forwarding_blanket_body(ti: &TraitImplX, func: &FunctionX) -> Option<LExpr> {
    // Self: a single SHARED-ref wrapper over a bare type-param. MutRef
    // is excluded: the synth assumes the class field receiver is
    // `Tactus.Ref Self` (a `&self` method) and re-wraps with
    // `Tactus.Ref.mk`; a `&mut self` forwarding method would have a
    // `MutRef`-typed receiver and need different handling (none exists in
    // vstd's View blankets, so excluding it is a no-op that removes a
    // latent wrong-synth).
    let self_typ = ti.trait_typ_args.first()?;
    match &**self_typ {
        TypX::Decorate(deco, _, inner)
            if crate::expr_shared::decoration_wrapper(*deco).is_some()
                && !matches!(deco, vir::ast::TypDecoration::MutRef)
                && matches!(&**inner, TypX::TypParam(_)) => {}
        _ => return None,
    }
    // Exactly the receiver param (no extra args to forward).
    if func.params.len() != 1 { return None; }
    let self_name = func.params[0].x.name.0.as_str();
    let method_short = func.name.path.segments.last()?.as_str();
    // Body (peeling a trivial wrapping Block) is `Trait::method(recv)`.
    let body = func.body.as_ref()?;
    let inner = match &body.x {
        ExprX::Block(stmts, Some(e)) if stmts.is_empty() => e,
        _ => body,
    };
    let ExprX::Call(CallTarget::Fun(_, fun, _, _, _, _), args, _) = &inner.x
        else { return None; };
    // The call targets the SAME trait method:
    // `fun.path.segments == trait_path.segments ++ [method_short]`.
    let tsegs = &ti.trait_path.segments;
    let fsegs = &fun.path.segments;
    if fsegs.len() != tsegs.len() + 1 { return None; }
    if !tsegs.iter().zip(fsegs.iter()).all(|(a, b)| a == b) { return None; }
    if fsegs.last().map(|s| s.as_str()) != Some(method_short) { return None; }
    // The single receiver arg reads the self param (`(**self)`).
    if args.len() != 1 || !recv_reads_local(&args[0], self_name) { return None; }
    // Build `<Trait.method> (Tactus.Ref.mk (self.deref.deref))`.
    // Deref depth 2: one `.deref` peels the class field's `&self`
    // (`view : Tactus.Ref Self → V`), one more peels the single Self
    // wrapper to the inner type-param. The gate above guarantees Self is
    // exactly one wrapper over a bare TypParam, so the depth is fixed at
    // 2 — if that gate ever admits a multi-layer Self, this must change
    // with it. The outer `.mk` is always `Tactus.Ref` (the class field is
    // `Ref Self` regardless of whether Self's wrapper is Box/Rc/Arc), so
    // the inner instance's `Ref inner` receiver matches.
    const CLASS_FIELD_REF_PLUS_SELF_WRAPPER: usize = 2;
    let method_qualified = format!("{}.{}", lean_name(&ti.trait_path), method_short);
    let self_var = LExpr::var_synthetic(sanitize(self_name));
    let inner_arg = crate::expr_shared::apply_wrap_chain(
        crate::expr_shared::apply_deref_chain(self_var, CLASS_FIELD_REF_PLUS_SELF_WRAPPER),
        &["Tactus.Ref"],
    );
    Some(LExpr::app1(LExpr::var_lit(&method_qualified), inner_arg))
}

pub fn trait_impl_to_ast(
    ti: &TraitImplX,
    method_impls: &[&FunctionX],
    assoc_types: &[&AssocTypeImplX],
    subst: &crate::impl_subst::ImplSubst,
    // Synthetic `[Nonempty T]` bounds the instance inherits from its
    // method-impl fns' `choose` usage (#122 layer 5). Merged into the
    // bound list alongside the impl's own bounds + the subst's fake
    // bounds, so they render via the same `trait_bounds_to_ast` path.
    nonempty_bounds: &[GenericBound],
    ectx: &crate::emit_ctx::EmitCtx,
) -> Instance {
    let mut binders: Vec<LBinder> = Vec::new();
    for tp in ti.typ_params.iter() {
        binders.push(LBinder::typ_param(tp.as_str(), BinderKind::Implicit));
    }
    // Fresh implicit binders from the projection substitution
    // (per-impl, Bug B step 2). Each fresh binder corresponds to a
    // `<X as T>::N` projection appearing in the impl's signature;
    // see `impl_subst::ImplSubst` for the design.
    for fresh in subst.fresh_binders.iter() {
        binders.push(LBinder::typ_param(fresh.as_str(), BinderKind::Implicit));
    }
    // Augmented bound list: original bounds + fake TypEquality
    // bounds that wire fresh binders into the relevant trait
    // brackets. `trait_bounds_to_ast` already iterates bounds and
    // appends matching TypEquality typs to the rendered args, so
    // synthesising fake equalities reuses that machinery.
    let augmented_bounds: Vec<GenericBound> = (*ti.typ_bounds).iter().cloned()
        .chain(subst.fake_bounds.iter().cloned())
        .chain(nonempty_bounds.iter().cloned())
        .collect();
    let augmented_bounds = std::sync::Arc::new(augmented_bounds);
    binders.extend(trait_bounds_to_ast(&augmented_bounds, &ectx.unemittable));

    // Build `TraitName <positional> <out-params…>`. `trait_typ_args` are the
    // positional trait type arguments (Self + extras). Then EACH of the class's
    // out-param slots (own + transitively inherited, in `trait_outparams`
    // order) is filled with, in priority:
    //   1. the forwarding fresh binder for that out-param NAME, if Source-1/2
    //      minted one — shared with the bound that supplies it, so head and
    //      bound agree (a free binder here → "no concrete values for
    //      out-params"). This covers BOTH the impl's own out-params (View's V)
    //      AND inherited ones whose value comes from a stronger bound (the
    //      `FnMut`/`FnOnce` head reusing the `[Fn F A]` bound's `Output`); it
    //      also sidesteps a declared `type Output = <F as FnOnce>::Output`
    //      whose projection trait differs from the bound's and wouldn't rewrite.
    //   2. else the impl's declared `type N = V` (a concrete assoc), rewritten.
    //   3. else unfilled — Lean surfaces the under-application.
    let mut target_args: Vec<LExpr> = Vec::new();
    for t in ti.trait_typ_args.iter() {
        target_args.push(typ_to_expr(&subst.rewrite_typ(t)));
    }
    if let Some(outparams) = ectx.trait_outparams.get(&ti.trait_path) {
        for name in outparams.iter() {
            if let Some(a) = assoc_types.iter().find(|a| a.name.as_str() == name.as_str()) {
                // The impl's OWN out-param: its declared `type N = V`, rewritten
                // (projections → fresh binders, incl. the transitive fallback
                // for a `<F as FnOnce>::Output` forwarded via a `Fn` bound, and
                // compound values like a pair's `(<A as View>::V, <B as
                // View>::V)`). Declared wins over a by-name fresh so a multi-arg
                // impl's own compound isn't replaced by one component's binder.
                target_args.push(typ_to_expr(&subst.rewrite_typ(&a.typ)));
            } else if let Some(fresh) = subst.outparam_binder(name) {
                // INHERITED out-param via a FORWARDING bound (blanket instance):
                // the forwarding fresh binder, by name (the head's trait may be
                // weaker than the bound's — `FnMut` head reusing the `Fn`
                // bound's `Output`).
                target_args.push(LExpr::var_tp(fresh.as_str()));
            } else if let Some(typ) = find_inherited_assoc(ti, name, &ectx.all_assoc_types) {
                // INHERITED out-param on a CONCRETE instance (no declared
                // `type N`, no forwarding bound): its value is the implementor's
                // sibling superclass-impl assoc — `Dog Rex`'s `Sound` = `Rex`'s
                // `Animal::Sound`. A free binder / unfilled slot here would
                // under-apply the now-N-ary class.
                target_args.push(typ_to_expr(typ));
            }
            // else: unfilled — Lean surfaces the under-application.
        }
    }
    let target = if target_args.is_empty() {
        LExpr::var(crate::lean_name::LeanName::from_path(&ti.trait_path))
    } else {
        LExpr::app(
            LExpr::var(crate::lean_name::LeanName::from_path(&ti.trait_path)),
            target_args,
        )
    };

    // #122 B3: drop binders for type-params the instance head doesn't
    // determine, plus any bound that references such a param. vstd's
    // `impl<T, A: Allocator> Allocator for Box<T, A>` renders Self as
    // `Tactus.Box T` — `typ_to_expr` maps the unary prelude wrapper
    // `Tactus.Box` and erases the allocator arg `A`, so `A` is left
    // free in the head with `[Allocator A]` unconstrained, and Lean
    // reports "cannot find synthesization order". An instance binder
    // not pinned by the head is unsynthesizable regardless; for the
    // empty marker class `Allocator` dropping it (and its bound) loses
    // no provable fact. Implicit binders the head determines (the
    // common case — `View (Tactus.Ref A) _assoc` pins both A and the
    // assoc V) are untouched, so this is a no-op for every existing
    // instance.
    let head_vars = crate::lean_ast::free_var_names(&target);
    let dropped: std::collections::HashSet<String> = binders.iter()
        .filter(|b| b.kind == BinderKind::Implicit)
        .filter_map(|b| b.name.as_ref().map(|n| n.as_str().to_string()))
        .filter(|name| !head_vars.contains(name))
        .collect();
    if !dropped.is_empty() {
        binders.retain(|b| match b.kind {
            // Keep a determined type-param binder; drop an undetermined one.
            BinderKind::Implicit => b.name.as_ref()
                .map(|n| !dropped.contains(n.as_str())).unwrap_or(true),
            // Drop a bound that mentions any dropped param.
            BinderKind::Instance =>
                crate::lean_ast::free_var_names(&b.ty).is_disjoint(&dropped),
            _ => true,
        });
    }

    // Skip body=None methods — they inherit from the class default.
    // Lean's typeclass machinery dispatches to the class default
    // when the instance omits a method. For an empty impl
    // (`impl Tr for T {}` with all method bodies inherited), the
    // result is `instance : Tr T where` with no method bodies —
    // Lean fills in everything from the class.
    //
    // Render strategy is mode-dispatched, see the inner `match`:
    // * Spec methods: render the actual body via `vir_expr_to_ast`
    //   (Lean's typeclass dispatch may unfold the instance's
    //   method during proof, so the body is load-bearing).
    // * Exec methods: emit `default` placeholder (the body isn't
    //   load-bearing — walk_call inlines specs at call sites, not
    //   bodies via typeclass dispatch). Rendering the exec body
    //   would panic on Assign / Loop / Return constructs.
    // * Proof methods, two sub-cases:
    //   - Unit return: instance produces a proof via `by <tactic>`.
    //   - Non-unit return: instance produces a `⟨value, proof⟩`
    //     pair (the body is the witness; rfl/simp_all closes the
    //     subtype equality).
    //
    // Note: if the trait method has NO default body AND the impl
    // also has body=None, that's a structurally invalid state
    // (Verus would have rejected the impl as missing a required
    // method) — skipping is still safe because Lean would catch
    // the missing-method-in-instance error directly.
    // Instance method bodies that reference sibling trait methods
    // must use the BARE standalone-def name, not the class-qualified
    // `Class.method` form — Lean's `instance` construction can't
    // forward-reference siblings (the instance isn't available for
    // synthesis during its own definition; see Lean reference manual
    // § "Instance Declarations"). The VIR-level
    // `rewrite_self_sibling_calls` handles the swap; `method_redirects`
    // maps each impl method's short name to its full `Fun`. The
    // rewrite gates on receiver type, leaving cross-instance calls
    // (blanket-impl case) as class dispatch.
    //
    // Source of truth: `subst.method_context.method_redirects`.
    // That map carries pre-renamed Funs (when the impl-method
    // natural-name rename applies), so sibling-call rewrites
    // produce `Bar.Counter.method` instead of `impl__N.method`.
    // Fallback to empty map when no method context is set (no impl
    // methods, or method_context absent).
    let empty_redirects: HashMap<String, Fun> = HashMap::new();
    let method_redirects: &HashMap<String, Fun> = subst.method_context.as_ref()
        .map(|c| &c.method_redirects)
        .unwrap_or(&empty_redirects);

    let methods: Vec<InstanceMethod> = method_impls.iter()
        .filter_map(|func| {
            let short = func.name.path.segments.last()
                .map(|s| s.as_str()).unwrap_or("_");
            // Body=None impl methods (`uninterp spec fn ...;`) get a
            // synthesized body that dispatches to the standalone axiom
            // emitted by `spec_fn_to_ast`. Without this the instance
            // declares but doesn't provide the method, and Lean rejects.
            // The standalone axiom has signature `(typ_params...)
            // [bounds...] (params...) -> RetTy`; partial-applying the
            // typ_params (which are in scope as implicit binders on the
            // instance) plus param vars in the lambda body gives a
            // function matching the class field type via eta-expansion.
            // Spec-mode only — body=None proof and exec methods are
            // structurally invalid (Verus would have rejected) so the
            // filter still drops them.
            let body_expr = match (func.mode, &func.body) {
                (vir::ast::Mode::Spec, None) => {
                    // Use the renamed Fun path from `method_redirects`
                    // — same source of truth as the body-rewrite
                    // path, carrying the natural-name rename when
                    // applied. Both `method_redirects` and this
                    // `method_impls.iter().filter_map(|func| ...)`
                    // loop iterate the same `method_impls` slice,
                    // so the lookup is guaranteed.
                    let method_short = func.name.path.segments.last()
                        .expect("impl method has at least one path segment")
                        .as_str();
                    let standalone_path = method_redirects.get(method_short)
                        .expect("method_redirects has an entry for every method_impl")
                        .path.clone();
                    let standalone =
                        LExpr::var(crate::lean_name::LeanName::from_path(&standalone_path));
                    let mut args: Vec<LExpr> = func.typ_params.iter()
                        .map(|tp| LExpr::var_tp(tp.as_str()))
                        .collect();
                    for p in func.params.iter() {
                        args.push(LExpr::var_synthetic(sanitize(p.x.name.0.as_str())));
                    }
                    if args.is_empty() {
                        standalone
                    } else {
                        LExpr::app(standalone, args)
                    }
                }
                (vir::ast::Mode::Proof, None) | (vir::ast::Mode::Exec, None) => return None,
                (vir::ast::Mode::Spec, Some(body)) => {
                    // VIR-level type-aware redirect of self-sibling
                    // Class.method calls to impl__N.method standalones.
                    // For blanket-impl bodies that call Trait.method on
                    // a typ-param (a different instance), the receiver-
                    // type check skips the rewrite and the call stays
                    // as class dispatch. See `rewrite_self_sibling_calls`
                    // docs for the full rationale (Bug B body fix).
                    // #122 B1: faithful synth for forwarding blanket-impl
                    // methods (`View for &A`/`Box`/`Rc`/`Arc`, body
                    // `(**self).view()`). Verus reduces the `**self` deref
                    // for `&`/Box (literal render works) but leaves the
                    // smart-pointer spec deref opaque for Rc/Arc, so the
                    // literal render dispatches `View.view` on `Rc A` =
                    // the instance itself (circular). The synth reproduces
                    // `(**self).view()` directly via the prelude wrappers'
                    // reducible `.deref`. Fires only on the exact
                    // forwarding shape; everything else falls through.
                    if let Some(synth) = forwarding_blanket_body(ti, func) {
                        synth
                    } else {
                        let self_typ = ti.trait_typ_args.first()
                            .expect("impl's trait_typ_args must include Self");
                        let rewritten = crate::impl_subst::rewrite_self_sibling_calls(
                            body, &ti.trait_path, self_typ, &method_redirects,
                        );
                        // Wrap with `let p := p.deref` for each reference-
                        // decorated param so the body sees inner types.
                        let body_binders = crate::to_lean_expr::binder_ctx_from_params(&func.params);
                        wrap_body_with_param_derefs(
                            crate::to_lean_expr::vir_expr_to_ast_with_binders(&rewritten, &body_binders, &crate::expr_shared::RenderCtx::empty()),
                            &func.params,
                        )
                    }
                }
                (vir::ast::Mode::Exec, Some(_)) => {
                    // Exec placeholder. `default` produces a value
                    // of any type, satisfying Lean's instance-completeness
                    // requirement without needing to render the
                    // (stateful) exec body. walk_call inlines specs
                    // at call sites, not bodies via typeclass dispatch.
                    LExpr::var_lit("default")
                }
                (vir::ast::Mode::Proof, Some(_)) => {
                    // Proof methods. Two cases based on return type:
                    //
                    // (a) Unit return: the class method's TYPE is
                    //     `∀ params, ensures` (a Prop). The instance
                    //     must produce a proof — the user's `by {
                    //     tactic }` body. Renders as ByBlock with
                    //     context-aware indentation.
                    //
                    // (b) Non-unit return: the class method's TYPE is
                    //     `∀ params, { r : RetTy // ensures }` (a
                    //     subtype). The instance must produce a
                    //     `⟨value, proof⟩` pair. Verus's `by { }`
                    //     syntax doesn't fit non-unit returns (the
                    //     sanitized body fails Rust's type check),
                    //     so the user writes a regular Verus-style
                    //     body expression. Tactus renders that body
                    //     as the WITNESS VALUE and emits `by rfl`
                    //     as the proof (the canonical case where the
                    //     body matches the ensures' RHS literally).
                    //     For non-trivial proofs, the user adds a
                    //     `proof { }` block in the body — Verus's
                    //     auto-postcondition-check handles it on the
                    //     Verus side.
                    if is_unit_typ(&func.ret.x.typ) {
                        let tac = ectx.tactic_bodies.get(&func.name)
                            .map(|s| s.as_str())
                            .unwrap_or(TACTIC_BODY_FALLBACK);
                        LExpr::by_block(tac)
                    } else {
                        // Non-unit return: subtype value pair
                        // `⟨body, by first | rfl | simp_all⟩` built
                        // via structured AST nodes (Anon + ByBlock)
                        // rather than Raw string formatting — pp
                        // handles composition, sanity checks the
                        // value's refs, indentation tracks context
                        // automatically.
                        //
                        // The body's references to sibling spec
                        // methods (e.g., `self.target()`) render via
                        // `vir_expr_to_ast` as the UNQUALIFIED
                        // standalone-def name. At instance-body
                        // emission position, sibling class-field
                        // refs aren't in scope (Lean's instance
                        // elaboration doesn't bring fields into
                        // scope mid-block), AND qualified
                        // `Class.method` refs fail because the
                        // typeclass instance is being constructed.
                        // The standalone def IS in scope —
                        // dep_order pre-seeds impl proof-fn method
                        // bodies for non-unit returns
                        // (`seed_impl_proof_method_bodies`) so the
                        // called spec methods emit as standalone
                        // defs before the instance.
                        let body = func.body.as_ref().unwrap();
                        // VIR-level rewrite (same as the Spec case).
                        let self_typ = ti.trait_typ_args.first()
                            .expect("impl's trait_typ_args must include Self");
                        let rewritten = crate::impl_subst::rewrite_self_sibling_calls(
                            body, &ti.trait_path, self_typ, &method_redirects,
                        );
                        let body_binders = crate::to_lean_expr::binder_ctx_from_params(&func.params);
                        let value = wrap_body_with_param_derefs(
                            crate::to_lean_expr::vir_expr_to_ast_with_binders(&rewritten, &body_binders, &crate::expr_shared::RenderCtx::empty()),
                            &func.params,
                        );
                        // `rfl` closes when body matches ensures
                        // literally; `simp_all` handles unfolding
                        // through standalone def chains.
                        let proof = LExpr::by_block(SUBTYPE_WITNESS_AUTO_PROOF);
                        LExpr::anon(vec![value, proof])
                    }
                }
            };
            let lambda = if func.params.is_empty() {
                body_expr
            } else {
                // `fun (p₁ : _) (p₂ : _) … => body`. The `_` lets Lean
                // infer each parameter type from the class's method
                // signature, which is what we want.
                let binders: Vec<LBinder> = func.params.iter().map(|p| LBinder::explicit(
                    crate::lean_name::LeanName::synthetic(sanitize(p.x.name.0.as_str())),
                    LExpr::var_lit("_"),
                )).collect();
                LExpr::lambda(binders, body_expr)
            };
            Some(InstanceMethod { name: sanitize(short), body: lambda })
        })
        .collect();

    Instance { binders, target, methods }
}
/// Drop `[Trait …]` bounds that reference an un-emittable (shell)
/// trait. A shell trait is a contentless marker (its method decls are
/// stripped cross-crate — e.g. `core::clone::Clone`), so a bound on it
/// carries no provable fact: dropping it loses nothing (the same
/// justification as the #122 B3 head-undetermined-binder drop —
/// "an undetermined binder is unsynthesizable anyway; dropping it loses
/// no provable fact"). Keeping such bounds instead produces unsatisfiable
/// synthesis: a `marker.Copy : [clone.Clone Self]` superclass plus
/// `[clone.Clone K]` / `[cmp.PartialEq T T]` instance binders over
/// abstract type params have no satisfiable base, and the
/// `Copy ↔ Clone` superclass/blanket pair forms a resolution cycle.
/// Non-Trait bounds and Trait bounds on emittable traits pass through.
fn drop_unemittable_trait_bounds(
    bounds: &GenericBounds,
    unemittable: &std::collections::HashSet<Path>,
) -> GenericBounds {
    std::sync::Arc::new(
        bounds.iter()
            .filter(|b| !matches!(&***b,
                GenericBoundX::Trait(TraitId::Path(p), _) if unemittable.contains(p)))
            .cloned()
            .collect()
    )
}

/// Generic bounds → Lean `[Trait T₁ T₂ …]` instance binders, with any
/// matching `TypEquality` bounds merged in as extra type arguments.
pub(crate) fn trait_bounds_to_ast(bounds: &GenericBounds, unemittable: &std::collections::HashSet<Path>) -> Vec<LBinder> {
    trait_bounds_to_ast_with(bounds, unemittable, |t| typ_to_expr(t))
}

/// For a CONCRETE instance whose trait inherits an out-param `name` from a
/// superclass (`impl Dog for Rex` where `Dog: Animal` and `Animal` has `type
/// Sound`), the value of that out-param: the implementor's sibling
/// superclass-impl assoc of the same name — `Rex`'s `Animal::Sound`. Matched by
/// the implementor Self type (`ti.trait_typ_args[0]`) + assoc name across ALL
/// the krate's assoc-type impls. Forwarding blanket instances never reach here
/// (they fill via the forwarding fresh binder); this is the concrete-Self path
/// where the inherited slot's value is a real type, not a binder. Matched by
/// (Self, name) — the source superclass isn't tracked, unambiguous when an
/// implementor has one assoc of a given name (the common case).
fn find_inherited_assoc<'a>(
    ti: &TraitImplX,
    name: &vir::ast::Ident,
    all_assoc_types: &'a [&AssocTypeImplX],
) -> Option<&'a Typ> {
    use vir::ast_util::types_equal;
    let self_ty = ti.trait_typ_args.first()?;
    all_assoc_types.iter().find_map(|a| {
        let a_self = a.trait_typ_args.first()?;
        (a.name.as_str() == name.as_str() && types_equal(a_self, self_ty))
            .then_some(&a.typ)
    })
}

/// For each emittable trait, the ordered list of associated-type out-param
/// names its Lean `class` carries — its OWN `assoc_typs` followed by those it
/// inherits (unpinned) through its superclass `extends` chain, deduplicated.
///
/// A child trait `extends` a parent whose class has out-params (`FnOnce`'s
/// `Output`); Lean requires every out-param slot of the parent be supplied in
/// the `extends` clause, and (unlike a normal positional arg) it can't be a
/// hole at declaration time — so the child must carry the parent's out-params
/// as its own `outParam` binders and thread them through. This is the
/// transitive closure that makes `Fn`/`FnMut`/`FnOnce` (and any user trait
/// whose superclass has an associated type) elaborate. Memoized; the
/// superclass relation is a DAG, with a visited guard for safety.
/// Shell (un-emittable) superclasses are skipped — their bounds are dropped,
/// so their out-params are never threaded.
pub fn compute_trait_outparams(
    trait_map: &HashMap<Path, &TraitX>,
    unemittable: &std::collections::HashSet<Path>,
) -> HashMap<Path, Vec<vir::ast::Ident>> {
    fn go(
        path: &Path,
        trait_map: &HashMap<Path, &TraitX>,
        unemittable: &std::collections::HashSet<Path>,
        memo: &mut HashMap<Path, Vec<vir::ast::Ident>>,
        on_stack: &mut std::collections::HashSet<Path>,
    ) -> Vec<vir::ast::Ident> {
        if let Some(v) = memo.get(path) { return v.clone(); }
        if !on_stack.insert(path.clone()) { return Vec::new(); } // cycle guard
        let mut out: Vec<vir::ast::Ident> = Vec::new();
        if let Some(tr) = trait_map.get(path) {
            // Own associated types first (declaration order).
            for a in tr.assoc_typs.iter() { out.push(a.clone()); }
            // Then inherited (unpinned) out-params per superclass bound.
            for bound in tr.typ_bounds.iter() {
                if let GenericBoundX::Trait(TraitId::Path(sp), _) = &**bound {
                    if unemittable.contains(sp) { continue; }
                    // Names this trait pins for sp via a TypEquality are
                    // concrete, not inherited as params.
                    let pinned: std::collections::HashSet<&str> = tr.typ_bounds.iter()
                        .filter_map(|b| match &**b {
                            GenericBoundX::TypEquality(ep, _, name, _)
                                if lean_name(ep) == lean_name(sp) => Some(name.as_str()),
                            _ => None,
                        })
                        .collect();
                    for name in go(sp, trait_map, unemittable, memo, on_stack) {
                        if pinned.contains(name.as_str()) { continue; }
                        if !out.iter().any(|n| n.as_str() == name.as_str()) {
                            out.push(name);
                        }
                    }
                }
            }
        }
        on_stack.remove(path);
        memo.insert(path.clone(), out.clone());
        out
    }
    let mut memo = HashMap::new();
    let mut on_stack = std::collections::HashSet::new();
    for path in trait_map.keys() {
        go(path, trait_map, unemittable, &mut memo, &mut on_stack);
    }
    memo
}

/// The `extends P₁, P₂, …` parent list for a trait's class declaration. Each
/// parent is the fully-applied class App with the parent's out-param slots
/// threaded — positional typ-args, then for each out-param of the parent
/// (in declaration order) either the value this trait pins via `TypEquality`,
/// or a reference to this trait's own (inherited) out-param binder of the
/// same name. Shell-trait bounds are dropped (`drop_unemittable_trait_bounds`).
fn class_extends_to_ast(
    bounds: &GenericBounds,
    unemittable: &std::collections::HashSet<Path>,
    trait_outparams: &HashMap<Path, Vec<vir::ast::Ident>>,
) -> Vec<LExpr> {
    let bounds = drop_unemittable_trait_bounds(bounds, unemittable);
    let mut out = Vec::new();
    for bound in bounds.iter() {
        if let GenericBoundX::Trait(TraitId::Path(path), typs) = &**bound {
            let mut args: Vec<LExpr> = typs.iter()
                .map(|t| typ_maybe_projection_to_expr(t)).collect();
            // Fill the parent's out-param slots in declaration order.
            if let Some(parent_outparams) = trait_outparams.get(path) {
                for name in parent_outparams.iter() {
                    // A TypEquality on THIS bound pinning `name` → its value.
                    let pinned = bounds.iter().find_map(|b| match &**b {
                        GenericBoundX::TypEquality(ep, et, n, typ)
                            if lean_name(ep) == lean_name(path)
                                && n.as_str() == name.as_str()
                                && et.len() == typs.len() => Some(typ),
                        _ => None,
                    });
                    args.push(match pinned {
                        Some(typ) => typ_maybe_projection_to_expr(typ),
                        // Inherited: this trait carries an out-param binder of
                        // the same name (added in `trait_to_ast`).
                        None => LExpr::var(crate::lean_name::LeanName::typ_param(name.as_str())),
                    });
                }
            }
            out.push(LExpr::app(
                LExpr::var(crate::lean_name::LeanName::from_path(path)),
                args,
            ));
        }
    }
    out
}

fn trait_bounds_to_ast_with<F>(
    bounds: &GenericBounds,
    unemittable: &std::collections::HashSet<Path>,
    typ_render: F,
) -> Vec<LBinder>
where
    F: Fn(&TypX) -> LExpr,
{
    use vir::ast_util::types_equal;
    // The single chokepoint for bound→binder rendering: drop bounds that
    // reference an un-emittable (shell) trait here, so EVERY bound site
    // — class superclass bounds, instance binders, AND fn-level generic
    // bounds (`fn f<K: Clone>`) — is filtered uniformly. A future caller
    // of this renderer can't forget the filter. See
    // `drop_unemittable_trait_bounds` for the soundness rationale (#122).
    let bounds = drop_unemittable_trait_bounds(bounds, unemittable);
    let bounds = &bounds;
    let mut out = Vec::new();
    for bound in bounds.iter() {
        if let GenericBoundX::Trait(TraitId::Path(path), typs) = &**bound {
            let mut args: Vec<LExpr> = typs.iter().map(|t| typ_render(t)).collect();
            // Append TypEquality typs whose (trait_path, trait_typ_args)
            // match THIS bound. Matching by path alone is too loose when
            // multiple bounds share a trait but differ on typ_args
            // (e.g., `impl<A: View, B: View>` produces two separate
            // bounds, each needing only its own TypEquality entries).
            // Pre-2026-05-19 this matched on path only and 2-typ-param
            // blanket impls produced malformed `[View A V_a V_b]`
            // 3-arg brackets. Pinned by
            // `test_view_blanket_impl_multi_param_probe`.
            for other in bounds.iter() {
                if let GenericBoundX::TypEquality(eq_path, eq_typs, _, typ) = &**other {
                    if lean_name(eq_path) != lean_name(path) { continue; }
                    if typs.len() != eq_typs.len() { continue; }
                    let typs_match = typs.iter().zip(eq_typs.iter())
                        .all(|(a, b)| types_equal(a, b));
                    if !typs_match { continue; }
                    args.push(typ_render(typ));
                }
            }
            let target = LExpr::app(
                LExpr::var(crate::lean_name::LeanName::from_path(path)),
                args,
            );
            out.push(LBinder::instance(target));
        }
    }
    out
}
