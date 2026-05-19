//! Per-impl projection-to-binder substitution (Bug B step 2).
//!
//! ## The problem
//!
//! Blanket impls express associated-type passthrough via projections:
//!
//! ```rust
//! impl<A: View> View for Wrap<A> {
//!     type V = A::V;
//!     spec fn view(&self) -> A::V { ... }
//! }
//! ```
//!
//! `<A as View>::V` appears in the impl method's return type, in the
//! `assoc_type_impl`'s value, and in the instance's positional V slot.
//! Tactus emits the `View` trait class with V as an `outParam`, so V
//! is *bound by* the instance, not *projected from* it. `View.V A` as
//! an accessor is malformed under outParam encoding (the renderer
//! produces this syntax in [`typ_to_expr`]'s Projection arm, but `V`
//! is a type-class index, not a field).
//!
//! ## The fix
//!
//! Introduce a fresh implicit binder `_tactus_assoc_<X>_<N>` for each
//! `<X as T>::N` projection that appears in the impl's signature, where
//! X is one of the impl's typ_params and T is a trait bound on X.
//! Augment the trait bound from `[T X]` to `[T X _tactus_assoc_X_N]`,
//! and rewrite the projection to `TypParam(_tactus_assoc_X_N)`.
//!
//! Augmented Lean:
//! ```text
//! noncomputable def impl__0.view (A : Type) {_tactus_assoc_A_V : Type}
//!   [View A _tactus_assoc_A_V] (self : Wrap A) : _tactus_assoc_A_V
//!   := View.view self.val0
//!
//! noncomputable instance {A : Type} {_tactus_assoc_A_V : Type}
//!   [View A _tactus_assoc_A_V] : View (Wrap A) _tactus_assoc_A_V where
//!   view := fun self => View.view self.val0
//! ```
//!
//! The augmented `[View A _tactus_assoc_A_V]` bracket lets Lean's
//! instance search bind `_tactus_assoc_A_V` to whatever `A::V` resolves
//! to, by outParam — the same mechanism every other instance uses.
//!
//! ## "Fake TypEquality bound" — reusing existing machinery
//!
//! Instead of teaching `trait_bounds_to_ast` about the substitution
//! directly, we synthesise a `GenericBoundX::TypEquality(T, [X], N,
//! TypParam(fresh))` bound and prepend it to the impl's typ_bounds.
//! `trait_bounds_to_ast` *already* iterates bounds looking for matching
//! TypEquality entries and appending their typs to the rendered trait
//! arg list — that's the existing mechanism for `where A::V = SomeType`
//! constraints. The synthesised bound piggybacks on it: the fresh-
//! binder TypParam flows through the same path as any user-written
//! equality, with no new code in the bound renderer.
//!
//! ## Scope of the rewrite
//!
//! - **Instance emission** ([`trait_impl_to_ast`]): rewrite
//!   `ti.trait_typ_args` and `assoc_types[i].typ` before they reach
//!   `typ_to_expr`. Extend instance binders with subst.fresh_binders.
//!   Prepend subst.fake_bounds to `ti.typ_bounds` for the bound render.
//! - **Impl method standalone def** ([`augment_function`]): same surface
//!   — extend `f.typ_params`, prepend to `f.typ_bounds`, rewrite
//!   `f.ret.x.typ` and `f.params[i].x.typ`. The augmented FunctionX is
//!   passed unchanged to `spec_fn_to_ast`.
//!
//! Bodies are NOT walked. The body of `view` is `self.0.view()` which
//! renders to `View.view self.val0` — no projection in the rendered
//! Lean (the call's result type is inferred via class dispatch from
//! `[View A _tactus_assoc_A_V]`, no explicit annotation needed). The
//! signature-only scope keeps the rewrite localised and avoids invasive
//! changes to vir_expr_to_ast.

use std::collections::HashMap;
use std::sync::Arc;

use vir::ast::{
    GenericBound, GenericBoundX, Ident, Idents, GenericBounds, FunctionKind, FunctionX,
    Param, ParamX, Params, Path, TraitId, Typ, TypX, Typs,
};
use vir::def::Spanned;

/// Per-impl substitution: fresh binders + fake bounds + projection
/// rewrite map. Built once per impl_path from the impl's signature
/// typs; consumed by `trait_impl_to_ast` (instance side) and
/// `augment_function` (impl method standalone side).
#[derive(Debug, Clone, Default)]
pub struct ImplSubst {
    /// Fresh implicit type binders to inject into the impl's typ_params.
    /// E.g., `["_tactus_assoc_A_V"]` for `impl<A: View>` where
    /// `<A as View>::V` appears in the signature.
    pub fresh_binders: Vec<Ident>,
    /// Synthesised `TypEquality` bounds that augment the impl's
    /// trait bounds. Order parallels `fresh_binders`. `trait_bounds_
    /// to_ast` will pick these up alongside the impl's real bounds.
    pub fake_bounds: Vec<GenericBound>,
    /// `(X, T, N) -> fresh_binder_name` for projections like
    /// `<X as T>::N`. Used by `rewrite_typ` to replace each
    /// matching `Projection` with `TypParam(fresh)`.
    pub proj_map: HashMap<(Ident, Path, Ident), Ident>,
}

impl ImplSubst {
    pub fn is_empty(&self) -> bool {
        self.fresh_binders.is_empty()
    }

    /// Build the subst by walking `typs` for projections of the form
    /// `<X as T>::N` where X is in `impl_typ_params` and there's a
    /// `Trait(T, [X, ...])` bound in `impl_typ_bounds`.
    pub fn build<'a>(
        impl_typ_params: &Idents,
        impl_typ_bounds: &GenericBounds,
        typs: impl Iterator<Item = &'a Typ>,
    ) -> Self {
        let impl_params: std::collections::HashSet<&Ident> =
            impl_typ_params.iter().collect();
        // Map each typ-param X to the set of trait paths T such that
        // there's a `Trait(T, [X, ...])` bound. Used to validate that
        // a discovered projection's (X, T) pair has a matching bound.
        let mut param_to_traits: HashMap<&Ident, Vec<&Path>> = HashMap::new();
        for bound in impl_typ_bounds.iter() {
            if let GenericBoundX::Trait(TraitId::Path(p), bound_typs) = &**bound {
                for bt in bound_typs.iter() {
                    if let TypX::TypParam(x) = &**bt {
                        if impl_params.contains(x) {
                            param_to_traits.entry(x).or_default().push(p);
                        }
                    }
                }
            }
        }

        let mut subst = ImplSubst::default();
        let mut seen: HashMap<(Ident, Path, Ident), ()> = HashMap::new();
        for typ in typs {
            walk_typ_for_projections(typ, &mut |x, trait_path, assoc_name| {
                if !impl_params.contains(&x) { return; }
                if !param_to_traits.get(&x)
                    .map(|ts| ts.iter().any(|p| **p == *trait_path))
                    .unwrap_or(false)
                {
                    return;
                }
                let key = (x.clone(), trait_path.clone(), assoc_name.clone());
                if seen.contains_key(&key) { return; }
                seen.insert(key.clone(), ());

                let fresh: Ident = Arc::new(format!(
                    "_tactus_assoc_{}_{}", x.as_str(), assoc_name.as_str()
                ));
                subst.fresh_binders.push(fresh.clone());

                let bound_typs: Typs = Arc::new(vec![
                    Arc::new(TypX::TypParam(x.clone())),
                ]);
                let target_typ: Typ = Arc::new(TypX::TypParam(fresh.clone()));
                let fake_bound: GenericBound = Arc::new(GenericBoundX::TypEquality(
                    trait_path.clone(),
                    bound_typs,
                    assoc_name.clone(),
                    target_typ,
                ));
                subst.fake_bounds.push(fake_bound);

                subst.proj_map.insert(key, fresh);
            });
        }
        subst
    }

    /// Rewrite each `<X as T>::N` projection in `typ` to `TypParam(fresh)`
    /// when `(X, T, N)` is in `proj_map`. Other projections pass through
    /// unchanged.
    pub fn rewrite_typ(&self, typ: &Typ) -> Typ {
        rewrite_typ_rec(typ, &self.proj_map)
    }

    /// Clone `f` with extended typ_params (originals + fresh binders),
    /// extended typ_bounds (originals + fake bounds), and rewritten
    /// param/return typs. Body is left alone — see module docs for
    /// the signature-only scope rationale.
    pub fn augment_function(&self, f: &FunctionX) -> FunctionX {
        let mut typ_params: Vec<Ident> = (*f.typ_params).iter().cloned().collect();
        typ_params.extend(self.fresh_binders.iter().cloned());

        let mut typ_bounds: Vec<GenericBound> = (*f.typ_bounds).iter().cloned().collect();
        typ_bounds.extend(self.fake_bounds.iter().cloned());

        let ret = {
            let new_typ = self.rewrite_typ(&f.ret.x.typ);
            let new_x = ParamX { typ: new_typ, ..f.ret.x.clone() };
            Spanned::new(f.ret.span.clone(), new_x)
        };

        let params: Vec<Param> = f.params.iter().map(|p| {
            let new_typ = self.rewrite_typ(&p.x.typ);
            let new_x = ParamX { typ: new_typ, ..p.x.clone() };
            Spanned::new(p.span.clone(), new_x)
        }).collect();

        FunctionX {
            typ_params: Arc::new(typ_params),
            typ_bounds: Arc::new(typ_bounds),
            ret,
            params: Arc::new(params) as Params,
            ..f.clone()
        }
    }
}

/// Visit `typ` looking for `Projection { trait_typ_args: [TypParam(X),
/// ...], trait_path: T, name: N }`. For each match, call `visit(X, T,
/// N)`. Only the first trait_typ_arg position is inspected (the
/// projection's "Self" slot); other positions are walked recursively
/// for nested projections.
fn walk_typ_for_projections<'a>(
    typ: &'a Typ,
    visit: &mut impl FnMut(Ident, &'a Path, Ident),
) {
    match &**typ {
        TypX::Projection { trait_typ_args, trait_path, name } => {
            if let Some(first) = trait_typ_args.first() {
                if let TypX::TypParam(x) = &**first {
                    visit(x.clone(), trait_path, name.clone());
                }
                walk_typ_for_projections(first, visit);
            }
            for t in trait_typ_args.iter().skip(1) {
                walk_typ_for_projections(t, visit);
            }
        }
        TypX::Datatype(_, args, _) | TypX::Primitive(_, args) | TypX::FnDef(_, args, _)
        | TypX::Dyn(_, args, _) | TypX::Opaque { args, .. } => {
            for a in args.iter() { walk_typ_for_projections(a, visit); }
        }
        TypX::Boxed(inner) | TypX::Decorate(_, _, inner) | TypX::MutRef(inner) => {
            walk_typ_for_projections(inner, visit);
        }
        TypX::SpecFn(params, ret) | TypX::AnonymousClosure(params, ret, _, _) => {
            for p in params.iter() { walk_typ_for_projections(p, visit); }
            walk_typ_for_projections(ret, visit);
        }
        // Leaves and decoration-less variants — nothing to recurse into.
        _ => {}
    }
}

/// Recursive TypX → Typ rewriter that replaces matching projections
/// with `TypParam(fresh)`. Structurally identical to `walk_typ_for_
/// projections` but produces a new typ.
fn rewrite_typ_rec(typ: &Typ, proj_map: &HashMap<(Ident, Path, Ident), Ident>) -> Typ {
    match &**typ {
        TypX::Projection { trait_typ_args, trait_path, name } => {
            if let Some(first) = trait_typ_args.first() {
                if let TypX::TypParam(x) = &**first {
                    let key = (x.clone(), trait_path.clone(), name.clone());
                    if let Some(fresh) = proj_map.get(&key) {
                        return Arc::new(TypX::TypParam(fresh.clone()));
                    }
                }
            }
            // Non-matching projection: still recurse into args.
            let new_args: Typs = Arc::new(
                trait_typ_args.iter().map(|t| rewrite_typ_rec(t, proj_map)).collect()
            );
            Arc::new(TypX::Projection {
                trait_typ_args: new_args,
                trait_path: trait_path.clone(),
                name: name.clone(),
            })
        }
        TypX::Datatype(p, args, impls) => {
            let new_args: Typs = Arc::new(
                args.iter().map(|t| rewrite_typ_rec(t, proj_map)).collect()
            );
            Arc::new(TypX::Datatype(p.clone(), new_args, impls.clone()))
        }
        TypX::Primitive(prim, args) => {
            let new_args: Typs = Arc::new(
                args.iter().map(|t| rewrite_typ_rec(t, proj_map)).collect()
            );
            Arc::new(TypX::Primitive(prim.clone(), new_args))
        }
        TypX::Boxed(inner) => Arc::new(TypX::Boxed(rewrite_typ_rec(inner, proj_map))),
        TypX::Decorate(d, a, inner) => {
            Arc::new(TypX::Decorate(d.clone(), a.clone(), rewrite_typ_rec(inner, proj_map)))
        }
        TypX::MutRef(inner) => Arc::new(TypX::MutRef(rewrite_typ_rec(inner, proj_map))),
        TypX::SpecFn(params, ret) => {
            let new_params: Typs = Arc::new(
                params.iter().map(|t| rewrite_typ_rec(t, proj_map)).collect()
            );
            Arc::new(TypX::SpecFn(new_params, rewrite_typ_rec(ret, proj_map)))
        }
        // Variants without nested typs — clone-through.
        _ => typ.clone(),
    }
}

/// If `f` is a TraitMethodImpl, look up its impl_path in `impl_substs`
/// and return the augmented FunctionX. Otherwise return `f` unchanged
/// (as an owned clone, since the caller needs ownership).
pub fn maybe_augment_impl_method(
    f: &FunctionX,
    impl_substs: &HashMap<Path, ImplSubst>,
) -> FunctionX {
    if let FunctionKind::TraitMethodImpl { impl_path, .. } = &f.kind {
        if let Some(subst) = impl_substs.get(impl_path) {
            if !subst.is_empty() {
                return subst.augment_function(f);
            }
        }
    }
    f.clone()
}
