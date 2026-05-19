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
///
/// **Invariant** (by construction in [`ImplSubst::build`]): the three
/// fields are populated together for each unique `(X, T, N)` triple
/// discovered in the impl signature. So:
/// - `fresh_binders.len() == fake_bounds.len() == proj_map.len()`.
/// - For each `i`, `fresh_binders[i]` is the binder named in
///   `fake_bounds[i]`'s RHS `TypParam(_)`, and is also a value in
///   `proj_map` for some `(X, T, N)` key.
///
/// The three fields are parallel arrays in this sense; they're kept
/// separate because the consumers have genuinely different access
/// patterns (sequential for binder + bound emission, lookup-by-key
/// for projection rewrite). A fused `Vec<ImplSubstEntry>` would
/// force a re-iteration to build the lookup map. The build-site
/// discipline (one push per push, all in `ImplSubst::build`) keeps
/// the invariant inexpensive to maintain.
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
/// N)`. Only the first trait_typ_arg position is inspected for the
/// (X, T, N) extraction (the projection's "Self" slot); ALL positions
/// (including the first) are still walked recursively for nested
/// projections.
///
/// **Exhaustive match.** Every TypX variant is listed explicitly,
/// including leaves. A new TypX variant added in Verus compile-errors
/// here, forcing categorization (leaf vs composite) — silent miss is
/// a soundness risk because the missed projection wouldn't get a
/// fresh binder and the rendered Lean would be malformed.
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
            }
            for t in trait_typ_args.iter() {
                walk_typ_for_projections(t, visit);
            }
        }
        TypX::Datatype(_, args, _) | TypX::Primitive(_, args) | TypX::FnDef(_, args, _)
        | TypX::Dyn(_, args, _) | TypX::Opaque { args, .. } => {
            for a in args.iter() { walk_typ_for_projections(a, visit); }
        }
        TypX::Boxed(inner) | TypX::MutRef(inner) | TypX::PointeeMetadata(inner) => {
            walk_typ_for_projections(inner, visit);
        }
        TypX::Decorate(_, deco_arg, inner) => {
            walk_typ_for_projections(inner, visit);
            if let Some(da) = deco_arg {
                walk_typ_for_projections(&da.allocator_typ, visit);
            }
        }
        TypX::SpecFn(params, ret) | TypX::AnonymousClosure(params, ret, _, _) => {
            for p in params.iter() { walk_typ_for_projections(p, visit); }
            walk_typ_for_projections(ret, visit);
        }
        // Leaves — no nested Typ to recurse into.
        TypX::Bool | TypX::Int(_) | TypX::Real | TypX::Float(_)
        | TypX::TypParam(_) | TypX::TypeId
        | TypX::ConstInt(_) | TypX::ConstBool(_)
        | TypX::Air(_) => {}
    }
}

/// Recursive TypX → Typ rewriter that replaces matching projections
/// with `TypParam(fresh)`. Structurally identical to `walk_typ_for_
/// projections` but produces a new typ. **Exhaustive match** for the
/// same reason as the walker (see above).
fn rewrite_typ_rec(typ: &Typ, proj_map: &HashMap<(Ident, Path, Ident), Ident>) -> Typ {
    let rewrite_typs = |args: &Typs| -> Typs {
        Arc::new(args.iter().map(|t| rewrite_typ_rec(t, proj_map)).collect())
    };
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
            Arc::new(TypX::Projection {
                trait_typ_args: rewrite_typs(trait_typ_args),
                trait_path: trait_path.clone(),
                name: name.clone(),
            })
        }
        TypX::Datatype(p, args, impls) => {
            Arc::new(TypX::Datatype(p.clone(), rewrite_typs(args), impls.clone()))
        }
        TypX::Primitive(prim, args) => {
            Arc::new(TypX::Primitive(prim.clone(), rewrite_typs(args)))
        }
        TypX::FnDef(fun, args, resolved) => {
            Arc::new(TypX::FnDef(fun.clone(), rewrite_typs(args), resolved.clone()))
        }
        TypX::Dyn(p, args, impls) => {
            Arc::new(TypX::Dyn(p.clone(), rewrite_typs(args), impls.clone()))
        }
        TypX::Opaque { def_path, args } => {
            Arc::new(TypX::Opaque { def_path: def_path.clone(), args: rewrite_typs(args) })
        }
        TypX::Boxed(inner) => Arc::new(TypX::Boxed(rewrite_typ_rec(inner, proj_map))),
        TypX::Decorate(d, deco_arg, inner) => {
            let new_inner = rewrite_typ_rec(inner, proj_map);
            let new_deco_arg = deco_arg.as_ref().map(|da| {
                vir::ast::TypDecorationArg {
                    allocator_typ: rewrite_typ_rec(&da.allocator_typ, proj_map),
                }
            });
            Arc::new(TypX::Decorate(d.clone(), new_deco_arg, new_inner))
        }
        TypX::MutRef(inner) => Arc::new(TypX::MutRef(rewrite_typ_rec(inner, proj_map))),
        TypX::PointeeMetadata(inner) => {
            Arc::new(TypX::PointeeMetadata(rewrite_typ_rec(inner, proj_map)))
        }
        TypX::SpecFn(params, ret) => {
            Arc::new(TypX::SpecFn(rewrite_typs(params), rewrite_typ_rec(ret, proj_map)))
        }
        TypX::AnonymousClosure(params, ret, kind, id) => {
            Arc::new(TypX::AnonymousClosure(
                rewrite_typs(params),
                rewrite_typ_rec(ret, proj_map),
                *kind, *id,
            ))
        }
        // Leaves — no nested Typ to rewrite. Cheap clone (Arc bump).
        TypX::Bool | TypX::Int(_) | TypX::Real | TypX::Float(_)
        | TypX::TypParam(_) | TypX::TypeId
        | TypX::ConstInt(_) | TypX::ConstBool(_)
        | TypX::Air(_) => typ.clone(),
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

#[cfg(test)]
mod tests {
    use super::*;
    use vir::ast::{PathX, TraitId};

    fn mk_ident(s: &str) -> Ident {
        Arc::new(s.to_string())
    }

    fn mk_path(segments: &[&str]) -> Path {
        Arc::new(PathX {
            krate: None,
            segments: Arc::new(segments.iter().map(|s| mk_ident(s)).collect()),
        })
    }

    fn mk_proj(typ_param: &str, trait_segs: &[&str], assoc: &str) -> Typ {
        Arc::new(TypX::Projection {
            trait_typ_args: Arc::new(vec![Arc::new(TypX::TypParam(mk_ident(typ_param)))]),
            trait_path: mk_path(trait_segs),
            name: mk_ident(assoc),
        })
    }

    /// Empty inputs → empty subst (no fresh binders, no rewrites).
    #[test]
    fn build_empty_inputs_returns_empty_subst() {
        let typ_params: Idents = Arc::new(vec![]);
        let typ_bounds: GenericBounds = Arc::new(vec![]);
        let typs: Vec<Typ> = vec![];
        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter());
        assert!(subst.is_empty());
        assert_eq!(subst.fresh_binders.len(), 0);
        assert_eq!(subst.fake_bounds.len(), 0);
        assert_eq!(subst.proj_map.len(), 0);
    }

    /// Walking a typ with no projections → no subst entries even if
    /// the typ contains typ-params and the bounds reference them.
    #[test]
    fn build_skips_non_projection_typs() {
        let typ_params: Idents = Arc::new(vec![mk_ident("A")]);
        let typ_bounds: GenericBounds = Arc::new(vec![
            Arc::new(GenericBoundX::Trait(
                TraitId::Path(mk_path(&["View"])),
                Arc::new(vec![Arc::new(TypX::TypParam(mk_ident("A")))]),
            )),
        ]);
        // typ is just `Datatype(Wrap, [A])` — no projection inside.
        let wrap_a: Typ = Arc::new(TypX::Datatype(
            vir::ast::Dt::Path(mk_path(&["Wrap"])),
            Arc::new(vec![Arc::new(TypX::TypParam(mk_ident("A")))]),
            Arc::new(vec![]),
        ));
        let typs = vec![wrap_a];
        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter());
        assert!(subst.is_empty());
    }

    /// A projection `<A as View>::V` where `A: View` is a bound and
    /// `A` is in typ_params → one fresh binder + one fake bound +
    /// one proj_map entry.
    #[test]
    fn build_lifts_typ_param_projection_to_fresh_binder() {
        let typ_params: Idents = Arc::new(vec![mk_ident("A")]);
        let typ_bounds: GenericBounds = Arc::new(vec![
            Arc::new(GenericBoundX::Trait(
                TraitId::Path(mk_path(&["View"])),
                Arc::new(vec![Arc::new(TypX::TypParam(mk_ident("A")))]),
            )),
        ]);
        let proj = mk_proj("A", &["View"], "V");
        let typs = vec![proj];
        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter());
        assert!(!subst.is_empty());
        assert_eq!(subst.fresh_binders.len(), 1);
        assert_eq!(subst.fake_bounds.len(), 1);
        assert_eq!(subst.proj_map.len(), 1);
        // Invariant check: the three field lengths match.
        let key = (mk_ident("A"), mk_path(&["View"]), mk_ident("V"));
        assert!(subst.proj_map.contains_key(&key));
        let fresh = subst.proj_map.get(&key).unwrap();
        assert_eq!(fresh.as_str(), "_tactus_assoc_A_V");
        assert_eq!(subst.fresh_binders[0].as_str(), "_tactus_assoc_A_V");
    }

    /// Two impl typ-params each with a passthrough → two fresh
    /// binders, distinct.
    #[test]
    fn build_handles_multi_typ_param_passthrough() {
        let typ_params: Idents = Arc::new(vec![mk_ident("A"), mk_ident("B")]);
        let typ_bounds: GenericBounds = Arc::new(vec![
            Arc::new(GenericBoundX::Trait(
                TraitId::Path(mk_path(&["View"])),
                Arc::new(vec![Arc::new(TypX::TypParam(mk_ident("A")))]),
            )),
            Arc::new(GenericBoundX::Trait(
                TraitId::Path(mk_path(&["View"])),
                Arc::new(vec![Arc::new(TypX::TypParam(mk_ident("B")))]),
            )),
        ]);
        let typs = vec![mk_proj("A", &["View"], "V"), mk_proj("B", &["View"], "V")];
        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter());
        assert_eq!(subst.fresh_binders.len(), 2);
        let names: std::collections::HashSet<String> = subst.fresh_binders.iter()
            .map(|i| i.as_str().to_string())
            .collect();
        assert!(names.contains("_tactus_assoc_A_V"));
        assert!(names.contains("_tactus_assoc_B_V"));
    }

    /// Duplicate projections in the typs iter → single subst entry
    /// (dedup by (X, T, N) key).
    #[test]
    fn build_dedupes_repeated_projections() {
        let typ_params: Idents = Arc::new(vec![mk_ident("A")]);
        let typ_bounds: GenericBounds = Arc::new(vec![
            Arc::new(GenericBoundX::Trait(
                TraitId::Path(mk_path(&["View"])),
                Arc::new(vec![Arc::new(TypX::TypParam(mk_ident("A")))]),
            )),
        ]);
        let typs = vec![
            mk_proj("A", &["View"], "V"),
            mk_proj("A", &["View"], "V"),  // duplicate
        ];
        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter());
        assert_eq!(subst.fresh_binders.len(), 1);
        assert_eq!(subst.fake_bounds.len(), 1);
        assert_eq!(subst.proj_map.len(), 1);
    }

    /// Projection on a typ-param NOT in `impl_typ_params` → no
    /// subst entry. (E.g., `<SomeOtherT as View>::V` where
    /// SomeOtherT isn't the impl's parameter — typically can't
    /// arise in practice but the build is defensive.)
    #[test]
    fn build_ignores_projections_of_non_impl_typ_params() {
        let typ_params: Idents = Arc::new(vec![mk_ident("A")]);
        let typ_bounds: GenericBounds = Arc::new(vec![
            Arc::new(GenericBoundX::Trait(
                TraitId::Path(mk_path(&["View"])),
                Arc::new(vec![Arc::new(TypX::TypParam(mk_ident("A")))]),
            )),
        ]);
        // Projection on `B`, but B isn't in impl_typ_params.
        let proj = mk_proj("B", &["View"], "V");
        let typs = vec![proj];
        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter());
        assert!(subst.is_empty());
    }

    /// Projection on a typ-param without a matching trait bound →
    /// no subst entry. (E.g., `<A as View>::V` but bounds only
    /// have `A: OtherTrait`.)
    #[test]
    fn build_ignores_projections_without_matching_bound() {
        let typ_params: Idents = Arc::new(vec![mk_ident("A")]);
        let typ_bounds: GenericBounds = Arc::new(vec![
            // `A: OtherTrait`, not `A: View`.
            Arc::new(GenericBoundX::Trait(
                TraitId::Path(mk_path(&["OtherTrait"])),
                Arc::new(vec![Arc::new(TypX::TypParam(mk_ident("A")))]),
            )),
        ]);
        let proj = mk_proj("A", &["View"], "V");
        let typs = vec![proj];
        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter());
        assert!(subst.is_empty());
    }

    /// `rewrite_typ` on a typ with no matching projections returns
    /// a structurally-identical typ (modulo Arc bumps).
    #[test]
    fn rewrite_typ_identity_for_non_matching() {
        let subst = ImplSubst::default();
        let typ: Typ = Arc::new(TypX::Datatype(
            vir::ast::Dt::Path(mk_path(&["Wrap"])),
            Arc::new(vec![Arc::new(TypX::TypParam(mk_ident("A")))]),
            Arc::new(vec![]),
        ));
        let rewritten = subst.rewrite_typ(&typ);
        assert!(vir::ast_util::types_equal(&typ, &rewritten));
    }

    /// `rewrite_typ` replaces a matching `Projection` with the
    /// fresh `TypParam`.
    #[test]
    fn rewrite_typ_replaces_matching_projection() {
        let mut proj_map = HashMap::new();
        proj_map.insert(
            (mk_ident("A"), mk_path(&["View"]), mk_ident("V")),
            mk_ident("_tactus_assoc_A_V"),
        );
        let subst = ImplSubst {
            fresh_binders: vec![mk_ident("_tactus_assoc_A_V")],
            fake_bounds: vec![],
            proj_map,
        };
        let proj = mk_proj("A", &["View"], "V");
        let rewritten = subst.rewrite_typ(&proj);
        match &*rewritten {
            TypX::TypParam(name) => assert_eq!(name.as_str(), "_tactus_assoc_A_V"),
            other => panic!("expected TypParam, got {:?}", other),
        }
    }

    /// `rewrite_typ` walks INTO composite typs, replacing nested
    /// projections.
    #[test]
    fn rewrite_typ_walks_into_datatype_args() {
        let mut proj_map = HashMap::new();
        proj_map.insert(
            (mk_ident("A"), mk_path(&["View"]), mk_ident("V")),
            mk_ident("V_a"),
        );
        let subst = ImplSubst {
            fresh_binders: vec![mk_ident("V_a")],
            fake_bounds: vec![],
            proj_map,
        };
        // `Datatype(Wrap, [Projection<A as View>::V])`.
        let typ: Typ = Arc::new(TypX::Datatype(
            vir::ast::Dt::Path(mk_path(&["Wrap"])),
            Arc::new(vec![mk_proj("A", &["View"], "V")]),
            Arc::new(vec![]),
        ));
        let rewritten = subst.rewrite_typ(&typ);
        match &*rewritten {
            TypX::Datatype(_, args, _) => {
                assert_eq!(args.len(), 1);
                match &*args[0] {
                    TypX::TypParam(name) => assert_eq!(name.as_str(), "V_a"),
                    other => panic!("expected nested TypParam(V_a), got {:?}", other),
                }
            }
            other => panic!("expected Datatype, got {:?}", other),
        }
    }
}
