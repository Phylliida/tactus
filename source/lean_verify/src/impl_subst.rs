//! Per-impl projection-to-binder substitution (Bug B step 2).
//!
//! ## The problem
//!
//! Blanket impls express associated-type passthrough via projections:
//!
//! ```text
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
    CallTarget, CallTargetKind, Expr, ExprX, Exprs, Fun, FunX, GenericBound, GenericBoundX, Ident, Idents,
    GenericBounds, FunctionKind, FunctionX, Param, ParamX, Params, Path, PathX, SpannedTyped, TraitId,
    TraitImplX, TraitX, Typ, TypX, Typs,
};
use vir::def::Spanned;

/// Prefix for the synthetic associated-type binders `fresh_binder_name`
/// produces (`_tactus_assoc_<X>_<Trait>_<N>`). Each is constrained via
/// its trait's outParam instance bracket (`[Trait X _tactus_assoc_X_Trait_N]`),
/// so Lean infers it at use sites — these binders MUST render as
/// **implicit**, not explicit. Otherwise VIR-rendered call sites (which
/// pass only the original typ_args, knowing nothing of the synthetic
/// params) fail with an arity mismatch. Centralised here so the binder
/// renderer (`to_lean_fn::fn_binders`) and the generator agree on the
/// convention rather than duplicating the magic prefix.
pub const ASSOC_BINDER_PREFIX: &str = "_tactus_assoc_";

/// True iff `name` is a synthetic associated-type binder (see
/// [`ASSOC_BINDER_PREFIX`]) — i.e. should render as an implicit binder.
pub fn is_assoc_binder(name: &str) -> bool {
    name.starts_with(ASSOC_BINDER_PREFIX)
}

fn fresh_binder_name(x: &Ident, trait_path: &Path, assoc: &Ident) -> Ident {
    // Trait short name is the last segment of `trait_path`. Including
    // it disambiguates `_tactus_assoc_A_V` when the same X is bounded
    // by two traits that each have an assoc named `V` (e.g.,
    // `impl<A: View + DeepView>` where both traits have `type V`).
    let trait_short = trait_path.segments.last()
        .map(|s| s.as_str()).unwrap_or("_");
    Arc::new(format!(
        "{}{}_{}_{}", ASSOC_BINDER_PREFIX, x.as_str(), trait_short, assoc.as_str()
    ))
}

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
    /// Context for the body's self-sibling-call rewrite. Populated
    /// by `set_method_context`; consumed by `augment_function`'s
    /// body rewrite path. Pre-2026-05-19 (when `rewrite_self_
    /// sibling_calls` lived only in `trait_impl_to_ast`) the
    /// standalone def's body was rendered with class dispatch
    /// (`Trait.method self`), which forward-referenced the
    /// instance and failed to elaborate. Now the rewrite fires on
    /// the body too.
    pub method_context: Option<MethodContext>,
}

/// Per-impl context for the body's self-sibling-call rewrite.
/// Captured once per impl in `set_method_context` and consumed by
/// `augment_function`'s body rewrite. `trait_path` and `impl_self_typ`
/// gate the rewrite (only fires when the call's receiver structurally
/// matches Self); `method_redirects` provides the impl method `Fun`
/// to swap into the call target.
///
/// **Renaming**: if `name_prefix` is `Some("Bar.Counter")`, then
/// `augment_function` rewrites the standalone def's `f.name` from
/// `[impl%0, method]` to `[Bar, Counter, method]`. `method_redirects`
/// values are also pre-renamed so sibling-call rewrites refer to the
/// natural name. If `None`, the impl method keeps its original
/// `impl__N.method` path (e.g., collision case — multiple impls
/// would produce the same natural name).
#[derive(Debug, Clone)]
pub struct MethodContext {
    pub trait_path: Path,
    pub impl_self_typ: Typ,
    pub method_redirects: HashMap<String, Fun>,
    pub name_prefix: Option<Vec<Ident>>,
}

/// Given an impl method's Fun and the per-impl name prefix
/// (e.g., `[Bar, Counter]`), construct a renamed Fun with path
/// `[Bar, Counter, method_short_name]`. Krate is preserved.
fn rename_impl_method_fun(f: &Fun, prefix: &[Ident]) -> Fun {
    let method_short = f.path.segments.last()
        .cloned()
        .unwrap_or_else(|| Arc::new("_".to_string()));
    let mut segments: Vec<Ident> = prefix.to_vec();
    segments.push(method_short);
    Arc::new(FunX {
        path: Arc::new(PathX {
            krate: f.path.krate.clone(),
            segments: Arc::new(segments),
        }),
    })
}

impl ImplSubst {
    pub fn is_empty(&self) -> bool {
        self.fresh_binders.is_empty() && self.method_context.is_none()
    }

    /// Attach impl-method context (trait_path, Self typ, method
    /// redirects, optional rename prefix) so `augment_function` can
    /// rewrite self-sibling calls in the body AND rename the
    /// standalone def's path.
    ///
    /// `name_prefix`: if `Some([Bar, Counter])`, impl method standalones
    /// are renamed from `impl%N.method` to `Bar.Counter.method`.
    /// `method_redirects`' values are pre-renamed to match. If `None`,
    /// the impl method keeps its synthetic `impl__N.method` path
    /// (collision fallback — multiple impls would produce the same
    /// natural name).
    pub fn set_method_context(
        &mut self,
        ti: &TraitImplX,
        method_impls: &[&FunctionX],
        name_prefix: Option<Vec<Ident>>,
    ) {
        let Some(self_typ) = ti.trait_typ_args.first() else { return; };
        let method_redirects: HashMap<String, Fun> = method_impls.iter()
            .filter_map(|f| {
                let short = f.name.path.segments.last().map(|s| s.to_string())?;
                let target_fun = match &name_prefix {
                    Some(prefix) => rename_impl_method_fun(&f.name, prefix),
                    None => f.name.clone(),
                };
                Some((short, target_fun))
            })
            .collect();
        self.method_context = Some(MethodContext {
            trait_path: ti.trait_path.clone(),
            impl_self_typ: self_typ.clone(),
            method_redirects,
            name_prefix,
        });
    }

    /// Build the subst from the impl's signature.
    ///
    /// Two sources of fresh binders:
    /// 1. **Projections in the signature** (typs iter). For each
    ///    `<X as T>::N` where X is in `impl_typ_params` and there's
    ///    a matching `Trait(T, [X])` bound, allocate a fresh binder
    ///    and a `TypEquality(T, [X], N, TypParam(fresh))` bound. The
    ///    `proj_map` records the projection→fresh mapping for typ
    ///    rewriting.
    /// 2. **Uncovered assoc-type slots on bound traits** (audit fix,
    ///    2026-05-19). For each `Trait(T, [X])` bound where X is in
    ///    `impl_typ_params`, enumerate T's `assoc_typs` (consulting
    ///    `traits`). For each assoc that wasn't already covered by a
    ///    projection in (1), allocate a fresh binder anyway. This
    ///    fills the bound's outParam slots so the rendered bracket
    ///    `[T X V_n …]` has the right arity for the class —
    ///    otherwise `impl<A: View + DeepView>` (where only View's V
    ///    is referenced) generates a malformed `[DeepView A]`
    ///    1-arg bracket on a 2-arg class.
    ///
    /// The fresh binder from (2) is "unused" in the strict sense
    /// (no projection rewrites to it), but Lean's outParam inference
    /// will compute its value from instance lookup at use sites, so
    /// the resulting Lean is well-formed.
    pub fn build<'a>(
        impl_typ_params: &Idents,
        impl_typ_bounds: &GenericBounds,
        typs: impl Iterator<Item = &'a Typ>,
        traits: &HashMap<Path, &TraitX>,
    ) -> Self {
        let impl_params: std::collections::HashSet<&Ident> =
            impl_typ_params.iter().collect();
        // Map each typ-param X to the bounds `Trait(T, full_typs)`
        // where X appears in full_typs. We store the full bound
        // (not just the path) so we can later synthesise fake
        // `TypEquality(T, full_typs, ...)` bounds whose `typs` match
        // the original Trait bound's `typs` — required by
        // `trait_bounds_to_ast_with`'s `typs_match` filter (which
        // pairs each Trait bound with its matching TypEquality
        // entries by both path AND typ-args). For multi-arg traits
        // (e.g., `Converter<u8>` whose bound has typs `[A, u8]`),
        // the fake's `[A]` typs would otherwise not match the
        // original's `[A, u8]` typs and the fresh binder wouldn't
        // appear in the rendered bracket.
        let mut param_to_bounds: HashMap<&Ident, Vec<(&Path, &Typs)>> = HashMap::new();
        for bound in impl_typ_bounds.iter() {
            if let GenericBoundX::Trait(TraitId::Path(p), bound_typs) = &**bound {
                for bt in bound_typs.iter() {
                    if let TypX::TypParam(x) = &**bt {
                        if impl_params.contains(x) {
                            param_to_bounds.entry(x).or_default().push((p, bound_typs));
                        }
                    }
                }
            }
        }

        let mut subst = ImplSubst::default();
        let mut add_entry = |x: Ident, trait_path: Path, assoc_name: Ident,
                             full_bound_typs: Typs, subst: &mut ImplSubst| {
            let key = (x.clone(), trait_path.clone(), assoc_name.clone());
            if subst.proj_map.contains_key(&key) { return; }
            let fresh = fresh_binder_name(&x, &trait_path, &assoc_name);
            subst.fresh_binders.push(fresh.clone());
            let target_typ: Typ = Arc::new(TypX::TypParam(fresh.clone()));
            let fake_bound: GenericBound = Arc::new(GenericBoundX::TypEquality(
                trait_path.clone(),
                full_bound_typs,
                assoc_name.clone(),
                target_typ,
            ));
            subst.fake_bounds.push(fake_bound);
            subst.proj_map.insert(key, fresh);
        };

        // Source 1: projections in the signature.
        for typ in typs {
            walk_typ_for_projections(typ, &mut |x, trait_path, assoc_name| {
                if !impl_params.contains(&x) { return; }
                // Find a bound `Trait(trait_path, full_typs)` whose
                // typs include this X. The bound's full typs are
                // what we record in the fake TypEquality.
                let bound_typs = param_to_bounds.get(&x).and_then(|bs| {
                    bs.iter().find(|(p, _)| **p == *trait_path).map(|(_, ts)| (*ts).clone())
                });
                let Some(bound_typs) = bound_typs else { return; };
                add_entry(x, trait_path.clone(), assoc_name, bound_typs, &mut subst);
            });
        }

        // Source 2: uncovered assoc-type slots on bound traits. "Uncovered"
        // is load-bearing: a slot already constrained by an existing
        // `TypEquality(T, [X, …], N, _)` bound MUST be skipped, or we
        // synthesise a SECOND fresh binder for the same `<X as T>::N` and
        // `trait_bounds_to_ast` appends both → an over-arity bracket
        // (`View Q _ta1 _ta2` for a 2-param class). Surfaced by
        // `axiom_hashmap_deepview_borrow`, whose `View Q` bound pairs with a
        // separate `TypEquality(View, [Q], V, <K as DeepView>::V)` already
        // pinning V. Match by (trait path, the X in slot 0, assoc name).
        let assoc_already_constrained = |p: &Path, x: &Ident, assoc: &Ident| -> bool {
            impl_typ_bounds.iter().any(|b| match &**b {
                GenericBoundX::TypEquality(tp, ts, n, _) => {
                    **tp == **p
                        && **n == **assoc
                        && ts.first().map_or(false, |t| {
                            matches!(&**t, TypX::TypParam(tx) if **tx == **x)
                        })
                }
                _ => false,
            })
        };
        for bound in impl_typ_bounds.iter() {
            if let GenericBoundX::Trait(TraitId::Path(p), bound_typs) = &**bound {
                let Some(tr) = traits.get(p) else { continue; };
                for bt in bound_typs.iter() {
                    if let TypX::TypParam(x) = &**bt {
                        if !impl_params.contains(x) { continue; }
                        for assoc_name in tr.assoc_typs.iter() {
                            if assoc_already_constrained(p, x, assoc_name) { continue; }
                            add_entry(x.clone(), p.clone(), assoc_name.clone(),
                                      bound_typs.clone(), &mut subst);
                        }
                    }
                }
            }
        }

        subst
    }

    /// Rewrite each `<X as T>::N` projection in `typ` to `TypParam(fresh)`
    /// when `(X, T, N)` is in `proj_map`. Other projections pass through
    /// unchanged.
    pub fn rewrite_typ(&self, typ: &Typ) -> Typ {
        rewrite_typ_rec(typ, &self.proj_map)
    }

    /// Rewrite projections embedded in the typs of a single generic bound.
    /// A bound can carry a projection as a trait type-arg — e.g. the
    /// `axiom_hashmap_deepview_borrow` lemma's `[View Q <K as DeepView>::V]`
    /// — which must lift to the fresh binder alongside the signature/body/
    /// clause projections. Identity when `proj_map` is empty.
    fn rewrite_bound(&self, bound: &GenericBound) -> GenericBound {
        let gbx = match &**bound {
            GenericBoundX::Trait(path, typs) => GenericBoundX::Trait(
                path.clone(),
                Arc::new(typs.iter().map(|t| self.rewrite_typ(t)).collect()),
            ),
            GenericBoundX::TypEquality(path, typs, name, typ) => GenericBoundX::TypEquality(
                path.clone(),
                Arc::new(typs.iter().map(|t| self.rewrite_typ(t)).collect()),
                name.clone(),
                self.rewrite_typ(typ),
            ),
            GenericBoundX::ConstTyp(t1, t2) => {
                GenericBoundX::ConstTyp(self.rewrite_typ(t1), self.rewrite_typ(t2))
            }
        };
        Arc::new(gbx)
    }

    /// Clone `f` with extended typ_params (originals + fresh binders),
    /// extended typ_bounds (originals + fake bounds), and rewritten
    /// param/return typs. If `method_context` is set, the body is
    /// also rewritten: self-sibling `Trait.method(self_arg)` calls
    /// become direct calls to `impl__N.method(self_arg)`. This
    /// matters for the standalone def's body, which the OLD
    /// strip_class_qualifier (and step 1's `rewrite_self_sibling_
    /// calls` in `trait_impl_to_ast`) couldn't reach — the
    /// standalone is emitted before the instance, so any class
    /// dispatch in its body forward-references the instance and
    /// fails to elaborate.
    pub fn augment_function(&self, f: &FunctionX) -> FunctionX {
        let mut typ_params: Vec<Ident> = (*f.typ_params).iter().cloned().collect();
        typ_params.extend(self.fresh_binders.iter().cloned());

        // Rewrite projections in the EXISTING bounds (a bound may carry a
        // projection as a trait type-arg, e.g. `[View Q <K as DeepView>::V]`),
        // then append the synthesised fake TypEquality bounds (already in
        // terms of the fresh binders, so not re-rewritten).
        let mut typ_bounds: Vec<GenericBound> =
            f.typ_bounds.iter().map(|b| self.rewrite_bound(b)).collect();
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

        // Step 1: self-sibling call rewrite (method_context impls only).
        let sibling_rewritten = match (&f.body, &self.method_context) {
            (Some(body), Some(ctx)) => Some(rewrite_self_sibling_calls(
                body,
                &ctx.trait_path,
                &ctx.impl_self_typ,
                &ctx.method_redirects,
            )),
            _ => f.body.clone(),
        };
        // Step 2: lift assoc-type projections embedded in the BODY's typs
        // (lambda binder annotations, call/ctor type-args, …) to the same
        // fresh binders the signature rewrite uses. The param/ret rewrite
        // above is signature-only; a standalone generic spec fn like
        // `hash_map_deep_view_impl` also carries `<X as Trait>::N`
        // projections in its body (`fun (k : DeepView.V Key) => …`,
        // `Map.new (DeepView.V Key) …`), which would otherwise render as
        // the malformed `view.DeepView.V Key` accessor. No-op when there
        // are no projections (proj_map empty → every existing fn body is
        // returned unchanged). The rewrite is infallible (rewrite_typ_rec
        // is total over TypX).
        let body = match sibling_rewritten {
            Some(b) if !self.proj_map.is_empty() => Some(
                vir::ast_visitor::map_expr_typ_visitor(&b, &|t| {
                    Ok(rewrite_typ_rec(t, &self.proj_map))
                })
                .expect("map_expr_typ_visitor: projection rewrite is total"),
            ),
            other => other,
        };

        // Step 3: lift assoc-type projections in the SPEC CLAUSES (require /
        // ensure / returns). A function's facts that flow to call sites and
        // theorem goals live here, not in params/ret/body — most visibly a
        // cross-crate broadcast lemma like `axiom_hashmap_deepview_borrow`,
        // whose ensure projects `<K as DeepView>::V` (e.g. `contains_key
        // (DeepView.V K) …`) but whose params/ret carry no projection. No-op
        // when proj_map is empty (every existing fn's clauses unchanged).
        let (require, ensure, returns) = if self.proj_map.is_empty() {
            (f.require.clone(), f.ensure.clone(), f.returns.clone())
        } else {
            let rw = |e: &Expr| -> Expr {
                vir::ast_visitor::map_expr_typ_visitor(e, &|t| {
                    Ok(rewrite_typ_rec(t, &self.proj_map))
                })
                .expect("map_expr_typ_visitor: projection rewrite is total")
            };
            let require: Exprs = Arc::new(f.require.iter().map(|e| rw(e)).collect());
            let ensure: (Exprs, Exprs) = (
                Arc::new(f.ensure.0.iter().map(|e| rw(e)).collect()),
                Arc::new(f.ensure.1.iter().map(|e| rw(e)).collect()),
            );
            let returns = f.returns.as_ref().map(|e| rw(e));
            (require, ensure, returns)
        };

        // Rename the function's `name` when the impl-method natural
        // name prefix is set. The renamed `Fun` is consistent with
        // sibling-call references in the body (which use
        // `method_redirects`' pre-renamed Funs). See `MethodContext`
        // docs for the collision-fallback rationale.
        let name = match &self.method_context {
            Some(ctx) if ctx.name_prefix.is_some() => {
                rename_impl_method_fun(&f.name, ctx.name_prefix.as_ref().unwrap())
            }
            _ => f.name.clone(),
        };

        FunctionX {
            name,
            typ_params: Arc::new(typ_params),
            typ_bounds: Arc::new(typ_bounds),
            ret,
            params: Arc::new(params) as Params,
            require,
            ensure,
            returns,
            body,
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

/// VIR-level rewrite of self-sibling trait method calls in an impl
/// method body. Replaces `Trait::method(self_arg, ...)` with a direct
/// call to the impl's `impl__N.method` standalone def — but ONLY
/// when the call's first arg type structurally matches the impl's
/// Self type. For blanket impls where `Trait::method` is called on a
/// typ-param (a different instance), the rewrite is skipped and the
/// call stays as class dispatch (Lean resolves through the
/// `[Trait A]` bracket in scope).
///
/// Applied at two sites:
/// 1. Standalone def body (via `augment_function`'s body field). The
///    standalone def is emitted BEFORE its instance, so any class
///    dispatch in its body forward-references the instance and
///    fails to elaborate.
/// 2. Instance method body (via `trait_impl_to_ast`'s Spec/Proof
///    body rendering — see that function's call to
///    `rewrite_self_sibling_calls` re-exported from this module).
///
/// Was previously at LExpr level as `strip_class_qualifier` in
/// `to_lean_fn.rs`; that pass was type-blind and mis-rewrote
/// blanket-impl bodies. Moving the rewrite to VIR level (where
/// receiver types are preserved) and gating on `types_equal` solves
/// both that bug and the new forward-reference bug for standalone
/// def bodies.
pub fn rewrite_self_sibling_calls(
    body: &Expr,
    trait_path: &Path,
    impl_self_typ: &Typ,
    method_redirects: &HashMap<String, Fun>,
) -> Expr {
    use vir::ast_util::types_equal;
    // Peel transparent type wrappers (Decorate, Boxed) so
    // `args[0].typ` from `self.method()` (shape `Decorate(Ref, ...,
    // Self)`) compares structurally to the impl's `Self`.
    fn peel(t: &Typ) -> Typ {
        let mut cur = t.clone();
        loop {
            let next = match &*cur {
                TypX::Decorate(_, _, inner) => inner.clone(),
                TypX::Boxed(inner) => inner.clone(),
                _ => return cur,
            };
            cur = next;
        }
    }
    let impl_self_peeled = peel(impl_self_typ);
    vir::ast_visitor::map_expr_visitor(body, &|e: &Expr| {
        if let ExprX::Call(target, args, post_args) = &e.x {
            if let CallTarget::Fun(kind, fun, typs, impl_paths, autospec, const_var) = target {
                // Only rewrite genuinely-resolved self-sibling calls.
                // A call that dispatches through a `[Trait A]` bound —
                // a blanket impl forwarding to the inner type, e.g.
                // vstd's `View for Rc<A>`: `(**self).view()` — is
                // `Dynamic` (unresolved) and must stay class dispatch
                // so Lean resolves it via the bound. Its receiver can be
                // typed `&Self` (a smart-pointer's spec deref doesn't
                // reduce, so `**self` keeps type `Rc<A>`), making it
                // indistinguishable from a self-call by type alone — the
                // resolution kind is the reliable discriminator. A true
                // self-sibling call resolves to a concrete impl method
                // (`DynamicResolved`/`Static`). (#122 B1: without this,
                // blanket Rc/Arc View instances forwarded to a self-
                // referential `impl__N.view` standalone.)
                if !matches!(kind,
                    CallTargetKind::DynamicResolved { .. } | CallTargetKind::Static)
                {
                    return Ok(e.clone());
                }
                let segs = &fun.path.segments;
                if segs.len() < 2 { return Ok(e.clone()); }
                let method_short = segs[segs.len() - 1].as_str().to_string();
                let trait_segs = &trait_path.segments;
                if segs.len() != trait_segs.len() + 1 { return Ok(e.clone()); }
                let head_matches = segs.iter().zip(trait_segs.iter())
                    .take(trait_segs.len())
                    .all(|(a, b)| a == b);
                if !head_matches { return Ok(e.clone()); }
                let Some(impl_fun) = method_redirects.get(&method_short) else {
                    return Ok(e.clone());
                };
                let Some(first_arg) = args.first() else {
                    return Ok(e.clone());
                };
                let arg_peeled = peel(&first_arg.typ);
                if !types_equal(&arg_peeled, &impl_self_peeled) {
                    return Ok(e.clone());
                }
                // Conservative: typs.len() == 1 (non-generic trait,
                // non-generic method). More complex cases fall
                // through to class dispatch.
                if typs.len() != 1 {
                    return Ok(e.clone());
                }
                let new_target = CallTarget::Fun(
                    CallTargetKind::Static,
                    impl_fun.clone(),
                    Arc::new(vec![]),
                    impl_paths.clone(),
                    *autospec,
                    *const_var,
                );
                return Ok(SpannedTyped::new(
                    &e.span,
                    &e.typ,
                    ExprX::Call(new_target, args.clone(), post_args.clone()),
                ));
            }
        }
        Ok(e.clone())
    })
    .expect("rewrite_self_sibling_calls is structural and cannot error")
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

/// Lift associated-type projections in a STANDALONE generic function
/// (a spec/proof fn whose `FunctionKind` is not `TraitMethodImpl`, so
/// it has no enclosing impl in `impl_substs`). Mirrors
/// [`maybe_augment_impl_method`] but drives [`ImplSubst::build`] from the
/// fn's OWN `typ_params` / `typ_bounds` + signature typs — no impl, no
/// `method_context` (so no self-sibling rewrite, no name-prefix rename).
/// Returns `f` unchanged when it has no liftable projections (empty subst).
///
/// This is the RC2 generalization: projection-lifting is a property of
/// **every** emitted generic function, not just impl methods. The
/// canonical consumer is vstd's `std_specs::hash::hash_map_deep_view_impl`
/// — a `pub open spec fn` generic over `<Key: DeepView, Value: DeepView>`
/// returning `Map<<Key as DeepView>::V, <Value as DeepView>::V>` and
/// referencing the same projections in its body. `DeepView`'s assoc type
/// `V` is an `outParam`, so the projection can't render as an accessor;
/// the lift replaces each with a fresh `_tactus_assoc_X_DeepView_V` binder
/// constrained via the bound's instance bracket (the Bug-B mechanism).
///
/// `build`'s "Source 2" (uncovered assoc-type slots on bound traits)
/// covers body-only projections too: any `X` with a `DeepView X` bound
/// gets a fresh binder for each of `DeepView`'s assoc types regardless of
/// where (signature or body) the projection appears — so the body walk in
/// `augment_function` always finds the projection in `proj_map`.
pub fn maybe_augment_standalone_fn(
    f: &FunctionX,
    traits: &HashMap<Path, &TraitX>,
) -> FunctionX {
    let sig_typs =
        std::iter::once(&f.ret.x.typ).chain(f.params.iter().map(|p| &p.x.typ));
    let subst = ImplSubst::build(&f.typ_params, &f.typ_bounds, sig_typs, traits);
    if subst.is_empty() {
        return f.clone();
    }
    subst.augment_function(f)
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

    fn empty_lookup() -> HashMap<Path, &'static TraitX> {
        HashMap::new()
    }

    /// Empty inputs → empty subst (no fresh binders, no rewrites).
    #[test]
    fn build_empty_inputs_returns_empty_subst() {
        let typ_params: Idents = Arc::new(vec![]);
        let typ_bounds: GenericBounds = Arc::new(vec![]);
        let typs: Vec<Typ> = vec![];
        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &empty_lookup());
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
        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &empty_lookup());
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
        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &empty_lookup());
        assert!(!subst.is_empty());
        assert_eq!(subst.fresh_binders.len(), 1);
        assert_eq!(subst.fake_bounds.len(), 1);
        assert_eq!(subst.proj_map.len(), 1);
        // Invariant check: the three field lengths match.
        let key = (mk_ident("A"), mk_path(&["View"]), mk_ident("V"));
        assert!(subst.proj_map.contains_key(&key));
        let fresh = subst.proj_map.get(&key).unwrap();
        assert_eq!(fresh.as_str(), "_tactus_assoc_A_View_V");
        assert_eq!(subst.fresh_binders[0].as_str(), "_tactus_assoc_A_View_V");
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
        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &empty_lookup());
        assert_eq!(subst.fresh_binders.len(), 2);
        let names: std::collections::HashSet<String> = subst.fresh_binders.iter()
            .map(|i| i.as_str().to_string())
            .collect();
        assert!(names.contains("_tactus_assoc_A_View_V"));
        assert!(names.contains("_tactus_assoc_B_View_V"));
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
        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &empty_lookup());
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
        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &empty_lookup());
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
        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &empty_lookup());
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
            method_context: None,
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
            method_context: None,
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

    /// Audit-fix source 2: a trait bound on a typ-param with an
    /// assoc type that the impl signature DOESN'T use should still
    /// get a fresh binder, so the rendered bracket has the right
    /// arity. Pinned to prevent regression of the `[DeepView A]`
    /// 1-arg-on-2-arg-class bug surfaced by the multi-trait probe.
    #[test]
    fn build_fills_uncovered_assoc_slots_from_trait_bounds() {
        let typ_params: Idents = Arc::new(vec![mk_ident("A")]);
        let typ_bounds: GenericBounds = Arc::new(vec![
            Arc::new(GenericBoundX::Trait(
                TraitId::Path(mk_path(&["DeepView"])),
                Arc::new(vec![Arc::new(TypX::TypParam(mk_ident("A")))]),
            )),
        ]);
        // No projection in typs — but DeepView has assoc type V.
        let typs: Vec<Typ> = vec![];
        // Construct a fake TraitX with `assoc_typs: [V]`.
        let trait_decl = make_trait_with_assocs("DeepView", &["V"]);
        let mut lookup: HashMap<Path, &TraitX> = HashMap::new();
        lookup.insert(mk_path(&["DeepView"]), &trait_decl);

        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &lookup);
        assert_eq!(subst.fresh_binders.len(), 1);
        assert_eq!(subst.fresh_binders[0].as_str(), "_tactus_assoc_A_DeepView_V");
    }

    /// When both source-1 (projection) AND source-2 (uncovered slot)
    /// would produce a binder for the SAME (X, T, N), only one
    /// binder is allocated. The projection's entry wins.
    #[test]
    fn build_doesnt_double_count_when_projection_already_covers() {
        let typ_params: Idents = Arc::new(vec![mk_ident("A")]);
        let typ_bounds: GenericBounds = Arc::new(vec![
            Arc::new(GenericBoundX::Trait(
                TraitId::Path(mk_path(&["View"])),
                Arc::new(vec![Arc::new(TypX::TypParam(mk_ident("A")))]),
            )),
        ]);
        let typs = vec![mk_proj("A", &["View"], "V")];
        let trait_decl = make_trait_with_assocs("View", &["V"]);
        let mut lookup: HashMap<Path, &TraitX> = HashMap::new();
        lookup.insert(mk_path(&["View"]), &trait_decl);

        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &lookup);
        // Only ONE binder, not two — the projection's entry already
        // covered (A, View, V).
        assert_eq!(subst.fresh_binders.len(), 1);
    }

    /// Multi-trait bound on one typ-param, where each trait has its
    /// own assoc type — the audit case that surfaced the bug. Both
    /// brackets should get filled even when only one is used by a
    /// projection.
    #[test]
    fn build_handles_multi_trait_per_param_with_partial_coverage() {
        let typ_params: Idents = Arc::new(vec![mk_ident("A")]);
        let typ_bounds: GenericBounds = Arc::new(vec![
            Arc::new(GenericBoundX::Trait(
                TraitId::Path(mk_path(&["View"])),
                Arc::new(vec![Arc::new(TypX::TypParam(mk_ident("A")))]),
            )),
            Arc::new(GenericBoundX::Trait(
                TraitId::Path(mk_path(&["DeepView"])),
                Arc::new(vec![Arc::new(TypX::TypParam(mk_ident("A")))]),
            )),
        ]);
        // Only View's V appears as a projection; DeepView's V does
        // NOT — the audit case.
        let typs = vec![mk_proj("A", &["View"], "V")];
        let view_decl = make_trait_with_assocs("View", &["V"]);
        let deep_decl = make_trait_with_assocs("DeepView", &["V"]);
        let mut lookup: HashMap<Path, &TraitX> = HashMap::new();
        lookup.insert(mk_path(&["View"]), &view_decl);
        lookup.insert(mk_path(&["DeepView"]), &deep_decl);

        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &lookup);
        assert_eq!(subst.fresh_binders.len(), 2);
        let names: std::collections::HashSet<String> = subst.fresh_binders.iter()
            .map(|i| i.as_str().to_string())
            .collect();
        assert!(names.contains("_tactus_assoc_A_View_V"));
        assert!(names.contains("_tactus_assoc_A_DeepView_V"));
    }

    /// Multi-arg trait bounds: when a bound is `Trait(T, [A, Int])`
    /// (e.g., `A: Converter<u8>`), the synthesised fake `TypEquality`
    /// must carry the FULL typs `[A, Int]`, not just `[A]`. The
    /// `trait_bounds_to_ast_with` filter matches by both path AND
    /// typs structurally; if our fake has `[A]` and the bound has
    /// `[A, Int]`, the lengths differ and the fresh binder doesn't
    /// reach the rendered bracket. Pinned by audit follow-up.
    #[test]
    fn build_fake_bound_carries_full_typs_for_multi_arg_trait() {
        let typ_params: Idents = Arc::new(vec![mk_ident("A")]);
        // Bound: `A: Converter<u8>` → Trait(Converter, [A, U(8)]).
        let u8_typ: Typ = Arc::new(TypX::Int(vir::ast::IntRange::U(8)));
        let typ_bounds: GenericBounds = Arc::new(vec![
            Arc::new(GenericBoundX::Trait(
                TraitId::Path(mk_path(&["Converter"])),
                Arc::new(vec![
                    Arc::new(TypX::TypParam(mk_ident("A"))),
                    u8_typ.clone(),
                ]),
            )),
        ]);
        // Projection `<A as Converter<u8>>::Out` — trait_typ_args is
        // `[TypParam(A), U(8)]`.
        let proj: Typ = Arc::new(TypX::Projection {
            trait_typ_args: Arc::new(vec![
                Arc::new(TypX::TypParam(mk_ident("A"))),
                u8_typ.clone(),
            ]),
            trait_path: mk_path(&["Converter"]),
            name: mk_ident("Out"),
        });
        let typs = vec![proj];
        let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &empty_lookup());
        assert_eq!(subst.fake_bounds.len(), 1);
        match &*subst.fake_bounds[0] {
            GenericBoundX::TypEquality(_, fake_typs, _, _) => {
                assert_eq!(fake_typs.len(), 2,
                    "fake bound typs should match the original bound's arity (2), got {}",
                    fake_typs.len());
                // First typ is A, second is U(8).
                assert!(matches!(&**fake_typs.iter().next().unwrap(), TypX::TypParam(n) if n.as_str() == "A"));
            }
            other => panic!("expected TypEquality, got {:?}", other),
        }
    }

    /// Helper: minimal `TraitX` literal for tests.
    fn make_trait_with_assocs(name: &str, assocs: &[&str]) -> TraitX {
        TraitX {
            name: mk_path(&[name]),
            proxy: None,
            visibility: vir::ast::Visibility {
                restricted_to: None,
            },
            typ_params: Arc::new(vec![]),
            typ_bounds: Arc::new(vec![]),
            assoc_typs: Arc::new(assocs.iter().map(|s| mk_ident(s)).collect()),
            assoc_typs_bounds: Arc::new(vec![]),
            methods: Arc::new(vec![]),
            is_unsafe: false,
            external_trait_extension: None,
            dyn_compatible: None,
        }
    }
}
