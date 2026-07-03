//! `[Nonempty T]` instance-binder inference.
//!
//! Verus's `choose|x: T| P(x)` is total — it returns *some* value of `T`
//! even when nothing satisfies `P` — which is sound only because Verus
//! treats every spec type as inhabited. Tactus renders it as Lean's
//! `Classical.epsilon`, and Lean's `Classical.epsilon` carries a hard
//! `[Nonempty T]` requirement. So a faithful rendering inherits that
//! requirement: any generic fn / instance / lemma that (transitively)
//! picks an arbitrary value of a type-param `T` must declare `[Nonempty T]`.
//!
//! This is not Tactus heuristically adding constraints — it's emitting the
//! *exact* binder Lean itself would force a human writing this Lean by
//! hand to add, in the *exact* places it forces them. Seeded at the
//! `choose` site, propagated backward along the call graph (mapping
//! type-args at each boundary), and bottoming out at concrete types where
//! `Nonempty` resolves automatically (Tactus emits `Inhabited` ⟹
//! `Nonempty` for every concrete datatype). For `HashMap::contains_key`
//! the cascade is exactly four vstd-internal declarations
//! (`hash_map_deep_view_impl` → the forwarding def → the `DeepView`
//! instance → `axiom_hashmap_deepview_borrow`) and stops dead at the
//! user's `Key = u8`.
//!
//! The binder is synthesised as a `GenericBoundX::Trait(Nonempty, [T])`
//! and added at AUGMENT time (after `dep_order::collect_references` has
//! run), so it rides the existing `trait_bounds_to_ast` rendering and
//! never leaks into class/datatype emission. The single path segment
//! `Nonempty` renders verbatim via `LeanName::from_path`.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use vir::ast::*;
use crate::dep_order::walk_expr;

/// What a fn requires to elaborate against the Nonempty-bracketed
/// axiom environment (N1, DESIGN-nonempty-axioms.md).
#[derive(Default, Clone)]
pub struct NonemptyNeed {
    /// Type-param INDICES that require `[Nonempty]` binders.
    pub params: HashSet<usize>,
    /// Non-param typs that require `[Nonempty]` bounds — associated-type
    /// projections (`<X as Trait>::N`) passed at a needy axiom slot.
    /// Recorded PRE-augmentation; `impl_subst::augment_function`'s
    /// bound rewrite maps them to the synthetic `_tactus_assoc_*`
    /// binders (which is why nonempty bounds must be added BEFORE
    /// augmentation — see `generate.rs`'s `augment`). Deduped
    /// structurally.
    pub projs: Vec<Typ>,
}

/// `needs[F]` = what F requires. See [`NonemptyNeed`].
pub type NonemptyNeeds<'a> = HashMap<&'a Fun, NonemptyNeed>;

/// A fn's signature clauses we scan for `choose` sites and onward calls:
/// body, requires, ensures (both halves).
fn clauses(f: &FunctionX) -> impl Iterator<Item = &Expr> {
    f.body.iter()
        .chain(f.require.iter())
        .chain(f.ensure.0.iter())
        .chain(f.ensure.1.iter())
}

/// Compute, for every function in `all_fns`, which of its type-param
/// indices need a `[Nonempty T]` binder. See module docs for the model.
pub fn compute_nonempty_needs<'a>(all_fns: &[&'a FunctionX]) -> NonemptyNeeds<'a> {
    let mut needs: NonemptyNeeds<'a> = HashMap::new();

    // Seed 1: a fn that chooses over one of its own type-params.
    for f in all_fns {
        let mut seed: HashSet<usize> = HashSet::new();
        let scan = &mut |e: &Expr| {
            if let ExprX::Choose { params, .. } = &e.x {
                for b in params.iter() {
                    if let TypX::TypParam(name) = &*b.a {
                        if let Some(i) = f.typ_params.iter().position(|p| p == name) {
                            seed.insert(i);
                        }
                    }
                }
            }
        };
        for e in clauses(f) { walk_expr(e, scan); }
        if !seed.is_empty() {
            needs.entry(&f.name).or_default().params.extend(seed);
        }
    }

    // Seed 2 (DESIGN-nonempty-axioms.md N1): a body-less spec fn is
    // emitted as a Lean AXIOM (`spec_fn_to_ast`'s None branch —
    // uninterp / external_body / cross-crate-stripped specs). A bare
    // `axiom f : … → A` over a type param inhabits EVERY type,
    // including empty ones — the axiom environment becomes
    // inconsistent and a user tactic can derive False (see the
    // `test_soundness_hole_*` exploit pins). Bracket `[Nonempty]`
    // every typ param MENTIONED in the ret typ. Under the bracket the
    // axiom is satisfiable (model: interpret abstract type formers as
    // `Unit`; "some A" exists by assumption). Mentioned-ANYWHERE
    // over-approximates — a `Seq A`-returning axiom gets a bracket it
    // doesn't strictly need — but the cost is an instance binder that
    // auto-discharges (abstract types carry unconditional
    // `instInhabited` axioms; concrete types derive `Inhabited`), and
    // the simple rule beats a value-reachability analysis.
    //
    // TRAIT METHOD DECLS ARE EXCLUDED: they're body-less spec fns too,
    // but they emit as CLASS FIELDS, not standalone axioms — seeding
    // them cascades `[Nonempty Self]` premises onto every impl's
    // instance, which breaks typeclass resolution for fns that never
    // touch the axiom environment (found by
    // test_instance_body_projection_lifted). The class-field encoding
    // has its own inhabitedness story (an instance is a VALUE the user
    // constructs; axiom-valued instances are N3's ∃-audit).
    for f in all_fns {
        if f.mode != Mode::Spec
            || f.body.is_some()
            || matches!(f.kind, FunctionKind::TraitMethodDecl { .. })
        {
            continue;
        }
        let mut seed: HashSet<usize> = HashSet::new();
        let _ = vir::ast_visitor::typ_visitor_check::<(), _>(&f.ret.x.typ, &mut |t: &Typ| {
            if let TypX::TypParam(name) = &**t {
                if let Some(i) = f.typ_params.iter().position(|p| p == name) {
                    seed.insert(i);
                }
            }
            Ok(())
        });
        if !seed.is_empty() {
            needs.entry(&f.name).or_default().params.extend(seed);
        }
    }

    // Propagate backward along calls to a fixpoint: if F calls G with
    // type-args and G needs `[Nonempty G.param_j]`, then F must be able
    // to DISCHARGE `Nonempty` at whatever typ it passes for slot j:
    // * a bare `TypParam` of F's own → F needs `[Nonempty that_param]`
    //   (the classic case);
    // * a COMPOSITE typ (`Box Q`, `Seq (Q, R)`) → F needs `[Nonempty]`
    //   for every OWN typ param mentioned inside — the prelude's
    //   wrapper `Nonempty` instances / instInhabited axioms lift
    //   param-level nonemptiness through the structure;
    // * an assoc-type PROJECTION (`<X as Trait>::N`, possibly nested
    //   in a composite) → F needs a `[Nonempty <proj>]` bound on the
    //   projection typ itself — nothing lifts TO a projection, it's
    //   an opaque typ at this abstraction level. Recorded as a Typ;
    //   `impl_subst`'s bound rewrite later maps it to the synthetic
    //   `_tactus_assoc_*` binder.
    // Concrete typs mentioned nowhere → nothing recorded; Lean
    // synthesizes their `Nonempty` from `Inhabited` instances.
    // Seed 3 (DESIGN-nonempty-axioms.md N2): array/slice indexing
    // renders as the prelude's `Tactus.index : Vector α n → Int → α`,
    // which is `[Nonempty α]`-bracketed (same inhabitedness hole as
    // generated axioms — the empty vector inhabits `Vector Empty 0`).
    // Indexing is NOT a call (spec-mode `a[i]` is `BinaryOp::Index`;
    // exec-mode is `PlaceX::Index`), so the call-graph propagation
    // can't see it: seed directly from every index site's ELEMENT typ
    // (the Binary expr's own typ / the Index place node's typ).
    for f in all_fns {
        let mut params: HashSet<usize> = HashSet::new();
        let mut projs: Vec<Typ> = Vec::new();
        {
            let mut record_elem_typ = |t: &Typ, params: &mut HashSet<usize>, projs: &mut Vec<Typ>| {
                let _ = vir::ast_visitor::typ_visitor_check::<(), _>(t, &mut |t: &Typ| {
                    match &**t {
                        TypX::TypParam(name) => {
                            if let Some(i) = f.typ_params.iter().position(|p| p == name) {
                                params.insert(i);
                            }
                        }
                        TypX::Projection { .. } => {
                            let key = format!("{:?}", t);
                            if !projs.iter().any(|p| format!("{:?}", p) == key) {
                                projs.push(t.clone());
                            }
                        }
                        _ => {}
                    }
                    Ok(())
                });
            };
            fn scan_place(place: &vir::ast::Place, out: &mut Vec<Typ>) {
                match &place.x {
                    vir::ast::PlaceX::Index(inner, _, _, _) => {
                        out.push(place.typ.clone());
                        scan_place(inner, out);
                    }
                    vir::ast::PlaceX::Field(_, inner)
                    | vir::ast::PlaceX::DerefMut(inner)
                    | vir::ast::PlaceX::ModeUnwrap(inner, _)
                    | vir::ast::PlaceX::WithExpr(_, inner) => scan_place(inner, out),
                    _ => {}
                }
            }
            let scan = &mut |e: &Expr| {
                let mut elem_typs: Vec<Typ> = Vec::new();
                match &e.x {
                    ExprX::Binary(BinaryOp::Index(..), _, _) => {
                        elem_typs.push(e.typ.clone());
                    }
                    ExprX::ReadPlace(p, _)
                    | ExprX::AssignToPlace { place: p, .. }
                    | ExprX::BorrowMut(p)
                    | ExprX::TwoPhaseBorrowMut(p)
                    | ExprX::BorrowMutTracked(p) => scan_place(p, &mut elem_typs),
                    _ => {}
                }
                for t in &elem_typs {
                    record_elem_typ(t, &mut params, &mut projs);
                }
            };
            for e in clauses(f) { walk_expr(e, scan); }
        }
        if !params.is_empty() || !projs.is_empty() {
            let entry = needs.entry(&f.name).or_default();
            entry.params.extend(params);
            for t in projs {
                let key = format!("{:?}", t);
                if !entry.projs.iter().any(|p| format!("{:?}", p) == key) {
                    entry.projs.push(t);
                }
            }
        }
    }

    // Seed 4 (DESIGN-nonempty-axioms.md N3): a Prop-valued axiom whose
    // CONCLUSION asserts `∃ x : T, …` inhabits T via Classical.choice
    // just as surely as a value-typed axiom returns one. Seed
    // [Nonempty] for every typ param / projection mentioned in an
    // Exists binder typ within the ENSURES clauses. Ensures-only:
    // requires-side ∃ are hypotheses, not productions. Over-
    // approximates position (an ∃ under negation isn't producing) —
    // sound, the bracket just narrows instantiation. Known residual
    // (documented in DESIGN.md): classically-existential shapes with
    // no Exists node (`¬∀`) are not caught.
    for f in all_fns {
        let mut params: HashSet<usize> = HashSet::new();
        let mut projs: Vec<Typ> = Vec::new();
        {
            let scan = &mut |e: &Expr| {
                let ExprX::Quant(q, binders, _) = &e.x else { return; };
                if q.quant != air::ast::Quant::Exists {
                    return;
                }
                for b in binders.iter() {
                    let _ = vir::ast_visitor::typ_visitor_check::<(), _>(&b.a, &mut |t: &Typ| {
                        match &**t {
                            TypX::TypParam(name) => {
                                if let Some(i) = f.typ_params.iter().position(|p| p == name) {
                                    params.insert(i);
                                }
                            }
                            TypX::Projection { .. } => {
                                let key = format!("{:?}", t);
                                if !projs.iter().any(|p| format!("{:?}", p) == key) {
                                    projs.push(t.clone());
                                }
                            }
                            _ => {}
                        }
                        Ok(())
                    });
                }
            };
            for e in f.ensure.0.iter().chain(f.ensure.1.iter()) {
                walk_expr(e, scan);
            }
        }
        if !params.is_empty() || !projs.is_empty() {
            let entry = needs.entry(&f.name).or_default();
            entry.params.extend(params);
            for t in projs {
                let key = format!("{:?}", t);
                if !entry.projs.iter().any(|p| format!("{:?}", p) == key) {
                    entry.projs.push(t);
                }
            }
        }
    }

    // Fn lookup for proj-need substitution (callee typ_params).
    let fn_by_name: HashMap<&Fun, &FunctionX> =
        all_fns.iter().map(|f| (&f.name, *f)).collect();

    loop {
        let mut changed = false;
        for f in all_fns {
            // Collect what this pass would pull in, reading `needs`
            // immutably; mutate `needs` only after the scan closure drops.
            let mut pulled_params: HashSet<usize> = HashSet::new();
            let mut pulled_projs: Vec<Typ> = Vec::new();
            {
                let mut record_typ = |t: &Typ, pulled_params: &mut HashSet<usize>, pulled_projs: &mut Vec<Typ>| {
                    let _ = vir::ast_visitor::typ_visitor_check::<(), _>(t, &mut |t: &Typ| {
                        match &**t {
                            TypX::TypParam(name) => {
                                if let Some(i) = f.typ_params.iter().position(|p| p == name) {
                                    pulled_params.insert(i);
                                }
                            }
                            TypX::Projection { .. } => {
                                // TypX lacks PartialEq; dedup via Debug key
                                // (projection typs are small).
                                let key = format!("{:?}", t);
                                if !pulled_projs.iter().any(|p| format!("{:?}", p) == key) {
                                    pulled_projs.push(t.clone());
                                }
                            }
                            _ => {}
                        }
                        Ok(())
                    });
                };
                let scan = &mut |e: &Expr| {
                    let ExprX::Call(CallTarget::Fun(kind, g, typs, ..), _, _) = &e.x else { return; };
                    // The dispatch target + its type-args. For a resolved
                    // trait-method call the requirement lives on the
                    // resolved impl method, instantiated by `DynamicResolved.typs`.
                    let (callee, typ_args): (&Fun, &Typs) = match kind {
                        CallTargetKind::DynamicResolved { resolved, typs: rtyps, .. } => (resolved, rtyps),
                        _ => (g, typs),
                    };
                    if let Some(callee_needs) = needs.get(callee) {
                        for &j in &callee_needs.params {
                            let Some(arg) = typ_args.get(j) else { continue };
                            record_typ(arg, &mut pulled_params, &mut pulled_projs);
                        }
                        // Projection needs propagate caller-ward SUBSTITUTED:
                        // the callee's `[Nonempty <Value as Trait>::N]` at a
                        // call with Value := Q becomes the caller's
                        // `<Q as Trait>::N`. If the substituted projection
                        // mentions NO caller typ params it's concrete —
                        // skipped: Lean resolves the projection through the
                        // concrete instance and synthesizes Nonempty itself
                        // (recording it would render an unrewritable
                        // projection name).
                        if !callee_needs.projs.is_empty() {
                            if let Some(callee_fx) = fn_by_name.get(callee) {
                                if typ_args.len() >= callee_fx.typ_params.len() {
                                    let map: HashMap<Ident, Typ> = callee_fx.typ_params.iter()
                                        .cloned()
                                        .zip(typ_args.iter().cloned())
                                        .collect();
                                    for pt in &callee_needs.projs {
                                        let st = vir::sst_util::subst_typ(&map, pt);
                                        let mut mentions_param = false;
                                        let _ = vir::ast_visitor::typ_visitor_check::<(), _>(&st, &mut |t: &Typ| {
                                            if matches!(&**t, TypX::TypParam(_)) {
                                                mentions_param = true;
                                            }
                                            Ok(())
                                        });
                                        if mentions_param {
                                            record_typ(&st, &mut pulled_params, &mut pulled_projs);
                                        }
                                    }
                                }
                            }
                        }
                    }
                };
                for e in clauses(f) { walk_expr(e, scan); }
            }
            if !pulled_params.is_empty() || !pulled_projs.is_empty() {
                let entry = needs.entry(&f.name).or_default();
                for i in pulled_params {
                    if entry.params.insert(i) { changed = true; }
                }
                for t in pulled_projs {
                    let key = format!("{:?}", t);
                    if !entry.projs.iter().any(|p| format!("{:?}", p) == key) {
                        entry.projs.push(t);
                        changed = true;
                    }
                }
            }
        }
        if !changed { break; }
    }

    needs
}

/// The synthetic `[Nonempty T]` bound — a `GenericBoundX::Trait` whose
/// single-segment path renders to `Nonempty` and whose sole type-arg is
/// `T`. Rendered by the ordinary `trait_bounds_to_ast` path.
fn nonempty_bound(param: &Ident) -> GenericBound {
    nonempty_bound_typ(Arc::new(TypX::TypParam(param.clone())))
}

/// `[Nonempty <typ>]` for an arbitrary typ — used for assoc-type
/// projection needs (the typ is a `TypX::Projection` pre-augmentation).
fn nonempty_bound_typ(typ: Typ) -> GenericBound {
    let path = Arc::new(PathX {
        krate: None,
        segments: Arc::new(vec![Arc::new("Nonempty".to_string())]),
    });
    Arc::new(GenericBoundX::Trait(TraitId::Path(path), Arc::new(vec![typ])))
}

/// Append `[Nonempty T]` bounds to a fn's `typ_bounds` for each needed
/// type-param index, plus `[Nonempty <proj>]` bounds for each needed
/// projection typ. Identity when the need is empty. Must run BEFORE
/// `impl_subst` augmentation so the projection bounds get rewritten to
/// the synthetic `_tactus_assoc_*` binders.
pub fn add_fn_nonempty_bounds(f: FunctionX, need: &NonemptyNeed) -> FunctionX {
    if need.params.is_empty() && need.projs.is_empty() { return f; }
    let mut bounds: Vec<GenericBound> = (*f.typ_bounds).iter().cloned().collect();
    for &i in &need.params {
        if let Some(name) = f.typ_params.get(i) {
            bounds.push(nonempty_bound(name));
        }
    }
    for t in &need.projs {
        bounds.push(nonempty_bound_typ(t.clone()));
    }
    FunctionX { typ_bounds: Arc::new(bounds), ..f }
}

/// Synthetic `[Nonempty T]` bounds for an instance, derived from its
/// method-impl fns' needs: a method that needs `[Nonempty (its param i)]`
/// contributes `[Nonempty name]` to the instance iff `name` is one of the
/// instance's own type-params. Appended to the instance's bound list.
pub fn instance_nonempty_bounds<'a>(
    needs: &NonemptyNeeds<'a>,
    method_impls: &[&'a FunctionX],
    impl_typ_params: &[Ident],
) -> Vec<GenericBound> {
    let mut names: HashSet<&Ident> = HashSet::new();
    let mut projs: Vec<Typ> = Vec::new();
    for m in method_impls {
        if let Some(need) = needs.get(&m.name) {
            for &i in &need.params {
                if let Some(name) = m.typ_params.get(i) {
                    if impl_typ_params.iter().any(|p| p == name) {
                        names.insert(name);
                    }
                }
            }
            // Projection needs (N1): the instance's method VALUE
            // references the standalone def, which demands
            // `[Nonempty <proj>]` — the instance must bind the same
            // premise to elaborate. Only projs whose typ params are
            // all impl-level attach (method-only generics can't be
            // bound at the instance). The caller rewrites these
            // through the impl's `ImplSubst` so they land on the
            // synthetic `_tactus_assoc_*` binders.
            'proj: for pt in &need.projs {
                let mut all_impl_params = true;
                let _ = vir::ast_visitor::typ_visitor_check::<(), _>(pt, &mut |t: &Typ| {
                    if let TypX::TypParam(name) = &**t {
                        if !impl_typ_params.iter().any(|p| p == name) {
                            all_impl_params = false;
                        }
                    }
                    Ok(())
                });
                if !all_impl_params {
                    continue 'proj;
                }
                let key = format!("{:?}", pt);
                if !projs.iter().any(|p| format!("{:?}", p) == key) {
                    projs.push(pt.clone());
                }
            }
        }
    }
    names.into_iter().map(nonempty_bound)
        .chain(projs.into_iter().map(nonempty_bound_typ))
        .collect()
}
