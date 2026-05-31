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

/// `needs[F]` = the set of F's type-param INDICES that require `[Nonempty]`.
pub type NonemptyNeeds<'a> = HashMap<&'a Fun, HashSet<usize>>;

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

    // Seed: a fn that chooses over one of its own type-params.
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
        if !seed.is_empty() { needs.insert(&f.name, seed); }
    }

    // Propagate backward along calls to a fixpoint: if F calls G with
    // type-args and G needs `[Nonempty G.param_j]`, and F passes one of
    // its OWN type-params for slot j, then F needs `[Nonempty that_param]`.
    loop {
        let mut changed = false;
        for f in all_fns {
            // Collect what this pass would pull in, reading `needs`
            // immutably; mutate `needs` only after the scan closure drops.
            let mut pulled: HashSet<usize> = HashSet::new();
            {
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
                        for &j in callee_needs {
                            if let Some(TypX::TypParam(name)) = typ_args.get(j).map(|t| &**t) {
                                if let Some(i) = f.typ_params.iter().position(|p| p == name) {
                                    pulled.insert(i);
                                }
                            }
                        }
                    }
                };
                for e in clauses(f) { walk_expr(e, scan); }
            }
            if !pulled.is_empty() {
                let entry = needs.entry(&f.name).or_default();
                for i in pulled {
                    if entry.insert(i) { changed = true; }
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
    let path = Arc::new(PathX {
        krate: None,
        segments: Arc::new(vec![Arc::new("Nonempty".to_string())]),
    });
    Arc::new(GenericBoundX::Trait(
        TraitId::Path(path),
        Arc::new(vec![Arc::new(TypX::TypParam(param.clone()))]),
    ))
}

/// Append `[Nonempty T]` bounds to a fn's `typ_bounds` for each needed
/// type-param index. Identity when `indices` is empty.
pub fn add_fn_nonempty_bounds(f: FunctionX, indices: &HashSet<usize>) -> FunctionX {
    if indices.is_empty() { return f; }
    let mut bounds: Vec<GenericBound> = (*f.typ_bounds).iter().cloned().collect();
    for &i in indices {
        if let Some(name) = f.typ_params.get(i) {
            bounds.push(nonempty_bound(name));
        }
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
    for m in method_impls {
        if let Some(indices) = needs.get(&m.name) {
            for &i in indices {
                if let Some(name) = m.typ_params.get(i) {
                    if impl_typ_params.iter().any(|p| p == name) {
                        names.insert(name);
                    }
                }
            }
        }
    }
    names.into_iter().map(nonempty_bound).collect()
}
