//! Unit tests for `impl_subst` — extracted to `src/tests/` (a `#[path]`'d
//! `mod tests` child of `impl_subst`, so `use super::*` reaches private items).

use super::*;
use vir::ast::{PathX, TraitId, TraitX};

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

/// `build` now takes the per-trait out-param map (own + transitively-inherited
/// assoc out-params), not the raw trait lookup. Derive it from a test lookup via
/// the real `compute_trait_outparams` (so these tests also exercise it). Tests
/// have no shells, so `unemittable` is empty.
fn outparams(lookup: &HashMap<Path, &TraitX>) -> HashMap<Path, Vec<vir::ast::Ident>> {
    crate::to_lean_fn::compute_trait_outparams(lookup, &std::collections::HashSet::new())
}

/// Empty inputs → empty subst (no fresh binders, no rewrites).
#[test]
fn build_empty_inputs_returns_empty_subst() {
    let typ_params: Idents = Arc::new(vec![]);
    let typ_bounds: GenericBounds = Arc::new(vec![]);
    let typs: Vec<Typ> = vec![];
    let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &outparams(&empty_lookup()));
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
    let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &outparams(&empty_lookup()));
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
    let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &outparams(&empty_lookup()));
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
    let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &outparams(&empty_lookup()));
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
    let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &outparams(&empty_lookup()));
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
    let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &outparams(&empty_lookup()));
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
    let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &outparams(&empty_lookup()));
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

    let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &outparams(&lookup));
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

    let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &outparams(&lookup));
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

    let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &outparams(&lookup));
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
    let subst = ImplSubst::build(&typ_params, &typ_bounds, typs.iter(), &outparams(&empty_lookup()));
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
