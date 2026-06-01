//! Unit tests for `to_lean_fn` — extracted to `src/tests/` (a `#[path]`'d
//! `mod tests` child of `to_lean_fn`, so `use super::*` reaches private items).

use super::*;
use crate::test_fixtures::{mk_path, typ_datatype};
use std::collections::HashSet;
use std::sync::Arc;

fn trait_bound(trait_name: &str, arg: &str) -> GenericBound {
    Arc::new(GenericBoundX::Trait(
        TraitId::Path(mk_path(trait_name)),
        Arc::new(vec![typ_datatype(arg)]),
    ))
}

// R-1 (#122): the shared bound→binder chokepoint
// (`trait_bounds_to_ast_with`) drops bounds that reference an
// un-emittable (shell) trait. Centralizing the filter here means
// EVERY bound site — class superclass bounds, instance binders, AND
// fn-level generic bounds (spec/proof fns via `fn_binders`) — is
// covered uniformly. This pins the chokepoint behaviour directly so
// a future caller of the renderer can't silently regress the
// fn-level path (the site the call-site pre-filter missed).
#[test]
fn trait_bounds_to_ast_drops_shell_trait_bounds() {
    let bounds: GenericBounds = Arc::new(vec![
        trait_bound("Clone", "T"),      // shell — should be dropped
        trait_bound("Emittable", "T"),  // ordinary — should survive
    ]);

    // With Clone marked un-emittable: only the Emittable bound survives.
    let mut unemittable: HashSet<Path> = HashSet::new();
    unemittable.insert(mk_path("Clone"));
    let binders = trait_bounds_to_ast(&bounds, &unemittable);
    assert_eq!(binders.len(), 1,
        "the shell-trait bound (Clone) must be dropped at the chokepoint");

    // Empty un-emittable set: nothing dropped (both bounds render).
    let none: HashSet<Path> = HashSet::new();
    let binders = trait_bounds_to_ast(&bounds, &none);
    assert_eq!(binders.len(), 2,
        "no shell traits → no bounds dropped");
}
