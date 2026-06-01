//! Unit tests for `inline_spec` — extracted to `src/tests/` (a `#[path]`'d
//! `mod tests` child of `inline_spec`, so `use super::*` reaches private items).

use super::*;
use vir::ast::{Path, PathX};

fn dummy_path() -> Path {
    Arc::new(PathX { krate: None, segments: Arc::new(vec![]) })
}

// `inline_okay` is the gate that lets blanket-impl `#[inline]` methods
// (`TraitMethodImpl`) be inlined while a trait method *decl* (whose default
// body might be overridden) is never inlined — mirroring Verus's own
// `FunctionKind::inline_okay`. It also underpins `can_drop` (drop only
// `Static`). The richer behaviour (self-as-`ReadPlace` substitution,
// trivial-block peel, typ-preservation, Static-drop vs TraitMethodImpl-keep)
// is exercised end-to-end by `test_cross_crate_map_contains_key`,
// `test_cross_crate_set_contains`, and `test_exec_call_mut_arg_vec_index`.
#[test]
fn inline_okay_matches_verus() {
    assert!(inline_okay(&FunctionKind::Static));
    assert!(inline_okay(&FunctionKind::TraitMethodImpl {
        method: Arc::new(vir::ast::FunX { path: dummy_path() }),
        impl_path: dummy_path(),
        trait_path: dummy_path(),
        trait_typ_args: Arc::new(vec![]),
        inherit_body_from: None,
    }));
    assert!(!inline_okay(&FunctionKind::TraitMethodDecl {
        trait_path: dummy_path(),
        has_default: true,
    }));
}
