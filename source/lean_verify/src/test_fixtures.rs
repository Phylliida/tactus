//! Shared synthetic fixtures for unit tests across `lean_verify`'s
//! modules. Helpers here are used by `sst_to_lean::tests`,
//! `dep_order::tests`, and `generate::tests` — extracting them
//! prevents the natural drift where each module's tests grow their
//! own copy of "make me a synthetic Path / Typ / Krate" boilerplate.
//!
//! Per-module-specific helpers (e.g., `mk_test_emitter` in
//! `sst_to_lean::tests`, `mk_datatype` in `dep_order::tests`) stay
//! close to their consumers — the rule of thumb is: extract here
//! when at least two modules need the same shape, otherwise leave
//! it where it's used.
//!
//! Gated on `#[cfg(test)]` so production builds skip this module
//! entirely. `pub(crate)` visibility lets the three `tests` modules
//! `use crate::test_fixtures::...`.

use std::sync::Arc;
use vir::ast::{
    Arch, ArchWordBits, Dt, IntRange, KrateX, Path, PathX, Typ, TypX,
};

/// Synthetic single-segment local-crate `Path`. `mk_path("Tree")`
/// produces a path with one segment "Tree" and `krate: None`. Used
/// for naming datatypes / functions in synthetic fixtures.
pub(crate) fn mk_path(name: &str) -> Path {
    Arc::new(PathX {
        krate: None,
        segments: Arc::new(vec![Arc::new(name.to_string())]),
    })
}

/// `TypX::Int(IntRange::Int)` Typ — the "int" type used in spec
/// position. Common as a non-recursive field type that doesn't
/// produce edges in the SCC graph (`dep_order::order_datatypes`)
/// or as the type of synthetic loop bounds, decrease measures,
/// etc.
pub(crate) fn typ_int() -> Typ {
    Arc::new(TypX::Int(IntRange::Int))
}

/// Synthetic `Typ` for a non-generic concrete datatype reference,
/// e.g., `typ_datatype("Tree")` →
/// `TypX::Datatype(Dt::Path("Tree"), [], [])`. No type args, no
/// impl paths — sufficient for SCC-graph / height-fn dispatch
/// tests where the structural shape of the reference is what
/// matters, not the specific instantiation.
pub(crate) fn typ_datatype(name: &str) -> Typ {
    Arc::new(TypX::Datatype(
        Dt::Path(mk_path(name)),
        Arc::new(vec![]),
        Arc::new(vec![]),
    ))
}

/// Build an empty `KrateX` for tests. All collections empty;
/// `arch` set to `Either32Or64` (the architecture-agnostic option,
/// matching how production preamble generation defaults when no
/// specific target is provided).
///
/// Useful as a baseline for testing krate-level entry points
/// (`krate_preamble`, `WpCtx::new`) where the krate's content is
/// not under test — for those, populate fields incrementally on
/// top of `empty_krate()`.
pub(crate) fn empty_krate() -> KrateX {
    KrateX {
        functions: vec![],
        reveal_groups: vec![],
        datatypes: vec![],
        opaque_types: vec![],
        traits: vec![],
        trait_impls: vec![],
        assoc_type_impls: vec![],
        modules: vec![],
        external_fns: vec![],
        external_types: vec![],
        path_as_rust_names: vec![],
        arch: Arch { word_bits: ArchWordBits::Either32Or64 },
    }
}
