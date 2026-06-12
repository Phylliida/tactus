//! Krate-level emission context (REFACTORING2 § 1.2).
//!
//! Before this module, each emission entry point (`krate_preamble`,
//! `emit_proof_fn`) rebuilt the same krate-level tables independently —
//! the all-fn map existed as `method_lookup`, `fn_map` (twice in one
//! function), and a third copy in the proof-fn path — and threaded them
//! through every intermediate signature (`trait_impl_to_ast` peaked at
//! nine parameters). Adding the next table meant touching every
//! signature on the path.
//!
//! `EmitCtx` builds the tables once per emission entry and is threaded
//! as a single reference. Narrow leaf helpers that need exactly one
//! table (e.g. `trait_bounds_to_ast`) keep their narrow parameter and
//! receive a field reference (`&ectx.unemittable`) — the context is for
//! the *threading* layers, not a license for leaves to grab ambient
//! state.
//!
//! Deliberately NOT here (yet): the ambient thread-local tables
//! (`to_lean_type`'s inherent-method renames, `to_lean_sst_expr`'s
//! datatype field bounds) — those are installed by `generate.rs` and
//! consulted from deep call sites that don't see any ctx today. Folding
//! them in requires the typed-renderer migration (REFACTORING2 § 2.A)
//! to thread context through the renderers first.

use std::collections::{HashMap, HashSet};

use vir::ast::{AssocTypeImplX, Fun, KrateX, Path, TraitX};

/// Krate-level tables shared by everything one emission pass renders.
/// Build once per entry point with [`EmitCtx::build`]; thread by
/// reference.
pub struct EmitCtx<'a> {
    /// All-fn lookup (spec + proof + exec, unfiltered). Backs
    /// trait-method resolution, callee-spec inlining, and
    /// [`Self::render_ctx`].
    pub fn_map: crate::sst_to_lean::FnMap<'a>,
    /// Shell traits whose class can't render faithfully because a
    /// method decl is stripped cross-crate (#122). Their classes emit
    /// as empty markers; their instances and bounds are dropped.
    pub unemittable: HashSet<Path>,
    /// Per-trait ordered out-param assoc-type names (own + transitively
    /// inherited via `extends`), from `compute_trait_outparams`.
    pub trait_outparams: HashMap<Path, Vec<vir::ast::Ident>>,
    /// Every assoc-type impl in the krate — for filling a concrete
    /// instance's inherited out-param from the implementor's sibling
    /// superclass impl.
    pub all_assoc_types: Vec<&'a AssocTypeImplX>,
    /// Lean tactic bodies harvested by the FileLoader, keyed by fn.
    pub tactic_bodies: &'a HashMap<Fun, String>,
}

impl<'a> EmitCtx<'a> {
    pub fn build(krate: &'a KrateX, tactic_bodies: &'a HashMap<Fun, String>) -> Self {
        let fn_map: crate::sst_to_lean::FnMap<'a> =
            krate.functions.iter().map(|f| (&f.x.name, &f.x)).collect();
        let unemittable = crate::expr_shared::unemittable_traits(krate, &fn_map);
        let trait_lookup: HashMap<Path, &TraitX> =
            krate.traits.iter().map(|tr| (tr.x.name.clone(), &tr.x)).collect();
        let trait_outparams =
            crate::to_lean_fn::compute_trait_outparams(&trait_lookup, &unemittable);
        let all_assoc_types: Vec<&'a AssocTypeImplX> =
            krate.assoc_type_impls.iter().map(|a| &a.x).collect();
        EmitCtx { fn_map, unemittable, trait_outparams, all_assoc_types, tactic_bodies }
    }

    /// Renderer view of this context: a [`RenderCtx`] backed by the
    /// shared fn_map.
    ///
    /// [`RenderCtx`]: crate::expr_shared::RenderCtx
    pub fn render_ctx(&self) -> crate::expr_shared::RenderCtx<'_> {
        crate::expr_shared::RenderCtx::with_fn_map(&self.fn_map)
    }
}
