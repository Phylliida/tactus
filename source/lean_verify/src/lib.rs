pub mod broadcast_collect;
pub mod call_inlining;
pub mod crate_defs;
pub mod dep_order;
pub mod driver_client;
pub mod expr_shared;
pub mod emit_ctx;
pub mod generate;
pub mod impl_subst;
pub mod inline_spec;
pub mod lean_ast;
pub mod lean_name;
pub mod lean_pp;
pub mod lean_process;
pub mod link_discharge;
pub mod wf_synth;
pub mod loop_normalize;
pub mod mut_ref_normalize;
pub mod nonempty;
pub mod obligation_naming;
pub mod prelude;
pub mod project;
pub mod ret_subst;
pub mod sanity;
pub mod script;
pub mod tactic_select;
pub mod source_util;
pub mod sourcemap;
pub mod sst_serialize;
pub mod sst_to_lean;
#[cfg(test)]
pub(crate) mod test_fixtures;
pub mod to_lean_expr;
pub mod to_lean_fn;
pub mod to_lean_sst_expr;
pub mod trait_emit;
pub mod to_lean_type;
pub mod typed_expr;

// Re-export the main entry points
pub use generate::{
    check_exec_fn, check_package, check_proof_fn, emit_exec_fn, emit_proof_fn,
    prime_lean_driver, sourcemap_path, PrimeJob,
    CheckResult, DiagLocation, EmitOutput, PackageGateReport, TactusDiag,
    closer_census_report,
};
pub use to_lean_fn::LeanSourceMap;
pub use sourcemap::{Sidecar, SidecarFn};

// Golden tripwire for the bootstrap mirror types (N2) — see the
// test file header.
#[cfg(test)]
#[path = "tests/bootstrap_coverage.rs"]
mod bootstrap_coverage_tests;
