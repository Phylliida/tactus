pub mod call_inlining;
pub mod dep_order;
pub mod expr_shared;
pub mod generate;
pub mod impl_subst;
pub mod lean_ast;
pub mod lean_name;
pub mod lean_pp;
pub mod lean_process;
pub mod prelude;
pub mod project;
pub mod sanity;
pub mod source_util;
pub mod sst_to_lean;
#[cfg(test)]
pub(crate) mod test_fixtures;
pub mod to_lean_expr;
pub mod to_lean_fn;
pub mod to_lean_sst_expr;
pub mod to_lean_type;

// Re-export the main entry points
pub use generate::{check_exec_fn, check_proof_fn, CheckResult, DiagLocation, TactusDiag};
