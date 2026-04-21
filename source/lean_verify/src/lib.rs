pub mod dep_order;
pub mod expr_shared;
pub mod generate;
pub mod lean_ast;
pub mod lean_pp;
pub mod lean_process;
pub mod prelude;
pub mod project;
pub mod sanity;
pub mod sst_to_lean;
pub mod to_lean_expr;
pub mod to_lean_fn;
pub mod to_lean_sst_expr;
pub mod to_lean_type;

// Re-export the main entry points
pub use generate::{check_exec_fn, check_proof_fn, CheckResult};
