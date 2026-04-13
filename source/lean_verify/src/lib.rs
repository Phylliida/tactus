pub mod dep_order;
pub mod generate;
pub mod lean_process;
pub mod prelude;
pub mod project;
pub mod to_lean_expr;
pub mod to_lean_fn;
pub mod to_lean_type;

// Re-export the main entry point
pub use generate::{check_proof_fn, CheckResult};
