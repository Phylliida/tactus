//! Orchestrates Lean file generation and verification.
//!
//! This is the main entry point for lean_verify. Given a VIR krate and a
//! proof fn, it generates a complete .lean file, invokes Lean, and returns
//! a formatted error message on failure.

use vir::ast::*;
use crate::dep_order::{self, FnGroup};
use crate::lean_process;
use crate::prelude::TACTUS_PRELUDE;
use crate::project;
use crate::to_lean_fn;
use crate::to_lean_type::{short_name, find_collisions};

/// Result of checking a proof fn through Lean.
pub enum CheckResult {
    /// Lean verified the proof successfully.
    Success,
    /// Lean rejected the proof. The string is a formatted error message.
    Failed(String),
    /// Lean could not be invoked (not installed, project missing, etc.)
    Error(String),
}

/// Check a tactic proof fn by generating Lean and invoking the Lean checker.
///
/// This is the single entry point for the verifier. It handles:
/// - Collecting referenced spec fns, datatypes, and traits from the krate
/// - Generating the complete .lean file with proper declaration ordering
/// - Invoking Lean (via Lake project if available, bare lean otherwise)
/// - Formatting error diagnostics with source map and goal states
pub fn check_proof_fn(
    krate: &KrateX,
    proof_fn: &FunctionX,
    tactic_body: &str,
    imports: &[String],
    namespace: Option<&str>,
) -> CheckResult {
    let lean_source = generate_lean(krate, proof_fn, tactic_body, imports, namespace);

    // Check for unsupported features (soundness): count "sorry" in the generated
    // definitions (everything before the theorem), excluding the tactic body which
    // legitimately uses sorry for user-written `assume`.
    let defs_end = lean_source.text.rfind(":= by\n").unwrap_or(lean_source.text.len());
    let defs_text = &lean_source.text[..defs_end];
    let sorry_count = defs_text.matches("sorry").count();
    if sorry_count > 0 {
        let fn_short = short_name(&proof_fn.name.path);
        return CheckResult::Failed(format!(
            "Lean translation for {} contains {} unsupported VIR feature(s) (sorry).\n\
             The generated Lean may not faithfully represent the VIR definition.",
            fn_short, sorry_count,
        ));
    }

    // Invoke Lean
    let result = match project::default_project_dir() {
        Some(dir) if project::project_ready(&dir) => {
            lean_process::check_lean_in_project(&lean_source.text, &dir)
        }
        _ => lean_process::check_lean_stdin(&lean_source.text),
    };

    match result {
        Ok(r) if r.success => CheckResult::Success,
        Ok(r) => {
            let errors: Vec<_> = r.diagnostics.iter()
                .filter(|d| d.severity == "error")
                .map(|d| lean_process::format_error(d, &lean_source.source_map))
                .collect();
            let fn_short = short_name(&proof_fn.name.path);
            CheckResult::Failed(format!(
                "Lean tactic failed for {}:\n\n{}",
                fn_short, errors.join("\n"),
            ))
        }
        Err(e) => CheckResult::Error(e),
    }
}

/// Generated Lean source with source map for error reporting.
struct LeanOutput {
    text: String,
    source_map: to_lean_fn::LeanSourceMap,
}

/// Generate a complete .lean file from a VIR krate and proof fn.
fn generate_lean(
    krate: &KrateX,
    proof_fn: &FunctionX,
    tactic_body: &str,
    imports: &[String],
    namespace: Option<&str>,
) -> LeanOutput {
    let mut out = String::new();

    // Imports before any commands (Lean requirement)
    for imp in imports {
        out.push_str("import ");
        out.push_str(imp);
        out.push('\n');
    }
    if !imports.is_empty() { out.push('\n'); }

    out.push_str(TACTUS_PRELUDE);

    if let Some(ns) = namespace {
        out.push_str("namespace ");
        out.push_str(ns);
        out.push_str("\n\n");
    }

    let all_fns: Vec<&FunctionX> = krate.functions.iter().map(|f| &f.x).collect();
    let spec_fn_map = dep_order::build_spec_fn_map(&all_fns);

    // Collect all referenced entities (shares spec_fn_map with order_spec_fns)
    let refs = dep_order::collect_references(&spec_fn_map, &[proof_fn]);

    // Build collision set: short names that appear more than once
    let all_names = krate.functions.iter().map(|f| short_name(&f.x.name.path))
        .chain(krate.datatypes.iter().filter_map(|d| match &d.x.name {
            Dt::Path(p) => Some(short_name(p)),
            _ => None,
        }))
        .chain(krate.traits.iter().map(|t| short_name(&t.x.name)));
    let collisions = find_collisions(all_names);

    // Function lookup for trait class method signatures
    let method_lookup: std::collections::HashMap<&Fun, &FunctionX> = all_fns.iter()
        .map(|f| (&f.name, *f))
        .collect();

    // 1. Traits
    for tr in &krate.traits {
        if refs.traits.contains(short_name(&tr.x.name)) {
            to_lean_fn::write_trait(&mut out, &tr.x, &method_lookup, &collisions);
            out.push('\n');
        }
    }

    // 2. Datatypes
    for dt in &krate.datatypes {
        if let Dt::Path(p) = &dt.x.name {
            if refs.datatypes.contains(short_name(p)) {
                to_lean_fn::write_datatype(&mut out, &dt.x, &collisions);
                out.push('\n');
            }
        }
    }

    // 3. Spec fns (topologically sorted, with mutual recursion groups)
    let groups = dep_order::order_spec_fns(&spec_fn_map, &all_fns, &[proof_fn]);
    for group in &groups {
        match group {
            FnGroup::Single(f) => {
                to_lean_fn::write_spec_fn(&mut out, f, &collisions);
                out.push('\n');
            }
            FnGroup::Mutual(fns) => {
                out.push_str("mutual\n");
                for f in fns {
                    to_lean_fn::write_spec_fn(&mut out, f, &collisions);
                    out.push('\n');
                }
                out.push_str("end\n\n");
            }
        }
    }

    // 4. Proof fn theorem
    let tactic_start_line = to_lean_fn::write_proof_fn(&mut out, proof_fn, tactic_body, &collisions);
    let source_map = to_lean_fn::LeanSourceMap {
        fn_name: short_name(&proof_fn.name.path).to_string(),
        tactic_start_line,
        tactic_line_count: tactic_body.lines().count().max(1),
    };
    out.push('\n');

    if let Some(ns) = namespace {
        out.push_str("end ");
        out.push_str(ns);
        out.push('\n');
    }

    LeanOutput { text: out, source_map }
}
