//! Orchestrates Lean file generation and verification.
//!
//! This is the main entry point for lean_verify. Given a VIR krate and a
//! proof fn, it generates a complete .lean file, invokes Lean, and returns
//! a formatted error message on failure.

use std::path::{Path, PathBuf};
use vir::ast::*;
use vir::sst::{FuncCheckSst, FunctionSst};
use crate::dep_order::{self, FnGroup};
use crate::lean_process;
use crate::prelude::TACTUS_PRELUDE;
use crate::project;
use crate::sst_to_lean;
use crate::to_lean_fn;
use crate::to_lean_type::{lean_name, sanitize_ident, short_name};

/// Where to write generated Lean artifacts.
///
/// Priority: `$TACTUS_LEAN_OUT` → `$CARGO_TARGET_DIR/tactus-lean` → `./target/tactus-lean`.
/// The last fallback is CWD-relative, which works correctly when Tactus is
/// invoked from a Cargo project root (cargo's convention) but will scatter
/// artifacts if invoked from elsewhere. Set `$TACTUS_LEAN_OUT` explicitly
/// for reproducible builds outside Cargo.
fn lean_out_root() -> PathBuf {
    if let Ok(dir) = std::env::var("TACTUS_LEAN_OUT") {
        return PathBuf::from(dir);
    }
    if let Ok(dir) = std::env::var("CARGO_TARGET_DIR") {
        return PathBuf::from(dir).join("tactus-lean");
    }
    PathBuf::from("target").join("tactus-lean")
}

/// Compute the on-disk artifact path for a given function.
///
/// Structure: `{root}/{crate}/{fn_lean_name_with_underscores}.lean`.
/// Dots in Lean names (module separators) become `__` so the file name stays flat.
fn lean_file_path(crate_name: &str, fn_path: &vir::ast::Path) -> PathBuf {
    let ns = sanitize_ident(crate_name);
    let leaf = lean_name(fn_path).replace('.', "__");
    lean_out_root().join(ns).join(format!("{}.lean", leaf))
}

/// Write `source` to `path`, creating parents as needed.
fn write_lean_file(path: &Path, source: &str) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)
            .map_err(|e| format!("could not create {}: {}", parent.display(), e))?;
    }
    std::fs::write(path, source)
        .map_err(|e| format!("could not write {}: {}", path.display(), e))
}

/// Emit the shared preamble (imports, prelude, namespace opener, and entity
/// declarations transitively referenced by `root_fns`). Returns the opened
/// namespace so the caller can emit a matching `end <ns>` after the theorem.
///
/// Both `generate_lean` (proof fns) and `generate_lean_exec` (exec fns) use
/// this — they differ only in the theorem that comes after.
///
/// Note: reference collection walks VIR-AST bodies. For exec fns the SST
/// body may reference spec fns not reachable from the VIR body alone; the
/// first slice only hits pure arithmetic so this isn't an issue yet. When
/// `sst_to_lean` starts emitting calls into spec code, extend this to also
/// walk the SST body.
fn write_krate_preamble(
    out: &mut String,
    krate: &KrateX,
    imports: &[String],
    crate_name: &str,
    root_fns: &[&FunctionX],
) -> String {
    for imp in imports {
        out.push_str("import ");
        out.push_str(imp);
        out.push('\n');
    }
    if !imports.is_empty() { out.push('\n'); }

    out.push_str(TACTUS_PRELUDE);

    let ns = sanitize_ident(crate_name);
    out.push_str("namespace ");
    out.push_str(&ns);
    out.push('\n');

    let all_fns: Vec<&FunctionX> = krate.functions.iter().map(|f| &f.x).collect();
    let spec_fn_map = dep_order::build_spec_fn_map(&all_fns);
    let refs = dep_order::collect_references(&spec_fn_map, root_fns);
    let method_lookup: std::collections::HashMap<&Fun, &FunctionX> = all_fns.iter()
        .map(|f| (&f.name, *f))
        .collect();

    for tr in &krate.traits {
        if refs.traits.contains(short_name(&tr.x.name)) {
            to_lean_fn::write_trait(out, &tr.x, &method_lookup);
            out.push('\n');
        }
    }

    for dt in &krate.datatypes {
        if let Dt::Path(p) = &dt.x.name {
            if refs.datatypes.contains(short_name(p)) {
                to_lean_fn::write_datatype(out, &dt.x);
                out.push('\n');
            }
        }
    }

    let groups = dep_order::order_spec_fns(&spec_fn_map, &all_fns, root_fns);
    for group in &groups {
        match group {
            FnGroup::Single(f) => {
                to_lean_fn::write_spec_fn(out, f);
                out.push('\n');
            }
            FnGroup::Mutual(fns) => {
                out.push_str("mutual\n");
                for f in fns {
                    to_lean_fn::write_spec_fn(out, f);
                    out.push('\n');
                }
                out.push_str("end\n\n");
            }
        }
    }

    for ti in &krate.trait_impls {
        if !refs.traits.contains(short_name(&ti.x.trait_path)) { continue; }
        let method_impls: Vec<&FunctionX> = all_fns.iter()
            .filter(|f| matches!(&f.kind, FunctionKind::TraitMethodImpl { impl_path, .. }
                if impl_path == &ti.x.impl_path))
            .copied()
            .collect();
        let assoc_types: Vec<&AssocTypeImplX> = krate.assoc_type_impls.iter()
            .filter(|a| a.x.impl_path == ti.x.impl_path)
            .map(|a| &a.x)
            .collect();
        if !method_impls.is_empty() || !assoc_types.is_empty() {
            to_lean_fn::write_trait_impl(out, &ti.x, &method_impls, &assoc_types);
            out.push('\n');
        }
    }

    ns
}

/// Result of checking a proof fn through Lean.
#[must_use]
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
    crate_name: &str,
) -> CheckResult {
    let lean_source = generate_lean(krate, proof_fn, tactic_body, imports, crate_name);

    // Write the generated Lean to disk as a build artifact, then invoke Lean on it.
    // This gives (a) debuggable on-disk output, (b) real file paths in Lean's
    // diagnostics, and (c) a foundation for Lake-managed `.olean` caching later.
    let file_path = lean_file_path(crate_name, &proof_fn.name.path);
    if let Err(e) = write_lean_file(&file_path, &lean_source.text) {
        return CheckResult::Error(e);
    }

    let dir = project::default_project_dir();
    let lake_dir = if project::project_ready(&dir) { Some(dir.as_path()) } else { None };
    let result = lean_process::check_lean_file(&file_path, lake_dir);

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
    crate_name: &str,
) -> LeanOutput {
    let mut out = String::new();
    let ns = write_krate_preamble(&mut out, krate, imports, crate_name, &[proof_fn]);

    let tactic_start_line = to_lean_fn::write_proof_fn(&mut out, proof_fn, tactic_body);
    let source_map = to_lean_fn::LeanSourceMap {
        fn_name: short_name(&proof_fn.name.path).to_string(),
        tactic_start_line,
        tactic_line_count: tactic_body.lines().count().max(1),
    };
    out.push('\n');

    out.push_str("end ");
    out.push_str(&ns);
    out.push('\n');

    LeanOutput { text: out, source_map }
}

/// Check an exec fn by generating its body VC through SST → Lean WP and invoking Lean.
///
/// First-slice entry point for Track B. Takes the VIR krate (for prelude +
/// spec fn dependencies), the VIR function (for imports), and the SST view
/// (`FunctionSst` + `FuncCheckSst`) which carries the body in a form where
/// VC generation is tractable.
pub fn check_exec_fn(
    krate: &KrateX,
    vir_fn: &FunctionX,
    fn_sst: &FunctionSst,
    check: &FuncCheckSst,
    imports: &[String],
    crate_name: &str,
) -> CheckResult {
    // Bail out clearly if the body has shapes we haven't implemented yet.
    if let Err(reason) = sst_to_lean::supported_body(check) {
        return CheckResult::Failed(format!(
            "tactus_auto: {} (first slice supports only straight-line exec fns)",
            reason
        ));
    }

    let lean_source = generate_lean_exec(krate, vir_fn, fn_sst, check, imports, crate_name);

    let file_path = lean_file_path(crate_name, &vir_fn.name.path);
    if let Err(e) = write_lean_file(&file_path, &lean_source) {
        return CheckResult::Error(e);
    }

    let dir = project::default_project_dir();
    let lake_dir = if project::project_ready(&dir) { Some(dir.as_path()) } else { None };
    let result = lean_process::check_lean_file(&file_path, lake_dir);

    // Empty source map — exec fns don't have a tactic body to map into yet.
    // `format_error` gracefully handles zero-length tactic ranges.
    let empty_source_map = to_lean_fn::LeanSourceMap {
        fn_name: short_name(&vir_fn.name.path).to_string(),
        tactic_start_line: 0,
        tactic_line_count: 0,
    };

    match result {
        Ok(r) if r.success => CheckResult::Success,
        Ok(r) => {
            let errors: Vec<_> = r.diagnostics.iter()
                .filter(|d| d.severity == "error")
                .map(|d| lean_process::format_error(d, &empty_source_map))
                .collect();
            CheckResult::Failed(format!(
                "Lean tactus_auto failed for {}:\n\n{}",
                short_name(&vir_fn.name.path),
                errors.join("\n"),
            ))
        }
        Err(e) => CheckResult::Error(e),
    }
}

/// Emit the full Lean source for an exec fn body check.
/// Shares the imports/prelude/traits/datatypes/spec-fns preamble with the
/// proof-fn path; differs only in the final theorem (WP from SST).
fn generate_lean_exec(
    krate: &KrateX,
    vir_fn: &FunctionX,
    fn_sst: &FunctionSst,
    check: &FuncCheckSst,
    imports: &[String],
    crate_name: &str,
) -> String {
    let mut out = String::new();
    let ns = write_krate_preamble(&mut out, krate, imports, crate_name, &[vir_fn]);

    sst_to_lean::write_exec_fn_theorem(&mut out, fn_sst, check);
    out.push('\n');

    out.push_str("end ");
    out.push_str(&ns);
    out.push('\n');

    out
}
