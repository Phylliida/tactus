//! Orchestrates Lean file generation and verification.
//!
//! Build a `Vec<Command>` via the AST, pretty-print once, and invoke Lean
//! on the resulting `.lean` file. Per-declaration writers live in
//! `to_lean_fn` / `sst_to_lean`; this file only sequences them and handles
//! artifact I/O.

use std::path::{Path, PathBuf};
use vir::ast::*;
use vir::sst::{FuncCheckSst, FunctionSst};
use crate::dep_order::{self, FnGroup};
use crate::lean_ast::Command;
use crate::lean_pp::pp_commands;
use crate::lean_process;
use crate::prelude::TACTUS_PRELUDE;
use crate::project;
use crate::sst_to_lean;
use crate::to_lean_fn::{self, LeanSourceMap};
use crate::to_lean_type::{lean_name, sanitize, short_name};

// ── Artifact location ──────────────────────────────────────────────────

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
/// Structure: `{root}/{crate}/{fn_lean_name_with_underscores}.lean`.
/// Dots in Lean names (module separators) become `__` so the file name stays flat.
fn lean_file_path(crate_name: &str, fn_path: &vir::ast::Path) -> PathBuf {
    let ns = sanitize(crate_name);
    let leaf = lean_name(fn_path).replace('.', "__");
    lean_out_root().join(ns).join(format!("{}.lean", leaf))
}

fn write_lean_file(path: &Path, source: &str) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)
            .map_err(|e| format!("could not create {}: {}", parent.display(), e))?;
    }
    std::fs::write(path, source)
        .map_err(|e| format!("could not write {}: {}", path.display(), e))
}

// ── Preamble builder ───────────────────────────────────────────────────

/// Build the shared preamble: imports, prelude, namespace-open, and entity
/// declarations transitively referenced by `root_fns`. Returns a (preamble
/// Vec, namespace) pair. Callers append the theorem command and the matching
/// `end <ns>` command.
///
/// Note: reference collection walks VIR-AST bodies. For exec fns the SST
/// body may reference spec fns not reachable from the VIR body alone; the
/// first slice only hits pure arithmetic so this isn't an issue yet. When
/// `sst_to_lean` starts emitting calls into spec code, extend this to also
/// walk the SST body.
fn krate_preamble(
    krate: &KrateX,
    imports: &[String],
    crate_name: &str,
    root_fns: &[&FunctionX],
) -> (Vec<Command>, String) {
    let mut cmds: Vec<Command> = Vec::new();
    for imp in imports {
        cmds.push(Command::Import(imp.clone()));
    }
    cmds.push(Command::Raw(TACTUS_PRELUDE.to_string()));

    let ns = sanitize(crate_name);
    cmds.push(Command::NamespaceOpen(ns.clone()));

    let all_fns: Vec<&FunctionX> = krate.functions.iter().map(|f| &f.x).collect();
    let spec_fn_map = dep_order::build_spec_fn_map(&all_fns);
    let refs = dep_order::collect_references(&spec_fn_map, root_fns);
    let method_lookup: std::collections::HashMap<&Fun, &FunctionX> = all_fns.iter()
        .map(|f| (&f.name, *f))
        .collect();

    for tr in &krate.traits {
        if refs.traits.contains(short_name(&tr.x.name)) {
            cmds.push(Command::Class(to_lean_fn::trait_to_ast(&tr.x, &method_lookup)));
        }
    }

    for dt in &krate.datatypes {
        if let Dt::Path(p) = &dt.x.name {
            if refs.datatypes.contains(short_name(p)) {
                if let Some(d) = to_lean_fn::datatype_to_ast(&dt.x) {
                    cmds.push(Command::Datatype(d));
                }
            }
        }
    }

    let groups = dep_order::order_spec_fns(&spec_fn_map, &all_fns, root_fns);
    for group in &groups {
        match group {
            FnGroup::Single(f) => {
                cmds.push(Command::Def(to_lean_fn::spec_fn_to_ast(f)));
            }
            FnGroup::Mutual(fns) => {
                let inner: Vec<Command> = fns.iter()
                    .map(|f| Command::Def(to_lean_fn::spec_fn_to_ast(f)))
                    .collect();
                cmds.push(Command::Mutual(inner));
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
            cmds.push(Command::Instance(
                to_lean_fn::trait_impl_to_ast(&ti.x, &method_impls, &assoc_types)
            ));
        }
    }

    (cmds, ns)
}

// ── Check results ──────────────────────────────────────────────────────

#[must_use]
pub enum CheckResult {
    /// Lean verified the proof successfully.
    Success,
    /// Lean rejected the proof. The string is a formatted error message.
    Failed(String),
    /// Lean could not be invoked (not installed, project missing, etc.)
    Error(String),
}

// ── Entry points ───────────────────────────────────────────────────────

/// Check a tactic proof fn.
pub fn check_proof_fn(
    krate: &KrateX,
    proof_fn: &FunctionX,
    tactic_body: &str,
    imports: &[String],
    crate_name: &str,
) -> CheckResult {
    let (mut cmds, ns) = krate_preamble(krate, imports, crate_name, &[proof_fn]);
    cmds.push(Command::Theorem(to_lean_fn::proof_fn_to_ast(proof_fn, tactic_body)));
    cmds.push(Command::NamespaceClose(ns));

    let rendered = pp_commands(&cmds);
    let source_map = LeanSourceMap {
        fn_name: short_name(&proof_fn.name.path).to_string(),
        // One proof fn per file → exactly one `Tactic::Raw` emission.
        tactic_start_line: rendered.tactic_starts.first().copied().unwrap_or(0),
        tactic_line_count: tactic_body.lines().count().max(1),
    };

    let file_path = lean_file_path(crate_name, &proof_fn.name.path);
    if let Err(e) = write_lean_file(&file_path, &rendered.text) {
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
                .map(|d| lean_process::format_error(d, &source_map))
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

/// Check an exec fn via SST → WP → Lean.
pub fn check_exec_fn(
    krate: &KrateX,
    vir_fn: &FunctionX,
    fn_sst: &FunctionSst,
    check: &FuncCheckSst,
    imports: &[String],
    crate_name: &str,
) -> CheckResult {
    if let Err(reason) = sst_to_lean::supported_body(check) {
        return CheckResult::Failed(format!(
            "tactus_auto: {} (first slice supports only straight-line exec fns)",
            reason
        ));
    }

    let (mut cmds, ns) = krate_preamble(krate, imports, crate_name, &[vir_fn]);
    cmds.push(Command::Theorem(sst_to_lean::exec_fn_theorem_to_ast(fn_sst, check)));
    cmds.push(Command::NamespaceClose(ns));

    let rendered = pp_commands(&cmds);

    let file_path = lean_file_path(crate_name, &vir_fn.name.path);
    if let Err(e) = write_lean_file(&file_path, &rendered.text) {
        return CheckResult::Error(e);
    }

    let dir = project::default_project_dir();
    let lake_dir = if project::project_ready(&dir) { Some(dir.as_path()) } else { None };
    let result = lean_process::check_lean_file(&file_path, lake_dir);

    // Exec fns don't have a user-written tactic body yet (see TODO in
    // `sst_to_lean::exec_fn_theorem_to_ast`). Use an empty source map.
    let empty = LeanSourceMap {
        fn_name: short_name(&vir_fn.name.path).to_string(),
        tactic_start_line: 0,
        tactic_line_count: 0,
    };

    match result {
        Ok(r) if r.success => CheckResult::Success,
        Ok(r) => {
            let errors: Vec<_> = r.diagnostics.iter()
                .filter(|d| d.severity == "error")
                .map(|d| lean_process::format_error(d, &empty))
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

