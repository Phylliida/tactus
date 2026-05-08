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
use crate::sanity;
use crate::sst_to_lean;
use crate::to_lean_fn::{self, LeanSourceMap};
use crate::to_lean_type::{lean_name, sanitize, short_name};

// ── BitVec-mode Int instances (#130) ───────────────────────────────────
//
// Lean has no `HXor Int Int Int` etc. by default. Tactus needs them
// only for files that use `assert(P) by(bit_vector)` — Verus's
// ast_to_sst pre-injects an Int-mode `Assume(ens)` before each
// AssertBitVector, and the post-assert continuation theorems contain
// `x ^^^ y` (bitwise xor) for `x, y : Int`. Without these instances,
// those theorems fail to typecheck.
//
// Defined here (not in TactusPrelude) so other generated files don't
// inherit the wonky-for-negative-Int semantics. Emitted as a single
// `Command::Raw` block, conditionally per-file based on
// `ExecFnTheorems::needs_bitvec_instances`.
//
// For ACTUAL bitwise reasoning, use `assert(P) by(bit_vector)` —
// Tactus renders the goal in BitVec mode where `^^^` etc. resolve
// to BitVec instances with proper bit-vector semantics.
const BITVEC_INT_INSTANCES: &str = "\
-- HXor/HAnd/HOr/HShiftLeft/HShiftRight Int instances (#130).
-- Conditionally emitted for files using `by(bit_vector)`.
-- Mathlib.Data.BitVec is imported conditionally above (in the
-- preamble's import section) so it's available here.
instance : HXor Int Int Int := ⟨fun a b => ((a.toNat ^^^ b.toNat : Nat) : Int)⟩
instance : HAnd Int Int Int := ⟨fun a b => ((a.toNat &&& b.toNat : Nat) : Int)⟩
instance : HOr Int Int Int := ⟨fun a b => ((a.toNat ||| b.toNat : Nat) : Int)⟩
instance : HShiftLeft Int Int Int := ⟨fun a b => ((a.toNat <<< b.toNat : Nat) : Int)⟩
instance : HShiftRight Int Int Int := ⟨fun a b => ((a.toNat >>> b.toNat : Nat) : Int)⟩
";

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

/// Codegen mode for `krate_preamble` — distinguishes the two entry
/// points (proof fns vs exec fns) and, for exec fns, whether the
/// file uses `assert(P) by(bit_vector)`.
///
/// Replaces a pair of correlated `bool` parameters whose valid
/// combinations were `(false, false)` for proof fns and
/// `(true, _)` for exec fns. The enum makes the correlation
/// structural — there's no `(false, true)` to worry about, and
/// each call site says what it is rather than encoding it as
/// positional bools.
enum PreambleConfig {
    /// Proof fns: native match rendering (no accessor fns), no
    /// bitvec instance emission. Emitting accessors for types
    /// with non-Inhabited fields breaks Lean elaboration even
    /// when unused, so the proof-fn path keeps them off.
    ProofFn,
    /// Exec fns: emit accessor fns for desugared match (via
    /// `IsVariant` / `Field`). `needs_bitvec` is `true` when
    /// the fn used `assert(P) by(bit_vector)` (#130) — adds
    /// `import Mathlib.Data.BitVec` and the
    /// `HXor`/`HAnd`/`HOr`/`HShiftLeft`/`HShiftRight Int Int Int`
    /// instances. Kept out of the default prelude so non-bitvec
    /// files don't pay the cost (Mathlib.Data.BitVec's simp
    /// lemmas can change closing behavior of unrelated proof
    /// fns).
    ExecFn { needs_bitvec: bool },
}

impl PreambleConfig {
    /// Whether the preamble should emit per-variant accessor fns
    /// for multi-variant inductives.
    fn emit_accessors(&self) -> bool {
        matches!(self, PreambleConfig::ExecFn { .. })
    }

    /// Whether the preamble should include `Mathlib.Data.BitVec` /
    /// `Lean.Elab.Tactic.BVDecide` imports plus the Int-bitwise
    /// instance block.
    fn bitvec_mode(&self) -> bool {
        matches!(self, PreambleConfig::ExecFn { needs_bitvec: true })
    }
}

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
    config: PreambleConfig,
) -> (Vec<Command>, String) {
    let bitvec_mode = config.bitvec_mode();
    let emit_accessors = config.emit_accessors();

    let mut cmds: Vec<Command> = Vec::new();
    for imp in imports {
        cmds.push(Command::Import(imp.clone()));
    }
    if bitvec_mode {
        cmds.push(Command::Import("Mathlib.Data.BitVec".to_string()));
        // Lean core's full SAT-backed bit-vector decision procedure
        // (#130 follow-up). Lives at `Lean/Elab/Tactic/BVDecide` in
        // the v4.25.0 toolchain — must be imported explicitly; the
        // top-level `import Lean` doesn't pull it in.
        cmds.push(Command::Import("Lean.Elab.Tactic.BVDecide".to_string()));
    }
    cmds.push(Command::Raw(TACTUS_PRELUDE.to_string()));
    if bitvec_mode {
        cmds.push(Command::Raw(BITVEC_INT_INSTANCES.to_string()));
    }

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

    // Filter datatypes to those referenced by the proof/exec fns and
    // not synthesized closure types (#93), then transitively close over
    // field-type references and group into SCCs so mutually recursive
    // datatypes (#109) emit as `mutual ... end` blocks.
    let referenced_dts = collect_referenced_datatypes(krate, &refs);
    for group in dep_order::order_datatypes(&referenced_dts) {
        cmds.extend(to_lean_fn::datatype_group_to_cmds(&group, emit_accessors));
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
    /// Lean verified the proof successfully. `warnings` carries
    /// non-fatal diagnostics — currently used for `assume(P)` site
    /// notifications (each `assume` is a soundness escape hatch
    /// backed by `sorry`).
    Success { warnings: Vec<String> },
    /// Lean rejected the proof. The string is a formatted error
    /// message. `warnings` carries non-fatal diagnostics from the
    /// same crate (assume sites, etc.) that are worth surfacing
    /// even when verification itself fails.
    Failed { error: String, warnings: Vec<String> },
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
    // Proof fns render match expressions natively (spec fns
    // preserve match through to VIR-AST), so accessor fns are
    // unnecessary and would fail elaboration for enum types whose
    // field types lack Inhabited.
    let (mut cmds, ns) = krate_preamble(
        krate, imports, crate_name, &[proof_fn], PreambleConfig::ProofFn,
    );
    cmds.push(Command::Theorem(to_lean_fn::proof_fn_to_ast(proof_fn, tactic_body)));
    cmds.push(Command::NamespaceClose(ns));

    debug_check(&cmds);

    let rendered = pp_commands(&cmds);
    let source_map = LeanSourceMap::ProofFn {
        fn_name: short_name(&proof_fn.name.path).to_string(),
        // One proof fn per file → exactly one `Tactic::Raw` emission.
        tactic_start_line: rendered.landmarks.tactic_starts.first().copied().unwrap_or(0),
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
        Ok(r) if r.success => CheckResult::Success { warnings: vec![] },
        Ok(r) => {
            let errors: Vec<_> = r.diagnostics.iter()
                .filter(|d| d.severity == "error")
                .map(|d| lean_process::format_error(d, &source_map))
                .collect();
            let fn_short = short_name(&proof_fn.name.path);
            CheckResult::Failed {
                error: format!("Lean tactic failed for {}:\n\n{}", fn_short, errors.join("\n")),
                warnings: vec![],
            }
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
    // Collect `assume(P)` sites first so warnings surface even when
    // the rest of the codegen rejects the fn. Each `assume` is a
    // soundness escape hatch — `assume(P)` enters its expression
    // as a hypothesis without a backing proof obligation, so users
    // need a visible reminder per site. Walks the VIR-AST body
    // (`vir_fn.body`) rather than the SST so synthetic
    // `StmX::Assume` injected by Verus's later passes (overflow,
    // call-ensures) doesn't produce false positives.
    let warnings: Vec<String> = vir_fn.body.as_ref()
        .map(|body| sst_to_lean::collect_assume_sites(body))
        .unwrap_or_default()
        .iter()
        .map(|span| format!(
            "unproved assumption at {}: backed by an unverified hypothesis (`assume(P)` \
             enters the spec as fact without a proof). Replace with a proven \
             `assert(P) by {{ ... }}` before relying on this in production.",
            sst_to_lean::format_span_loc(span),
        ))
        .collect();

    let exec_fn = match sst_to_lean::exec_fn_theorems_to_ast(krate, fn_sst, check) {
        Ok(r) => r,
        Err(reason) => return CheckResult::Failed {
            error: format!(
                "tactus_auto: {} (first slice supports only straight-line exec fns)",
                reason,
            ),
            warnings,
        },
    };

    // Exec fns lower matches to if-chains over `IsVariant` and
    // `Field`, which the SST renderer routes to the synthesised
    // accessor fns — so the preamble must include them.
    let (mut cmds, ns) = krate_preamble(
        krate, imports, crate_name, &[vir_fn],
        PreambleConfig::ExecFn { needs_bitvec: exec_fn.needs_bitvec_instances },
    );

    for theorem in exec_fn.theorems {
        cmds.push(Command::Theorem(theorem));
    }
    cmds.push(Command::NamespaceClose(ns));

    debug_check(&cmds);

    let rendered = pp_commands(&cmds);

    let file_path = lean_file_path(crate_name, &vir_fn.name.path);
    if let Err(e) = write_lean_file(&file_path, &rendered.text) {
        return CheckResult::Error(e);
    }

    let dir = project::default_project_dir();
    let lake_dir = if project::project_ready(&dir) { Some(dir.as_path()) } else { None };
    let result = lean_process::check_lean_file(&file_path, lake_dir);

    // Exec fns map errors via `span_marks` populated by the pp's
    // `SpanMark` walker (#51 source mapping) — Rust source
    // location for each obligation in `lower_wp`'s output.
    let source_map = LeanSourceMap::ExecFn {
        fn_name: short_name(&vir_fn.name.path).to_string(),
        span_marks: rendered.landmarks.span_marks.clone(),
    };

    match result {
        Ok(r) if r.success => CheckResult::Success { warnings },
        Ok(r) => {
            let errors: Vec<_> = r.diagnostics.iter()
                .filter(|d| d.severity == "error")
                .map(|d| lean_process::format_error(d, &source_map))
                .collect();
            CheckResult::Failed {
                error: format!(
                    "Lean tactus_auto failed for {}:\n\n{}\n\n\
                     (generated .lean file: {})",
                    short_name(&vir_fn.name.path),
                    errors.join("\n"),
                    file_path.display(),
                ),
                warnings,
            }
        }
        Err(e) => CheckResult::Error(e),
    }
}

/// Collect the datatypes that need Lean declarations emitted: the ones
/// directly referenced by the proof/exec fns plus their transitive
/// closure over field-type references.
///
/// `dep_order::collect_references` walks fn parameter / return / require /
/// ensure / body types and collects datatype names — but it doesn't
/// recurse into datatype variant fields. So a fn that references `Tree`
/// only via `(t: Tree) → ...` wouldn't surface `Forest` even when `Tree`'s
/// variant has a `Box<Forest>` field. Without that, mutually recursive
/// datatypes (#109) would emit only one half of the SCC and Lean would
/// reject the missing half.
///
/// Output is in original `krate.datatypes` order so emission is stable
/// across runs. Filters out tuples (no decl needed) and Verus-synthesized
/// `anonymous_closure%`-prefixed types (#93).
fn collect_referenced_datatypes<'a>(
    krate: &'a vir::ast::KrateX,
    refs: &dep_order::References<'_>,
) -> Vec<&'a vir::ast::DatatypeX> {
    use std::collections::{HashMap, HashSet};
    let path_to_dt: HashMap<&'a vir::ast::Path, &'a vir::ast::DatatypeX> =
        krate.datatypes.iter()
            .filter_map(|dt| match &dt.x.name {
                Dt::Path(p) => {
                    let short = short_name(p);
                    if short.starts_with("anonymous_closure") { None }
                    else { Some((p, &dt.x)) }
                }
                Dt::Tuple(_) => None,
            })
            .collect();

    let mut seen: HashSet<&'a vir::ast::Path> = HashSet::new();
    let mut worklist: Vec<&'a vir::ast::Path> = path_to_dt.keys()
        .filter(|p| refs.datatypes.contains(short_name(p)))
        .copied()
        .collect();
    while let Some(p) = worklist.pop() {
        if !seen.insert(p) { continue; }
        let Some(dt) = path_to_dt.get(p) else { continue };
        for variant in dt.variants.iter() {
            for field in variant.fields.iter() {
                dep_order::walk_typ_paths(&field.a.0, &mut |q| {
                    if path_to_dt.contains_key(q) && !seen.contains(q) {
                        worklist.push(q);
                    }
                });
            }
        }
    }

    // Preserve original krate.datatypes order.
    krate.datatypes.iter()
        .filter_map(|dt| match &dt.x.name {
            Dt::Path(p) if seen.contains(p) => Some(&dt.x),
            _ => None,
        })
        .collect()
}

/// In debug builds, verify the command stream is internally consistent —
/// every `Var` in a theorem goal / def body / instance method body is
/// either a local binder, an earlier top-level definition, or a known
/// Lean/Mathlib built-in. A violation means we lost track of a
/// dependency and Lean would reject the file; panicking here points at
/// the exact identifier instead of forcing the user to decode a Lean
/// unknown-identifier error.
///
/// Compiled out of release builds.
fn debug_check(_cmds: &[Command]) {
    #[cfg(debug_assertions)]
    {
        let violations = sanity::check_references(_cmds);
        if !violations.is_empty() {
            let lines: Vec<String> = violations.iter()
                .map(|v| format!("  in `{}`: unresolved `{}`", v.context, v.name))
                .collect();
            panic!(
                "Tactus codegen produced unresolved references:\n{}\n\nThis usually means \
                 `dep_order` missed a fn while walking VIR (check `walk_expr` / `walk_place` \
                 coverage for any new ExprX/PlaceX variants).",
                lines.join("\n")
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_fixtures::empty_krate;

    /// REVIEW lens 14: `bitvec_mode = false` must NOT emit any
    /// BitVec-related preamble. Important because `Mathlib.Data.BitVec`
    /// brings in simp lemmas that change closing behavior of
    /// unrelated proof fns; conditional emission means files that
    /// don't use `by(bit_vector)` keep their previous behavior.
    #[test]
    fn krate_preamble_omits_bitvec_when_mode_false() {
        let krate = empty_krate();
        let (cmds, _ns) = krate_preamble(
            &krate, &[], "test_crate", &[], PreambleConfig::ProofFn,
        );

        // Check imports: no Mathlib.Data.BitVec, no Lean.Elab.Tactic.BVDecide.
        for cmd in &cmds {
            if let Command::Import(s) = cmd {
                assert!(s != "Mathlib.Data.BitVec",
                    "non-bitvec preamble should not import Mathlib.Data.BitVec");
                assert!(s != "Lean.Elab.Tactic.BVDecide",
                    "non-bitvec preamble should not import BVDecide");
            }
        }
        // Check Raw blocks: no actual Int-bitwise instance
        // *definitions*. Substrings like "HXor Int Int Int" appear
        // in TACTUS_PRELUDE comments explaining the design — those
        // are fine; only the executable `instance : HXor ...` lines
        // would change Lean elaboration behavior.
        for cmd in &cmds {
            if let Command::Raw(s) = cmd {
                assert!(!s.contains("instance : HXor Int Int Int"),
                    "non-bitvec preamble should not emit HXor Int instance");
                assert!(!s.contains("instance : HShiftLeft Int Int Int"),
                    "non-bitvec preamble should not emit HShiftLeft Int instance");
            }
        }
    }

    /// REVIEW lens 14 companion: `bitvec_mode = true` MUST emit the
    /// BitVec-related preamble — both imports AND the Int-bitwise
    /// instance block. Pinpoints the contract from the other side.
    #[test]
    fn krate_preamble_emits_bitvec_when_mode_true() {
        let krate = empty_krate();
        let (cmds, _ns) = krate_preamble(
            &krate, &[], "test_crate", &[],
            PreambleConfig::ExecFn { needs_bitvec: true },
        );

        let imports: Vec<&String> = cmds.iter()
            .filter_map(|c| if let Command::Import(s) = c { Some(s) } else { None })
            .collect();
        assert!(imports.iter().any(|s| s.as_str() == "Mathlib.Data.BitVec"),
            "bitvec preamble must import Mathlib.Data.BitVec; got imports: {:?}",
            imports);
        assert!(imports.iter().any(|s| s.as_str() == "Lean.Elab.Tactic.BVDecide"),
            "bitvec preamble must import Lean.Elab.Tactic.BVDecide; got imports: {:?}",
            imports);

        let raw_blob: String = cmds.iter()
            .filter_map(|c| if let Command::Raw(s) = c { Some(s.as_str()) } else { None })
            .collect::<Vec<_>>().join("\n");
        assert!(raw_blob.contains("instance : HXor Int Int Int"),
            "bitvec preamble must emit HXor Int instance");
        assert!(raw_blob.contains("instance : HShiftLeft Int Int Int"),
            "bitvec preamble must emit HShiftLeft Int instance");
    }

    /// REVIEW lens 4/3: shape-drift guard for the `bv_decide` module
    /// path. `Lean.Elab.Tactic.BVDecide` is in Lean 4 core (v4.25.0)
    /// — must be imported explicitly (top-level `import Lean` doesn't
    /// pull it in). If a future Lean toolchain bump moves this
    /// module (e.g., to a Mathlib-only path, or splits into a
    /// renamed submodule), `tactus_bit_vector`'s primary rung
    /// (`bv_decide`) silently fails to elaborate; `assert by(bit_vector)`
    /// regresses to the simp/decide fallbacks, losing SAT-backed
    /// reasoning for parameterized BitVec terms.
    ///
    /// The failing assertion's message names the fix site:
    /// `generate.rs::krate_preamble`'s `bitvec_mode` branch.
    #[test]
    fn bv_decide_import_path_pinned() {
        let krate = empty_krate();
        let (cmds, _ns) = krate_preamble(
            &krate, &[], "test_crate", &[],
            PreambleConfig::ExecFn { needs_bitvec: true },
        );

        const EXPECTED: &str = "Lean.Elab.Tactic.BVDecide";
        let bvdecide_import: Option<&String> = cmds.iter()
            .filter_map(|c| if let Command::Import(s) = c { Some(s) } else { None })
            .find(|s| s.contains("BVDecide"));
        assert_eq!(
            bvdecide_import.map(|s| s.as_str()),
            Some(EXPECTED),
            "BVDecide import path drift detected. Tactus expects \
             `{}` (Lean core, v4.25.0). Update `krate_preamble`'s \
             bitvec_mode branch in generate.rs if the toolchain has \
             moved this module.",
            EXPECTED,
        );
    }

    /// REVIEW lens 4/1: shape-drift guard for the `anonymous_closure`
    /// path prefix used by Verus to name synthesized closure types.
    /// `collect_referenced_datatypes` filters these out via
    /// `short.starts_with("anonymous_closure")` because:
    ///
    /// * `Wp::LetRaw` binds the closure as a first-class Lean lambda
    ///   (#93 slice B), not as an inductive datatype.
    /// * The synthesized closure datatypes have zero variants — Lean's
    ///   `deriving Inhabited` rejects zero-variant inductives.
    ///
    /// If Verus changes the prefix (e.g., to `closure_anon%` or some
    /// other shape), our filter silently misses, the synthesized
    /// types reach `datatype_to_cmds`, and Lean elaboration fails on
    /// the `deriving Inhabited` synthesis. The error surface (via
    /// e2e) would be obscure — this test points at the fix site
    /// directly.
    ///
    /// Verus exposes `vir::def::prefix_closure_type(i)` which we use
    /// as the canonical source of truth.
    #[test]
    fn anonymous_closure_prefix_pinned() {
        let path = vir::def::prefix_closure_type(0);
        let segment = path.segments[0].as_str();
        assert!(
            segment.starts_with("anonymous_closure"),
            "Verus closure-type prefix drift detected. Tactus's \
             `collect_referenced_datatypes` filter (in generate.rs) \
             expects synthesized closure paths to start with \
             `anonymous_closure`; Verus is now producing `{}`. \
             Update the filter substring to match.",
            segment,
        );
    }

    /// REVIEW lens 3/6: defensive check that `BITVEC_INT_INSTANCES`'
    /// HXor/HAnd/HOr/HShiftLeft/HShiftRight Int instances use `.toNat`
    /// in their bodies — which is total on `Int` (returns 0 for
    /// negatives). Tactus only emits these ops on bounded-non-negative
    /// u-type Ints, so the negative-Int path is unreachable from
    /// emitted code; but the *instances themselves* must remain total
    /// to elaborate without warning, and a future refactor switching
    /// to a partial function would silently regress this property.
    ///
    /// Documented as a soundness trade-off in DESIGN.md: the
    /// `(-1 : Int).toNat = 0` semantics means `(-1) ^^^ x = x.toNat`
    /// — wonky but total. If a future Tactus path emits these on
    /// negative Ints, the values are wrong but no panic; the wonky
    /// semantics stays a "watch out" item, not a hard error.
    #[test]
    fn bitvec_int_instances_use_to_nat_total_form() {
        // The structural property: each instance's RHS goes through
        // `.toNat` (which is total). If a maintainer changes one to
        // (e.g.) `Int.toNat!` — partial, panics on negative — the
        // test fires.
        for op in &["HXor", "HAnd", "HOr", "HShiftLeft", "HShiftRight"] {
            let instance_line: Option<&str> = BITVEC_INT_INSTANCES.lines()
                .find(|l| l.contains(&format!("instance : {} Int Int Int", op)));
            let line = instance_line.unwrap_or_else(|| panic!(
                "BITVEC_INT_INSTANCES missing instance for {}", op
            ));
            assert!(line.contains("a.toNat"),
                "{} instance must use a.toNat (total form) in its body; got: {}",
                op, line);
            assert!(line.contains("b.toNat"),
                "{} instance must use b.toNat (total form) in its body; got: {}",
                op, line);
        }
    }
}

