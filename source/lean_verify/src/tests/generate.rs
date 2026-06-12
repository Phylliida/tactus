//! Unit tests for `generate` — extracted to `src/tests/` (a `#[path]`'d
//! `mod tests` child of `generate`, so `use super::*` reaches private items).

use super::*;
use crate::lean_ast::{Expr as LExpr, PreambleFragment, Tactic, Theorem};
use crate::test_fixtures::empty_krate;

/// Build a stub Theorem with the given preamble fragments.
/// Other fields take placeholder values — these tests are only
/// about how `krate_preamble` aggregates fragments, not about
/// theorem content.
fn stub_theorem(name: &str, requires_preamble: Vec<PreambleFragment>) -> Theorem {
    Theorem {
        name: name.to_string(),
        binders: Vec::new(),
        goal: LExpr::lit_bool(true),
        tactic: Tactic::Named("tactus_auto".to_string()),
        requires_preamble,
        heartbeats: None,
        termination_by: Vec::new(),
        decreasing_by: None,
    }
}

/// Right-way #4: with no theorems, no per-fn preamble fragments
/// are emitted. The default Tactus preamble is still present
/// (TACTUS_PRELUDE) but no extra Imports / PreludeAddendums leak
/// in. Pins the "files that don't request anything pay nothing"
/// contract.
#[test]
fn krate_preamble_with_no_theorems_emits_no_extra_fragments() {
    let krate = empty_krate();
    let (cmds, _ns) = krate_preamble(
        &krate, &[], "test_crate", &[], PreambleConfig::ProofFn, &[],
        &std::collections::HashMap::new(),
        &[], None,
    );

    // The default preamble has exactly one Import-class chunk
    // (the `imports` parameter, here empty) and one Raw block
    // (TACTUS_PRELUDE). No extra Imports or Raws should appear
    // before the Namespace open from per-fn aggregation.
    let import_count = cmds.iter()
        .filter(|c| matches!(c, Command::Import(_)))
        .count();
    assert_eq!(import_count, 0,
        "no theorems → no aggregated imports; got cmds: {:?}",
        cmds.iter().map(|c| std::mem::discriminant(c)).collect::<Vec<_>>());

    // No Raw command should contain bitvec instance definitions
    // (substring check on `instance : HXor` skips comments in
    // the prelude that mention the type name — only executable
    // instance lines would matter).
    let bitvec_raw_count = cmds.iter()
        .filter_map(|c| if let Command::Raw(s) = c { Some(s) } else { None })
        .filter(|s| s.contains("instance : HXor Int Int Int"))
        .count();
    assert_eq!(bitvec_raw_count, 0,
        "no theorems → no aggregated PreludeAddendums");
}

/// Right-way #4: a theorem requesting an Import fragment causes
/// `krate_preamble` to emit that Import (in the import section,
/// before TACTUS_PRELUDE).
#[test]
fn krate_preamble_aggregates_import_fragments_from_theorems() {
    let krate = empty_krate();
    let theorems = vec![stub_theorem(
        "test_thm",
        vec![PreambleFragment::Import("Mathlib.Tactic.Polyrith".to_string())],
    )];
    let (cmds, _ns) = krate_preamble(
        &krate, &[], "test_crate", &[], PreambleConfig::ExecFn, &theorems,
        &std::collections::HashMap::new(),
        &[], None,
    );

    let imports: Vec<&str> = cmds.iter()
        .filter_map(|c| if let Command::Import(s) = c { Some(s.as_str()) } else { None })
        .collect();
    assert!(imports.contains(&"Mathlib.Tactic.Polyrith"),
        "theorem-required Import should appear in preamble; got: {:?}", imports);

    // Sanity check: the Import appears BEFORE the prelude (Lean
    // requires all imports at file top).
    let import_idx = cmds.iter().position(|c| matches!(c, Command::Import(s) if s == "Mathlib.Tactic.Polyrith"));
    let prelude_idx = cmds.iter().position(|c| matches!(c, Command::Raw(s) if s.contains("set_option")));
    assert!(import_idx < prelude_idx,
        "imports must come before TACTUS_PRELUDE");
}

/// Right-way #4: a theorem requesting a PreludeAddendum fragment
/// causes `krate_preamble` to emit that Raw block AFTER the
/// prelude (instances typically depend on the prelude's defs).
#[test]
fn krate_preamble_aggregates_prelude_addendums_after_prelude() {
    let krate = empty_krate();
    let addendum = "instance : MyClass Foo := ⟨...⟩\n";
    let theorems = vec![stub_theorem(
        "test_thm",
        vec![PreambleFragment::PreludeAddendum(addendum.to_string())],
    )];
    let (cmds, _ns) = krate_preamble(
        &krate, &[], "test_crate", &[], PreambleConfig::ExecFn, &theorems,
        &std::collections::HashMap::new(),
        &[], None,
    );

    // Find the addendum Raw and confirm it's AFTER the prelude Raw.
    let addendum_idx = cmds.iter().position(|c|
        matches!(c, Command::Raw(s) if s.contains("MyClass Foo")));
    let prelude_idx = cmds.iter().position(|c|
        matches!(c, Command::Raw(s) if s.contains("set_option")));
    assert!(addendum_idx.is_some(), "addendum should appear");
        assert!(addendum_idx > prelude_idx,
            "PreludeAddendums must come after TACTUS_PRELUDE");
}

/// Right-way #4: when multiple theorems request the same fragment,
/// `krate_preamble` emits it once (dedup). Important because the
/// common case is N exec-fn theorems all needing the same BitVec
/// preamble.
#[test]
fn krate_preamble_dedups_repeated_fragments() {
    let krate = empty_krate();
    let frag = PreambleFragment::Import("Mathlib.Data.BitVec".to_string());
    let theorems = vec![
        stub_theorem("thm1", vec![frag.clone()]),
        stub_theorem("thm2", vec![frag.clone()]),
        stub_theorem("thm3", vec![frag.clone()]),
    ];
    let (cmds, _ns) = krate_preamble(
        &krate, &[], "test_crate", &[], PreambleConfig::ExecFn, &theorems,
        &std::collections::HashMap::new(),
        &[], None,
    );

    let bitvec_imports: Vec<&str> = cmds.iter()
        .filter_map(|c| if let Command::Import(s) = c { Some(s.as_str()) } else { None })
        .filter(|s| *s == "Mathlib.Data.BitVec")
        .collect();
    assert_eq!(bitvec_imports.len(), 1,
        "duplicate fragments should emit once; got {} copies", bitvec_imports.len());
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

// RC3 (#122): `collect_referenced_datatypes` honours `extra_seed` —
// datatypes referenced only by emitted instance heads (canonically
// `DefaultHasher` in `instance : hash.BuildHasher RandomState
// DefaultHasher`), reachable by neither fn-body refs nor the
// field-type closure. Pins that a seeded path is collected and an
// un-seeded one is not, so a regression that drops the seed
// (DefaultHasher's `axiom T : Type` vanishing → "Unknown constant")
// is caught directly — no Map/Set op verifies a DefaultHasher-pulling
// path until RC4 lands, so there's no e2e to lean on yet.
#[test]
fn collect_referenced_datatypes_honours_extra_seed() {
    use crate::test_fixtures::{empty_krate, mk_path};
    use vir::def::Spanned;
    use vir::messages::Span;
    use std::collections::HashSet;
    use std::sync::Arc;

    // External-body opaque datatype `Foo`, referenced by nothing in
    // the fn-body ref set — the RC3 instance-head-only shape.
    let foo_x = DatatypeX {
        name: Dt::Path(mk_path("Foo")),
        proxy: None,
        owning_module: None,
        visibility: Visibility { restricted_to: None },
        transparency: DatatypeTransparency::Never,
        typ_params: Arc::new(vec![]),
        typ_bounds: Arc::new(vec![]),
        variants: Arc::new(vec![]),
        mode: Mode::Exec,
        ext_equal: false,
        user_defined_invariant_fn: None,
        sized_constraint: None,
        destructor: false,
    };
    let mut krate = empty_krate();
    krate.datatypes = vec![Spanned::new(Span::dummy(), foo_x)];

    let refs = dep_order::References { datatypes: HashSet::new(), traits: HashSet::new() };
    let foo_path = mk_path("Foo");

    // No seed → Foo is NOT collected (reached only via a seed).
    let empty_seed: HashSet<&vir::ast::Path> = HashSet::new();
    assert!(collect_referenced_datatypes(&krate, &refs, &empty_seed).is_empty(),
        "Foo reached by nothing should not be collected without a seed");

    // Seed = {Foo} → Foo IS collected (the RC3 path).
    let seed: HashSet<&vir::ast::Path> = std::iter::once(&foo_path).collect();
    let got = collect_referenced_datatypes(&krate, &refs, &seed);
    assert_eq!(got.len(), 1, "a seeded datatype must be collected");
    assert!(matches!(&got[0].name, Dt::Path(p) if short_name(p) == "Foo"),
        "the collected datatype should be Foo");
}
