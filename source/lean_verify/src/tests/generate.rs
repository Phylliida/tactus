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
        closer_census: None,
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

// ── b67 (W4b): bridge pass cache + emitter fingerprint pins ─────────

#[test]
fn bridge_cache_key_deterministic_and_sensitive() {
    let k1 = bridge_cache_key("text-a", "core-1");
    let k2 = bridge_cache_key("text-a", "core-1");
    assert_eq!(k1, k2, "same inputs must give the same key");
    assert_ne!(
        bridge_cache_key("text-b", "core-1"), k1,
        "bridge module text is a key component"
    );
    assert_ne!(
        bridge_cache_key("text-a", "core-2"), k1,
        "the core-olean hash is a key component"
    );
    // Component boundaries are unambiguous (separator between pieces):
    // ("ab","c") must not collide with ("a","bc").
    assert_ne!(
        bridge_cache_key("ab", "c"), bridge_cache_key("a", "bc"),
        "concatenation-ambiguous inputs must not collide"
    );
}

#[test]
fn bridge_cache_hit_marker_discipline() {
    let pid = std::process::id();
    let marker = std::env::temp_dir().join(format!("tactus_b67_marker_{}.verified", pid));
    let _ = std::fs::remove_file(&marker);
    let key = bridge_cache_key("text", "core");
    // No marker → miss.
    assert!(!bridge_cache_hit(&marker, &key));
    // Marker with the wrong key → miss.
    std::fs::write(&marker, "fnv1a:0000000000000000").unwrap();
    assert!(!bridge_cache_hit(&marker, &key));
    // Marker with the exact key → hit.
    std::fs::write(&marker, &key).unwrap();
    assert!(bridge_cache_hit(&marker, &key));
    let _ = std::fs::remove_file(&marker);
}

#[test]
fn emitter_fingerprint_stable_and_shaped() {
    let fp1 = crate::project::emitter_fingerprint();
    let fp2 = crate::project::emitter_fingerprint();
    assert_eq!(fp1, fp2, "memoized per process");
    assert!(fp1.contains(":fnv1a:"), "version:fnv1a:<hash> shape, got {}", fp1);
}

// ── P3(a)/b68: partition build-once + olean srckey freshness ────────

/// F1 pin: `stmt_partition_for` builds the partition ONCE per scope
/// per process even under a concurrent first wave — every caller
/// shares the one build's Arc. The pre-fix check-then-act memo let
/// every worker thread build concurrently (the trace showed ~50
/// builds in one tactus-core run); the last insert won, and its
/// all-`false` changed flags sent genuinely-changed stmt modules down
/// the `may_skip` path, leaving fresh `TactusStmts_*.lean` beside
/// stale oleans forever.
#[test]
fn stmt_partition_builds_once_under_concurrency() {
    let defs = crate::crate_defs::CrateDefs {
        module_name: "TactusDefs_p3a_unit".to_string(),
        scope: "p3a_unit".to_string(),
        breaking: false,
        covers_exec: true,
        dir: std::env::temp_dir().join(format!("tactus_p3a_part_{}", std::process::id())),
        cmds: Vec::new(),
    };
    let krate = empty_krate();
    let bodies = std::collections::HashMap::new();
    let (defs, krate, bodies) = (&defs, &krate, &bodies);
    let results = std::thread::scope(|s| {
        let handles: Vec<_> = (0..8)
            .map(|_| s.spawn(move || stmt_partition_for(krate, "p3a_unit", bodies, defs)))
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect::<Vec<_>>()
    });
    assert!(results.iter().all(|r| r.is_some()), "partition build succeeds");
    let first = results[0].as_ref().unwrap();
    assert!(
        results.iter().all(|r| std::sync::Arc::ptr_eq(r.as_ref().unwrap(), first)),
        "every concurrent caller must share the ONE build's partition"
    );
    // A later serial caller gets the same build (memo hit).
    let again = stmt_partition_for(krate, "p3a_unit", bodies, defs);
    assert!(std::sync::Arc::ptr_eq(&again.unwrap(), first));
}

/// F2 pin: an olean is fresh iff its srckey marker proves it was built
/// from the CURRENT source content. Bare existence is NOT trust — the
/// interrupted-run skew (fresh `.lean`, stale olean) must force a
/// rebuild, not a silent skip (FINDINGS §4's misleading cascade).
#[test]
fn olean_srckey_freshness_contract() {
    let dir =
        std::env::temp_dir().join(format!("tactus_p3a_srckey_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let lean = dir.join("M.lean");
    let olean = dir.join("M.olean");
    let prelude = std::path::Path::new("/tactus-p3a-test-prelude");
    std::fs::write(&lean, "theorem a : True := by triv").unwrap();
    std::fs::write(&olean, b"olean-bytes").unwrap();
    let key_v1 = stmt_srckey(&lean, prelude).unwrap();
    // Existence alone is NOT freshness (the P3(a) hole).
    assert!(!olean_fresh(&olean, &key_v1));
    // After a successful build the marker makes it fresh...
    record_olean_built(&olean, &key_v1);
    assert!(olean_fresh(&olean, &key_v1));
    // ...and any source change invalidates it (the skew detector).
    std::fs::write(&lean, "theorem a : True := by triv\n-- touched\n").unwrap();
    let key_v2 = stmt_srckey(&lean, prelude).unwrap();
    assert_ne!(key_v1, key_v2);
    assert!(!olean_fresh(&olean, &key_v2));
    // Re-recording after a rebuild restores freshness.
    record_olean_built(&olean, &key_v2);
    assert!(olean_fresh(&olean, &key_v2));
    // Marker removed before a live run (island discipline) → not
    // fresh even with the content unchanged.
    std::fs::remove_file(srckey_path(&olean)).unwrap();
    assert!(!olean_fresh(&olean, &key_v2));
    let _ = std::fs::remove_dir_all(&dir);
}

/// The srckey covers everything an olean depends on: content,
/// toolchain, and the prelude — distinct inputs give distinct keys,
/// and the separator keeps concatenation-ambiguous inputs apart.
#[test]
fn olean_srckey_components() {
    let prelude_a = std::path::Path::new("/prelude-a");
    let prelude_b = std::path::Path::new("/prelude-b");
    let lean = std::env::temp_dir().join(format!("tactus_p3a_c_{}.lean", std::process::id()));
    std::fs::write(&lean, "x").unwrap();
    let key_with = |p: &std::path::Path| stmt_srckey(&lean, p).unwrap();
    assert_ne!(
        key_with(prelude_a), key_with(prelude_b),
        "prelude fingerprint is part of the key"
    );
    std::fs::write(&lean, "ab").unwrap();
    let k1 = key_with(prelude_a);
    std::fs::write(&lean, "a\nb").unwrap();
    assert_ne!(k1, key_with(prelude_a), "content is part of the key");
    assert!(
        k1.starts_with("fnv1a:"),
        "scheme-tagged key, got {}", k1
    );
    let _ = std::fs::remove_file(&lean);
}

/// R1 pin (post-landing review, b68): a pkg olean's key covers the
/// CURRENT content of every imported `TactusStmts_*` module — a pkg
/// module references helper stmt defs BY NAME, so its own text is
/// unchanged when a helper's statement changes, and Lean never
/// re-checks olean contents on load. Without the import half the pkg
/// olean would be silently trusted (warm green where a cold tree
/// reds).
#[test]
fn pkg_srckey_covers_stmt_imports() {
    let dir = std::env::temp_dir().join(format!("tactus_p3a_pkg_{}", std::process::id()));
    let defs_dir = dir.join("defs");
    std::fs::create_dir_all(&defs_dir).unwrap();
    let prelude = std::path::Path::new("/tactus-p3a-test-prelude");
    let stmt = defs_dir.join("TactusStmts_x__x__lemma_a.lean");
    std::fs::write(&stmt, "-- stmt v1\n").unwrap();
    let pkg = dir.join("pkg.lean");
    std::fs::write(
        &pkg,
        "import TactusDefs_x\nimport TactusStmts_x__x__lemma_a\ntheorem t : True := by triv\n",
    )
    .unwrap();
    let k1 = pkg_srckey(&pkg, &defs_dir, prelude).unwrap();
    // Own-content change flips the key...
    std::fs::write(
        &pkg,
        "import TactusDefs_x\nimport TactusStmts_x__x__lemma_a\ntheorem t : True := by triv\n-- v2\n",
    )
    .unwrap();
    let k2 = pkg_srckey(&pkg, &defs_dir, prelude).unwrap();
    assert_ne!(k1, k2, "own content is part of the key");
    std::fs::write(
        &pkg,
        "import TactusDefs_x\nimport TactusStmts_x__x__lemma_a\ntheorem t : True := by triv\n",
    )
    .unwrap();
    assert_eq!(k1, pkg_srckey(&pkg, &defs_dir, prelude).unwrap());
    // ...and so does an imported stmt module's content change, with
    // the pkg text untouched (the R1 hole).
    std::fs::write(&stmt, "-- stmt v2\n").unwrap();
    assert_ne!(
        k1,
        pkg_srckey(&pkg, &defs_dir, prelude).unwrap(),
        "imported stmt content is part of the key (R1)"
    );
    // A missing imported stmt module is not-fresh, never a silent key.
    std::fs::remove_file(&stmt).unwrap();
    assert!(pkg_srckey(&pkg, &defs_dir, prelude).is_none());
    let _ = std::fs::remove_dir_all(&dir);
}

// ── b83: Boundary inventory (explicit cross-crate trust surface) ─────

fn stub_axiom(name: &str, class: Option<crate::lean_ast::BoundaryClass>) -> Command {
    Command::Axiom(crate::lean_ast::Axiom {
        name: name.to_string(),
        binders: Vec::new(),
        ret_ty: LExpr::lit_bool(true),
        attrs: Vec::new(),
        comment: None,
        boundary_class: class,
    })
}

/// The inventory is derived from the same `Command::Axiom` stream the
/// closure-check whitelist uses, sorted by name, with per-class totals;
/// an unclassified entry is rendered LOUD, never silently dropped.
#[test]
fn boundary_inventory_classification_and_totals() {
    use crate::lean_ast::BoundaryClass;
    let cmds = vec![
        // interleaved with non-axiom commands; unsorted on purpose
        stub_axiom("z.seq.axiom_seq_push_len", Some(BoundaryClass::StipulatedBase)),
        Command::Raw("theorem t : True := by triv\n".to_string()),
        stub_axiom("a.seq_lib.lemma_concat", Some(BoundaryClass::ProvedUpstream)),
        stub_axiom("m.mystery", None),
    ];
    let inv = boundary_inventory(&cmds);
    let names: Vec<&str> = inv.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(names, vec!["a.seq_lib.lemma_concat", "m.mystery", "z.seq.axiom_seq_push_len"],
        "sorted by name, non-axiom commands excluded");
    let header = boundary_inventory_header(&inv);
    assert!(header.contains("a.seq_lib.lemma_concat — proved-upstream"), "{}", header);
    assert!(header.contains("z.seq.axiom_seq_push_len — stipulated-base"), "{}", header);
    assert!(header.contains("m.mystery — UNCLASSIFIED (!)"), "{}", header);
    assert!(header.contains("totals: 3 axiom(s): 1 stipulated-base, 1 proved-upstream, 1 unclassified"),
        "{}", header);
}

/// The empty Boundary is explicit about it (tactus-core's shape).
#[test]
fn boundary_inventory_empty_is_explicit() {
    let header = boundary_inventory_header(&[]);
    assert!(header.contains("(empty — crate is self-contained)"), "{}", header);
    assert!(header.contains("totals: 0 axiom(s): 0 stipulated-base, 0 proved-upstream, 0 unclassified"),
        "{}", header);
}
