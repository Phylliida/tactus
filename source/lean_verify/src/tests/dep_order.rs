//! Unit tests for `dep_order` — extracted to `src/tests/` (a `#[path]`'d
//! `mod tests` child of `dep_order`, so `use super::*` reaches private items).

use super::*;
use crate::test_fixtures::{mk_path, typ_datatype, typ_int};
use air::ast::BinderX;
use std::sync::Arc;

/// Build a minimal `DatatypeX` with the given name and one
/// variant containing `field_types` as positional fields. All
/// boilerplate fields (proxy / owning_module / visibility /
/// transparency / typ_params / ext_equal / etc.) take "default"
/// values that don't affect SCC graph construction.
fn mk_datatype(name: &str, field_types: Vec<Typ>) -> DatatypeX {
    let path = mk_path(name);
    let fields: Fields = Arc::new(field_types.into_iter().enumerate().map(|(i, t)| {
        Arc::new(BinderX {
            name: Arc::new(format!("{}", i)),
            a: (t, Mode::Exec, Visibility { restricted_to: None }),
        })
    }).collect());
    let variant = Variant {
        name: Arc::new(format!("{}_variant", name)),
        fields,
        ctor_style: CtorPrintStyle::Parens,
    };
    DatatypeX {
        name: Dt::Path(path),
        proxy: None,
        owning_module: None,
        visibility: Visibility { restricted_to: None },
        transparency: DatatypeTransparency::WhenVisible(Visibility { restricted_to: None }),
        typ_params: Arc::new(vec![]),
        typ_bounds: Arc::new(vec![]),
        variants: Arc::new(vec![variant]),
        mode: Mode::Exec,
        ext_equal: false,
        user_defined_invariant_fn: None,
        sized_constraint: None,
        destructor: false,
    }
}

/// Helper: returns the first segment of the datatype's path
/// (e.g., "Tree" for a Datatype named `Dt::Path("Tree")`).
fn dt_short_name(dt: &DatatypeX) -> &str {
    match &dt.name {
        Dt::Path(p) => p.segments[0].as_str(),
        Dt::Tuple(_) => panic!("test fixture should not produce Dt::Tuple"),
    }
}

/// REVIEW lens 3/8: a non-recursive datatype produces a Single
/// group. Just one inductive declaration; no `mutual` block needed.
#[test]
fn order_datatypes_non_recursive_is_single() {
    let a = mk_datatype("A", vec![typ_int()]);
    let groups = order_datatypes(&[&a]);
    assert_eq!(groups.len(), 1);
    match &groups[0] {
        DatatypeGroup::Single(dt) => assert_eq!(dt_short_name(dt), "A"),
        DatatypeGroup::Mutual(_) => panic!("non-recursive datatype should be Single"),
    }
}

/// REVIEW lens 3/8: a self-recursive datatype (Stack referencing
/// Stack in its own field) produces a Single group — Lean's
/// equation compiler handles structural self-recursion without a
/// `mutual` block. Documented invariant in the docstring of
/// `DatatypeGroup`.
#[test]
fn order_datatypes_self_recursive_is_single() {
    let stack = mk_datatype("Stack", vec![typ_datatype("Stack")]);
    let groups = order_datatypes(&[&stack]);
    assert_eq!(groups.len(), 1);
    match &groups[0] {
        DatatypeGroup::Single(dt) => assert_eq!(dt_short_name(dt), "Stack"),
        DatatypeGroup::Mutual(_) => panic!("self-recursive should be Single, not Mutual"),
    }
}

/// REVIEW lens 3/8: Tree ↔ Forest mutual recursion produces a
/// 2-element Mutual group. Pinned by e2e
/// (`test_exec_mutually_recursive_datatypes`); this direct unit
/// test isolates the SCC algorithm without going through Verus.
#[test]
fn order_datatypes_tree_forest_scc_is_mutual() {
    let tree = mk_datatype("Tree", vec![typ_datatype("Forest")]);
    let forest = mk_datatype("Forest", vec![typ_datatype("Tree")]);
    let groups = order_datatypes(&[&tree, &forest]);
    assert_eq!(groups.len(), 1);
    match &groups[0] {
        DatatypeGroup::Mutual(dts) => {
            assert_eq!(dts.len(), 2);
            let names: Vec<&str> = dts.iter().map(|d| dt_short_name(d)).collect();
            assert!(names.contains(&"Tree") && names.contains(&"Forest"),
                "Mutual group should contain both Tree and Forest; got {:?}", names);
        }
        DatatypeGroup::Single(_) => panic!("Tree ↔ Forest should produce a Mutual group"),
    }
}

/// REVIEW lens 3/8: 3-element SCC (A → B → C → A). Pinpoints
/// the algorithm scales beyond the 2-element case.
#[test]
fn order_datatypes_three_element_scc_is_mutual() {
    let a = mk_datatype("A", vec![typ_datatype("B")]);
    let b = mk_datatype("B", vec![typ_datatype("C")]);
    let c = mk_datatype("C", vec![typ_datatype("A")]);
    let groups = order_datatypes(&[&a, &b, &c]);
    assert_eq!(groups.len(), 1);
    match &groups[0] {
        DatatypeGroup::Mutual(dts) => assert_eq!(dts.len(), 3),
        DatatypeGroup::Single(_) => panic!("3-cycle should be Mutual, got Single"),
    }
}

/// REVIEW lens 3/8: SCC + standalone — a 2-element Mutual group
/// (Tree ↔ Forest) alongside a non-recursive Single (Pair).
/// Verifies that order_datatypes correctly partitions the input
/// rather than collapsing everything into one group.
#[test]
fn order_datatypes_scc_plus_standalone() {
    let tree = mk_datatype("Tree", vec![typ_datatype("Forest")]);
    let forest = mk_datatype("Forest", vec![typ_datatype("Tree")]);
    let pair = mk_datatype("Pair", vec![typ_int()]);
        let groups = order_datatypes(&[&tree, &forest, &pair]);
        assert_eq!(groups.len(), 2);

        let mutual_count = groups.iter()
            .filter(|g| matches!(g, DatatypeGroup::Mutual(_)))
            .count();
        let single_count = groups.iter()
            .filter(|g| matches!(g, DatatypeGroup::Single(_)))
            .count();
        assert_eq!(mutual_count, 1, "expected one Mutual group (Tree ↔ Forest)");
    assert_eq!(single_count, 1, "expected one Single group (Pair)");

    // Verify the Single is Pair specifically.
    for g in &groups {
        if let DatatypeGroup::Single(dt) = g {
            assert_eq!(dt_short_name(dt), "Pair");
            }
        }
    }

    /// REVIEW lens 3/8: empty input produces an empty result. Edge
    /// case — would be silly to fail but good to pin against a
    /// future refactor that assumes non-empty input.
    #[test]
    fn order_datatypes_empty_input_returns_empty() {
        let groups = order_datatypes(&[]);
        assert!(groups.is_empty(), "empty input should produce empty output");
}

// ── kahn_emit (spec-fn ↔ instance ordering) ──────────────────────
//
// Pinned over the pure graph (plain usize prereq sets) rather than
// fabricating `FunctionX` bodies — the VIR edge-extraction is covered
// e2e by `test_cross_crate_map_contains_key`.

/// Render an emit order as ('G'|'I', idx) pairs for assertions.
fn tags(order: &[EmitStep]) -> Vec<(char, usize)> {
    order.iter().map(|s| match s {
        EmitStep::Group(i) => ('G', *i),
        EmitStep::Instance(j) => ('I', *j),
    }).collect()
}

/// Build prereqs for `n` groups + `m` instances from explicit edges,
/// pinning the group-order chain (`i` after `i-1`) the same way
/// `order_emission` does.
fn prereqs(n: usize, m: usize, edges: &[(usize, usize)]) -> Vec<HashSet<usize>> {
    let mut p = vec![HashSet::new(); n + m];
    for i in 1..n { p[i].insert(i - 1); }
    for &(node, before) in edges { p[node].insert(before); }
    p
}

/// No cross edges: groups stay in order, instances trail by id.
#[test]
fn kahn_emit_unconstrained_instances_trail() {
    let order = kahn_emit(prereqs(2, 2, &[]), 2);
    assert_eq!(tags(&order), vec![('G', 0), ('G', 1), ('I', 0), ('I', 1)]);
}

/// The View shape: group 1 (deep_view) dispatches to instance 0
/// (View), which depends on group 0 (its method def). Instance 0 must
/// land between group 0 and group 1; instance 1 (DeepView) depends on
/// group 1 and trails. Node ids: groups 0,1; instances 2,3.
#[test]
fn kahn_emit_dispatched_instance_pulled_before_its_group() {
    // group 1 after instance 0 (node 2); instance 0 (node 2) after group 0;
    // instance 1 (node 3) after group 1.
    let order = kahn_emit(prereqs(2, 2, &[(1, 2), (2, 0), (3, 1)]), 2);
    assert_eq!(tags(&order),
        vec![('G', 0), ('I', 0), ('G', 1), ('I', 1)],
        "View pulled between its def-group and its dispatcher; DeepView trails");
}

/// An instance depending on a later group is held until that group.
#[test]
fn kahn_emit_instance_waits_for_its_dependency() {
    // instance 0 (node 2) depends on group 1.
    let order = kahn_emit(prereqs(2, 1, &[(2, 1)]), 2);
    assert_eq!(tags(&order), vec![('G', 0), ('G', 1), ('I', 0)]);
}

/// A 2-cycle (instance and group each require the other) can't sort;
/// remnants append in id order rather than vanish.
#[test]
fn kahn_emit_cycle_remnants_appended() {
    // group 0 after instance 0 (node 1), instance 0 after group 0 — cycle.
    let order = kahn_emit(prereqs(1, 1, &[(0, 1), (1, 0)]), 1);
    assert_eq!(order.len(), 2, "both nodes still emitted (no silent drop)");
}
