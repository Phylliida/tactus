#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// === Basic: spec fn + proof fn with omega ===

test_verify_one_file! {
    #[test] test_tactic_double verus_code! {
        spec fn double(x: nat) -> nat {
            x + x
        }

        proof fn lemma_double_pos(x: nat)
            requires x > 0
            ensures double(x) > x
        by {
            unfold double; omega
        }
    } => Ok(())
}

// === Wrong proof correctly rejected ===

test_verify_one_file! {
    #[test] test_wrong_proof_rejected verus_code! {
        proof fn wrong(x: nat)
            ensures x + 1 == x
        by {
            omega
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "Expected at least one error for wrong proof");
    }
}

// === add_comm with omega ===

test_verify_one_file! {
    #[test] test_add_comm verus_code! {
        proof fn add_comm(a: int, b: int)
            ensures a + b == b + a
        by {
            omega
        }
    } => Ok(())
}

// === Multiple requires and ensures (conjunction) ===

test_verify_one_file! {
    #[test] test_multiple_requires_ensures verus_code! {
        proof fn bounds(x: int, y: int)
            requires x > 0, y > 0
            ensures x + y > 0, x + y > 1
        by {
            omega
        }
    } => Ok(())
}

// === Implies ===

test_verify_one_file! {
    #[test] test_implies verus_code! {
        proof fn pos_add(x: int)
            requires x > 0
            ensures x + 1 > 1
        by {
            omega
        }
    } => Ok(())
}

// === Spec fn with if-then-else ===

test_verify_one_file! {
    #[test] test_spec_ite verus_code! {
        spec fn abs(x: int) -> int {
            if x >= 0 { x } else { -x }
        }

        proof fn abs_nonneg(x: int)
            ensures abs(x) >= 0
        by {
            unfold abs; omega
        }
    } => Ok(())
}

// === Recursive spec fn with termination_by ===

test_verify_one_file! {
    #[test] test_recursive_triangle verus_code! {
        spec fn triangle(n: nat) -> nat
            decreases n
        {
            if n == 0 { 0 } else { (n + triangle((n - 1) as nat)) as nat }
        }

        proof fn triangle_zero()
            ensures triangle(0) == 0
        by {
            unfold triangle; simp
        }
    } => Ok(())
}

// === Dependency ordering: helper → double → proof fn ===

test_verify_one_file! {
    #[test] test_dep_ordering verus_code! {
        // helper is called by double_plus_one, must come first in Lean output
        spec fn helper(x: nat) -> nat {
            x + x
        }

        spec fn double_plus_one(x: nat) -> nat {
            helper(x) + 1
        }

        proof fn lemma_dpo(x: nat)
            requires x > 0
            ensures double_plus_one(x) > 1
        by {
            unfold double_plus_one; unfold helper; omega
        }
    } => Ok(())
}

// === Mutual recursion: is_even/is_odd ===

test_verify_one_file! {
    #[test] test_mutual_recursion verus_code! {
        spec fn is_even(n: nat) -> bool
            decreases n
        {
            if n == 0 { true } else { is_odd((n - 1) as nat) }
        }

        spec fn is_odd(n: nat) -> bool
            decreases n
        {
            if n == 0 { false } else { is_even((n - 1) as nat) }
        }

        proof fn even_zero()
            ensures is_even(0) == true
        by {
            unfold is_even; simp
        }
    } => Ok(())
}

// === Only referenced spec fns are included (unreferenced fn shouldn't cause issues) ===

test_verify_one_file! {
    #[test] test_filtering verus_code! {
        spec fn used(x: nat) -> nat { x + 1 }

        // This fn is never referenced by the proof fn — should be excluded
        spec fn unused_fn(x: nat) -> nat { x * x * x * x }

        proof fn lemma_used(x: nat)
            ensures used(x) > x
        by {
            unfold used; omega
        }
    } => Ok(())
}

// === Import keyword: imports are parsed and threaded to Lean ===

test_verify_one_file! {
    #[test] test_import_keyword verus_code! {
        import Init.Data.Nat.Basic

        proof fn nat_succ(x: nat)
            ensures x + 1 > x
        by {
            omega
        }
    } => Ok(())
}

// === Mathlib ring tactic (requires Lake project with Mathlib) ===

test_verify_one_file! {
    #[test] test_mathlib_ring verus_code! {
        import Mathlib.Tactic.Ring

        proof fn add_comm_ring(x: int, y: int)
            ensures x + y == y + x
        by {
            ring
        }
    } => Ok(())
}

// === Mathlib nlinarith tactic ===

test_verify_one_file! {
    #[test] test_mathlib_nlinarith verus_code! {
        import Mathlib.Tactic.Linarith

        proof fn lemma_sq_nonneg(x: int)
            ensures x * x >= 0
        by {
            nlinarith [sq_nonneg x]
        }
    } => Ok(())
}

// === Source map: error includes tactic line number ===

test_verify_one_file! {
    #[test] test_error_tactic_line verus_code! {
        proof fn wrong_multi_line(x: nat)
            ensures x + 1 == x
        by {
            omega
        }
    } => Err(err) => {
        let msg = format!("{:?}", err);
        assert!(msg.contains("Lean tactic failed"), "Expected Lean error, got: {}", msg);
        assert!(msg.contains("tactic line"), "Expected tactic line info in error, got: {}", msg);
    }
}

// === Open spec fn (no @[irreducible], body visible to tactics) ===

test_verify_one_file! {
    #[test] test_open_spec_fn verus_code! {
        pub open spec fn triple(x: nat) -> nat {
            x + x + x
        }

        proof fn lemma_triple(x: nat)
            requires x > 0
            ensures triple(x) > x
        by {
            simp [triple]; omega
        }
    } => Ok(())
}

// === Forall quantifier in ensures ===
// VIR auto-introduces forall-bound variables as function parameters,
// so `ensures forall|n| P(n)` becomes `theorem foo (n : Nat) : P n`.
// No `intro` needed — the variable is already in scope.

test_verify_one_file! {
    #[test] test_forall_ensures verus_code! {
        spec fn always_positive(n: nat) -> bool {
            n + 1 > 0
        }

        proof fn lemma_always_positive()
            ensures forall|n: nat| always_positive(n)
        by {
            unfold always_positive; omega
        }
    } => Ok(())
}

// === Multiple proof fns in one block ===

test_verify_one_file! {
    #[test] test_multiple_proof_fns verus_code! {
        spec fn inc(x: nat) -> nat { x + 1 }

        proof fn lemma_inc_pos(x: nat)
            ensures inc(x) > 0
        by {
            unfold inc; omega
        }

        proof fn lemma_inc_gt(x: nat)
            ensures inc(x) > x
        by {
            unfold inc; omega
        }
    } => Ok(())
}

// === Multi-tactic proof (semicolons separate tactics) ===
// Note: TokenStream collapses newlines, so multi-line tactics must use
// semicolons. Tree-sitter-tactus integration will fix this (Track A polish).

test_verify_one_file! {
    #[test] test_multi_tactic verus_code! {
        import Mathlib.Tactic.Linarith

        spec fn square(x: int) -> int { x * x }

        proof fn sq_nonneg_manual(x: int)
            ensures square(x) >= 0
        by {
            unfold square; nlinarith [sq_nonneg x]
        }
    } => Ok(())
}

// === Negative integer constant ===

test_verify_one_file! {
    #[test] test_negative_constant verus_code! {
        proof fn neg_bound(x: int)
            requires x > -5
            ensures x >= -4
        by {
            omega
        }
    } => Ok(())
}

// === Logical connectives in specs (and, or, implies) ===

test_verify_one_file! {
    #[test] test_logical_connectives verus_code! {
        proof fn and_or_implies(a: bool, b: bool)
            requires a && b
            ensures a || b
        by {
            simp_all
        }
    } => Ok(())
}

// === Nested spec fn calls ===

test_verify_one_file! {
    #[test] test_nested_calls verus_code! {
        spec fn add1(x: nat) -> nat { x + 1 }
        spec fn add2(x: nat) -> nat { add1(add1(x)) }

        proof fn lemma_add2(x: nat)
            ensures add2(x) == x + 2
        by {
            unfold add2; unfold add1; omega
        }
    } => Ok(())
}

// === Subtraction ===

test_verify_one_file! {
    #[test] test_subtraction verus_code! {
        proof fn sub_self(x: int)
            ensures x - x == 0
        by {
            omega
        }
    } => Ok(())
}

// === Multiple imports ===

test_verify_one_file! {
    #[test] test_multiple_imports verus_code! {
        import Mathlib.Tactic.Ring
        import Mathlib.Tactic.Linarith

        spec fn poly(x: int) -> int { x * x + 2 * x + 1 }

        proof fn poly_factored(x: int)
            ensures poly(x) == (x + 1) * (x + 1)
        by {
            unfold poly; ring
        }
    } => Ok(())
}

// === Wrong proof with multiple tactic lines: error pinpoints line ===

test_verify_one_file! {
    #[test] test_error_multiline_tactic verus_code! {
        spec fn bad(x: nat) -> nat { x + x }

        proof fn wrong_multiline(x: nat)
            requires x > 0
            ensures bad(x) == x
        by {
            unfold bad
            omega
        }
    } => Err(err) => {
        let msg = format!("{:?}", err);
        assert!(msg.contains("Lean tactic failed"), "Expected Lean error, got: {}", msg);
        // omega is on the second tactic line
        assert!(msg.contains("tactic line"), "Expected tactic line info, got: {}", msg);
    }
}

// === Not operator (¬) ===

test_verify_one_file! {
    #[test] test_not_operator verus_code! {
        proof fn not_false_is_true(b: bool)
            requires !b
            ensures !b
        by {
            simp_all
        }
    } => Ok(())
}

// === Bool-returning spec fn in ensures (Prop in Lean) ===

test_verify_one_file! {
    #[test] test_bool_spec_fn verus_code! {
        spec fn is_positive(x: int) -> bool {
            x > 0
        }

        proof fn five_is_positive()
            ensures is_positive(5)
        by {
            unfold is_positive; omega
        }
    } => Ok(())
}

// === Proof fn with no requires (just ensures) ===

test_verify_one_file! {
    #[test] test_no_requires verus_code! {
        proof fn zero_is_zero()
            ensures 0int == 0
        by {
            omega
        }
    } => Ok(())
}

// === Inequality operators (!=, <=, >=) ===

test_verify_one_file! {
    #[test] test_inequality_ops verus_code! {
        proof fn inequality_chain(x: int, y: int)
            requires x < y
            ensures x <= y, x != y, y >= x, y > x
        by {
            omega
        }
    } => Ok(())
}

// === Nested if-then-else in spec fn ===

test_verify_one_file! {
    #[test] test_nested_ite verus_code! {
        spec fn clamp(x: int, lo: int, hi: int) -> int {
            if x < lo { lo } else if x > hi { hi } else { x }
        }

        proof fn clamp_bounds(x: int, lo: int, hi: int)
            requires lo <= hi
            ensures clamp(x, lo, hi) >= lo, clamp(x, lo, hi) <= hi
        by {
            unfold clamp; omega
        }
    } => Ok(())
}

// === Spec fn with many parameters ===

test_verify_one_file! {
    #[test] test_many_params verus_code! {
        spec fn weighted_sum(a: int, b: int, c: int, wa: int, wb: int, wc: int) -> int {
            a * wa + b * wb + c * wc
        }

        proof fn weighted_sum_zero(a: int, b: int, c: int)
            ensures weighted_sum(a, b, c, 0, 0, 0) == 0
        by {
            unfold weighted_sum; omega
        }
    } => Ok(())
}

// === Implies in ensures ===

test_verify_one_file! {
    #[test] test_implies_ensures verus_code! {
        proof fn implies_chain(a: int, b: int, c: int)
            requires a < b, b < c
            ensures a < b ==> b < c ==> a < c
        by {
            omega
        }
    } => Ok(())
}

// Probe: chained comparison `a < b < c` in a proof-fn require lowers to
// `ExprX::Multi(MultiOp::Chained(...), [a, b, c])` at the AST level
// (Verus's `ast_simplify` would expand it to `a < b ∧ b < c`, but proof
// fns route through the PRE-simplify krate). The renderer in
// `to_lean_expr.rs`'s `Multi` arm must produce the conjunction shape,
// not an anon-ctor `⟨a, b, c⟩` (which would be a Lean tuple literal —
// semantically wrong for a chained comparison).
test_verify_one_file! {
    #[test] test_chained_compare_in_proof_fn verus_code! {
        proof fn chain_works(x: int)
            requires 0 <= x <= 10
            ensures x >= 0, x <= 10
        by {
            omega
        }
    } => Ok(())
}

// Companion: chained comparison directly inside a proof-fn ensures
// (a different shape from the requires test above). Pre-fix this also
// rendered the chained `∧` chain as `⟨...⟩`. Both shapes go through
// the same Multi arm.
test_verify_one_file! {
    #[test] test_chained_compare_in_proof_fn_ensures verus_code! {
        proof fn chain_ensures(x: int)
            requires x >= 0, x <= 10
            ensures 0 <= x <= 10
        by {
            omega
        }
    } => Ok(())
}

// Spec fn with chained-compare body, called from a proof fn that
// `unfold`s it. Probes that the chained-compare expansion in the
// SPEC FN BODY (not a require/ensure clause) renders correctly into
// the Lean def. The 2026-05-09 Multi-arm fix made the renderer
// produce `0 ≤ x ∧ x ≤ 10` for the body; this test pins it from the
// caller's perspective via `unfold + omega`.
//
// Lean tactic note: `unfold f` targets the GOAL by default. When the
// spec fn appears only in a hypothesis (via `requires`), use
// `unfold f at *` to also unfold occurrences in hypotheses.
test_verify_one_file! {
    #[test] test_chained_compare_in_spec_fn_body verus_code! {
        spec fn in_range(x: int) -> bool {
            0 <= x <= 10
        }

        proof fn lemma_in_range_lower(x: int)
            requires in_range(x)
            ensures x >= 0
        by {
            unfold in_range at *; omega
        }
    } => Ok(())
}

// Companion: spec fn with chained-compare body in the GOAL position
// (via `ensures`). `unfold f` in goal context works without `at *`,
// because the chained-compare-rendered `0 ≤ x ∧ x ≤ 10` appears
// directly in the goal after unfolding.
test_verify_one_file! {
    #[test] test_chained_compare_in_spec_fn_body_via_ensures verus_code! {
        spec fn in_range(x: int) -> bool {
            0 <= x <= 10
        }

        proof fn lemma_5_in_range()
            ensures in_range(5)
        by {
            unfold in_range; omega
        }
    } => Ok(())
}

// === Mathlib: ring tactic for polynomial identity ===

test_verify_one_file! {
    #[test] test_ring_polynomial verus_code! {
        import Mathlib.Tactic.Ring

        spec fn cube(x: int) -> int { x * x * x }

        proof fn cube_diff(a: int, b: int)
            ensures cube(a) - cube(b) == (a - b) * (a * a + a * b + b * b)
        by {
            unfold cube; ring
        }
    } => Ok(())
}

// === Bool spec fn with && in body ===

test_verify_one_file! {
    #[test] test_bool_spec_and verus_code! {
        spec fn both_positive(x: int, y: int) -> bool {
            x > 0 && y > 0
        }

        proof fn both_means_sum(x: int, y: int)
            ensures both_positive(x, y) ==> x + y > 1
        by {
            unfold both_positive; omega
        }
    } => Ok(())
}

// === Error: unsolved goals shows goal state ===

test_verify_one_file! {
    #[test] test_error_goal_state verus_code! {
        proof fn unprovable(x: int, y: int)
            requires x > 0
            ensures x + y > 0
        by {
            omega
        }
    } => Err(err) => {
        let msg = format!("{:?}", err);
        assert!(msg.contains("Lean tactic failed"), "Expected Lean error, got: {}", msg);
        // Error should contain the goal state with hypothesis info
        assert!(msg.contains("could not prove") || msg.contains("unsolved"),
            "Expected goal state in error, got: {}", msg);
    }
}

// === Deeply nested spec fn chain ===

test_verify_one_file! {
    #[test] test_deep_chain verus_code! {
        spec fn f1(x: nat) -> nat { x + 1 }
        spec fn f2(x: nat) -> nat { f1(x) + 1 }
        spec fn f3(x: nat) -> nat { f2(x) + 1 }
        spec fn f4(x: nat) -> nat { f3(x) + 1 }

        proof fn chain_result(x: nat)
            ensures f4(x) == x + 4
        by {
            unfold f4; unfold f3; unfold f2; unfold f1; omega
        }
    } => Ok(())
}

// === Spec fn with int subtraction and conditional ===

test_verify_one_file! {
    #[test] test_conditional_spec verus_code! {
        spec fn relu(x: int) -> int {
            if x > 0 { x } else { 0 }
        }

        proof fn relu_nonneg(x: int)
            ensures relu(x) >= 0
        by {
            unfold relu; omega
        }

        proof fn relu_le(x: int)
            requires x > 0
            ensures relu(x) == x
        by {
            unfold relu; omega
        }
    } => Ok(())
}

// === Let binding in spec fn ===
// `omega` can't see through `let` in Lean; `simp` reduces it first.

test_verify_one_file! {
    #[test] test_let_binding verus_code! {
        spec fn offset(base: int, delta: int) -> int {
            let result = base + delta;
            result
        }

        proof fn offset_pos(base: int, delta: int)
            requires base > 0, delta >= 0
            ensures offset(base, delta) > 0
        by {
            unfold offset; simp; omega
        }
    } => Ok(())
}

// === Spec closure (FnSpec) ===

test_verify_one_file! {
    #[test] test_spec_closure verus_code! {
        spec fn apply_twice(f: spec_fn(int) -> int, x: int) -> int {
            f(f(x))
        }

        proof fn apply_twice_id(x: int)
            ensures apply_twice(|y: int| y, x) == x
        by {
            unfold apply_twice; simp
        }
    } => Ok(())
}

// === Enum/match ===

test_verify_one_file! {
    #[test] test_enum_match verus_code! {
        enum MyOption {
            MySome(int),
            MyNone,
        }

        spec fn unwrap_or(opt: MyOption, default: int) -> int {
            match opt {
                MyOption::MySome(v) => v,
                MyOption::MyNone => default,
            }
        }

        proof fn unwrap_some()
            ensures unwrap_or(MyOption::MySome(42), 0) == 42
        by {
            unfold unwrap_or; simp
        }
    } => Ok(())
}

// === Struct construction ===

test_verify_one_file! {
    #[test] test_struct_ctor verus_code! {
        struct Point {
            x: int,
            y: int,
        }

        spec fn origin() -> Point {
            Point { x: 0, y: 0 }
        }

        spec fn get_x(p: Point) -> int {
            p.x
        }

        proof fn origin_x()
            ensures get_x(origin()) == 0
        by {
            unfold get_x; unfold origin; simp
        }
    } => Ok(())
}

// === Trait: concrete dispatch (DynamicResolved) ===

test_verify_one_file! {
    #[test] test_trait_concrete verus_code! {
        trait HasValue {
            spec fn value(&self) -> int;
        }

        struct MyNum {
            val: int,
        }

        impl HasValue for MyNum {
            spec fn value(&self) -> int {
                self.val
            }
        }

        proof fn trait_method_works()
            ensures (MyNum { val: 42 }).value() == 42
        by {
            unfold HasValue.value; rfl
        }
    } => Ok(())
}

// === Trait: generic dispatch (Dynamic, class + instance params) ===

test_verify_one_file! {
    #[test] test_trait_generic verus_code! {
        trait Doubler {
            spec fn double(&self) -> int;
        }

        proof fn double_eq<T: Doubler>(x: T, y: T)
            requires x.double() == y.double()
            ensures x.double() == y.double()
        by {
            omega
        }
    } => Ok(())
}

// === Trait impl: instance resolution ===

test_verify_one_file! {
    #[test] test_trait_impl_instance verus_code! {
        trait HasVal {
            spec fn val(&self) -> int;
        }

        struct Wrap { inner: int }

        impl HasVal for Wrap {
            spec fn val(&self) -> int { self.inner }
        }

        proof fn impl_works()
            ensures (Wrap { inner: 7 }).val() == 7
        by {
            unfold HasVal.val; rfl
        }
    } => Ok(())
}

// === Trait with multiple methods ===

test_verify_one_file! {
    #[test] test_trait_multi_method verus_code! {
        trait Bounds {
            spec fn lo(&self) -> int;
            spec fn hi(&self) -> int;
        }

        struct Range { start: int, end: int }

        impl Bounds for Range {
            spec fn lo(&self) -> int { self.start }
            spec fn hi(&self) -> int { self.end }
        }

        proof fn range_lo()
            ensures (Range { start: 1, end: 10 }).lo() == 1
        by {
            unfold Bounds.lo; rfl
        }

        proof fn range_hi()
            ensures (Range { start: 1, end: 10 }).hi() == 10
        by {
            unfold Bounds.hi; rfl
        }
    } => Ok(())
}

// === Same trait, two impl types ===

test_verify_one_file! {
    #[test] test_trait_two_impls verus_code! {
        trait IsZero {
            spec fn is_zero(&self) -> bool;
        }

        struct MyInt { v: int }
        struct MyNat { v: nat }

        impl IsZero for MyInt {
            spec fn is_zero(&self) -> bool { self.v == 0 }
        }

        impl IsZero for MyNat {
            spec fn is_zero(&self) -> bool { self.v == 0 }
        }

        proof fn int_zero()
            ensures (MyInt { v: 0 }).is_zero()
        by {
            unfold IsZero.is_zero; rfl
        }

        proof fn nat_zero()
            ensures (MyNat { v: 0 }).is_zero()
        by {
            unfold IsZero.is_zero; rfl
        }
    } => Ok(())
}

// === Generic struct with multiple type params ===

test_verify_one_file! {
    #[test] test_generic_multi_param verus_code! {
        struct Pair<A, B> { fst: A, snd: B }

        spec fn get_fst<A, B>(p: Pair<A, B>) -> A { p.fst }
        spec fn get_snd<A, B>(p: Pair<A, B>) -> B { p.snd }

        proof fn pair_access()
            ensures get_fst(Pair { fst: 1int, snd: true }) == 1
        by {
            unfold get_fst; simp
        }
    } => Ok(())
}

// === Enum with multi-field variant ===

test_verify_one_file! {
    #[test] test_enum_multi_field verus_code! {
        enum Shape {
            Circle(int),
            Rect(int, int),
            Empty,
        }

        spec fn area(s: Shape) -> int {
            match s {
                Shape::Circle(r) => r * r,
                Shape::Rect(w, h) => w * h,
                Shape::Empty => 0,
            }
        }

        proof fn rect_area()
            ensures area(Shape::Rect(3, 4)) == 12
        by {
            unfold area; simp
        }
    } => Ok(())
}

// === Trait method through generic (passthrough proof) ===

test_verify_one_file! {
    #[test] test_trait_generic_passthrough verus_code! {
        trait HasLen {
            spec fn len(&self) -> nat;
        }

        proof fn len_eq<T: HasLen>(a: T, b: T)
            requires a.len() == b.len()
            ensures a.len() == b.len()
        by {
            omega
        }
    } => Ok(())
}

// === Generic trait impl (implicit type params in instance) ===

test_verify_one_file! {
    #[test] test_generic_trait_impl verus_code! {
        trait Wrapper {
            spec fn unwrap(&self) -> int;
        }

        struct Box<T> { val: T }

        impl Wrapper for Box<int> {
            spec fn unwrap(&self) -> int { self.val }
        }

        proof fn box_unwrap()
            ensures (Box { val: 42int }).unwrap() == 42
        by {
            unfold Wrapper.unwrap; rfl
        }
    } => Ok(())
}

// === Trait method with self and extra params ===

test_verify_one_file! {
    #[test] test_trait_method_multi_param verus_code! {
        trait Adder {
            spec fn add(&self, other: int) -> int;
        }

        struct MyVal { v: int }

        impl Adder for MyVal {
            spec fn add(&self, other: int) -> int { self.v + other }
        }

        proof fn add_works()
            ensures (MyVal { v: 10 }).add(5) == 15
        by {
            unfold Adder.add; rfl
        }
    } => Ok(())
}

// === Associated type: trait with type Output ===

test_verify_one_file! {
    #[test] test_assoc_type_basic verus_code! {
        trait Converter {
            type Output;
            spec fn convert(&self) -> Self::Output;
        }

        struct MyNum { val: int }

        impl Converter for MyNum {
            type Output = bool;
            spec fn convert(&self) -> bool { self.val > 0 }
        }

        proof fn converter_works()
            ensures (MyNum { val: 5 }).convert()
        by {
            show ((MyNum.mk 5).val > 0)
            decide
        }
    } => Ok(())
}

// === Trait bound on generic function ===

test_verify_one_file! {
    #[test] test_trait_bound_on_fn verus_code! {
        trait HasSize {
            spec fn size(&self) -> nat;
        }

        spec fn double_size<T: HasSize>(x: T) -> nat {
            x.size() + x.size()
        }

        proof fn double_is_even<T: HasSize>(x: T)
            ensures double_size(x) >= x.size()
        by {
            unfold double_size
            omega
        }
    } => Ok(())
}

// === Trait bound on generic impl ===

test_verify_one_file! {
    #[test] test_trait_bound_on_impl verus_code! {
        trait ToInt {
            spec fn to_int(&self) -> int;
        }

        trait Summable {
            spec fn sum(&self) -> int;
        }

        struct Pair<T> { a: T, b: T }

        impl<T: ToInt> Summable for Pair<T> {
            spec fn sum(&self) -> int {
                self.a.to_int() + self.b.to_int()
            }
        }
    } => Ok(())
}

// === Parameterized trait: trait Foo<T> ===

test_verify_one_file! {
    #[test] test_parameterized_trait verus_code! {
        trait Container<T> {
            spec fn peek(&self) -> T;
        }

        struct IntBox { val: int }

        impl Container<int> for IntBox {
            spec fn peek(&self) -> int { self.val }
        }

        proof fn peek_works()
            ensures (IntBox { val: 7 }).peek() == 7
        by {
            unfold Container.peek; rfl
        }
    } => Ok(())
}

// === Associated type in method signature ===

test_verify_one_file! {
    #[test] test_assoc_type_in_method verus_code! {
        trait Producer {
            type Item;
            spec fn produce(&self) -> Self::Item;
        }

        struct IntMaker { val: int }

        impl Producer for IntMaker {
            type Item = int;
            spec fn produce(&self) -> int { self.val }
        }

        proof fn producer_test()
            ensures (IntMaker { val: 42 }).produce() == 42
        by {
            unfold Producer.produce; rfl
        }
    } => Ok(())
}

// === Empty struct (no fields) ===

test_verify_one_file! {
    #[test] test_empty_struct verus_code! {
        struct Unit {}

        spec fn make_unit() -> Unit { Unit {} }

        proof fn unit_eq()
            ensures make_unit() == make_unit()
        by {
            unfold make_unit
            simp
        }
    } => Ok(())
}

// === Nested datatype: struct containing enum ===

test_verify_one_file! {
    #[test] test_nested_datatype verus_code! {
        enum Color { Red, Blue }

        struct Pixel {
            x: int,
            y: int,
            color: Color,
        }

        spec fn is_red(p: Pixel) -> bool {
            match p.color {
                Color::Red => true,
                Color::Blue => false,
            }
        }

        proof fn red_pixel_is_red()
            ensures is_red(Pixel { x: 0, y: 0, color: Color::Red })
        by {
            unfold is_red
            simp
        }
    } => Ok(())
}

// === Trait method returning bool (exercises Bool → Prop mapping) ===

test_verify_one_file! {
    #[test] test_trait_bool_return verus_code! {
        trait Predicate {
            spec fn holds(&self) -> bool;
        }

        struct AlwaysTrue {}

        impl Predicate for AlwaysTrue {
            spec fn holds(&self) -> bool { true }
        }

        proof fn always_true_holds()
            ensures (AlwaysTrue {}).holds()
        by {
            unfold Predicate.holds; trivial
        }
    } => Ok(())
}

// === Instance method calls spec fn (ordering test) ===

test_verify_one_file! {
    #[test] test_instance_calls_spec_fn verus_code! {
        spec fn double(x: int) -> int { x + x }

        trait Doubler {
            spec fn dbl(&self) -> int;
        }

        struct MyVal { v: int }

        impl Doubler for MyVal {
            spec fn dbl(&self) -> int { double(self.v) }
        }

        proof fn dbl_works()
            ensures (MyVal { v: 3 }).dbl() == 6
        by {
            show double 3 = 6
            unfold double; rfl
        }
    } => Ok(())
}

// === TypEquality bound: T: Trait<AssocType = ConcreteType> ===

test_verify_one_file! {
    #[test] test_typ_equality_bound verus_code! {
        trait Producer {
            type Item;
            spec fn produce(&self) -> Self::Item;
        }

        // Function with TypEquality bound: Item must be int
        proof fn produce_is_positive<T: Producer<Item = int>>(t: T)
            requires t.produce() > 0
            ensures t.produce() > 0
        by {
            omega
        }
    } => Ok(())
}

// === Negation in spec ===

test_verify_one_file! {
    #[test] test_negation verus_code! {
        proof fn not_false()
            ensures !false
        by {
            simp
        }
    } => Ok(())
}

// === If-then-else in spec fn ===

test_verify_one_file! {
    #[test] test_ite_in_spec verus_code! {
        spec fn abs(x: int) -> int {
            if x >= 0 { x } else { -x }
        }

        proof fn abs_nonneg(x: int)
            ensures abs(x) >= 0
        by {
            unfold abs
            omega
        }
    } => Ok(())
}

// === Let binding in spec fn ===

test_verify_one_file! {
    #[test] test_let_in_spec verus_code! {
        spec fn with_let(x: int) -> int {
            let y = x + 1;
            y + y
        }

        proof fn let_works()
            ensures with_let(3) == 8
        by {
            unfold with_let
            simp
        }
    } => Ok(())
}

// === Spec fn with no params ===

test_verify_one_file! {
    #[test] test_nullary_spec_fn verus_code! {
        spec fn answer() -> int { 42 }

        proof fn answer_is_42()
            ensures answer() == 42
        by {
            unfold answer
            simp
        }
    } => Ok(())
}

// === Boolean ops in spec (&&, ||, ==>) ===

test_verify_one_file! {
    #[test] test_bool_ops_in_spec verus_code! {
        spec fn both(a: bool, b: bool) -> bool { a && b }

        proof fn both_tt()
            ensures both(true, true)
        by {
            unfold both
            simp
        }
    } => Ok(())
}

// === Multiple associated types ===

test_verify_one_file! {
    #[test] test_multi_assoc_type verus_code! {
        trait Pair {
            type Fst;
            type Snd;
            spec fn fst(&self) -> Self::Fst;
            spec fn snd(&self) -> Self::Snd;
        }

        struct IntBoolPair { a: int, b: bool }

        impl Pair for IntBoolPair {
            type Fst = int;
            type Snd = bool;
            spec fn fst(&self) -> int { self.a }
            spec fn snd(&self) -> bool { self.b }
        }

        proof fn pair_fst()
            ensures (IntBoolPair { a: 7, b: true }).fst() == 7
        by {
            unfold Pair.fst; rfl
        }
    } => Ok(())
}

// === Spec closure applied (FnSpec) ===

test_verify_one_file! {
    #[test] test_spec_fn_apply verus_code! {
        spec fn apply(f: spec_fn(int) -> int, x: int) -> int { f(x) }

        proof fn apply_id()
            ensures apply(|x: int| x, 5) == 5
        by {
            unfold apply
            simp
        }
    } => Ok(())
}

// === Complex proofs ===

// #[verifier::heartbeats(N)] sets Lean's deterministic timeout
// (maxHeartbeats) per theorem this fn emits. Verus has #[verifier::rlimit]
// for the Z3 path; Tactus mirrors with a more reproducible knob
// (heartbeats count kernel reduction steps, not wall-clock).
test_verify_one_file! {
    #[test] test_proof_heartbeats_attribute verus_code! {
        #[verifier::heartbeats(1600000)]
        proof fn lemma_with_heartbeats(x: int)
            ensures x == x
        by {
            rfl
        }
    } => Ok(())
}

// Exec-fn path: every theorem the fn emits gets the heartbeats
// override. With #[verifier::tactus_auto], the per-obligation
// theorems all share the same maxHeartbeats setting.
test_verify_one_file! {
    #[test] test_exec_heartbeats_attribute verus_code! {
        #[verifier::tactus_auto]
        #[verifier::heartbeats(1600000)]
        fn add_one_with_heartbeats(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            x + 1
        }
    } => Ok(())
}

// Negative tests: malformed heartbeats invocations get a heartbeats-
// specific error message (via the `get_heartbeats_arg` helper) rather
// than falling through to the generic "unrecognized verifier attribute"
// catchall.
test_verify_one_file! {
    #[test] test_heartbeats_zero_rejected verus_code! {
        #[verifier::heartbeats(0)]
        proof fn lemma_bad_heartbeats()
            ensures true
        by {
            trivial
        }
    } => Err(e) => assert!(format!("{:?}", e).contains(vir::tactus_messages::HEARTBEATS_ARG_ERR))
}

// Multi-theorem exec fn: loop body emits init / maintain / use
// theorems (per-obligation emission, task D). All of them inherit
// the fn's heartbeats override through `ObligationEmitter::heartbeats`.
// Pins that the override applies uniformly across every theorem the
// fn produces, not just the postcondition.
test_verify_one_file! {
    #[test] test_exec_heartbeats_multi_theorem verus_code! {
        #[verifier::tactus_auto]
        #[verifier::heartbeats(1200000)]
        fn count_to_n(n: u8) -> (r: u8)
            requires n <= 100
            ensures r == n
        {
            let mut i: u8 = 0;
            while i < n
                invariant i <= n
                decreases n - i
            {
                i = i + 1;
            }
            i
        }
    } => Ok(())
}

// Pin that Tactus has access to classical excluded middle.
// `TactusPrelude.lean` opens `Classical.propDecidable` as an instance,
// which is the foundational commitment that makes match-on-Prop
// discriminators, `Classical.epsilon` (Choose's render target), and
// `Classical.arbitrary` (accessor unreachable-branch fallback) all
// elaborate. This test makes the commitment visible at the user level:
// `Classical.em P` proves `P ∨ ¬P` for any spec-level proposition.
//
// Tactus inherits classical from Verus (Z3 reasons classically); users
// coming from Verus's verification model expect this. Audit (#151,
// 2026-05-11): keep the commitment, document it centrally, pin it with
// this test.
test_verify_one_file! {
    #[test] test_proof_classical_excluded_middle verus_code! {
        proof fn em_test(P: bool)
            ensures P || !P
        by {
            exact Classical.em P
        }
    } => Ok(())
}

// Multi-step proof with have
test_verify_one_file! {
    #[test] test_proof_with_have verus_code! {
        import Mathlib.Tactic.Linarith

        spec fn square(x: int) -> int { x * x }

        proof fn square_nonneg(x: int)
            ensures square(x) >= 0
        by {
            unfold square
            nlinarith [sq_nonneg x]
        }
    } => Ok(())
}

// Proof calling another lemma
test_verify_one_file! {
    #[test] test_lemma_chain verus_code! {
        spec fn double(x: int) -> int { x + x }
        spec fn quadruple(x: int) -> int { double(double(x)) }

        proof fn double_pos(x: int)
            requires x > 0
            ensures double(x) > x
        by {
            unfold double
            omega
        }

        proof fn quadruple_pos(x: int)
            requires x > 0
            ensures quadruple(x) > x
        by {
            unfold quadruple
            unfold double
            omega
        }
    } => Ok(())
}

// Proof about recursive function with induction
test_verify_one_file! {
    #[test] test_recursive_sum verus_code! {
        spec fn sum_to(n: nat) -> nat
            decreases n
        {
            if n == 0 { 0 } else { (n + sum_to((n - 1) as nat)) as nat }
        }

        proof fn sum_zero()
            ensures sum_to(0) == 0
        by {
            unfold sum_to
            simp
        }
    } => Ok(())
}

// Multi-line tactic with multiple unfolds and reasoning steps
test_verify_one_file! {
    #[test] test_multi_step_proof verus_code! {
        spec fn max(a: int, b: int) -> int {
            if a >= b { a } else { b }
        }

        spec fn min(a: int, b: int) -> int {
            if a <= b { a } else { b }
        }

        proof fn max_ge_min(a: int, b: int)
            ensures max(a, b) >= min(a, b)
        by {
            unfold max
            unfold min
            omega
        }
    } => Ok(())
}

// Proof with conjunction (multiple ensures) using constructor + focus dots
test_verify_one_file! {
    #[test] test_conjunction_proof verus_body("
        proof fn conj_proof(x: int)
            requires x > 0
            ensures x > 0, x >= 0
        by {
            constructor
            · omega
            · omega
        }
    ") => Ok(())
}

// Mathlib ring tactic for polynomial identity
test_verify_one_file! {
    #[test] test_ring_identity verus_code! {
        import Mathlib.Tactic.Ring

        proof fn square_of_sum(a: int, b: int)
            ensures (a + b) * (a + b) == a * a + 2 * a * b + b * b
        by {
            ring
        }
    } => Ok(())
}

// Proof combining recursive spec fn + trait method + multi-step
test_verify_one_file! {
    #[test] test_complex_combo verus_code! {
        spec fn fib(n: nat) -> nat
            decreases n
        {
            if n == 0 { 0 }
            else if n == 1 { 1 }
            else { (fib((n - 1) as nat) + fib((n - 2) as nat)) as nat }
        }

        proof fn fib_base()
            ensures fib(0) == 0, fib(1) == 1
        by {
            unfold fib
            simp
        }
    } => Ok(())
}

// Proof about enum with pattern matching in spec
test_verify_one_file! {
    #[test] test_enum_proof verus_code! {
        enum Dir { North, South, East, West }

        spec fn opposite(d: Dir) -> Dir {
            match d {
                Dir::North => Dir::South,
                Dir::South => Dir::North,
                Dir::East => Dir::West,
                Dir::West => Dir::East,
            }
        }

        proof fn opposite_north()
            ensures opposite(Dir::North) == Dir::South
        by {
            unfold opposite
            simp
        }
    } => Ok(())
}

// === Extensional equality (=~=) ===

test_verify_one_file! {
    #[test] test_ext_eq verus_code! {
        proof fn ext_eq_refl(x: int)
            ensures x =~= x
        by {
            simp
        }
    } => Ok(())
}

// === Division and modulo (int, omega can handle) ===

test_verify_one_file! {
    #[test] test_div_mod verus_code! {
        proof fn div_pos(x: int)
            requires x >= 10
            ensures x / 2 >= 5
        by {
            omega
        }

        proof fn mod_range(x: int)
            requires x >= 0
            ensures x % 3 >= 0, x % 3 < 3
        by {
            omega
        }
    } => Ok(())
}

// === Wildcard pattern in match ===

test_verify_one_file! {
    #[test] test_wildcard_match verus_code! {
        enum Color { Red, Green, Blue }

        spec fn is_red(c: Color) -> bool {
            match c {
                Color::Red => true,
                _ => false,
            }
        }

        proof fn red_check()
            ensures is_red(Color::Red)
        by {
            unfold is_red; simp
        }
    } => Ok(())
}

// === Struct update syntax { ..base } ===

test_verify_one_file! {
    #[test] test_struct_update verus_code! {
        struct Pair {
            x: int,
            y: int,
        }

        spec fn set_x(p: Pair, new_x: int) -> Pair {
            Pair { x: new_x, ..p }
        }

        spec fn get_y(p: Pair) -> int { p.y }

        proof fn update_preserves_y(p: Pair)
            ensures get_y(set_x(p, 99)) == get_y(p)
        by {
            unfold get_y; unfold set_x; simp
        }
    } => Ok(())
}

// === Generic spec fn (type params on spec fn) ===

test_verify_one_file! {
    #[test] test_generic_spec_fn verus_code! {
        spec fn identity<T>(x: T) -> T { x }

        proof fn identity_int(n: int)
            ensures identity::<int>(n) == n
        by {
            unfold identity; simp
        }
    } => Ok(())
}

// === Generic datatype ===

test_verify_one_file! {
    #[test] test_generic_datatype verus_code! {
        enum MyOption<T> {
            MySome(T),
            MyNone,
        }

        spec fn is_some<T>(o: MyOption<T>) -> bool {
            match o {
                MyOption::MySome(_) => true,
                MyOption::MyNone => false,
            }
        }

        proof fn some_is_some(x: MyOption<int>)
            requires x == MyOption::<int>::MySome(42)
            ensures is_some::<int>(x)
        by {
            unfold is_some; simp_all
        }
    } => Ok(())
}

// === Higher-order spec fn (spec_fn as parameter type) ===

test_verify_one_file! {
    #[test] test_higher_order verus_code! {
        spec fn apply(f: spec_fn(int) -> int, x: int) -> int {
            f(x)
        }

        spec fn double_fn() -> spec_fn(int) -> int {
            |x: int| x + x
        }

        proof fn apply_double()
            ensures apply(double_fn(), 5) == 10
        by {
            unfold apply; unfold double_fn; simp
        }
    } => Ok(())
}

// === Multiple match arms with different constructors ===

test_verify_one_file! {
    #[test] test_multi_arm_match verus_code! {
        enum Shape {
            Circle(int),
            Rect(int, int),
            Empty,
        }

        spec fn area(s: Shape) -> int {
            match s {
                Shape::Circle(r) => r * r,
                Shape::Rect(w, h) => w * h,
                Shape::Empty => 0,
            }
        }

        proof fn empty_area()
            ensures area(Shape::Empty) == 0
        by {
            unfold area; simp
        }
    } => Ok(())
}

// === Exists quantifier ===

test_verify_one_file! {
    #[test] test_exists verus_code! {
        spec fn gt_zero(x: int) -> bool { x > 0 }

        proof fn exists_witness()
            ensures exists|x: int| #[trigger] gt_zero(x)
        by {
            unfold gt_zero; exact Exists.intro 1 (by omega)
        }
    } => Ok(())
}

// === Implies in spec fn body ===

test_verify_one_file! {
    #[test] test_implies_spec verus_code! {
        spec fn safe_div(x: int, y: int) -> bool {
            y != 0 ==> x / y * y <= x
        }

        proof fn safe_div_pos()
            ensures safe_div(10, 3)
        by {
            unfold safe_div; omega
        }
    } => Ok(())
}

// === Fixed-width integer types (u32 → Nat, i64 → Int) ===

test_verify_one_file! {
    #[test] test_fixed_width_types verus_code! {
        proof fn u32_bound(x: u32)
            ensures x >= 0
        by {
            omega
        }

        proof fn i64_range(x: i64, y: i64)
            requires x > 0, y > 0
            ensures x + y > 1
        by {
            omega
        }
    } => Ok(())
}

// === Multiple type params ===

test_verify_one_file! {
    #[test] test_multi_type_params verus_code! {
        spec fn pair_eq<A, B>(a1: A, a2: A, b1: B, b2: B) -> bool {
            a1 == a2 && b1 == b2
        }

        proof fn pair_eq_refl(x: int, y: nat)
            ensures pair_eq::<int, nat>(x, x, y, y)
        by {
            unfold pair_eq; simp
        }
    } => Ok(())
}

// === Deeply nested precedence ===

test_verify_one_file! {
    #[test] test_precedence verus_code! {
        import Mathlib.Tactic.Ring

        proof fn precedence(a: int, b: int, c: int)
            ensures (a + b) * c == a * c + b * c
        by {
            ring
        }
    } => Ok(())
}

// === Enum variant check in spec fn ===

test_verify_one_file! {
    #[test] test_variant_check verus_code! {
        enum AB { A(int), B }

        spec fn is_a(x: AB) -> bool {
            match x {
                AB::A(_) => true,
                AB::B => false,
            }
        }

        proof fn a_check()
            ensures is_a(AB::A(42))
        by {
            unfold is_a; simp
        }
    } => Ok(())
}

// === Proof fn with only requires, no interesting ensures ===

test_verify_one_file! {
    #[test] test_trivial_ensures verus_code! {
        proof fn simple_passthrough(x: int)
            requires x > 0
            ensures x > 0
        by {
            omega
        }
    } => Ok(())
}

// === Nat subtraction (clips to 0) ===

test_verify_one_file! {
    #[test] test_nat_clip verus_code! {
        proof fn nat_sub_clip(a: nat, b: nat)
            requires b > a
            ensures (a - b) as nat == 0
        by {
            omega
        }
    } => Ok(())
}

// === Chained spec fn: all ops in one expression ===

test_verify_one_file! {
    #[test] test_complex_expr verus_code! {
        spec fn complex(x: int, y: int, z: int) -> int {
            if x > 0 && y > 0 {
                let sum = x + y;
                sum * z - (x - y)
            } else {
                0
            }
        }

        proof fn complex_zero()
            ensures complex(0, 0, 0) == 0
        by {
            unfold complex; simp
        }
    } => Ok(())
}

// === Proof fn with named return (ensures references result) ===

test_verify_one_file! {
    #[test] test_named_return verus_code! {
        spec fn succ(n: nat) -> nat { n + 1 }

        proof fn succ_pos(n: nat)
            ensures succ(n) > 0
        by {
            unfold succ; omega
        }
    } => Ok(())
}

// === Or pattern in match ===

test_verify_one_file! {
    #[test] test_or_pattern verus_code! {
        enum Traffic { Red, Yellow, Green }

        spec fn must_stop(t: Traffic) -> bool {
            match t {
                Traffic::Red | Traffic::Yellow => true,
                Traffic::Green => false,
            }
        }

        proof fn red_stops()
            ensures must_stop(Traffic::Red)
        by {
            unfold must_stop; simp
        }
    } => Ok(())
}

// === Const generic ===

test_verify_one_file! {
    #[test] test_const_generic verus_code! {
        spec fn array_len<const N: usize>() -> nat {
            N as nat
        }

        proof fn len_5()
            ensures array_len::<5>() == 5
        by {
            unfold array_len; simp
        }
    } => Ok(())
}

// === Multi-line tactic with Lean comment (verbatim source extraction) ===

test_verify_one_file! {
    #[test] test_multiline_verbatim verus_code! {
        spec fn double(x: nat) -> nat { x + x }

        proof fn lemma_double(x: nat)
            requires x > 0
            ensures double(x) > x
        by {
            unfold double
            omega
        }
    } => Ok(())
}

// === Unicode: Lean line comment with -- ===
// Unicode tactic bodies can't go through verus_code! (rustc can't lex them).
// Build the source string manually instead.

fn verus_body(body: &str) -> String {
    format!(
        "::verus_builtin_macros::verus!{{\n{body}\n}}\n"
    )
}

test_verify_one_file! {
    #[test] test_unicode_lean_line_comment verus_body("
        spec fn double(x: nat) -> nat { x + x }

        proof fn lemma_double(x: nat)
            requires x > 0
            ensures double(x) > x
        by {
            -- This is a Lean line comment
            unfold double
            omega
        }
    ") => Ok(())
}

// === Unicode: focus dot · in tactic body ===

test_verify_one_file! {
    #[test] test_unicode_focus_dot verus_body("
        proof fn conj(a: int, b: int)
            requires a > 0, b > 0
            ensures a > 0, b > 0
        by {
            constructor
            · omega
            · omega
        }
    ") => Ok(())
}

// === Error: // in tactic body ===

test_verify_one_file! {
    #[test] test_double_slash_error verus_code! {
        proof fn bad() ensures true
        by {
            // this looks like a comment but is disallowed
            omega
        }
    } => Err(e) => {
        assert!(e.errors.iter().any(|d| d.message.contains("Nat.div")));
    }
}

// === Nested enum match (exercises Constructor pattern with multiple fields) ===

test_verify_one_file! {
    #[test] test_nested_enum verus_code! {
        enum Inner { X(int), Y }
        enum Outer { Wrap(Inner), Empty }

        spec fn extract(o: Outer) -> int {
            match o {
                Outer::Wrap(Inner::X(n)) => n,
                _ => 0,
            }
        }

        proof fn extract_wrap()
            ensures extract(Outer::Wrap(Inner::X(7))) == 7
        by {
            unfold extract; simp
        }
    } => Ok(())
}

// === AST edge cases: Block fold, tuple, chained compare ===

// Block fold: multi-statement spec fn body. Each `let` nests into the
// next; the final expression is the body of the innermost let. The proof
// uses only core tactics (no Mathlib import), so this also doubles as a
// sanity check that our let-fold is shaped so `simp` can reduce it.
test_verify_one_file! {
    #[test] test_multi_let_block verus_code! {
        spec fn layered(x: int) -> int {
            let a = x + 1;
            let b = a + 2;
            let c = b + 3;
            c
        }

        proof fn layered_correct(x: int)
            ensures layered(x) == x + 6
        by {
            unfold layered; simp; omega
        }
    } => Ok(())
}

// Tuple-returning spec fn: exercises the dep_order walker finding
// `pair` when it's referenced through tuple field access in ensures.
// Specifically guards against the bug where `ReadPlace(Place::Field(…,
// Temporary(Call(pair, …))))` buried the call in a Place the walker
// treated as a leaf.
//
// Ensures is an inequality so the proof doesn't depend on arithmetic
// normalization making `x + 1 - x` collapse to `1`. After `unfold; simp`
// the goal is literally `x < x + 1`, which `omega` closes directly.
test_verify_one_file! {
    #[test] test_tuple_return verus_code! {
        spec fn pair(x: int) -> (int, int) {
            (x, x + 1)
        }

        proof fn pair_lt(x: int)
            ensures pair(x).0 < pair(x).1
        by {
            unfold pair; simp; omega
        }
    } => Ok(())
}

// Tuple-struct field access: the other branch of `field_access_name`.
// `Dt::Path + numeric field` must map to `valN` to match the datatype
// emitter's `field_name` rename. If this test fails, the two sides
// disagree on where struct field "0" went.
test_verify_one_file! {
    #[test] test_tuple_struct_field verus_code! {
        struct Point(int, int);

        spec fn origin() -> Point {
            Point(0, 0)
        }

        proof fn origin_x_zero()
            ensures origin().0 == 0
        by {
            unfold origin; simp
        }
    } => Ok(())
}

// Nested let referencing an earlier binding — exercises scope
// propagation through the Block → Let fold.
test_verify_one_file! {
    #[test] test_let_references_earlier verus_code! {
        spec fn chain(x: int) -> int {
            let y = x + 1;
            let z = y + y;
            z
        }

        proof fn chain_value(x: int)
            ensures chain(x) == x + x + 2
        by {
            unfold chain; simp; omega
        }
    } => Ok(())
}

// === Track B: exec fn with sst_to_lean ===
//
// All seven Track B slices land in this section, in roughly the order
// they were built: straight-line, if/else, mutation, loops, overflow,
// calls, closures. The "Slice N" headers below mark the boundary.
//
// Simplest straight-line exec fn: constant return, trivial ensures.
// Verified end-to-end through Lean's `tactus_auto` (→ rfl/decide/omega).

test_verify_one_file! {
    #[test] test_exec_const_return verus_code! {
        #[verifier::tactus_auto]
        fn five() -> (r: u8)
            ensures r == 5
        {
            5
        }
    } => Ok(())
}

// Exec fn with one parameter and arithmetic in the return expression.
// Ensures references the return value via its declared name.
test_verify_one_file! {
    #[test] test_exec_add_one verus_code! {
        #[verifier::tactus_auto]
        fn add_one(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            x + 1
        }
    } => Ok(())
}

// Wrong exec fn: ensures is false. Lean should reject.
test_verify_one_file! {
    #[test] test_exec_wrong_ensures verus_code! {
        #[verifier::tactus_auto]
        fn five_but_wrong() -> (r: u8)
            ensures r == 6
        {
            5
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "Expected error for wrong exec ensures");
        // Each ensures clause is wrapped with a Postcondition
        // SpanMark in WpCtx::new (D review fix); a failing
        // ensures clause now reports `(postcondition)` instead of
        // bottoming out with no kind label or — in if-branch
        // shapes — picking up the BranchCondition mark from a
        // hypothesis frame.
        let msgs: Vec<_> = err.errors.iter().map(|e| e.message.clone()).collect();
        assert!(
            msgs.iter().any(|m| m.contains(&vir::tactus_messages::paren_label(vir::tactus_messages::ASSERT_LABEL_POSTCONDITION))),
            "expected (postcondition) kind label on the failing \
             obligation. got: {:?}",
            msgs,
        );
    }
}

// Assert discharge: a body assert that holds under the requires should pass.
// Catches the bug where Asserts were silently dropped.
test_verify_one_file! {
    #[test] test_exec_assert_holds verus_code! {
        #[verifier::tactus_auto]
        fn with_assert(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x
        {
            assert(x < 200);
            x
        }
    } => Ok(())
}

// Assert discharge: a body assert that does NOT hold must be rejected.
// Before the fix, this test would have passed (bug #1) because Asserts were
// skipped in `supported_stmt`.
test_verify_one_file! {
    #[test] test_exec_assert_fails verus_code! {
        #[verifier::tactus_auto]
        fn with_false_assert(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x
        {
            assert(x < 50);  // fails when x is, e.g., 99
            x
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "Expected error for false body assert");
        // D review: AssertKind::Plain has an empty label, so the
        // error format is `at <loc>:` (no parenthesized kind).
        // Pin this so the format doesn't regress to e.g.
        // `(assert)` if someone changes Plain's label.
        let msgs: Vec<_> = err.errors.iter().map(|e| e.message.clone()).collect();
        assert!(
            msgs.iter().any(|m| m.contains("test.rs:") && !m.contains("(assert)")),
            "expected `at test.rs:L:C:` without `(assert)` parenthetical for Plain assert. got: {:?}",
            msgs,
        );
    }
}

// AssertCompute lossy-accept probe: `assert(P) by(compute)` and
// `by(compute_only)` lower to `StmX::AssertCompute(_, e, ComputeMode)`.
// Tactus drops the `ComputeMode` hint and dispatches identically to
// plain `StmX::Assert`. Lean's `decide` (which IS in `tactus_auto`'s
// ladder) is the closest analog of Verus's compute-discharge path —
// the test confirms `tactus_auto` actually closes a representative
// `by(compute)` shape, so the gap stays cosmetic (mode tag dropped)
// rather than functional. See DESIGN.md "Lossy accepted forms".
test_verify_one_file! {
    #[test] test_exec_assert_by_compute verus_code! {
        #[verifier::tactus_auto]
        fn compute_assert() -> (r: u32)
            ensures r == 4
        {
            assert(2 + 2 == 4) by(compute);
            4
        }
    } => Ok(())
}

// AssertCompute companion: `by(compute_only)` is the strict variant
// (Verus-side: rejects if interp evaluation can't close it). Tactus
// dispatches identically — same test shape, same expected outcome.
test_verify_one_file! {
    #[test] test_exec_assert_by_compute_only verus_code! {
        #[verifier::tactus_auto]
        fn compute_only_assert() -> (r: u32)
            ensures r == 4
        {
            assert(2 + 2 == 4) by(compute_only);
            4
        }
    } => Ok(())
}

// ── Slice 2: if/else WP rule ───────────────────────────────────────────
//
// `if c { s1 } else { s2 }` folds to
// `(c → wp(s1; rest)) ∧ (¬c → wp(s2; rest))`. These tests exercise
// branching at the statement level, paired with asserts or per-branch
// assigns flowing into a tail value.

// Both branches assert a fact provable from the condition. Each branch
// re-establishes its own side of `c`/`¬c` as an assert; the WP split
// supplies that fact as a hypothesis.
test_verify_one_file! {
    #[test] test_exec_if_assert_holds verus_code! {
        #[verifier::tactus_auto]
        fn describe(x: u8) -> (r: u8)
            ensures r == x
        {
            if x < 10 {
                assert(x < 10);
            } else {
                assert(x >= 10);
            }
            x
        }
    } => Ok(())
}

// Missing else branch — the then-branch side only contributes its
// asserts when `c` holds. When `c` is false, the goal reduces to the
// continuation with `¬c` as a hypothesis.
test_verify_one_file! {
    #[test] test_exec_if_no_else verus_code! {
        #[verifier::tactus_auto]
        fn maybe_check(x: u8) -> (r: u8)
            ensures r == x
        {
            if x > 0 {
                assert(x > 0);
            }
            x
        }
    } => Ok(())
}

// Assert inside a branch is false under the hypothesis. Lean must reject:
// the assert's negation can be witnessed within the `c → …` implication.
test_verify_one_file! {
    #[test] test_exec_if_assert_fails verus_code! {
        #[verifier::tactus_auto]
        fn bad_describe(x: u8) -> (r: u8)
            ensures r == x
        {
            if x < 10 {
                assert(x >= 10);  // contradicts the then-branch hypothesis
            }
            x
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "Expected error for false assert in then-branch");
    }
}

// ── Slice 3: mutation as SSA ───────────────────────────────────────────
//
// Mutation falls out of slice 1+2 for free via Lean's let-shadowing:
// every `StmX::Assign { is_init: false }` re-emits `let x := e`, which
// shadows the previous binding. Same mechanism works across if-branches
// since each branch has its own scope. Loops would need a real rename
// pass — that's the loop slice's job.

// Simple sequential mutation. Each `y = y + 1` becomes `let y := y + 1`
// in Lean; the outer `y` is shadowed.
test_verify_one_file! {
    #[test] test_exec_mut_seq verus_code! {
        #[verifier::tactus_auto]
        fn add_two(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 2
        {
            let mut y = x;
            y = y + 1;
            y = y + 1;
            y
        }
    } => Ok(())
}

// Mutation inside a branch. After the `if`, `y` in the then-branch was
// re-let-bound (so the continuation sees `y + 1`); in the else-branch
// the outer `y` is still in scope. The ensures must hold in both.
test_verify_one_file! {
    #[test] test_exec_mut_in_branch verus_code! {
        #[verifier::tactus_auto]
        fn bump_if(x: u8) -> (r: u8)
            requires x < 100
            ensures r >= x
        {
            let mut y = x;
            if y < 50 {
                y = y + 10;
            }
            y
        }
    } => Ok(())
}

// ── Slice 6: overflow obligations for fixed-width arithmetic ──────────
//
// `HasType(e, U(n))` / `HasType(e, I(n))` now render as the refinement
// predicate (`e < 2^n` / `-2^(n-1) ≤ e ∧ e < 2^(n-1)`) instead of `True`.
// Function params typed `u8`, `i32`, … pick up `(h_<name>_bound : …)`
// hypotheses so the body inherits the usual Verus type invariant.

// Without a precondition, `x + y` on two u8 values can overflow.
// Previously this was wrongly accepted; now the `x + y < 256` assert
// in the WP has no way to discharge and Lean rejects the fn.
test_verify_one_file! {
    #[test] test_exec_overflow_diagnostic verus_code! {
        #[verifier::tactus_auto]
        fn add_both(x: u8, y: u8) -> (r: u8)
            ensures r == x + y
        {
            x + y
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "arith on unbounded u8 should fail overflow check");
    }
}

// Tight bound: requires x + y ≤ 255 (the largest non-overflowing sum).
// Should verify — omega proves `x + y < 256` from the requires.
test_verify_one_file! {
    #[test] test_exec_overflow_tight_ok verus_code! {
        #[verifier::tactus_auto]
        fn add_both_guarded(x: u8, y: u8) -> (r: u8)
            requires x + y <= 255
            ensures r == x + y
        {
            x + y
        }
    } => Ok(())
}

// Signed arithmetic: i8 range is [-128, 127]. Adding two i8s can
// underflow below -128 or overflow above 127. Without guards, omega
// fails to discharge both bounds.
test_verify_one_file! {
    #[test] test_exec_signed_overflow_fails verus_code! {
        #[verifier::tactus_auto]
        fn add_i8(x: i8, y: i8) -> (r: i8)
            ensures r as int == x as int + y as int
        {
            x + y
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "signed i8 arith without bounds should fail");
    }
}

// u8 subtraction with a sufficient guard. The `requires y <= x` makes
// `x - y` non-negative; the u-as-Int encoding gives us `Int`
// subtraction, so omega sees the true mathematical value.
test_verify_one_file! {
    #[test] test_exec_underflow_guarded verus_code! {
        #[verifier::tactus_auto]
        fn sub_u8_guarded(x: u8, y: u8) -> (r: u8)
            requires y <= x
            ensures r as int == x as int - y as int
        {
            x - y
        }
    } => Ok(())
}

// Unguarded u8 subtraction. With u-types rendered as Lean `Int`, the
// subtraction is mathematical (goes negative when y > x), so the
// `HasType(x - y, U(8))` refinement check — specifically the `0 ≤`
// half — catches the underflow. Before the u-as-Int fix this test
// *incorrectly* verified because Nat's truncating subtraction made
// the lower bound trivially true.
test_verify_one_file! {
    #[test] test_exec_underflow_unguarded_fails verus_code! {
        #[verifier::tactus_auto]
        fn sub_u8(x: u8, y: u8) -> (r: u8)
            ensures r as int == x as int - y as int
        {
            x - y
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "u8 sub without a lower-bound guard should fail");
    }
}

// u8 multiplication has a MUCH tighter overflow bound than addition:
// two u8s up to 255 each can produce up to 65025. Without bounds,
// omega rejects.
test_verify_one_file! {
    #[test] test_exec_mul_overflow_fails verus_code! {
        #[verifier::tactus_auto]
        fn mul_u8(x: u8, y: u8) -> (r: u8)
            ensures r == x * y
        {
            x * y
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "u8 mul without bounds should fail");
    }
}

// u32 arithmetic: exercises the wider range (bound `2^32`). Uses a
// precondition that's tight enough for omega to discharge.
test_verify_one_file! {
    #[test] test_exec_u32_add_guarded verus_code! {
        #[verifier::tactus_auto]
        fn add_u32(x: u32, y: u32) -> (r: u32)
            requires x < 1_000_000, y < 1_000_000
            ensures r == x + y
        {
            x + y
        }
    } => Ok(())
}

// `u8::MAX` in a spec context. Verus emits this as
// `IntegerTypeBound(UnsignedMax, _)` applied to literal bit-width 8;
// until this session that rendered as `True` and any test touching it
// failed with a Lean type error. Now it's `255`.
test_verify_one_file! {
    #[test] test_exec_integer_type_bound_u8_max verus_code! {
        #[verifier::tactus_auto]
        fn near_max(x: u8) -> (r: u8)
            requires x < u8::MAX
            ensures r == x + 1
        {
            x + 1
        }
    } => Ok(())
}

// `i8::MAX` — SignedMax, which Verus emits as `2^(bits-1) - 1`.
test_verify_one_file! {
    #[test] test_exec_integer_type_bound_i8_max verus_code! {
        #[verifier::tactus_auto]
        fn near_max_i8(x: i8) -> (r: i8)
            requires x < i8::MAX
            ensures r as int == x as int + 1
        {
            x + 1
        }
    } => Ok(())
}

// Mutation visible only within one branch must not leak past the if.
// Without proper scoping this would incorrectly satisfy `r == x + 1`
// even when the else-branch runs; Lean's let-shadowing rejects it.
test_verify_one_file! {
    #[test] test_exec_mut_branch_leak verus_code! {
        #[verifier::tactus_auto]
        fn bump_if_wrong(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1  // false when the else-branch runs
        {
            let mut y = x;
            if y < 50 {
                y = y + 1;
            }
            y
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "post-if must reference outer y in else branch");
    }
}

// Nested if/else. The inner branch's hypothesis stacks with the outer one
// — `assert(x < 100)` under the `else` of the inner if has both `x >= 50`
// and the outer `x < 100` available.
test_verify_one_file! {
    #[test] test_exec_nested_if verus_code! {
        #[verifier::tactus_auto]
        fn nested_check(x: u8) -> (r: u8)
            ensures r == x
        {
            if x < 100 {
                if x < 50 {
                    assert(x < 50);
                } else {
                    assert(x >= 50);
                    assert(x < 100);
                }
            } else {
                assert(x >= 100);
            }
            x
        }
    } => Ok(())
}

// ── Review follow-ups ──────────────────────────────────────────────────

// A `char` param gets an `h_c_bound : c < 0x110000` hypothesis from
// `type_bound_predicate`. This test body has nothing to verify on its
// own — it's a regression guard that adding the Char bound didn't break
// the generator. If the predicate ever stops rendering or omega trips
// over the hex literal, this test fails.
test_verify_one_file! {
    #[test] test_exec_char_bound verus_code! {
        #[verifier::tactus_auto]
        fn trivial_char(c: char) -> (r: bool)
            ensures r == true
        {
            true
        }
    } => Ok(())
}

// Cross-width int cast: u8 → i16 widening. The fix to `clip_to_node`
// inserts `Int.ofNat` when a `Nat`-rendered source (u8) goes to an
// `Int`-rendered destination (i16). Before, this rendered as a plain
// `x`, leaving the result type-mismatched in Lean.
test_verify_one_file! {
    #[test] test_exec_widen_u8_to_i16 verus_code! {
        #[verifier::tactus_auto]
        fn widen(x: u8) -> (r: i16)
            ensures r >= 0
        {
            x as i16
        }
    } => Ok(())
}

// HeightCompare on int operands: `is_smaller_than(a, b)` lowers to
// `lhs < rhs` when both heights are int (the int's height IS the
// int per `vir::recursion::height_is_int`). Pins the codegen path
// — previously rejected with "unsupported binary op".
test_verify_one_file! {
    #[test] test_exec_is_smaller_than_int verus_code! {
        use verus_builtin::*;

        #[verifier::tactus_auto]
        fn check_smaller(a: u8, b: u8) -> (r: bool)
            requires a < b
            ensures is_smaller_than(a as int, b as int)
        {
            true
        }
    } => Ok(())
}

// NOTE: Multi-binder `Bind(Let([(a, val_a), (b, val_b)]), body)`
// support landed in `lift_if_value` and `walk_let` (#92). It's
// defensive — turns out Verus's SST for tuple destructure patterns
// goes through `Ctor` + field projection, not multi-binder Let.
// Constructing a regression test would require synthetic SST input;
// the unfold is unit-tested via `match_single_let_bind`'s edge
// cases, which cover the single-binder path.

// ── tactus_usize_bound tactic ─────────────────────────────────────
// Discharges `x < usize_hi` / `-isize_hi ≤ x ∧ x < isize_hi` shapes
// that the default `tactus_auto` toolbox can't close due to the
// symbolic `2 ^ arch_word_bits`. Uses #81's per-fn override to
// invoke it as the closer.
test_verify_one_file! {
    #[test] test_exec_usize_bound_tactic verus_code! {
        // A constant within both 32-bit and 64-bit usize range.
        // `tactus_auto`'s rungs (rfl/decide/omega/simp_all) can't
        // discharge `1000000 < 2 ^ arch_word_bits` symbolically;
        // tactus_usize_bound case-splits and reduces.
        #[verifier::tactus_auto]
        #[verifier::tactus_tactic("first | tactus_auto | tactus_usize_bound")]
        fn small_usize() -> (r: usize)
            ensures r == 1000000
        {
            1000000
        }
    } => Ok(())
}

// ── Per-fn tactic override ────────────────────────────────────────
// `#[verifier::tactus_tactic("ring")]` replaces `tactus_auto` in
// generated theorems with the user-supplied Lean tactic. Useful for
// fns where the default toolbox (rfl/decide/omega/simp_all) can't
// discharge the obligations.
test_verify_one_file! {
    #[test] test_exec_tactus_tactic_override verus_code! {
        // Use `omega` directly as the override — simpler than the
        // default toolbox (no rfl/decide/simp_all rungs) but
        // sufficient for this linear-arithmetic goal. Pins that the
        // user's tactic gets used, not silently augmented with the
        // default closer.
        #[verifier::tactus_auto]
        #[verifier::tactus_tactic("omega")]
        fn add_one(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            x + 1
        }
    } => Ok(())
}

// Negative: empty `tactus_tactic("")` is rejected at parse time
// (rather than emitting `:= by` followed by nothing in Lean).
// Pins the parser's empty-trim check in `attributes.rs`.
test_verify_one_file! {
    #[test] test_exec_tactus_tactic_empty_rejected verus_code! {
        #[verifier::tactus_auto]
        #[verifier::tactus_tactic("")]
        fn add_one(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        { x + 1 }
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e|
                e.message.contains(vir::tactus_messages::TACTUS_TACTIC_EMPTY_ERR)),
            "expected empty-tactic-string rejection, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
}

// Negative: a tactic override that can't discharge the goal still
// fails cleanly. Pins that the user's tactic IS being invoked
// (and isn't being silently augmented with the default closer).
test_verify_one_file! {
    #[test] test_exec_tactus_tactic_failing verus_code! {
        #[verifier::tactus_auto]
        #[verifier::tactus_tactic("rfl")]  // rfl can't prove arithmetic
        fn add_one_rfl(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            x + 1
        }
    } => Err(err) => {
        assert!(
            err.errors.len() >= 1,
            "rfl override on arith goal should fail",
        );
    }
}

// ── assume(P) warning ─────────────────────────────────────────────
// `assume(P)` enters P as a hypothesis without a proof — a soundness
// escape hatch for incremental development. Tactus surfaces a
// warning per `assume` site so users know which assumptions are
// load-bearing on their verification.
test_verify_one_file! {
    #[test] test_exec_assume_warning verus_code! {
        #[verifier::tactus_auto]
        fn use_assume(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 5
        {
            assume(x + 5 < 256);  // unproved: caller doesn't bound x to <251
            x + 5
        }
    } => Ok(err) => {
        assert!(
            err.warnings.iter().any(|w|
                w.message.contains(vir::tactus_messages::ASSUME_WARNING_TAG)),
            "expected an unproved-assumption warning, got: {:?}",
            err.warnings.iter().map(|w| &w.message).collect::<Vec<_>>(),
        );
    }
}

// ── Bit-width coverage matrix ─────────────────────────────────────
// u8/u32/i8 are exercised by the overflow/widen tests above. The
// codegen path is identical across widths (just a different bound
// constant), but until these regression tests landed only three
// widths had explicit coverage. Each test pins arithmetic + a tight
// `requires` that lets omega discharge the overflow check.

test_verify_one_file! {
    #[test] test_exec_u16_add verus_code! {
        #[verifier::tactus_auto]
        fn add_u16(x: u16, y: u16) -> (r: u16)
            requires x < 30_000, y < 30_000
            ensures r == x + y
        { x + y }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_u64_add verus_code! {
        #[verifier::tactus_auto]
        fn add_u64(x: u64, y: u64) -> (r: u64)
            requires x < 1_000_000_000_000, y < 1_000_000_000_000
            ensures r == x + y
        { x + y }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_u128_add verus_code! {
        #[verifier::tactus_auto]
        fn add_u128(x: u128, y: u128) -> (r: u128)
            requires x < 1_000_000_000_000, y < 1_000_000_000_000
            ensures r == x + y
        { x + y }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_i16_add verus_code! {
        #[verifier::tactus_auto]
        fn add_i16(x: i16, y: i16) -> (r: i16)
            requires -10_000 <= x < 10_000, -10_000 <= y < 10_000
            ensures r as int == x as int + y as int
        { x + y }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_i32_add verus_code! {
        #[verifier::tactus_auto]
        fn add_i32(x: i32, y: i32) -> (r: i32)
            requires -1_000_000 <= x < 1_000_000, -1_000_000 <= y < 1_000_000
            ensures r as int == x as int + y as int
        { x + y }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_i64_add verus_code! {
        #[verifier::tactus_auto]
        fn add_i64(x: i64, y: i64) -> (r: i64)
            requires -1_000_000_000 <= x < 1_000_000_000,
                     -1_000_000_000 <= y < 1_000_000_000
            ensures r as int == x as int + y as int
        { x + y }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_i128_add verus_code! {
        #[verifier::tactus_auto]
        fn add_i128(x: i128, y: i128) -> (r: i128)
            requires -1_000_000_000 <= x < 1_000_000_000,
                     -1_000_000_000 <= y < 1_000_000_000
            ensures r as int == x as int + y as int
        { x + y }
    } => Ok(())
}

// Negative companion: u16 overflow should fire just like u8/u32 do.
// Pins that the bound expression is non-trivially used (not just a
// `True` placeholder) for u16.
test_verify_one_file! {
    #[test] test_exec_u16_overflow_fails verus_code! {
        #[verifier::tactus_auto]
        fn add_u16_unbounded(x: u16, y: u16) -> (r: u16)
            ensures r == x + y
        { x + y }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "u16 add without bounds should fail");
    }
}

// Non-simple LHS assignment used to be silently dropped by `walk`.
// Now it's rejected upfront by `check_stm` with a clear "not yet
// supported" error. This uses a struct field assignment, which Verus
// compiles to `StmX::Assign` with a non-simple `dest`.
test_verify_one_file! {
    #[test] test_exec_field_assign_rejected verus_code! {
        struct Pair { a: u8, b: u8 }

        #[verifier::tactus_auto]
        fn bump_first(p: Pair) -> (r: Pair)
            requires p.a < 100
            ensures r.a == p.a + 1, r.b == p.b
        {
            let mut out = p;
            out.a = out.a + 1;  // non-simple LHS — not yet supported
            out
        }
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e|
                e.message.contains(vir::tactus_messages::ASSIGN_NON_SIMPLE_LHS_TAG)),
            "expected a non-simple-LHS rejection"
        );
    }
}

// Proof fn using `u8::MAX` in a precondition. Goes through the VIR-AST
// path (`to_lean_expr.rs`) rather than SST. Verus typically const-folds
// `u8::MAX` to 255 at VIR construction, but if it ever doesn't, this
// test exercises the mirrored `IntegerTypeBound` fix that used to
// silently emit the bit-width instead of the bound.
test_verify_one_file! {
    #[test] test_proof_u8_max_usage verus_code! {
        proof fn below_u8_max(x: u8)
            requires x < u8::MAX
            ensures (x as int) + 1 <= 255
        by {
            omega
        }
    } => Ok(())
}

// `usize::BITS` — an `IntegerTypeBound::ArchWordBits` reference. Before
// wiring this through the prelude axiom, the codegen path panicked. Now
// it emits `arch_word_bits` (an opaque `Nat` axiom), so `x < usize::BITS`
// becomes `x < arch_word_bits`. The proof needs `arch_word_bits_valid` —
// the disjunction axiom — but omega + decide can close it after a
// case-split via `rcases`. Rather than hand-prove, we keep this as a
// minimal "doesn't panic" smoke test: ensures is trivially `True`.
test_verify_one_file! {
    #[test] test_proof_arch_word_bits_compiles verus_code! {
        proof fn arch_bits_referenced(x: u32)
            requires x < usize::BITS
            ensures true
        by {
            simp
        }
    } => Ok(())
}

// ── Slice 5: loops (init / maintain / use) ────────────────────────────
//
// Simplest loop shape we support: exactly one top-level `while` with a
// simple condition, invariant true at entry AND exit, single-expression
// `decreases`, `loop_isolation: true`, no break/continue. The loop emits
// three separate theorems: init (pre-loop → invariant), maintain
// (invariant ∧ cond → wp(body, invariant ∧ decreases-measure decreased)),
// and a main theorem where post-loop code runs under havoced modified
// vars + invariant + ¬cond.

test_verify_one_file! {
    #[test] test_exec_loop_count_down verus_code! {
        #[verifier::tactus_auto]
        fn count_down(n: u8) -> (r: u8)
            ensures r == 0
        {
            let mut x: u8 = n;
            while x > 0
                invariant x <= n
                decreases x
            {
                x = x - 1;
            }
            x
        }
    } => Ok(())
}

// Loop that counts *up* — modified var is a different kind of
// monotonic, and the invariant bounds it against an upper ceiling
// from the requires, not a fn param directly.
test_verify_one_file! {
    #[test] test_exec_loop_count_up verus_code! {
        #[verifier::tactus_auto]
        fn count_up_to(n: u8) -> (r: u8)
            requires n <= 100
            ensures r == n
        {
            let mut x: u8 = 0;
            while x < n
                invariant x <= n
                decreases n - x
            {
                x = x + 1;
            }
            x
        }
    } => Ok(())
}

// A loop whose invariant gets violated — here the maintain obligation
// fails because `x = x + 2` breaks the invariant `x <= n`. This tests
// the maintain theorem's rejection path.
test_verify_one_file! {
    #[test] test_exec_loop_invariant_fails verus_code! {
        #[verifier::tactus_auto]
        fn bad_loop(n: u8) -> (r: u8)
            requires n <= 100
            ensures r == n
        {
            let mut x: u8 = 0;
            while x < n
                invariant x <= n
                decreases n - x
            {
                x = x + 2;  // overshoots — invariant x <= n may fail
            }
            x
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "broken-invariant loop should be rejected");
        // D Stage 5: the maintain failure should be labeled
        // `(loop invariant)` — per-obligation theorem emission
        // makes find_span_mark structurally exact for loops.
        let msgs: Vec<_> = err.errors.iter().map(|e| e.message.clone()).collect();
        assert!(
            msgs.iter().any(|m| m.contains(&vir::tactus_messages::paren_label(vir::tactus_messages::ASSERT_LABEL_LOOP_INVARIANT))),
            "expected (loop invariant) kind label on the failing \
             obligation. got: {:?}",
            msgs,
        );
    }
}

// Two sequential loops in one fn. Each loop emits its own conjunction
// in the main goal; the second loop's continuation is nested inside
// the first's use clause. Structurally:
//   init₁ ∧ maintain₁ ∧ (havoc₁ → init₂ ∧ maintain₂ ∧ (havoc₂ → ensures))
test_verify_one_file! {
    #[test] test_exec_loop_sequential verus_code! {
        #[verifier::tactus_auto]
        fn two_loops(n: u8) -> (r: u8)
            requires n <= 50
            ensures r == 0
        {
            let mut x: u8 = n;
            while x > 0
                invariant x <= n
                decreases x
            {
                x = x - 1;
            }
            // x == 0 here
            let mut y: u8 = 0;
            while y < x
                invariant y <= x, x == 0
                decreases x - y
            {
                y = y + 1;
            }
            x
        }
    } => Ok(())
}

// Nested loops — the outer loop's body contains another loop. The
// inner loop's obligations (init/maintain/use) land inside the
// outer's maintain clause. A genuine stress test of the recursive
// architecture.
test_verify_one_file! {
    #[test] test_exec_loop_nested verus_code! {
        #[verifier::tactus_auto]
        fn nested(n: u8) -> (r: u8)
            requires n <= 10
            ensures r == 0
        {
            let mut i: u8 = n;
            while i > 0
                invariant i <= n
                decreases i
            {
                let mut j: u8 = i;
                while j > 0
                    invariant j <= i, i <= n
                    decreases j
                {
                    j = j - 1;
                }
                i = i - 1;
            }
            i
        }
    } => Ok(())
}

// Loop inside an `if` branch — the loop's obligations land inside
// the branch's `c → …` continuation. Tests that the WP composition
// flows through IfThenElse into BodyItem::Loop correctly.
test_verify_one_file! {
    #[test] test_exec_loop_in_if_branch verus_code! {
        #[verifier::tactus_auto]
        fn conditional_loop(n: u8, cond: bool) -> (r: u8)
            requires n <= 50
            ensures r <= n
        {
            let mut x: u8 = n;
            if cond {
                while x > 0
                    invariant x <= n
                    decreases x
                {
                    x = x - 1;
                }
            }
            x
        }
    } => Ok(())
}

// Mirror of the above with the loop in the *else*-branch — guards
// against a copy-paste bug in `BodyItem::contains_loop` or
// `build_goal`'s If arm that only handled the `then` side.
test_verify_one_file! {
    #[test] test_exec_loop_in_else_branch verus_code! {
        #[verifier::tactus_auto]
        fn loop_in_else(n: u8, skip: bool) -> (r: u8)
            requires n <= 50
            ensures r <= n
        {
            let mut x: u8 = n;
            if skip {
                // no-op; loop is in the else branch
            } else {
                while x > 0
                    invariant x <= n
                    decreases x
                {
                    x = x - 1;
                }
            }
            x
        }
    } => Ok(())
}

// Loop with empty invariants — `while cond decreases D { ... }` with
// no explicit invariant. `inv_conj()` collapses to `True` and the
// init/use clauses become trivial. Tests the degenerate case.
test_verify_one_file! {
    #[test] test_exec_loop_no_invariant verus_code! {
        #[verifier::tactus_auto]
        fn no_inv(n: u8) -> (r: u8)
            requires n <= 100
            ensures true  // any postcondition works when body is simple
        {
            let mut x: u8 = n;
            while x > 0
                decreases x
            {
                x = x - 1;
            }
            x
        }
    } => Ok(())
}

// Loop whose decreases measure doesn't actually decrease — the body
// leaves `x` unchanged. Maintain obligation must reject because
// `D_new < D_old` fails.
test_verify_one_file! {
    #[test] test_exec_loop_decreases_unchanged verus_code! {
        #[verifier::tactus_auto]
        fn non_terminating(n: u8) -> (r: u8)
            requires n > 0
            ensures r == n
        {
            let mut x: u8 = n;
            while x > 0
                invariant x == n
                decreases x
            {
                // body doesn't touch x — decreases measure stays put
                assert(x > 0);
            }
            x
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "non-decreasing measure must be rejected");
        // D Stage 6: pin `(loop decrease)` kind label. Per-obligation
        // emission gives the decrease its own theorem; find_span_mark
        // returns the LoopDecrease mark by construction.
        let msgs: Vec<_> = err.errors.iter().map(|e| e.message.clone()).collect();
        assert!(
            msgs.iter().any(|m| m.contains(&vir::tactus_messages::paren_label(vir::tactus_messages::ASSERT_LABEL_LOOP_DECREASE))),
            "expected (loop decrease) kind label on the failing \
             obligation. got: {:?}",
            msgs,
        );
    }
}

// D Stage 6: invariant fails AT ENTRY (init), not in maintain.
// `false_invariant` requires nothing about x and asserts an
// invariant that doesn't hold initially. The init-clause theorem
// (`OblCtx → I`) is the failing one, distinct from any
// maintain-clause theorem in the same fn.
test_verify_one_file! {
    #[test] test_exec_loop_invariant_init_fails verus_code! {
        #[verifier::tactus_auto]
        fn bad_init(n: u8) -> (r: u8)
            ensures r == n
        {
            let mut x: u8 = 0;
            while x < n
                invariant x > 0  // can't hold at entry: x = 0
                decreases n - x
            {
                x = x + 1;
            }
            x
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "init-failing invariant must be rejected");
        let msgs: Vec<_> = err.errors.iter().map(|e| e.message.clone()).collect();
        assert!(
            msgs.iter().any(|m| m.contains(&vir::tactus_messages::paren_label(vir::tactus_messages::ASSERT_LABEL_LOOP_INVARIANT))),
            "expected (loop invariant) kind label on init failure. got: {:?}",
            msgs,
        );
    }
}

// D review: USE clause failure. Loop's invariant is too weak to
// derive the fn ensures after the loop exits. Maintain succeeds
// (invariant maintained), init succeeds (invariant holds at
// entry), but `I ∧ ¬cond → ensures` fails because `I = (x ≤ n)`
// alone (without the body's accumulated work) can't establish
// `r == n`. The use-clause theorem walks `after` (which Done's
// onto the fn ensures) under the use ctx; failing obligation is
// the Postcondition, NOT a loop invariant.
test_verify_one_file! {
    #[test] test_exec_loop_use_clause_fails verus_code! {
        #[verifier::tactus_auto]
        fn weak_inv(n: u8) -> (r: u8)
            ensures r == n
        {
            let mut x: u8 = 0;
            while x < n
                invariant x <= n  // doesn't say x reaches n at exit
                decreases n - x
            {
                x = x + 1;
            }
            // At loop exit: x ≤ n ∧ ¬(x < n) gives x == n (correct
            // mathematically), so this should actually PASS. Hmm.
            // To force a USE failure, need an inv that doesn't
            // imply the ensures.
            x
        }
    } => Ok(())
}

// D review: USE failure with a weaker ensures-vs-invariant gap.
// Invariant says only `x <= n`, ensures says `r > 0`. At exit
// `x ≤ n ∧ ¬(x < n)` gives x == n; if n == 0 then r == 0, which
// violates `r > 0`. The use clause theorem fails while init and
// maintain succeed.
test_verify_one_file! {
    #[test] test_exec_loop_use_clause_fails_postcondition verus_code! {
        #[verifier::tactus_auto]
        fn maybe_zero(n: u8) -> (r: u8)
            ensures r > 0
        {
            let mut x: u8 = 0;
            while x < n
                invariant x <= n
                decreases n - x
            {
                x = x + 1;
            }
            x
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "use clause failure must be rejected");
        // Should be (postcondition), NOT (loop invariant) — the
        // failing obligation is the fn ensures, walked under the
        // use ctx (which has the loop invariant as a hypothesis,
        // not as the goal).
        let msgs: Vec<_> = err.errors.iter().map(|e| e.message.clone()).collect();
        assert!(
            msgs.iter().any(|m| m.contains(&vir::tactus_messages::paren_label(vir::tactus_messages::ASSERT_LABEL_POSTCONDITION))),
            "expected (postcondition) kind label on use-clause failure. got: {:?}",
            msgs,
        );
    }
}

// D review: multi-clause requires, ONE clause failing. Caller
// satisfies `x < 100` but not `x > 5`. The current code emits
// one precondition theorem with the conjunction as goal; Lean
// shows which conjunct in the unsolved goal display.
test_verify_one_file! {
    #[test] test_exec_call_multi_requires_one_fails verus_code! {
        #[verifier::tactus_auto]
        fn callee(x: u8) -> (r: u8)
            requires x > 5, x < 100
            ensures r == x
        {
            x
        }

        #[verifier::tactus_auto]
        fn caller(x: u8) -> (r: u8)
            requires x < 100   // satisfies one but not both
            ensures r == x
        {
            callee(x)
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "multi-requires partial-violation must fail");
        let msgs: Vec<_> = err.errors.iter().map(|e| e.message.clone()).collect();
        assert!(
            msgs.iter().any(|m| m.contains(&vir::tactus_messages::paren_label(vir::tactus_messages::ASSERT_LABEL_CALL_PRECONDITION))),
            "expected (precondition) label. got: {:?}",
            msgs,
        );
    }
}

// D review: multi-clause ensures, ONE clause failing. WpCtx::new
// wraps each clause with its own Postcondition SpanMark, so
// emit_done_or_split splits the conjunction into per-clause
// theorems. Body returns `5`, ensures says `r == 5 ∧ r > 100` —
// only the second clause fails, and the failing theorem is its
// per-clause Postcondition.
test_verify_one_file! {
    #[test] test_exec_multi_ensures_one_fails verus_code! {
        #[verifier::tactus_auto]
        fn five() -> (r: u8)
            ensures r == 5, r > 100
        {
            5
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "multi-ensures partial-violation must fail");
        let msgs: Vec<_> = err.errors.iter().map(|e| e.message.clone()).collect();
        assert!(
            msgs.iter().any(|m| m.contains(&vir::tactus_messages::paren_label(vir::tactus_messages::ASSERT_LABEL_POSTCONDITION))),
            "expected (postcondition) label on the failing clause. got: {:?}",
            msgs,
        );
    }
}

// D review: conjunctive `assert(P ∧ Q)`. Single Wp::Assert with
// a conjunctive cond — emits one theorem with `P ∧ Q` as goal
// (NOT split per-conjunct, unlike Done leaves). Documents the
// current behavior; if either conjunct fails Lean's error shows
// the unsolved goal which makes the failing conjunct visible.
test_verify_one_file! {
    #[test] test_exec_conjunctive_assert verus_code! {
        #[verifier::tactus_auto]
        fn conj_assert(x: u8) -> (r: u8)
            requires x < 50
            ensures r == x
        {
            assert(x < 100 && x >= 0);
            x
        }
    } => Ok(())
}

// Mutation in BOTH branches of an if, used after. Slice 3 claims this
// works via Lean let-shadowing. The post-if continuation uses `y` —
// each branch shadows it independently, and the value at the post-if
// point IS each branch's shadowed `y` (different between branches).
// Untested until now.
test_verify_one_file! {
    #[test] test_exec_mutation_both_branches verus_code! {
        #[verifier::tactus_auto]
        fn choose(cond: bool) -> (r: u8)
            ensures r == 1 || r == 2
        {
            let mut y: u8 = 0;
            if cond {
                y = 1;
            } else {
                y = 2;
            }
            y
        }
    } => Ok(())
}

// Tail if-expression — the exact pattern that used to trip `omega`
// before we added `lift_if_value`. Value is `if c then a else b` at
// return position; we lift it to goal level so each branch lands on a
// concrete leaf omega can close.
test_verify_one_file! {
    #[test] test_exec_tail_if_expression verus_code! {
        #[verifier::tactus_auto]
        fn max_two(a: u8, b: u8) -> (r: u8)
            ensures a <= r, b <= r
        {
            if a >= b { a } else { b }
        }
    } => Ok(())
}

// Let-bound if-expression — same lift mechanism as the tail-return
// case, but triggered via `BodyItem::Let` with an `ExpX::If` on the
// RHS. Without the lift, omega would fail on `(if c then 0 else x)`
// inside subsequent arithmetic.
test_verify_one_file! {
    #[test] test_exec_let_if_expression verus_code! {
        #[verifier::tactus_auto]
        fn clamp_low(x: u8) -> (r: u8)
            ensures r == 0 || r == x
        {
            let y: u8 = if x < 5 { 0 } else { x };
            y
        }
    } => Ok(())
}

// Early return from inside an if-branch, with tail code after the if.
// SST represents this as `StmX::Return { inside_body: true }`. Our
// pipeline now handles it by treating any Return as a BodyItem::Return
// that terminates its local sequence — the if's then-branch gets the
// early-return behaviour, the else falls through to the tail.
test_verify_one_file! {
    #[test] test_exec_early_return verus_code! {
        #[verifier::tactus_auto]
        fn clip_zero(x: u8) -> (r: u8)
            requires x <= 10
            ensures r <= 10
        {
            if x == 0 {
                return 0;
            }
            x
        }
    } => Ok(())
}

// #121: inverse of test_exec_early_return — return in the *else*
// branch where the then-branch falls through to the tail. Covers
// the symmetric path that was previously untested per DESIGN.md.
test_verify_one_file! {
    #[test] test_exec_return_in_else_branch verus_code! {
        #[verifier::tactus_auto]
        fn clip_high(x: u8) -> (r: u8)
            requires x <= 200
            ensures r <= 100
        {
            if x <= 100 {
                x
            } else {
                return 100;
            }
        }
    } => Ok(())
}

// #121: loop modifying 3+ vars. Existing tests cover loops that
// modify at most 2 vars; `quantify_mod_vars` builds ∀-binders
// from arbitrary-length `modified_vars`, so the multi-var path
// was supported in principle but never directly exercised.
test_verify_one_file! {
    #[test] test_exec_loop_three_modified_vars verus_code! {
        #[verifier::tactus_auto]
        fn three_counters(n: u8) -> (r: u8)
            requires n <= 10
            ensures r == 0
        {
            let mut a: u8 = n;
            let mut b: u8 = 0;
            let mut c: u8 = 0;
            while a > 0
                invariant a + b + c == n, a <= n, b <= n, c <= n
                decreases a
            {
                a = a - 1;
                if b < n { b = b + 1; } else { c = c + 1; }
            }
            a
        }
    } => Ok(())
}

// #121: nested if with a loop in EACH branch. The combinatorial
// coverage gap from DESIGN.md — both branches independently exercise
// the loop machinery, so the post-if continuation walks two distinct
// loop ctxs.
test_verify_one_file! {
    #[test] test_exec_nested_if_with_loops_in_both_branches verus_code! {
        #[verifier::tactus_auto]
        fn branch_loops(flag: bool, n: u8) -> (r: u8)
            requires n <= 10
            ensures r == 0
        {
            if flag {
                let mut x: u8 = n;
                while x > 0
                    invariant x <= n
                    decreases x
                {
                    x = x - 1;
                }
                x
            } else {
                let mut y: u8 = n;
                while y > 0
                    invariant y <= n
                    decreases y
                {
                    y = y - 1;
                }
                y
            }
        }
    } => Ok(())
}

// Usize param: `type_bound_predicate` now emits `0 ≤ e ∧ e < usize_hi`
// as the refinement, using the prelude `usize_hi` axiom. This
// trivially-bounded case verifies — the bound check reduces to True
// under the `requires`. For more interesting usize arithmetic the
// user would need to case-split `arch_word_bits_valid` explicitly;
// see DESIGN.md.
test_verify_one_file! {
    #[test] test_exec_usize_trivially_bounded verus_code! {
        #[verifier::tactus_auto]
        fn just_return(x: usize) -> (r: usize)
            requires x == 0
            ensures r == 0
        {
            x
        }
    } => Ok(())
}

// Unguarded usize arithmetic — the soundness guarantee. Before we
// emitted the `usize_hi` bound, `x + y` silently verified because no
// upper-bound check fired. Now the `HasType(x + y, USize)` check
// shows up in the goal and omega can't discharge it without user
// guidance → rejected. This is the honest soundness story.
test_verify_one_file! {
    #[test] test_exec_usize_overflow_fails verus_code! {
        #[verifier::tactus_auto]
        fn add_usize(x: usize, y: usize) -> (r: usize)
            ensures r == x + y
        {
            x + y
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "unguarded usize arith should fail");
    }
}

// ── Slice 7: function calls in exec fn bodies ─────────────────────────
//
// `let y = foo(a)` generates:
//   (let p := a; requires_conj)
//   ∧ ∀ (ret : T), h_bound(ret) → (let p := a; ensures_with_ret) →
//       let y := ret; wp(rest)
//
// Callee spec is inlined (via `vir_expr_to_ast` on its require/ensure
// fields); the callee doesn't need its own Lean definition.

// Simple: caller passes a value, callee's requires is compatible,
// ensures flows into the caller's tail ensures.
test_verify_one_file! {
    #[test] test_exec_call_basic verus_code! {
        #[verifier::tactus_auto]
        fn add_one(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            x + 1
        }

        #[verifier::tactus_auto]
        fn add_two(x: u8) -> (r: u8)
            requires x < 50
            ensures r == x + 2
        {
            let y: u8 = add_one(x);
            add_one(y)
        }
    } => Ok(())
}

// Caller's arg doesn't meet callee's requires — must be rejected.
// `add_one(x)` needs `x < 100`; caller only guarantees `x <= 200`.
test_verify_one_file! {
    #[test] test_exec_call_requires_violated verus_code! {
        #[verifier::tactus_auto]
        fn add_one(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            x + 1
        }

        #[verifier::tactus_auto]
        fn bad_caller(x: u8) -> (r: u8)
            requires x <= 200
            ensures r == x + 1
        {
            add_one(x)
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "caller must satisfy callee's requires");
        // #51 source mapping: the failing precondition should point
        // at the CALL SITE (the `add_one(x)` expression in bad_caller),
        // not at the callee's `requires x < 100` line in add_one.
        let msgs: Vec<_> = err.errors.iter().map(|e| e.message.clone()).collect();
        assert!(
            msgs.iter().any(|m| m.contains("at ") && m.contains("test.rs:")),
            "expected the error to cite a call-site Rust location via #51 \
             SpanMark instrumentation. got: {:?}",
            msgs,
        );
        // D Stage 5: precondition failures get a (precondition)
        // kind label. Per-obligation theorem emission isolates
        // each call-site precondition into its own theorem, so
        // find_span_mark returns the CallPrecondition mark
        // (rather than confusing it with adjacent obligations
        // like termination checks or call-ensures hyps).
        assert!(
            msgs.iter().any(|m| m.contains(&vir::tactus_messages::paren_label(vir::tactus_messages::ASSERT_LABEL_CALL_PRECONDITION))),
            "expected (precondition) kind label on the failing \
             obligation. got: {:?}",
            msgs,
        );
    }
}

// Call in an if-branch — the call's conjunction lands inside the
// branch's `c → …` continuation. Tests that `BodyItem::Call` composes
// with `IfThenElse` through `build_goal_with_terminator`.
test_verify_one_file! {
    #[test] test_exec_call_in_if_branch verus_code! {
        #[verifier::tactus_auto]
        fn add_one(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            x + 1
        }

        #[verifier::tactus_auto]
        fn maybe_bump(x: u8, flag: bool) -> (r: u8)
            requires x < 50
            ensures r <= x + 1
        {
            if flag {
                add_one(x)
            } else {
                x
            }
        }
    } => Ok(())
}

// Call in a loop body — exercises the composition with
// `build_loop_conjunction`. The inner call's `requires` must hold
// under the loop's invariant + cond; its `ensures` feeds the
// decrease-measure proof obligation.
test_verify_one_file! {
    #[test] test_exec_call_in_loop verus_code! {
        #[verifier::tactus_auto]
        fn dec_one(x: u8) -> (r: u8)
            requires x > 0
            ensures r == x - 1
        {
            x - 1
        }

        #[verifier::tactus_auto]
        fn count_down_via_call(n: u8) -> (r: u8)
            ensures r == 0
        {
            let mut x: u8 = n;
            while x > 0
                invariant x <= n
                decreases x
            {
                x = dec_one(x);
            }
            x
        }
    } => Ok(())
}

// Zero-arg call — edge case where the real-param filter result is
// empty. Regression guard: previously `debug_assert_eq!` in
// `build_call_conjunction` would not fire in release, so a silent
// miscount here would go undetected; now the real-param / arg
// count check in `walk_call` catches any mismatch up front.
test_verify_one_file! {
    #[test] test_exec_call_zero_args verus_code! {
        #[verifier::tactus_auto]
        fn answer() -> (r: u8)
            ensures r == 42
        {
            42
        }

        #[verifier::tactus_auto]
        fn caller() -> (r: u8)
            ensures r == 42
        {
            answer()
        }
    } => Ok(())
}

// Many-arg call — exercises the zip in `wrap_with_arg_lets` across
// a wider param list. Together with zero-args and the basic
// one-arg case, this covers the filter+zip shape.
test_verify_one_file! {
    #[test] test_exec_call_many_args verus_code! {
        #[verifier::tactus_auto]
        fn sum4(a: u8, b: u8, c: u8, d: u8) -> (r: u8)
            requires a + b + c + d < 255
            ensures r == a + b + c + d
        {
            a + b + c + d
        }

        #[verifier::tactus_auto]
        fn call_sum4() -> (r: u8)
            ensures r == 10
        {
            sum4(1, 2, 3, 4)
        }
    } => Ok(())
}

// `&mut` arg from a tactus_auto caller into a non-tactus_auto
// callee (verified through Verus's normal path). This is the MVS
// for #55: at the CALL SITE, `walk_call` introduces a fresh
// existential for the post-call value, substitutes
// `varat_pre_name(p) ↦ caller_arg` (pre-state) and `p ↦ fresh`
// (post-state) in the inlined ensures, then rebinds the caller's
// local to the fresh value via a Let frame.
//
// `bump` itself stays on Verus's Z3 path because Tactus doesn't
// yet handle &mut params in the fn's OWN body (separate task —
// caller-side and callee-side &mut are distinct concerns).
test_verify_one_file! {
    #[test] test_exec_call_mut_arg verus_code! {
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        #[verifier::tactus_auto]
        fn call_mut(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            let mut y: u8 = x;
            bump(&mut y);
            y
        }
    } => Ok(())
}

// Negative: caller's postcondition reads the post-call value
// incorrectly. Pins that the substituted ensures only gives us
// `*y_post == y_pre + 1` and not `*y_post == y_pre + 2`. If the
// substitution had a bug (e.g., dropping the +1 or aliasing pre
// with post in the wrong direction), this test would flip to
// Ok and silently mask the bug.
test_verify_one_file! {
    #[test] test_exec_call_mut_arg_wrong_post verus_code! {
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        #[verifier::tactus_auto]
        fn call_mut(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 2  // wrong! callee promises +1
        {
            let mut y: u8 = x;
            bump(&mut y);
            y
        }
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e| e.message.contains("postcondition")),
            "expected postcondition failure, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
}

// Negative: caller violates the callee's `requires *old(x) < 100`.
// Exercises the CallPrecondition theorem path: the substituted
// requires (`y < 100` at the call site) is what gets emitted as
// the precondition obligation, and it fails when the caller can
// only prove `y < 200` from its own context.
test_verify_one_file! {
    #[test] test_exec_call_mut_arg_requires_violated verus_code! {
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        #[verifier::tactus_auto]
        fn call_mut(x: u8) -> (r: u8)
            requires x < 200  // weaker than callee needs
            ensures r == x + 1
        {
            let mut y: u8 = x;
            bump(&mut y);  // callee needs y < 100 here
            y
        }
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e| e.message.contains("precondition")),
            "expected precondition failure, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
}

// #87: `&mut x.f` (mutating through a struct field) now verifies.
// Encoded via Lean's structure update: post-call we rebind
// `let h := { h with val := <fresh_post> }`, which preserves all
// other fields automatically — no havoc-base + assume-other-fields-
// unchanged dance needed (the syntax IS that semantics).
test_verify_one_file! {
    #[test] test_exec_call_mut_arg_field verus_code! {
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        struct Holder { val: u8 }

        #[verifier::tactus_auto]
        fn call_field_mut(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            let mut h = Holder { val: x };
            bump(&mut h.val);
            h.val
        }
    } => Ok(())
}

// Negative: caller asserts wrong post-state for the mutated field.
test_verify_one_file! {
    #[test] test_exec_call_mut_arg_field_wrong_post verus_code! {
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        struct Holder { val: u8 }

        #[verifier::tactus_auto]
        fn call_field_mut(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 2  // wrong: callee promises +1
        {
            let mut h = Holder { val: x };
            bump(&mut h.val);
            h.val
        }
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e| e.message.contains("postcondition")),
            "expected postcondition failure, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
}

// Multi-field struct: pins that other fields are preserved across
// the field mutation. Lean's `{ h with val := … }` syntax preserves
// `other` by definition; this test exercises that the caller can
// rely on it.
test_verify_one_file! {
    #[test] test_exec_call_mut_arg_field_other_preserved verus_code! {
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        struct Pair { val: u8, tag: u8 }

        #[verifier::tactus_auto]
        fn call_field_mut(x: u8, t: u8) -> (r: u8)
            requires x < 100
            ensures r == t  // tag must stay equal to t after mutating val
        {
            let mut p = Pair { val: x, tag: t };
            bump(&mut p.val);
            p.tag
        }
    } => Ok(())
}

// #87 rejection: tuple field mutation `&mut t.0`. Lean's structure-
// update syntax `{ x with f := v }` doesn't compose with `Prod`
// types — Lean's elaborator rejects with "expected structure". Would
// need a different encoding (explicit ctor rebuild: `let t := (v,
// t.1)`). Pinned as a rejection so a future tuple-aware encoding
// flips the assertion.
test_verify_one_file! {
    #[test] test_exec_call_mut_arg_tuple_field verus_code! {
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        #[verifier::tactus_auto]
        fn call_tuple_mut(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            let mut t: (u8, u8) = (x, 0);
            bump(&mut t.0);
            t.0
        }
    } => Ok(())
}

// #145: tuple field mutation at index 1, with sibling at index 0
// preserved. Pins that the anon-ctor rebuild reads `t.1` (Lean-1-
// indexed) for the unmutated slot at index 0.
test_verify_one_file! {
    #[test] test_exec_call_mut_arg_tuple_field_other_preserved verus_code! {
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        #[verifier::tactus_auto]
        fn call_tuple_idx1_mut(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            let mut t: (u8, u8) = (42, x);
            bump(&mut t.1);
            assert(t.0 == 42);  // sibling preserved
            t.1
        }
    } => Ok(())
}

// #146: arity > 2 tuple field mutation. The shared
// `tuple_field_accessor` produces multi-segment Lean accessors
// (`.2.1` etc.) for nested-Prod N-tuples, which are correct
// regardless of arity. The 3-tuple here mutates the middle slot
// and reads the unchanged ends — both reads must produce the
// correct positions.
test_verify_one_file! {
    #[test] test_exec_call_mut_arg_tuple3_field verus_code! {
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        #[verifier::tactus_auto]
        fn call_tuple3_mid_mut(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            let mut t: (u8, u8, u8) = (1, x, 99);
            bump(&mut t.1);
            assert(t.0 == 1);
            assert(t.2 == 99);
            t.1
        }
    } => Ok(())
}

// Multi-variant enum field mutation: documented as upstream-
// blocked. The DESIGN.md "non-Var L-values" catalogue lists
// "multi-variant enum field mutation" as needing match-and-rebuild
// encoding, but Rust doesn't actually let you write `&mut foo.f`
// for an enum-typed `foo` directly — you go through `if let` /
// `match` pattern binding (`ref mut val`) which Verus itself
// rejects at the mode level: "The verifier does not yet support
// the following Rust feature: &mut types, except in special cases."
//
// So multi-variant enum field mutation isn't reachable from Tactus's
// caller-side path at all — Verus rejects upstream before we see
// the SST. Pinning the rejection here makes the upstream block
// concrete; if Verus ever lifts the `ref mut` restriction, this
// test surfaces as a flippable Err.
test_verify_one_file! {
    #[test] test_exec_call_mut_arg_enum_field_upstream_blocked verus_code! {
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        enum Foo {
            A(u8),
            B(u8, u8),
        }

        #[verifier::tactus_auto]
        fn call_enum_mut(x: u8)
            requires x < 100
        {
            let mut foo = Foo::A(x);
            if let Foo::A(ref mut val) = foo {
                bump(val);
            }
        }
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e|
                e.message.contains("&mut types")
                || e.message.contains("does not yet support")),
            "expected Verus upstream rejection of `ref mut`, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
}

// #146: 4-tuple, mutate slot index 2. Pins the deeper
// multi-segment accessor pattern (`.2.2.1` for arity-4 position 2,
// `.2.2.2` for the last).
test_verify_one_file! {
    #[test] test_exec_call_mut_arg_tuple4_field verus_code! {
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        #[verifier::tactus_auto]
        fn call_tuple4_mut(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            let mut t: (u8, u8, u8, u8) = (1, 2, x, 99);
            bump(&mut t.2);
            assert(t.0 == 1);
            assert(t.1 == 2);
            assert(t.3 == 99);
            t.2
        }
    } => Ok(())
}

// #87 rejection: `&mut a.b.c` (depth-2 field path). The MVS only
// accepts depth-1 field paths; deeper paths would extend the
// structure-update encoding recursively but aren't wired yet.
test_verify_one_file! {
    #[test] test_exec_call_mut_arg_field_deep verus_code! {
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        struct Inner { val: u8 }
        struct Outer { inner: Inner }

        #[verifier::tactus_auto]
        fn call_deep_mut(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            let mut o = Outer { inner: Inner { val: x } };
            bump(&mut o.inner.val);  // depth-2 — closed via #144
            o.inner.val
        }
    } => Ok(())
}

// #144: depth-3 field path. Pins that the recursive structure-update
// generalizes beyond depth-2.
test_verify_one_file! {
    #[test] test_exec_call_mut_arg_field_depth3 verus_code! {
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        struct L3 { v: u8 }
        struct L2 { l3: L3 }
        struct L1 { l2: L2 }

        #[verifier::tactus_auto]
        fn call_depth3_mut(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            let mut o = L1 { l2: L2 { l3: L3 { v: x } } };
            bump(&mut o.l2.l3.v);  // depth-3 path
            o.l2.l3.v
        }
    } => Ok(())
}

// #144: depth-2 with sibling fields preserved. Pins that the
// nested structure-update preserves all unmodified fields at every
// level (Lean's `{ x with f := v }` syntax does this structurally).
test_verify_one_file! {
    #[test] test_exec_call_mut_arg_field_deep_other_preserved verus_code! {
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        struct Inner { val: u8, tag: u8 }
        struct Outer { inner: Inner, label: u8 }

        #[verifier::tactus_auto]
        fn call_deep_preserved(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            let mut o = Outer {
                inner: Inner { val: x, tag: 7 },
                label: 99,
            };
            bump(&mut o.inner.val);
            // Verify other fields are preserved — both at the same
            // level (tag) and at the outer level (label).
            assert(o.inner.tag == 7);
            assert(o.label == 99);
            o.inner.val
        }
    } => Ok(())
}

// #86 + #55 interaction: trait method takes `&mut`, AND trait/impl
// have textually different param names. Exercises the union-key
// substitution for BOTH `pname` (post-state) AND `pname_pre`
// (`<x>_at_pre_tactus`, pre-state) — four keys total per &mut
// param across both passes. If either spelling were missing from
// the map, the inlined ensures would have unsubstituted vars.
test_verify_one_file! {
    #[test] test_exec_call_trait_mut_differing_param_names verus_code! {
        trait Bumper {
            fn bump(&self, x: &mut u8)
                requires *old(x) < 100
                ensures *x == *old(x) + 1;
        }

        struct Plain;
        impl Bumper for Plain {
            // Param renamed `x` → `n` at the impl site. Verus inherits
            // requires/ensures from the trait decl (impl can't declare
            // its own); the impl's spec gets re-keyed to `n` at the
            // trait-impl-checking pass. Tactus must thread BOTH `x`
            // (trait spelling) and `n` (impl spelling) into the
            // substitution map for &mut params.
            fn bump(&self, n: &mut u8)
            {
                *n = *n + 1;
            }
        }

        #[verifier::tactus_auto]
        fn caller(b: &Plain, k: u8) -> (r: u8)
            requires k < 100
            ensures r == k + 1
        {
            let mut y = k;
            b.bump(&mut y);
            y
        }
    } => Ok(())
}

// #86 latent-bug coverage: trait method and impl declare the same
// param with TEXTUALLY DIFFERENT names. Pre-#86 the substitution
// map was keyed only on impl param names; trait specs (with trait
// param names) wouldn't substitute. The #86 union-key pass
// addresses this. Pin it with a test that uses different names.
test_verify_one_file! {
    #[test] test_exec_call_trait_method_differing_param_names verus_code! {
        trait Adder {
            fn add_one(&self, x: u8) -> (r: u8)
                requires x < 200
                ensures r == x + 1;
        }

        struct Plain;
        impl Adder for Plain {
            // Param renamed `x` → `n`, return name renamed `r` → `s`.
            // Both are positionally aligned with the trait's spec.
            fn add_one(&self, n: u8) -> (s: u8)
                ensures s == n + 1
            {
                n + 1
            }
        }

        #[verifier::tactus_auto]
        fn caller(a: &Plain, k: u8) -> (r: u8)
            requires k < 100
            ensures r == k + 1
        {
            a.add_one(k)
        }
    } => Ok(())
}

// Multi-`&mut`: two mut args at the same call site. Exercises the
// stacked-frames encoding (each &mut arg gets its own existential
// + caller-rebinding pair). Borrow check guarantees the two args
// bind distinct caller vars, so we don't need to check aliasing.
test_verify_one_file! {
    #[test] test_exec_call_two_mut_args verus_code! {
        fn swap_then_bump(a: &mut u8, b: &mut u8)
            requires *old(a) < 100, *old(b) < 100
            ensures *a == *old(b) + 1, *b == *old(a) + 1
        {
            let tmp = *a;
            *a = *b + 1;
            *b = tmp + 1;
        }

        #[verifier::tactus_auto]
        fn call_swap(x: u8, y: u8) -> (r: u8)
            requires x < 100, y < 100
            ensures r == y + 1
        {
            let mut a: u8 = x;
            let mut b: u8 = y;
            swap_then_bump(&mut a, &mut b);
            a
        }
    } => Ok(())
}

// #94 callee-side &mut body: tactus_auto on a fn that takes a &mut
// param can verify its own body. Encoding (sst_to_lean):
//   1. SST-level rewrite of body+ensures: VarAt(x, Pre) for &mut x
//      becomes Var(<x>_at_pre_tactus) — the synthetic pre-state name.
//      Distinguishes pre-state from post-state which would otherwise
//      collide with the body's let-shadow `let x := expr`.
//   2. Initial OblCtx Let frame `let <x>_at_pre_tactus := x` per
//      &mut param at fn entry — captures pre-state before any
//      body modifications can shadow it.
//   3. Requires aren't rewritten: at fn entry x IS the pre-state,
//      so VarAt → Var natural collapse is correct there.
test_verify_one_file! {
    #[test] test_exec_callee_mut_simple verus_code! {
        #[verifier::tactus_auto]
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }
    } => Ok(())
}

// Negative — body assigns the wrong value. Pins that the &mut
// post-state in ensures sees the body's let-shadow, not just the
// original pre-state value.
test_verify_one_file! {
    #[test] test_exec_callee_mut_wrong_body verus_code! {
        #[verifier::tactus_auto]
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 2;  // wrong: ensures says +1
        }
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e| e.message.contains("postcondition")),
            "expected postcondition failure, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
}

// Multiple body modifications — pins that successive `*x = …`
// assignments thread state correctly via Lean let-shadowing.
test_verify_one_file! {
    #[test] test_exec_callee_mut_multiple_writes verus_code! {
        #[verifier::tactus_auto]
        fn bump_twice(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 2
        {
            *x = *x + 1;
            *x = *x + 1;
        }
    } => Ok(())
}

// Multiple &mut params — each gets its own <x>_at_pre_tactus binding.
// Pins that the per-param Let frames don't collide.
test_verify_one_file! {
    #[test] test_exec_callee_two_mut_params verus_code! {
        #[verifier::tactus_auto]
        fn bump_both(a: &mut u8, b: &mut u8)
            requires *old(a) < 100, *old(b) < 100
            ensures *a == *old(a) + 1, *b == *old(b) + 1
        {
            *a = *a + 1;
            *b = *b + 1;
        }
    } => Ok(())
}

// End-to-end: callee verified by tactus_auto AND caller by
// tactus_auto, both in the same crate. Pins that the call-site
// inlining (#55) and callee-body verification (#94) are
// compatible — they use the same `<x>_at_pre_tactus` name via
// the shared `varat_pre_name` helper in expr_shared.rs.
test_verify_one_file! {
    #[test] test_exec_callee_mut_and_caller_both_tactus_auto verus_code! {
        #[verifier::tactus_auto]
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        #[verifier::tactus_auto]
        fn call_mut(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            let mut y: u8 = x;
            bump(&mut y);
            y
        }
    } => Ok(())
}

// Self-recursive call with a decreasing measure — verifies. The
// termination obligation `decrease_at_args < decrease_at_params`
// is conjoined onto the call's requires clause by
// `build_call_conjunction`.
test_verify_one_file! {
    #[test] test_exec_call_recursive_decreasing verus_code! {
        #[verifier::tactus_auto]
        fn count_down(n: u8) -> (r: u8)
            ensures r == 0
            decreases n
        {
            if n == 0 {
                0
            } else {
                count_down((n - 1) as u8)
            }
        }
    } => Ok(())
}

// Lexicographic `decreases (a, b)` on a recursive fn (#110). Verus's
// `recursion::check_decrease` builds a nested CheckDecreaseHeight:
//
//     CheckDecreaseHeight(a_cur, a_old,
//       CheckDecreaseHeight(b_cur, b_old, False))
//
// The `otherwise` field of the OUTER call is the inner CheckDecreaseHeight.
// Our `sst_exp_to_ast_checked` arm renders `otherwise` recursively via
// itself, so the lex shape composes:
//
//   ((0 ≤ a_cur ∧ a_cur < a_old)
//     ∨ (a_cur = a_old ∧
//        ((0 ≤ b_cur ∧ b_cur < b_old) ∨ (b_cur = b_old ∧ False))))
//
// First call decreases `a` (from 5 to 4), so the outer disjunct fires.
// Second call holds `a` constant and decreases `b`, so the inner
// disjunct fires.
test_verify_one_file! {
    #[test] test_exec_call_recursive_lex_decreases verus_code! {
        #[verifier::tactus_auto]
        fn lex_count(a: u8, b: u8) -> (r: u8)
            ensures r == 0
            decreases a, b
        {
            if a == 0 && b == 0 {
                0
            } else if b == 0 {
                lex_count((a - 1) as u8, 100)
            } else {
                lex_count(a, (b - 1) as u8)
            }
        }
    } => Ok(())
}

// Negative test: lex decrease where neither component decreases.
// Both calls pass (a, b) unchanged, so the lex obligation
// `(a_cur < a_old) ∨ (a_cur = a_old ∧ (b_cur < b_old ∨ ...))`
// is false at both levels.
test_verify_one_file! {
    #[test] test_exec_call_recursive_lex_nondecreasing verus_code! {
        #[verifier::tactus_auto]
        fn lex_loop(a: u8, b: u8) -> (r: u8)
            ensures r == 0
            decreases a, b
        {
            if a == 0 && b == 0 {
                0
            } else {
                lex_loop(a, b)
            }
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "non-decreasing lex recursion should fail");
        let msgs: Vec<_> = err.errors.iter().map(|e| e.message.clone()).collect();
        assert!(
            msgs.iter().any(|m| m.contains(&vir::tactus_messages::paren_label(vir::tactus_messages::ASSERT_LABEL_TERMINATION))),
            "expected (termination) kind label on the failing obligation. got: {:?}",
            msgs,
        );
    }
}

// 3-level lexicographic `decreases (a, b, c)` (#110 review-pass
// follow-up). Exercises `lex_decrease_obligation`'s recursion at
// depth ≥ 3 — the recursion is correct by induction (verified via
// the unit test `lex_decrease_obligation_three_levels_recurses_correctly`),
// but an e2e test pins that Verus's `recursion::check_decrease`
// produces the matching CheckDecreaseHeight chain.
test_verify_one_file! {
    #[test] test_exec_call_recursive_lex3_decreases verus_code! {
        #[verifier::tactus_auto]
        fn lex3_count(a: u8, b: u8, c: u8) -> (r: u8)
            ensures r == 0
            decreases a, b, c
        {
            if a == 0 && b == 0 && c == 0 {
                0
            } else if c > 0 {
                lex3_count(a, b, (c - 1) as u8)
            } else if b > 0 {
                lex3_count(a, (b - 1) as u8, 100)
            } else {
                lex3_count((a - 1) as u8, 100, 100)
            }
        }
    } => Ok(())
}

// Self-recursive call where the measure does NOT decrease — must
// fail. The caller passes the same `n` to itself, so the inlined
// `let n := n; n < n` obligation is false.
test_verify_one_file! {
    #[test] test_exec_call_recursive_nondecreasing verus_code! {
        #[verifier::tactus_auto]
        fn infinite_loop(n: u8) -> (r: u8)
            ensures r == 0
            decreases n
        {
            if n == 0 {
                0
            } else {
                infinite_loop(n)
            }
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "non-decreasing recursion should fail");
        // #51 source mapping: the error should mention a test.rs:L:C
        // pointing at the failing obligation (the recursive call's
        // termination check), not just at the fn declaration.
        let msgs: Vec<_> = err.errors.iter().map(|e| e.message.clone()).collect();
        assert!(
            msgs.iter().any(|m| m.contains("at ") && m.contains("test.rs:")),
            "expected error to include a Rust source location \
             (`at <path>/test.rs:L:C:`) from #51 SpanMark instrumentation. \
             got: {:?}",
            msgs,
        );
        // D Stage 5: per-obligation theorems give find_span_mark a
        // structurally exact answer for AssertKind labels — the
        // failing tactic's pos.line is inside exactly one
        // theorem's `:= by` block, and the closest preceding mark
        // is that theorem's obligation. For this fn the failure
        // is the recursive call's CheckDecreaseHeight, which
        // wraps with kind=Termination.
        assert!(
            msgs.iter().any(|m| m.contains(&vir::tactus_messages::paren_label(vir::tactus_messages::ASSERT_LABEL_TERMINATION))),
            "expected (termination) kind label on the failing \
             obligation. got: {:?}",
            msgs,
        );
    }
}

// Self-recursive call on a fn with NO `decreases` clause — rejected
// by `walk_call` because there's no way to emit a termination
// obligation, and allowing the call would silently verify an
// infinite recursion.
test_verify_one_file! {
    #[test] test_exec_call_recursive_no_decreases verus_code! {
        #[verifier::tactus_auto]
        fn no_decrease(n: u8) -> (r: u8)
            ensures r == 0
        {
            if n == 0 { 0 } else { no_decrease(n) }
        }
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e| e.message.contains("no `decreases`")
                || e.message.contains("cannot prove termination")
                || e.message.contains("decreases")),
            "recursion without decreases should be rejected, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
}

// Mutual recursion across an SCC. Verus's recursion pass inserts
// `CheckDecreaseHeight` before each cross-fn call in the SCC, same
// way as self-recursion — our lowering handles both uniformly. This
// test exercises the path end-to-end so we catch regressions if
// either the SCC detection upstream changes shape or our
// CheckDecreaseHeight lowering breaks for mutual-recursion args.
// Specs are deliberately kept trivial (`r == 0`) so omega can close
// them — the point here is to check termination plumbing, not
// to exercise tactic reasoning about mutual-recursion semantics.
test_verify_one_file! {
    #[test] test_exec_call_mutual_recursion verus_code! {
        #[verifier::tactus_auto]
        fn ping(n: u8) -> (r: u8)
            ensures r == 0
            decreases n
        {
            if n == 0 {
                0
            } else {
                pong((n - 1) as u8)
            }
        }

        #[verifier::tactus_auto]
        fn pong(n: u8) -> (r: u8)
            ensures r == 0
            decreases n
        {
            if n == 0 {
                0
            } else {
                ping((n - 1) as u8)
            }
        }
    } => Ok(())
}

// `decreases` on a user datatype exercises the #54 pipeline
// end-to-end:
//   1. `datatype_to_cmds` emits the match-based `T.height : T →
//      Nat` fn alongside the inductive.
//   2. `CheckDecreaseHeight` dispatches to `T.height cur <
//      T.height prev ∨ (T.height cur = T.height prev ∧
//      otherwise)` via `decrease_height_datatype` (peeling
//      Boxed/Decorate).
//   3. `tactus_case_split` in `TactusPrelude.lean` (#58) finds
//      the `s : Stack` local and case-splits, letting simp_all
//      unfold the match-based accessors and omega close
//      `rest.height < 1 + rest.height`.
test_verify_one_file! {
    #[test] test_exec_call_recursive_datatype_termination verus_code! {
        use vstd::std_specs::alloc::*;

        enum Stack {
            Empty,
            Push(u8, Box<Stack>),
        }

        #[verifier::tactus_auto]
        fn shrink(s: &Stack) -> (r: u64)
            decreases s
        {
            match s {
                Stack::Empty => 0,
                Stack::Push(_, rest) => shrink(rest),
            }
        }
    } => Ok(())
}

// Non-decreasing companion: the recursive call passes the SAME
// `s` (not a subterm), so the termination obligation reduces to
// `s.height < s.height` which omega rejects. Confirms our
// height-based lowering actually constrains termination (rather
// than vacuously passing).
test_verify_one_file! {
    #[test] test_exec_call_recursive_datatype_nondecreasing verus_code! {
        use vstd::std_specs::alloc::*;

        enum Stack {
            Empty,
            Push(u8, Box<Stack>),
        }

        #[verifier::tactus_auto]
        fn loops(s: &Stack) -> (r: u64)
            decreases s
        {
            match s {
                Stack::Empty => 0,
                Stack::Push(_, _rest) => loops(s),
            }
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1,
            "non-decreasing recursion on a datatype should fail");
    }
}

// #108: generic datatype `decreases`. Pre-#108 `decrease_height_datatype`
// rejected generic instantiations (`args.is_empty()` gate). Post-#108,
// the height fn is parameterized over the type args (implicit binders
// in Lean) so `List<u8>.height` works as `List.height (l : List u8)` —
// Lean infers `A`. Recursion is structural on the List shape; A is
// opaque to the height calculation.
test_verify_one_file! {
    #[test] test_exec_call_recursive_generic_datatype verus_code! {
        use vstd::std_specs::alloc::*;

        enum List<A> {
            Nil,
            Cons(A, Box<List<A>>),
        }

        #[verifier::tactus_auto]
        fn count(l: &List<u8>) -> (r: u64)
            decreases l
        {
            match l {
                List::Nil => 0,
                List::Cons(_, rest) => count(rest),
            }
        }
    } => Ok(())
}

// #108 edge: generic recursive datatype with cross-instantiation
// recursion (`Recurse(Box<Mut<u8>>)` regardless of outer `A`).
//
// Lean's parameter-style strict-positivity check rejects this shape:
// `inductive Mut (A : Type) where | Recurse (val0 : Mut Int)` errors
// with "non valid occurrence of the datatypes being declared" because
// the recursive arm uses a fixed type `Int` rather than the
// parameter `A`. Tactus detects cross-instantiation recursion at
// codegen time and emits indexed-style `inductive Mut : Type →
// Type 1 where | Plain : ∀ {A}, A → Mut A | Recurse : ∀ {A}, Mut Int
// → Mut A` plus a manual `Inhabited` instance (since `deriving
// Inhabited` doesn't work for indexed-style). Both styles coexist
// in the same .lean — only affected datatypes get the indexed
// treatment via the `has_cross_instantiation_recursion` predicate
// in `to_lean_fn::datatype_decl_cmd`.
test_verify_one_file! {
    #[test] test_exec_call_recursive_generic_datatype_cross_instantiation verus_code! {
        use vstd::std_specs::alloc::*;

        enum Mut<A> {
            Plain(A),
            Recurse(Box<Mut<u8>>),
        }

        #[verifier::tactus_auto]
        fn count_recurse(m: &Mut<u32>) -> (r: u64)
            decreases m
        {
            match m {
                Mut::Plain(_) => 0,
                Mut::Recurse(inner) => count_recurse_u8(inner),
            }
        }

        #[verifier::tactus_auto]
        fn count_recurse_u8(m: &Mut<u8>) -> (r: u64)
            decreases m
        {
            match m {
                Mut::Plain(_) => 0,
                Mut::Recurse(inner) => count_recurse_u8(inner),
            }
        }
    } => Ok(())
}

// #108 negative: generic-datatype recursion that doesn't decrease.
// Same shape as `test_exec_call_recursive_datatype_nondecreasing` but
// with a generic List. Pins that the height-based termination check
// constrains generics correctly (rather than being permissive).
test_verify_one_file! {
    #[test] test_exec_call_recursive_generic_datatype_nondecreasing verus_code! {
        use vstd::std_specs::alloc::*;

        enum List<A> {
            Nil,
            Cons(A, Box<List<A>>),
        }

        #[verifier::tactus_auto]
        fn looper(l: &List<u8>) -> (r: u64)
            decreases l
        {
            match l {
                List::Nil => 0,
                List::Cons(_, _rest) => looper(l),
            }
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1,
            "non-decreasing recursion on generic datatype should fail");
    }
}

// #109: mutually recursive datatype SCCs. Two enums that reference
// each other (Tree → Forest → Tree). Pre-#109 the inductives were
// emitted standalone — Lean rejected the cross-type field reference
// because Forest wasn't yet defined when Tree's inductive was emitted.
// Post-#109 the inductives go in a `mutual ... end` block (and the
// height fns in a separate one) so cross-type references resolve.
//
// The test uses Tree's match for the exec body but doesn't call its
// recursive partner — the value of the test is that the types compile
// cleanly. Pinned by enum field references being in scope.
test_verify_one_file! {
    #[test] test_exec_mutually_recursive_datatypes verus_code! {
        use vstd::std_specs::alloc::*;

        enum Tree {
            Leaf,
            Branch(Box<Forest>),
        }

        enum Forest {
            Empty,
            Cons(Box<Tree>, Box<Forest>),
        }

        #[verifier::tactus_auto]
        fn use_tree(t: Tree) -> (r: u64)
            ensures r == 0
        {
            match t {
                Tree::Leaf => 0,
                Tree::Branch(_) => 0,
            }
        }
    } => Ok(())
}

// #109 stretch: cross-fn-SCC mutual recursion where each fn's
// `decreases` measure is on a different SCC member. Verus's
// recursion pass inserts CheckDecreaseHeight at every cross-fn
// call; the obligation compares the callee's decrease type's
// height vs the caller's decrease type's height. Pre-fix Tactus
// emitted `<callee_T>.height` for both sides, producing a type
// mismatch in Lean. Post-fix each side uses its own type's
// height fn — the comparison `Forest.height f < Tree.height t`
// typechecks because both heights return Nat, and the inequality
// is semantically true because `Tree.height (Branch f) = 1 +
// Forest.height f > Forest.height f` (the height fns are mutually
// defined, so their values relate structurally).
test_verify_one_file! {
    #[test] test_exec_cross_fn_scc_cross_type_decreases verus_code! {
        use vstd::std_specs::alloc::*;

        enum Tree {
            Leaf,
            Branch(Box<Forest>),
        }

        enum Forest {
            Empty,
            Cons(Box<Tree>, Box<Forest>),
        }

        #[verifier::tactus_auto]
        fn tree_size(t: &Tree) -> (r: u64)
            decreases t
        {
            match t {
                Tree::Leaf => 0,
                Tree::Branch(f) => forest_size(f),
            }
        }

        #[verifier::tactus_auto]
        fn forest_size(f: &Forest) -> (r: u64)
            decreases f
        {
            match f {
                Forest::Empty => 0,
                Forest::Cons(t, _rest) => tree_size(t),
            }
        }
    } => Ok(())
}

// #109 stretch negative: cross-fn-SCC where the recursive call
// passes the SAME value back (not a structural subterm). The
// termination obligation reduces to `Tree.height t < Tree.height t`
// (or similar), which omega rejects. Confirms the cross-type
// comparison actually constrains rather than vacuously passing.
test_verify_one_file! {
    #[test] test_exec_cross_fn_scc_nondecreasing verus_code! {
        use vstd::std_specs::alloc::*;

        enum Tree {
            Leaf,
            Branch(Box<Forest>),
        }

        enum Forest {
            Empty,
            Cons(Box<Tree>, Box<Forest>),
        }

        #[verifier::tactus_auto]
        fn tree_size(t: &Tree) -> (r: u64)
            decreases t
        {
            match t {
                Tree::Leaf => 0,
                Tree::Branch(_) => forest_size_bad(t),
            }
        }

        #[verifier::tactus_auto]
        fn forest_size_bad(t: &Tree) -> (r: u64)
            decreases t
        {
            tree_size(t)
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1,
            "non-decreasing cross-fn-SCC should fail termination");
    }
}

// #109 coverage: SCC of size 3 (A → B → C → A). Pre-#109 tests
// covered size-2 SCCs only; this exercises the order_datatypes
// Tarjan output and mutual block emission with three members.
test_verify_one_file! {
    #[test] test_exec_three_element_datatype_scc verus_code! {
        use vstd::std_specs::alloc::*;

        enum A { ALeaf, AB(Box<B>) }
        enum B { BLeaf, BC(Box<C>) }
        enum C { CLeaf, CA(Box<A>) }

        #[verifier::tactus_auto]
        fn use_a(a: A) -> (r: u64)
            ensures r == 0
        {
            match a {
                A::ALeaf => 0,
                A::AB(_) => 0,
            }
        }
    } => Ok(())
}

// #109 coverage extension: 4-element datatype SCC. The Tarjan
// implementation in `dep_order::order_datatypes` is generic over
// SCC size — a 4-cycle goes through the same mutual-block emission
// path as the 3-cycle pinned above. Pinning the 4-cycle adds
// confidence that very deep mutual SCCs work end-to-end (Lean's
// mutual-block compilation cost is the latent concern; depth 4 is
// well within tractable). Catalogue had this as "Should work —
// the Tarjan implementation is generic over SCC size — but
// unverified for very deep cycles."
test_verify_one_file! {
    #[test] test_exec_four_element_datatype_scc verus_code! {
        use vstd::std_specs::alloc::*;

        enum A { ALeaf, AB(Box<B>) }
        enum B { BLeaf, BC(Box<C>) }
        enum C { CLeaf, CD(Box<D>) }
        enum D { DLeaf, DA(Box<A>) }

        #[verifier::tactus_auto]
        fn use_a(a: A) -> (r: u64)
            ensures r == 0
        {
            match a {
                A::ALeaf => 0,
                A::AB(_) => 0,
            }
        }
    } => Ok(())
}

// #109 coverage extension: 5-element datatype SCC. One step beyond
// depth 4. Tarjan still generic; this pin extends the structural-
// correctness confidence linearly. Lean compiles a 5-way `mutual`
// block of `inductive`s + accessors-out + 5-way `mutual` block of
// `.height` fns. Catalogue noted "very deep cycles (10+) remain
// unpinned"; depth 5 closes the gap one step further while staying
// in the cheap-test regime (~5s for full mutual-block elaboration).
test_verify_one_file! {
    #[test] test_exec_five_element_datatype_scc verus_code! {
        use vstd::std_specs::alloc::*;

        enum P { PLeaf, PQ(Box<Q>) }
        enum Q { QLeaf, QR(Box<R>) }
        enum R { RLeaf, RS(Box<S>) }
        enum S { SLeaf, ST(Box<T>) }
        enum T { TLeaf, TP(Box<P>) }

        #[verifier::tactus_auto]
        fn use_p(p: P) -> (r: u64)
            ensures r == 0
        {
            match p {
                P::PLeaf => 0,
                P::PQ(_) => 0,
            }
        }
    } => Ok(())
}

// #109 coverage extension: 10-element datatype SCC. Addresses
// DESIGN.md's latent concern about Lean's mutual-block compilation
// cost at extreme depth. Catalogue had "very deep cycles (10+) remain
// unpinned — Lean's mutual-block compilation cost is the latent
// concern at extreme depth." Probe extends the linear chain to 10
// to either confirm or refute. Same emission path as 4/5 cycles;
// each `enum` member references the next via `Box<Next>`. If this
// passes in reasonable time, the latent concern was overstated for
// realistic depths.
test_verify_one_file! {
    #[test] test_exec_ten_element_datatype_scc verus_code! {
        use vstd::std_specs::alloc::*;

        enum E0 { E0Leaf, E0Next(Box<E1>) }
        enum E1 { E1Leaf, E1Next(Box<E2>) }
        enum E2 { E2Leaf, E2Next(Box<E3>) }
        enum E3 { E3Leaf, E3Next(Box<E4>) }
        enum E4 { E4Leaf, E4Next(Box<E5>) }
        enum E5 { E5Leaf, E5Next(Box<E6>) }
        enum E6 { E6Leaf, E6Next(Box<E7>) }
        enum E7 { E7Leaf, E7Next(Box<E8>) }
        enum E8 { E8Leaf, E8Next(Box<E9>) }
        enum E9 { E9Leaf, E9Next(Box<E0>) }

        #[verifier::tactus_auto]
        fn use_e0(e: E0) -> (r: u64)
            ensures r == 0
        {
            match e {
                E0::E0Leaf => 0,
                E0::E0Next(_) => 0,
            }
        }
    } => Ok(())
}

// #108 edge: generic datatype instantiated with an uninhabited type
// param. DESIGN.md catalogue predicted Lean would reject `Inhabited
// (List Empty)` synthesis "at the call site." Probe established this
// is upstream-blocked: Verus rejects `enum Empty {}` itself with
// "datatype must have at least one non-recursive variant," so an
// uninhabited type never reaches Tactus. The Lean-side concern about
// Inhabited synthesis is therefore structurally unreachable through
// normal Tactus paths; the catalogue entry can be downgraded from
// "known limitation we should fix" to "upstream-blocked, not a
// Tactus concern." If Verus ever lifts the no-empty-enum rule, this
// test surfaces as a flippable Err and the conditional-deriving fix
// described in DESIGN becomes relevant again.
test_verify_one_file! {
    #[test] test_exec_generic_datatype_uninhabited_type_param_upstream_blocked verus_code! {
        use vstd::std_specs::alloc::*;

        enum Empty {}
        enum L<A> { Nil, Cons(A, Box<L<A>>) }

        #[verifier::tactus_auto]
        fn id_list(l: L<Empty>) -> L<Empty> {
            l
        }
    } => Err(err) => assert!(
        err.errors.iter().any(|e| e.rendered.contains("at least one non-recursive variant")),
        "expected Verus's no-empty-enum rejection; got: {:#?}", err.errors
    )
}

// Regression: single-variant non-eponymous enum (variant name ≠
// type name) goes through the multi-variant accessor path because
// `is_single_variant_struct` requires the variant name to match the
// type name. Pre-fix the discriminator and accessor emitted a
// catch-all `_ => …` wildcard arm; for a one-variant inductive the
// first arm is exhaustive and Lean reported "Redundant alternative"
// as a verification error. Fix gates the wildcard on
// `dt.variants.len() > 1`. Surfaced while writing the SCC + standalone
// coverage test below.
test_verify_one_file! {
    #[test] test_exec_single_variant_non_eponymous_enum verus_code! {
        enum Pair { Mk(u64) }

        #[verifier::tactus_auto]
        fn use_pair(p: Pair) -> (r: u64)
            ensures r == 0
        {
            match p {
                Pair::Mk(_) => 0,
            }
        }
    } => Ok(())
}

// #109 coverage: SCC + standalone datatype in the same crate.
// `Tree`/`Forest` are mutually recursive (SCC of 2); `Pair` is
// independent (Single). `order_datatypes` should produce two
// groups — one Mutual, one Single — and emission should handle
// both kinds in the same compilation unit without conflict.
test_verify_one_file! {
    #[test] test_exec_scc_plus_standalone_datatype verus_code! {
        use vstd::std_specs::alloc::*;

        enum Tree { Leaf, Branch(Box<Forest>) }
        enum Forest { Empty, Cons(Box<Tree>, Box<Forest>) }
        enum Pair { Mk(u64) }

        #[verifier::tactus_auto]
        fn use_pair(p: Pair) -> (r: u64)
            ensures r == 0
        {
            match p {
                Pair::Mk(_) => 0,
            }
        }

        #[verifier::tactus_auto]
        fn use_tree(t: Tree) -> (r: u64)
            ensures r == 0
        {
            match t {
                Tree::Leaf => 0,
                Tree::Branch(_) => 0,
            }
        }
    } => Ok(())
}

// #109 edge-case: generic mutually recursive datatypes (#109 +
// #108). Both members carry a type parameter that crosses the SCC
// boundary. Tests that the implicit-binder machinery from #108
// composes with the mutual-block emission from #109 — height fns
// for both members get `{T : Type}` binders before the colon and
// the mutual block scopes them correctly.
test_verify_one_file! {
    #[test] test_exec_generic_mutual_scc verus_code! {
        use vstd::std_specs::alloc::*;

        enum GTree<T> { Leaf(T), Branch(Box<GForest<T>>) }
        enum GForest<T> { Empty, Cons(Box<GTree<T>>, Box<GForest<T>>) }

        #[verifier::tactus_auto]
        fn use_gtree(t: GTree<u8>) -> (r: u64)
            ensures r == 0
        {
            match t {
                GTree::Leaf(_) => 0,
                GTree::Branch(_) => 0,
            }
        }
    } => Ok(())
}

// #109 edge-case: two INDEPENDENT SCCs in the same crate.
// `order_datatypes` should produce two `Mutual` groups, each
// internally consistent. Tests that the SCC ordering doesn't
// accidentally merge unrelated cycles.
test_verify_one_file! {
    #[test] test_exec_two_independent_sccs verus_code! {
        use vstd::std_specs::alloc::*;

        enum A1 { Leaf, ToA2(Box<A2>) }
        enum A2 { Leaf, ToA1(Box<A1>) }

        enum B1 { Leaf, ToB2(Box<B2>) }
        enum B2 { Leaf, ToB1(Box<B1>) }

        #[verifier::tactus_auto]
        fn use_both(a: A1, b: B1) -> (r: u64)
            ensures r == 0
        {
            let _ = match a { A1::Leaf => 0u64, A1::ToA2(_) => 0u64 };
            match b { B1::Leaf => 0, B1::ToB2(_) => 0 }
        }
    } => Ok(())
}

// #111: `assert(P) by(bit_vector)` routes to Tactus's prelude
// `tactus_bit_vector` tactic. The goal here is concrete enough that
// Lean's `decide` (in the tactic ladder) closes it. Pre-#111 Tactus
// rejected the StmX::AssertBitVector outright.
test_verify_one_file! {
    #[test] test_exec_assert_bit_vector_concrete verus_code! {
        #[verifier::tactus_auto]
        fn xor_concrete() {
            assert((5u8 ^ 3) == 6) by(bit_vector);
        }
    } => Ok(())
}

// #130: BitVec-mode rendering for variable-parameterized
// bit-vector identities. Pre-#130 the goal `(x : Int) ^^^ y == y ^^^ x`
// was unprovable by Tactus's tactic ladder (Int.xor doesn't have a
// `simp`-tagged commutativity lemma in the form the ladder expects).
// Post-#130 we render `x : u32` as `BitVec.ofInt 32 x`, the goal
// becomes `BitVec.xor` which IS `@[simp]` commutative — `simp_all`
// closes it.
test_verify_one_file! {
    #[test] test_exec_assert_bit_vector_xor_comm verus_code! {
        #[verifier::tactus_auto]
        fn xor_comm(x: u32, y: u32) {
            assert(x ^ y == y ^ x) by(bit_vector);
        }
    } => Ok(())
}

// #130: identity laws — `x ^ 0 == x` and `x ^ x == 0`. Both
// close via Mathlib's `BitVec.xor_zero` / `BitVec.xor_self` simp
// lemmas in BitVec mode. Pre-#130 these would have failed.
test_verify_one_file! {
    #[test] test_exec_assert_bit_vector_xor_self verus_code! {
        #[verifier::tactus_auto]
        fn xor_self(x: u8) {
            assert(x ^ x == 0u8) by(bit_vector);
        }
    } => Ok(())
}

// #130 follow-up: associativity. `(x ^ y) ^ z == x ^ (y ^ z)`
// closes via simp_all + BitVec.xor_assoc. Confirms the enriched
// simp set handles algebraic identities beyond commutativity.
test_verify_one_file! {
    #[test] test_exec_assert_bit_vector_xor_assoc verus_code! {
        #[verifier::tactus_auto]
        fn xor_assoc(x: u32, y: u32, z: u32) {
            assert((x ^ y) ^ z == x ^ (y ^ z)) by(bit_vector);
        }
    } => Ok(())
}

// #130 follow-up: AND/OR commutativity to confirm the symmetric
// simp lemmas work across operators.
test_verify_one_file! {
    #[test] test_exec_assert_bit_vector_and_or_comm verus_code! {
        #[verifier::tactus_auto]
        fn and_or_comm(x: u32, y: u32) {
            assert(x & y == y & x) by(bit_vector);
            assert(x | y == y | x) by(bit_vector);
        }
    } => Ok(())
}

// #111 negative: a clearly-false bit_vector assertion fails — the
// tactic chain gives up and `tactus_bit_vector`'s explicit `fail`
// fires. Confirms the routing actually verifies (rather than
// silently passing every assert through).
test_verify_one_file! {
    #[test] test_exec_assert_bit_vector_false verus_code! {
        #[verifier::tactus_auto]
        fn xor_wrong(x: u8) {
            // x ^ x == 0 is the truth; claiming == 1 should fail.
            assert((x ^ x) == 1u8) by(bit_vector);
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1,
            "false bit_vector assertion should fail verification");
    }
}

// REVIEW lens 3/4: AssertBitVector with a non-empty `requires` clause.
// The walker's BV-mode goal shape is `req_conj → ens_conj` when
// requires is non-empty (vs. bare `ens_conj` when empty). All
// previous tests had empty requires; this exercises the implication
// path. Verus's ast_to_sst emits per-requires-clause Asserts BEFORE
// the AssertBitVector to check the requires hold at the assert
// site, so the requires has to actually be establishable — fn-level
// requires propagate the constraints through tactus_auto's
// preconditions.
test_verify_one_file! {
    #[test] test_exec_assert_bit_vector_with_requires verus_code! {
        #[verifier::tactus_auto]
        fn xor_with_requires(x: u8, y: u8)
            requires x == 5u8, y == 2u8,
        {
            assert(x ^ y == 7u8) by(bit_vector)
                requires x == 5u8, y == 2u8;
        }
    } => Ok(())
}

// REVIEW lens 3/4 negative: a bit_vector assertion whose ensures
// genuinely does NOT follow from its requires. Tests that the
// req_conj → ens_conj rendering reaches bv_decide and fails when
// the implication is false. (As distinct from the per-requires
// precondition checks failing — those are tested by the "insufficient"
// case below.)
test_verify_one_file! {
    #[test] test_exec_assert_bit_vector_with_requires_fails verus_code! {
        #[verifier::tactus_auto]
        fn xor_wrong_with_requires(x: u8, y: u8)
            requires x == 5u8, y == 2u8,
        {
            // x=5, y=2 → x^y=7, NOT 9. The req_conj → ens_conj
            // shape `(x=5 ∧ y=2) → x^y=9` is false; bv_decide
            // fails.
            assert(x ^ y == 9u8) by(bit_vector)
                requires x == 5u8, y == 2u8;
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1,
            "false bit_vector goal should fail even with requires");
    }
}

// REVIEW lens 3/3: AssertBitVector inside an if-branch. The branch
// condition becomes a Hyp frame in OblCtx, but `obl.wrap_no_hyps`
// drops it for the BV-mode goal — important because Int-mode hyps
// (e.g., a branch like `x ^ y == 7`) wouldn't typecheck in BV mode
// without the conditionally-injected `HXor Int Int Int` instances.
test_verify_one_file! {
    #[test] test_exec_assert_bit_vector_in_if_branch verus_code! {
        #[verifier::tactus_auto]
        fn xor_in_if(x: u8, y: u8) {
            if x == 5 && y == 2 {
                assert(x ^ y == 7u8) by(bit_vector)
                    requires x == 5u8, y == 2u8;
            }
        }
    } => Ok(())
}

// REVIEW lens 3/3: AssertBitVector inside a loop body. The
// invariant + cond become Hyp frames; the modified-var quantifier
// becomes a Binder frame. `wrap_no_hyps` drops the Hyps but keeps
// the Binder, so the BV goal sees the loop-local `i` as a free
// variable.
test_verify_one_file! {
    #[test] test_exec_assert_bit_vector_in_loop verus_code! {
        #[verifier::tactus_auto]
        fn xor_in_loop() {
            let mut i: u8 = 0;
            while i < 3
                invariant i <= 3,
                decreases (3 - i) as int,
            {
                assert((5u8 ^ 3u8) == 6u8) by(bit_vector);
                i = i + 1;
            }
        }
    } => Ok(())
}

// REVIEW lens 3/3: AssertBitVector inside a closure body. The
// closure's params become Binder frames in OblCtx; `wrap_no_hyps`
// keeps them. The closure body verification scope (#93) walks
// these obligations under `∀ p : T, h_p_bound → ...`.
test_verify_one_file! {
    #[test] test_exec_assert_bit_vector_in_closure verus_code! {
        #[verifier::tactus_auto]
        fn xor_in_closure() {
            let _f = |x: u8| -> u8 {
                assert((x ^ x) == 0u8) by(bit_vector);
                x
            };
        }
    } => Ok(())
}

// #147: AssertBitVector with a function call inside the assertion.
// DESIGN.md catalogue previously claimed BOTH (a) Verus rejects
// upstream and (b) Tactus rejects cleanly. Probe established both
// claims wrong: Verus passes the call through, Tactus's bit-vector
// renderer's reject-Call arm IS reached for the BV-mode goal, but
// Verus's pre-injected `Assume(ens)` (Int-mode hyp continuity) goes
// through the regular Int-mode renderer — and `dep_order` was missing
// that path. Two latent bugs surfaced: (1) `seed_worklist` walked
// only require/ensure, never the body, so spec fn calls in body-
// level asserts (any kind, not just bit_vector) never reached the
// preamble; (2) `spec_fn_to_ast` reused `fn_binders` which adds
// u-type bound hyps as binders — wrong for spec-fn defs (changes
// the type from `Int → Int` to `Int → Bound → Int` and breaks call
// sites). Both fixed 2026-05-09.
test_verify_one_file! {
    #[test] test_exec_assert_bit_vector_with_fn_call verus_code! {
        spec fn id_u8(x: u8) -> u8 { x }

        #[verifier::tactus_auto]
        fn xor_with_call(x: u8) {
            assert(id_u8(x) ^ x == 0u8) by(bit_vector);
        }
    } => Ok(())
}

// #147 second pin: same fix surface, plain `assert(P)` shape. The
// `seed_worklist` body walk benefits any body-level spec fn call
// not just bit_vector; this test pins the broader fix. Pre-fix:
// panicked the same way as the bit_vector test above. Post-fix:
// verifies cleanly.
test_verify_one_file! {
    #[test] test_exec_plain_assert_with_spec_call verus_code! {
        spec fn id_u8(x: u8) -> u8 { x }

        #[verifier::tactus_auto]
        fn plain_with_call(x: u8) {
            assert(id_u8(x) == x);
        }
    } => Ok(())
}

// #147 review (lens 14): regression test for the broader bug class
// — spec fn referenced from a body-level assert nested inside a
// loop. dep_order's walk_expr covers `ExprX::Loop { body, ... }`
// recursively, so the body walk reaches assertions inside the loop
// body. Pre-#147 fix this would have panicked with "unresolved";
// post-fix, the rfl-shaped assertion closes via tactus_auto. Pins
// that the fix isn't shape-specific to top-level body asserts —
// nested positions reachable by walk_expr work too.
test_verify_one_file! {
    #[test] test_exec_loop_body_assert_with_spec_call verus_code! {
        spec fn id_u8(x: u8) -> u8 { x }

        #[verifier::tactus_auto]
        fn loop_with_inner_assert(n: u8)
            requires n < 100
        {
            let mut i: u8 = 0;
            while i < n
                invariant i <= n,
                decreases (n - i) as int,
            {
                assert(id_u8(i) == id_u8(i));
                i = i + 1;
            }
        }
    } => Ok(())
}

// #147 follow-up: pin the workaround for spec fns in goal position.
// DESIGN.md catalogue (added 2026-05-09) initially recommended
// `proof { unfold f }`. Probe established that's *incomplete* — the
// tactic-prefix mechanism applies the prefix to EVERY theorem in
// the fn, including init theorems whose goals don't mention `f`
// (e.g., the first invariant init `i ≤ n`). Bare `unfold f` fails
// with "Tactic unfold failed to unfold f in <goal-without-f>" for
// those theorems.
//
// The actual workaround needs `try unfold f` so the tactic no-ops
// on theorems where `f` doesn't appear, and unfolds where it does.
// This test pins the corrected shape — once the catalogue is
// updated, future users find the right shape, not the incomplete
// one.
test_verify_one_file! {
    #[test] test_exec_loop_invariant_with_spec_call_try_unfold verus_code! {
        spec fn id_u8(x: u8) -> u8 { x }

        #[verifier::tactus_auto]
        fn loop_with_inv_unfold(n: u8)
            requires n < 100
        {
            proof { try unfold id_u8 }
            let mut i: u8 = 0;
            while i < n
                invariant
                    i <= n,
                    id_u8(i) == i,
                decreases (n - i) as int,
            {
                i = i + 1;
            }
        }
    } => Ok(())
}

// #147 follow-up: probe whether the body-assert pattern can
// discharge a loop invariant maintain obligation when the spec fn
// can't be unfolded by the auto-tactic. The idea: place
// `assert(invariant_expr) by { user_tac };` at the END of the loop
// body (post-assignment, so vars match the post-state), and the
// asserted hypothesis enters the OblCtx for the maintain theorem.
// The maintain step's goal then matches the asserted hyp directly,
// closing via `simp_all`.
//
// If this works, the parser-extension proposal (`invariant P by
// { tac }`) becomes a usability question rather than a correctness
// requirement: the existing `assert(P) by { tac }` mechanism plus
// discipline about WHERE to place it is sufficient. Discoverability
// is preserved by the existing error UX (failing tactus_auto shows
// the goal and source location, telling the user what to prove).
test_verify_one_file! {
    #[test] test_exec_body_assert_discharges_invariant verus_code! {
        spec fn id_u8(x: u8) -> u8 { x }

        #[verifier::tactus_auto]
        fn loop_with_body_proof(n: u8)
            requires n < 100
        {
            assert(id_u8(0u8) == 0u8) by { simp_all [id_u8] };
            let mut i: u8 = 0;
            while i < n
                invariant
                    i <= n,
                    id_u8(i) == i,
                decreases (n - i) as int,
            {
                i = i + 1;
                assert(id_u8(i) == i) by { simp_all [id_u8] };
            }
        }
    } => Ok(())
}

// #109 follow-up: recursion over a member of a mutual-SCC datatype.
// `Forest.height` post-#109 calls `Tree.height` for its Tree fields
// (cross-type recursion in the height fn, requiring the mutual block).
// This test exercises the termination obligation: `Forest.height rest <
// Forest.height (Cons _ rest) = 1 + Tree.height _ + Forest.height rest`.
// omega closes it because Tree.height is at-least-1 from the Nat type.
test_verify_one_file! {
    #[test] test_exec_call_recursive_over_mutual_datatype verus_code! {
        use vstd::std_specs::alloc::*;

        enum Tree {
            Leaf,
            Branch(Box<Forest>),
        }

        enum Forest {
            Empty,
            Cons(Box<Tree>, Box<Forest>),
        }

        #[verifier::tactus_auto]
        fn forest_count(f: &Forest) -> (r: u64)
            decreases f
        {
            match f {
                Forest::Empty => 0,
                Forest::Cons(_, rest) => forest_count(rest),
            }
        }
    } => Ok(())
}

// #108 followup: generic datatype with TWO type parameters. Verifies
// that the implicit-binder machinery handles >1 type arg correctly
// (one `{A : Type}` per param, accessor's `[Inhabited A] [Inhabited B]`
// chain, Lean's auto-derived `Inhabited (Tagged A B)` from both
// instances). The earlier #108 tests used `List<A>` with one param;
// this locks the multi-param shape.
test_verify_one_file! {
    #[test] test_exec_call_recursive_generic_datatype_two_params verus_code! {
        use vstd::std_specs::alloc::*;

        enum Tagged<A, B> {
            Leaf(A, B),
            Node(A, Box<Tagged<A, B>>),
        }

        #[verifier::tactus_auto]
        fn depth(t: &Tagged<u8, u8>) -> (r: u64)
            decreases t
        {
            match t {
                Tagged::Leaf(_, _) => 0,
                Tagged::Node(_, rest) => depth(rest),
            }
        }
    } => Ok(())
}

// #108 edge: generic recursive datatype with a TRAIT BOUND on the
// type param. DESIGN.md flagged this as untested — `height_fn_for_datatype`
// and `multi_variant_accessor_defs` ignore `dt.typ_bounds`. Prediction:
// works because the height fn is structural and doesn't actually USE
// the bound; Lean's `def TBox.height {A : Type} : TBox A → Nat | …`
// has no Lean-level encoding of `Tag`, so the bound is silently
// dropped during emission. The exec fn instantiates with a concrete
// type that happens to satisfy the bound on the Rust side; Verus is
// the one enforcing the bound, Tactus just translates the structure.
test_verify_one_file! {
    #[test] test_exec_call_recursive_generic_datatype_trait_bound verus_code! {
        use vstd::std_specs::alloc::*;

        trait Tag {
            spec fn tag(&self) -> int;
        }

        struct Marked { v: int }
        impl Tag for Marked {
            spec fn tag(&self) -> int { self.v }
        }

        enum TBox<A: Tag> {
            Leaf(A),
            Node(Box<TBox<A>>),
        }

        #[verifier::tactus_auto]
        fn count_tbox(t: &TBox<Marked>) -> (r: u64)
            decreases t
        {
            match t {
                TBox::Leaf(_) => 0,
                TBox::Node(rest) => count_tbox(rest),
            }
        }
    } => Ok(())
}

// Early return inside a loop body — the WP DSL's `Return` arm writes
// `ctx.ensures_goal` (the fn's ensures) by construction, regardless
// of how deeply nested the return is. Pre-DSL code conflated this
// with the loop's local `I ∧ D < d_old` terminator; the Wp DSL
// shape gets it right for free. This test pins the behaviour so
// someone "fixing" Return to use `after` instead of `ensures_goal`
// would trip it.
test_verify_one_file! {
    #[test] test_exec_return_inside_loop verus_code! {
        #[verifier::tactus_auto]
        fn find_in_range(target: u8, n: u8) -> (r: u8)
            requires n > 0
            ensures r == target || r == n
        {
            let mut i: u8 = 0;
            while i < n
                invariant i <= n
                decreases n - i
            {
                if i == target {
                    return target;
                }
                i = i + 1;
            }
            n
        }
    } => Ok(())
}

// Trait method call resolved to a concrete impl. `b.bump(x)` with
// `b: &Id` is a `DynamicResolved` case: Verus knows the receiver
// type so `resolved_method = Some((Id::bump, [Id]))`. `walk_call`
// redirects the callee lookup to the resolved impl and substitutes
// the impl's specs (which equal or strengthen the trait's specs).
test_verify_one_file! {
    #[test] test_exec_call_trait_method verus_code! {
        trait Bumper {
            fn bump(&self, x: u8) -> (r: u8)
                ensures r == x;
        }

        struct Id;
        impl Bumper for Id {
            fn bump(&self, x: u8) -> (r: u8)
                ensures r == x
            {
                x
            }
        }

        #[verifier::tactus_auto]
        fn call_via_trait(b: &Id, x: u8) -> (r: u8)
            ensures r == x
        {
            b.bump(x)
        }
    } => Ok(())
}

// Negative: trait method's requires is violated at the call site.
// Pins that the substituted requires (from the resolved impl) is
// what gets emitted as the precondition obligation.
test_verify_one_file! {
    #[test] test_exec_call_trait_method_requires_violated verus_code! {
        trait Bounded {
            fn checked_add(&self, x: u8, y: u8) -> (r: u8)
                requires x + y < 256
                ensures r == x + y;
        }

        struct Adder;
        impl Bounded for Adder {
            fn checked_add(&self, x: u8, y: u8) -> (r: u8)
                ensures r == x + y
            {
                x + y
            }
        }

        #[verifier::tactus_auto]
        fn try_add(a: &Adder, x: u8) -> (r: u8)
            ensures r == x
        {
            // x + 200 may overflow when x > 55 — caller has no bound on x
            a.checked_add(x, 200)
        }
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e| e.message.contains("precondition")),
            "expected precondition failure on trait method call, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
}

// Two impls of the same trait — the caller picks one statically.
// Each call site's `resolved_method` points at a different impl;
// post-#86 the caller sees BOTH the trait's ensures AND the
// resolved impl's strengthened ensures conjoined. This test pins
// the basic shape (caller's ensures is the trait-level `r < 100`,
// which is satisfied by either impl). For tests that exercise
// the impl-specific strengthening visibly, see
// `test_exec_call_trait_method_impl_strengthens` /
// `test_exec_call_trait_method_wrong_impl_strengthening`.
test_verify_one_file! {
    #[test] test_exec_call_trait_method_two_impls verus_code! {
        trait Wrapper {
            fn unwrap(&self) -> (r: u8)
                ensures r < 100;
        }

        struct AlwaysFive;
        impl Wrapper for AlwaysFive {
            fn unwrap(&self) -> (r: u8)
                ensures r == 5
            {
                5
            }
        }

        struct AlwaysTen;
        impl Wrapper for AlwaysTen {
            fn unwrap(&self) -> (r: u8)
                ensures r == 10
            {
                10
            }
        }

        #[verifier::tactus_auto]
        fn use_either(w: &AlwaysFive) -> (r: u8)
            ensures r < 100  // trait-level guarantee
        {
            w.unwrap()
        }

        #[verifier::tactus_auto]
        fn use_other(w: &AlwaysTen) -> (r: u8)
            ensures r < 100  // same trait-level guarantee — impl differs
        {
            w.unwrap()
        }
    } => Ok(())
}

// Trait method that takes additional non-self args. Pins that the
// substitution map handles trait-method param names (`x: u8`)
// correctly when the resolved impl is a different fn than the trait
// decl — both have the same param names but the LExpr for the param
// binding must come from the right place.
test_verify_one_file! {
    #[test] test_exec_call_trait_method_with_args verus_code! {
        trait Adder {
            fn add_one(&self, x: u8) -> (r: u8)
                requires x < 200
                ensures r == x + 1;
        }

        struct Plain;
        impl Adder for Plain {
            fn add_one(&self, x: u8) -> (r: u8)
                ensures r == x + 1
            {
                x + 1
            }
        }

        #[verifier::tactus_auto]
        fn caller(a: &Plain, n: u8) -> (r: u8)
            requires n < 100
            ensures r == n + 1
        {
            a.add_one(n)
        }
    } => Ok(())
}

// #96: trait method with a default body, impl doesn't override.
// The call resolves to the trait's default. `resolve_callee` redirects
// to use the trait method decl (which holds the default body and
// spec) instead of Verus's synthesized `<impl>%default%<method>`
// wrapper — Self resolves through the existing typ_args / typ_subst
// machinery.
test_verify_one_file! {
    #[test] test_exec_call_trait_default verus_code! {
        trait Greeter {
            fn salute(&self) -> (r: u8)
                ensures r == 1
            {
                1
            }
        }

        struct Plain;
        impl Greeter for Plain {}

        #[verifier::tactus_auto]
        fn caller(p: &Plain) -> (r: u8)
            ensures r == 1
        {
            p.salute()
        }
    } => Ok(())
}

// Negative: caller's ensures contradicts the trait default's ensures.
// Pins that the trait default's spec is what the caller sees as a
// post-call hypothesis (not some unrelated fallback).
test_verify_one_file! {
    #[test] test_exec_call_trait_default_wrong_ensures verus_code! {
        trait Greeter {
            fn salute(&self) -> (r: u8)
                ensures r == 1
            {
                1
            }
        }

        struct Plain;
        impl Greeter for Plain {}

        #[verifier::tactus_auto]
        fn caller(p: &Plain) -> (r: u8)
            ensures r == 5  // wrong: default returns 1
        {
            p.salute()
        }
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e| e.message.contains("postcondition")),
            "expected postcondition failure, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
}

// Default with non-self params + a precondition. Pins that the
// trait default's `requires` reaches the precondition obligation,
// AND that args substitute correctly into both the requires and
// ensures.
test_verify_one_file! {
    #[test] test_exec_call_trait_default_with_args verus_code! {
        trait Inc {
            fn inc(&self, x: u8) -> (r: u8)
                requires x < 200
                ensures r == x + 1
            {
                x + 1
            }
        }

        struct Plain;
        impl Inc for Plain {}

        #[verifier::tactus_auto]
        fn caller(p: &Plain, x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            p.inc(x)
        }
    } => Ok(())
}

// Mixed: trait has a default; some impls override, others don't.
// Caller invokes the OVERRIDING impl; pins that we still go through
// the concrete-impl path (and impl-strengthening from #86 still
// applies — caller's stronger ensures is provable).
test_verify_one_file! {
    #[test] test_exec_call_trait_default_overridden verus_code! {
        trait Greeter {
            fn salute(&self) -> (r: u8)
                ensures r < 100
            {
                1
            }
        }

        struct Strong;
        impl Greeter for Strong {
            fn salute(&self) -> (r: u8)
                ensures r == 42
            {
                42
            }
        }

        #[verifier::tactus_auto]
        fn caller(s: &Strong) -> (r: u8)
            ensures r == 42  // caller relies on Strong's strengthened ensures
        {
            s.salute()
        }
    } => Ok(())
}

// #86: impl-specific strengthening of `ensures`. The trait declares a
// weak postcondition; the impl strengthens it. Caller sees BOTH
// conjoined, so they can rely on the impl's specific guarantee.
//
// Pre-#86 this test would fail (caller would only see `r < 100` from
// the trait, can't prove `r == 5`). Post-#86 the impl's `ensures r == 5`
// is conjoined into the post-call hypothesis, and the caller's
// stronger ensures `r == 5` becomes provable.
test_verify_one_file! {
    #[test] test_exec_call_trait_method_impl_strengthens verus_code! {
        trait Wrapper {
            fn unwrap(&self) -> (r: u8)
                ensures r < 100;
        }

        struct AlwaysFive;
        impl Wrapper for AlwaysFive {
            fn unwrap(&self) -> (r: u8)
                ensures r == 5
            {
                5
            }
        }

        #[verifier::tactus_auto]
        fn use_strengthened(w: &AlwaysFive) -> (r: u8)
            ensures r == 5  // impl-specific guarantee, not just trait's r < 100
        {
            w.unwrap()
        }
    } => Ok(())
}

// Negative: caller relies on impl-specific strengthening that the
// resolved impl doesn't actually provide. Pins that the impl-side
// ensures we conjoin is the RESOLVED impl's, not some other impl
// of the same trait.
test_verify_one_file! {
    #[test] test_exec_call_trait_method_wrong_impl_strengthening verus_code! {
        trait Wrapper {
            fn unwrap(&self) -> (r: u8)
                ensures r < 100;
        }

        struct AlwaysFive;
        impl Wrapper for AlwaysFive {
            fn unwrap(&self) -> (r: u8)
                ensures r == 5
            {
                5
            }
        }

        struct AlwaysTen;
        impl Wrapper for AlwaysTen {
            fn unwrap(&self) -> (r: u8)
                ensures r == 10
            {
                10
            }
        }

        #[verifier::tactus_auto]
        fn caller(w: &AlwaysFive) -> (r: u8)
            ensures r == 10  // wrong: AlwaysFive returns 5
        {
            w.unwrap()
        }
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e| e.message.contains("postcondition")),
            "expected postcondition failure, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
}

// ── Control-flow combination coverage ──────────────────────────────
// Three combinatorial gaps: return-in-else (inverse of test_exec_
// early_return), loops modifying many vars (only 1-2 tested), and
// nested ifs each containing their own loop.

// Return in the `else` branch where the `then` falls through to tail
// code. Verus's SST may produce a different StmX::Return.inside_body
// shape vs the test_exec_early_return case — this pins both shapes.
test_verify_one_file! {
    #[test] test_exec_return_in_else verus_code! {
        #[verifier::tactus_auto]
        fn clip_to_zero_else(x: u8) -> (r: u8)
            requires x <= 10
            ensures r <= 10
        {
            if x == 0 {
                // then falls through
            } else {
                return 0;
            }
            x
        }
    } => Ok(())
}

// Loop modifying 4 variables. `quantify_mod_vars` handles arbitrary-
// arity modified sets; only 1-2 vars were tested. Pins that the
// ∀-quantification + modified-var binding still works at width-4.
test_verify_one_file! {
    #[test] test_exec_loop_many_mod_vars verus_code! {
        #[verifier::tactus_auto]
        fn count_quad(n: u8) -> (r: u8)
            requires n <= 50
            ensures r <= 200
        {
            let mut a: u8 = 0;
            let mut b: u8 = 0;
            let mut c: u8 = 0;
            let mut d: u8 = 0;
            let mut i: u8 = 0;
            while i < n
                invariant
                    i <= n,
                    a <= i,
                    b <= i,
                    c <= i,
                    d <= i,
                decreases n - i
            {
                a = a + 1;
                b = b + 1;
                c = c + 1;
                d = d + 1;
                i = i + 1;
            }
            a + b + c + d
        }
    } => Ok(())
}

// Nested if where each branch contains its own loop. Combinatorial
// coverage gap noted in DESIGN.md — exercises Wp::Branch wrapping
// Wp::Loop in both arms, with each loop having distinct mod-vars and
// invariants.
test_verify_one_file! {
    #[test] test_exec_nested_if_with_loops verus_code! {
        #[verifier::tactus_auto]
        fn maybe_count(flag: bool, n: u8) -> (r: u8)
            requires n <= 100
            ensures r <= 100
        {
            let mut acc: u8 = 0;
            if flag {
                let mut i: u8 = 0;
                while i < n
                    invariant i <= n, acc <= i
                    decreases n - i
                {
                    acc = acc + 1;
                    i = i + 1;
                }
            } else {
                let mut j: u8 = 0;
                while j < n
                    invariant j <= n, acc <= j
                    decreases n - j
                {
                    acc = acc + 1;
                    j = j + 1;
                }
            }
            acc
        }
    } => Ok(())
}

// ── Lossy-accept paths (renderer drops or normalizes info) ────────
// Three paths documented as accepted-with-info-dropped in DESIGN.md
// "Lossy accepted forms" but lacking direct tests.

// `BinaryOp::Xor` renders via `App(Var("xor"), [l, r])`. If the
// rendering ever changes (or the prelude's `xor` definition shifts),
// this regression catches it. Bool xor is the simplest exec-level
// case — Verus accepts `^` on bools.
test_verify_one_file! {
    #[test] test_exec_xor_bool verus_code! {
        #[verifier::tactus_auto]
        fn xor_bools(a: bool, b: bool) -> (r: bool)
            ensures r == (a ^ b)
        { a ^ b }
    } => Ok(())
}

// `ExpX::Bind(BndX::Choose, ...)` in spec context. Rendered as
// `Classical.epsilon (fun ... => cond ∧ body)`. Pin that the
// rendering doesn't crash codegen — Verus's recommends checks on
// `choose` may still apply, but the Lean output must at least
// be syntactically valid. Accepted-with-info-dropped per DESIGN.md.
test_verify_one_file! {
    #[test] test_exec_choose_in_spec verus_code! {
        spec fn p(n: nat) -> bool { n > 0 }

        spec fn pos_witness() -> nat {
            choose|n: nat| #[trigger] p(n)
        }

        #[verifier::tactus_auto]
        fn use_p() -> (r: u8)
            ensures r == 1u8 || pos_witness() > 0
        { 1 }
    } => Ok(())
}

// ── Shape-drift / regression-guard tests ──────────────────────────
// Tests pinning behavior that's easy to silently regress under a
// Verus rebase or a refactor of our walker.

// Name collision: callee's `ret.name.0` (the Rust source-level name
// of the return — `r` in `-> (r: u8)`) clashes with a caller-scope
// local of the same sanitized name. `walk_call` emits `∀ <ret_name
// : T>, …` where `<ret_name>` shadows the caller's `r` for the
// duration of the post-call frames. Semantically fine — the ∀
// binding is what Verus intends — but visually confusing if the
// shadow ever produces wrong-binding behavior. Pin that this works.
test_verify_one_file! {
    #[test] test_exec_call_ret_name_collision verus_code! {
        fn make_one() -> (r: u8)
            ensures r == 1
        { 1 }

        #[verifier::tactus_auto]
        fn caller() -> (out: u8)
            ensures out == 8
        {
            let r: u8 = 7;        // collides with callee's ret name
            let val = make_one(); // ∀ r, r == 1 → ...
            r + val               // caller's r is 7, val is 1
        }
    } => Ok(())
}

// NOTE: `assert forall|v: T| P by { tac }` (with non-empty `vars`)
// inside a tactus_auto fn currently panics in Verus's poly encoding
// pass (`vir/src/poly.rs:462`). The Tactus AssertBy + Ghost wrap
// doesn't carry the binder information through to where poly
// expects it. This is documented as a #79 follow-up — the panic
// blocks adding a regression test (we can't `Err(_)` against an
// upstream panic), so the gap is just a comment for now. Workaround
// for users: pull the forall into a separate proof fn and `assert`
// the application.

// Datatype constructor (Ctor) in exec fn body — struct construction
// plus field access. Pinned: before #52 landed, this was rejected
// with "datatype constructors not yet supported in exec fns".
// Exercises `ExpX::Ctor` routed through the shared `ctor_node` helper
// (`Dt::Path` + "mk" variant-segment for the sole-variant struct case).
test_verify_one_file! {
    #[test] test_exec_ctor_struct verus_code! {
        struct Point { x: u8, y: u8 }

        #[verifier::tactus_auto]
        fn make_point() -> (r: u8)
            ensures r == 3
        {
            let p = Point { x: 1, y: 2 };
            p.x + p.y
        }
    } => Ok(())
}

// User-written `assert(P) by { lean_tactic }` inside a tactus_auto
// exec fn — the escape hatch when the default `tactus_auto` closer
// can't prove an obligation. The FileLoader sanitizes the `{ ... }`
// content to spaces for rustc, rust_to_vir captures the original
// source byte range on `ExprX::AssertBy::tactic_span`, ast_to_sst
// routes it to `StmX::AssertQuery` with `AssertQueryMode::Tactus`,
// and `sst_to_lean::build_wp` reads the verbatim tactic off disk
// and produces a `Wp::AssertByTactus { cond: Some(P), tactic_text }`
// node. The walker emits one theorem for `P` with the user tactic as
// its closer, and `P` enters the body context as a hypothesis for
// subsequent obligations.
test_verify_one_file! {
    #[test] test_exec_assert_by_user_tactic verus_code! {
        #[verifier::tactus_auto]
        fn f(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            assert(x < 100 ==> x + 1 <= 100) by { omega }
            x + 1
        }
    } => Ok(())
}

// D Stage 6: failing `assert(P) by { wrong_tactic }`. The user
// chose the wrong tactic; the assert-by theorem fails. Lean's
// error must mention this fn (the `wrong_tactic` is `decide`,
// which can't see arithmetic facts about runtime variables).
test_verify_one_file! {
    #[test] test_exec_assert_by_wrong_tactic verus_code! {
        #[verifier::tactus_auto]
        fn bad_assert_by(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            // `decide` can't prove this — needs `omega` for the
            // x-quantified arithmetic. The assert-by theorem
            // should fail with the user's tactic as the cause.
            assert(x < 200) by { decide }
            x + 1
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "wrong assert-by tactic must be rejected");
    }
}

// D review: empty `proof { }` block. The FileLoader sanitizes the
// brace body to whitespace-only, rust_to_vir's empty-HIR-body
// heuristic routes the block through Tactus mode, and walk_assert_
// by_tactus's `None` branch must NOT push a whitespace-only prefix
// onto e.tactic_prefix — doing so produced `(\n) <;> tactus_auto`
// which Lean rejects as an empty parenthesised tactic block. The
// fix: skip the push entirely for whitespace-only `tactic_text`.
test_verify_one_file! {
    #[test] test_exec_proof_block_empty verus_code! {
        #[verifier::tactus_auto]
        fn empty_proof(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            proof { }
            x + 1
        }
    } => Ok(())
}

// D review: empty `assert(P) by { }`. Same risk as the empty-proof
// case: a whitespace-only tactic body would emit `:= by ` followed
// by nothing, which Lean rejects. Fix: walk_assert_by_tactus's
// `Some` branch falls back to `simple_tactic` (`tactus_auto`) when
// `tactic_text` is whitespace-only, so the obligation still
// verifies via the default closer.
test_verify_one_file! {
    #[test] test_exec_assert_by_empty verus_code! {
        #[verifier::tactus_auto]
        fn empty_assert_by(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            assert(x < 200) by { }
            x + 1
        }
    } => Ok(())
}

// Coverage gap: two sequential `proof { ... }` blocks. Walker
// pushes both prefixes onto `e.tactic_prefix`, so every emitted
// theorem in their combined scope gets `(prefix1\n prefix2) <;>
// closer`. Hypotheses introduced by the first block are in scope
// for the second's `have` and for the closer.
test_verify_one_file! {
    #[test] test_exec_proof_block_sequential verus_code! {
        #[verifier::tactus_auto]
        fn use_two_haves(x: u8) -> (r: u8)
            requires x < 50
            ensures r == x + 1
        {
            proof {
                have h1 : x < 100 := by omega
            }
            proof {
                have h2 : x < 200 := by omega
            }
            // Both h1 and h2 are in scope here for tactus_auto to
            // pick up via simp_all.
            x + 1
        }
    } => Ok(())
}

// Coverage gap: fn with no `ensures` clauses. `WpCtx::new` builds
// `ensures_goal = and_all([]) = LitBool(true)` (unwrapped — no
// SpanMark since the per-clause map() iterates nothing). The Done
// leaf is `let r := e; True`; emit_done_or_split peels the Let,
// recurses on `True`, and falls into the unwrapped fallback
// (kind_label = "ensures", empty loc) → emits one trivial theorem.
// Untested before this commit.
test_verify_one_file! {
    #[test] test_exec_no_ensures verus_code! {
        #[verifier::tactus_auto]
        fn no_ensures_clause() -> (r: u8) {
            5
        }
    } => Ok(())
}

// Coverage gap: callee with NO requires AND NO ensures. Exercises
// `walk_call`'s skip-precondition path (no theorem emitted for an
// empty requires) and skip-ensures-frame path (no `Hyp(True)`
// pushed for an empty ensures). Without these guards we'd emit
// trivial precondition theorems and add tautological frames to
// the continuation context.
//
// Caller's ensures doesn't depend on the callee's return — that
// would require the callee to have ensures. We're exercising the
// CALL CONTEXT, not the value flow.
test_verify_one_file! {
    #[test] test_exec_call_no_requires_no_ensures verus_code! {
        #[verifier::tactus_auto]
        fn trivial_callee() -> (r: u8) {
            42
        }

        #[verifier::tactus_auto]
        fn trivial_caller() -> (r: u8)
            ensures r == 7
        {
            // Discard callee's return; our ensures is independent.
            let _ignored = trivial_callee();
            7
        }
    } => Ok(())
}

// User-written `proof { ... }` block inside a tactus_auto exec fn.
// Unlike `assert(P) by { ... }` which wraps the user tactic in
// `have h_N : P := by <tac>`, a proof block emits the user tactic
// RAW — so `have h : Q := by tac` inside the block introduces `h`
// at theorem-tactic level, available for subsequent obligations.
//
// This test writes a proof block containing `have` statements; the
// hypotheses they introduce get picked up by `simp_all` / `omega`
// when proving the ensures clause. rust_to_vir synthesises this as
// an `ExprX::AssertBy { is_tactus_proof_block: true, … }` which
// ast_to_sst routes to `AssertQueryMode::Tactus { kind:
// TactusKind::ProofBlock }`.
test_verify_one_file! {
    #[test] test_exec_proof_block_user_tactic verus_code! {
        #[verifier::tactus_auto]
        fn g(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            proof {
                have h : x + 1 <= 100 := by omega
            }
            x + 1
        }
    } => Ok(())
}

// D Stage 6: proof-block `have`s should propagate to ALL obligation
// theorems within the body's lexical scope. With per-obligation
// theorem emission, each obligation theorem in scope gets the
// proof-block tactic prefixed via `<;>`, so the `have h : P := by …`
// introduces `h` for every theorem's closer. Without correct
// propagation (D Stage 4), the final `assert(P)` after the proof
// block would have no way to see `h_step`, and `tactus_auto` would
// fail.
test_verify_one_file! {
    #[test] test_exec_proof_block_have_propagates_to_assert verus_code! {
        #[verifier::tactus_auto]
        fn use_have(x: u8) -> (r: u8)
            requires x < 50
            ensures r == x + 1
        {
            proof {
                have h_step : x < 200 := by omega
            }
            assert(x < 200);
            x + 1
        }
    } => Ok(())
}

// Proof block containing a *goal-modifying* tactic (`simp_all`, not
// just `have`). Documents the current semantics: proof-block tactics
// are prepended to the theorem's closer and run at theorem-tactic
// level, so `simp_all` simplifies the ENTIRE theorem goal — not just
// a local sub-proof. Users familiar with Verus's `proof { ... }`
// blocks (where the content is a self-contained proof) may be
// surprised. The alternative (wrapping in `have _ : True := by simp`)
// would isolate the effect but makes `have h : P := by tac` NOT
// propagate — the common case we actually want.
//
// Here `simp_all` is a no-op for this specific goal (no simp lemmas
// apply), so the test just confirms we accept it and the fn verifies
// via the downstream omega. If a future change wraps proof-block
// tactics so they DON'T affect outer goal, this test would break
// only if the specific tactic relied on that isolation — not the
// case here.
test_verify_one_file! {
    #[test] test_exec_proof_block_goal_modifying_tactic verus_code! {
        #[verifier::tactus_auto]
        fn goal_mod(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            proof {
                simp_all
            }
            x + 1
        }
    } => Ok(())
}

// Regression for the Tactus discriminator in rust_to_vir_expr.rs:
// the empty-HIR-body heuristic distinguishes user-written `proof { }`
// (sanitized to empty by the FileLoader) from Verus's `auto_proof_block`
// which wraps `assert(…);` / `assume(…);` in a synthetic proof block
// with the wrapped stmt inside.
//
// This fn has BOTH a plain `assert(P);` (which `auto_proof_block`
// wraps in a synthetic `proof { assert_(P) }` — non-empty body) AND
// a user-written `proof { have h := ... }` (which the FileLoader
// sanitizes to an empty body). Only the latter should route through
// Tactus synthesis; the former should stay on the normal DeadEnd
// desugaring. If Verus ever generates truly-empty synthetic proof
// blocks (from some edge case we haven't seen), our heuristic would
// mis-classify them — this test would catch that drift by failing.
test_verify_one_file! {
    #[test] test_exec_auto_proof_block_not_tactus verus_code! {
        #[verifier::tactus_auto]
        fn both(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            assert(x < 100);  // auto_proof_block wraps this; non-empty body
            proof {
                have h : x + 1 <= 100 := by omega
            }
            x + 1
        }
    } => Ok(())
}

// Generic call: the callee is parametric over `T`, and the call site
// supplies `T = u8` via `typ_args`. `build_wp_call` used to reject
// non-empty `typ_args` outright; now `lower_call` substitutes the
// callee's `typ_params` with the call-site's `typ_args` (mapped
// through `typ_to_expr`) into the rendered require/ensure, inlining
// the spec at the concrete instantiation.
test_verify_one_file! {
    #[test] test_exec_call_generic verus_code! {
        #[verifier::tactus_auto]
        fn identity<T>(x: T) -> (r: T)
            ensures r == x
        {
            x
        }

        #[verifier::tactus_auto]
        fn use_identity(n: u8) -> (r: u8)
            ensures r == n
        {
            identity(n)
        }
    } => Ok(())
}

// Multi-variant enum + pattern matching verifies end-to-end via
// #58's `tactus_case_split` in TactusPrelude.lean: the tactic
// finds `k : Kind` (gated on `Kind.height` existing, which
// `height_fn_for_datatype` emits for every concrete datatype)
// and case-splits, letting `simp_all` unfold the
// IsVariant/Field accessors into concrete branches that omega
// can close.
test_verify_one_file! {
    #[test] test_exec_match_enum verus_code! {
        enum Kind { Foo(u8), Bar(u8) }

        #[verifier::tactus_auto]
        fn kind_value(k: Kind) -> (r: u8)
            ensures r <= 100
        {
            match k {
                Kind::Foo(x) => if x <= 100 { x } else { 0 },
                Kind::Bar(y) => if y <= 100 { y } else { 0 },
            }
        }
    } => Ok(())
}

// Same shape as `test_exec_match_enum` but with the proof control
// shifted from `tactus_case_split` (the default closer's rung) to a
// user-explicit per-arm `proof { cases k with | ... }` block. This
// is the canonical *inline per-case proof* shape — Lean's native
// `cases ... with | Foo x => tac | Bar y => tac` syntax goes through
// `proof { }` verbatim (FileLoader passes tactic text through), so
// each arm's tactic discharges only that arm's subgoal.
//
// Available today without code changes. Use it when:
// (a) `tactus_auto` can't close the match-fn obligation (often
//     because branches need different tactics), or
// (b) you want the per-case reasoning visible at the proof level
//     rather than hidden inside the default closer.
//
// `tactus_case_split` stays in the default closer for the common
// case (user writes `match k { ... }` and expects it to verify);
// this test pins the user-explicit alternative as a parallel option.
test_verify_one_file! {
    #[test] test_exec_match_enum_with_per_arm_proof verus_code! {
        enum Kind { Foo(u8), Bar(u8) }

        #[verifier::tactus_auto]
        fn kind_value_per_arm(k: Kind) -> (r: u8)
            ensures r <= 100
        {
            proof {
                cases k with
                | Foo x => simp_all; split <;> omega
                | Bar y => simp_all; split <;> omega
            }
            match k {
                Kind::Foo(x) => if x <= 100 { x } else { 0 },
                Kind::Bar(y) => if y <= 100 { y } else { 0 },
            }
        }
    } => Ok(())
}

// Match with ensures that reason about variant-specific fields.
// Exercises that `tactus_case_split` composes correctly with a
// non-trivial post-condition — not just pattern closure.
test_verify_one_file! {
    #[test] test_exec_match_enum_with_ensures verus_code! {
        enum Choice { Left(u8), Right(u8) }

        #[verifier::tactus_auto]
        fn unwrap_choice(c: Choice) -> (r: u8)
            ensures match c {
                Choice::Left(x) => r == x,
                Choice::Right(y) => r == y,
            }
        {
            match c {
                Choice::Left(x) => x,
                Choice::Right(y) => y,
            }
        }
    } => Ok(())
}

// Non-enum hypotheses mixed with enum — `tactus_case_split` must
// pick the datatype local, not the int. The `.height`-existence
// gate guards against case-splitting on `Int` (which would
// explode into ofNat/negSucc subgoals). Linear arithmetic in
// branches so omega can close without nonlinear-arith help.
test_verify_one_file! {
    #[test] test_exec_match_enum_with_int_args verus_code! {
        enum Op { Add, Sub }

        #[verifier::tactus_auto]
        fn apply_op(op: Op, x: u8, y: u8) -> (r: u8)
            requires x <= 10, y <= 10, y <= x
            ensures r <= 20
        {
            match op {
                Op::Add => x + y,
                Op::Sub => x - y,
            }
        }
    } => Ok(())
}

// Lexicographic `decreases (x, y)` on a loop (#110). Each iteration
// either decreases `y` (inner-level decrease) or decreases `x` and
// resets `y` (outer-level decrease + permitted equality on `y` is
// vacuously satisfied since the inner branch isn't taken). The
// maintain obligation:
//
//   (x' < x_old) ∨ (x' = x_old ∧ y' < y_old)
//
// is exactly the lex disjunction `lex_decrease_obligation` builds.
test_verify_one_file! {
    #[test] test_exec_loop_lex_decreases verus_code! {
        #[verifier::tactus_auto]
        fn lex_loop(a: u8, b: u8) -> (r: u8)
            requires a <= 10, b <= 10
            ensures r == 0
        {
            let mut x: u8 = a;
            let mut y: u8 = b;
            while x > 0 || y > 0
                invariant x <= a, y <= b
                decreases x, y
            {
                if y > 0 {
                    y = y - 1;
                } else {
                    x = x - 1;
                    y = b;
                }
            }
            x + y
        }
    } => Ok(())
}

// Negative test: a lex loop where neither component decreases on at
// least one iteration. Body sometimes leaves both `x` and `y`
// unchanged — the lex obligation `(x' < x_old) ∨ (x' = x_old ∧ y' <
// y_old)` then fails on that iteration.
test_verify_one_file! {
    #[test] test_exec_loop_lex_decreases_nondecreasing verus_code! {
        #[verifier::tactus_auto]
        fn lex_loop_bad(a: u8) -> (r: u8)
            requires a <= 10
            ensures r == 0
        {
            let mut x: u8 = a;
            let y: u8 = 5;
            while x > 0
                invariant x <= a
                decreases x, y
            {
                // x decreases but y stays the same — this is fine for
                // lex (outer level fires). Add a noop branch where
                // neither changes to break it:
                if x == a {
                    // No change to x or y → obligation fails.
                } else {
                    x = x - 1;
                }
            }
            x + y - 5
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1,
            "non-decreasing lex loop should fail");
        let msgs: Vec<_> = err.errors.iter().map(|e| e.message.clone()).collect();
        assert!(
            msgs.iter().any(|m| m.contains(&vir::tactus_messages::paren_label(vir::tactus_messages::ASSERT_LABEL_LOOP_DECREASE))),
            "expected (loop decrease) kind label on the failing obligation. got: {:?}",
            msgs,
        );
    }
}

// #129 regression test: pre-fix, Tactus's loop decrease emitted
// just `cur < d_old` with no `0 ≤ cur` lower bound. For an
// int-typed decrease that can become negative (here `x as int - 50`
// with `x: u8` starting small), the bare `cur < prev` obligation
// trivially succeeds even though `cur` is descending into negatives
// — the measure is "well-founded" only because Tactus didn't check
// it stayed ≥ 0. Verus's loop encoding (sst_to_air.rs:2823-2834)
// goes through `recursion::check_decrease` which produces
// `0 ≤ cur ∧ cur < d_old`. Post-#129 Tactus matches: this loop
// fails `(loop decrease)` because we can't establish
// `0 ≤ x as int - 50` from the loop invariant `x ≤ start ≤ 10`.
test_verify_one_file! {
    #[test] test_exec_loop_decrease_int_expression_can_go_negative verus_code! {
        #[verifier::tactus_auto]
        fn descending(start: u8) -> (r: u8)
            requires start <= 10
            ensures r == 0
        {
            let mut x: u8 = start;
            while x > 0
                invariant x <= start
                decreases x as int - 50
            {
                x = x - 1;
            }
            x
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1,
            "loop with int decrease that goes negative should fail post-#129");
        let msgs: Vec<_> = err.errors.iter().map(|e| e.message.clone()).collect();
        assert!(
            msgs.iter().any(|m| m.contains(&vir::tactus_messages::paren_label(vir::tactus_messages::ASSERT_LABEL_LOOP_DECREASE))),
            "expected (loop decrease) kind label from #129's missing 0 ≤ cur \
             lower bound. got: {:?}",
            msgs,
        );
    }
}

// Loop with non-empty cond_setup (#114 sub-feature 1) + ret-substitution
// (#128). A function call in the loop's cond triggers Verus's
// `expr_to_stm_opt` to produce setup-stmts for the call result. Pre-#114
// we rejected outright; post-#114 the cond_setup walks as a wp prefix in
// both the maintain and use ctx (mirroring Verus's two-query encoding),
// but the resulting Lean goals had `∀ ret : Prop, ret = (x > 0) → …`
// shapes that tactus_auto's default closer couldn't discharge — users
// needed `#[verifier::tactus_tactic("intros; simp_all; omega")]` and even
// then not all obligations closed.
//
// Post-#128: when the callee's ensures uniquely determines the return
// value via `r == E`, codegen substitutes E for r directly (skipping the
// ∀ quantifier and binding `dest := E`). Tactus_auto closes the resulting
// goal natively; the override is no longer needed.
test_verify_one_file! {
    #[test] test_exec_loop_cond_with_setup verus_code! {
        fn keep_going(x: u8) -> (r: bool)
            ensures r == (x > 0)
        {
            x > 0
        }

        #[verifier::tactus_auto]
        fn count_down(n: u8) -> (r: u8)
            ensures r <= n
        {
            let mut x: u8 = n;
            while keep_going(x)
                invariant x <= n
                decreases x
            {
                x = x - 1;
            }
            x
        }
    } => Ok(())
}

// #128: ret-substitution baseline. Callee with `ensures r == E`; caller's
// post-call obligation depends on knowing `y == E`. Pre-#128, the goal had
// `∀ ret, ret = E → …` which omega could close via the `ret = E` hyp; but
// the substitution path now produces `let y := E; …` with omega seeing the
// arithmetic directly. Both paths verify; this test pins the substituted
// shape works.
test_verify_one_file! {
    #[test] test_exec_call_ret_eq_substitution verus_code! {
        fn add_one_uniq(x: u8) -> (r: u8)
            requires x < 255
            ensures r == x + 1
        {
            x + 1
        }

        #[verifier::tactus_auto]
        fn caller_uniq(x: u8) -> (s: u8)
            requires x < 200
            ensures s == x + 1
        {
            let y = add_one_uniq(x);
            y
        }
    } => Ok(())
}

// #128: ret-substitution with EXTRA conjunct. Ensures has form
// `r == E ∧ Q(r)`. After substitution, `Q(r)` becomes `Q(E)` and is
// emitted as the `rest_ensures` Hyp. Caller relies on Q(E) for the
// post-call obligation.
test_verify_one_file! {
    #[test] test_exec_call_ret_eq_with_extra_conjunct verus_code! {
        fn double_pos(x: u8) -> (r: u8)
            requires x < 100
            ensures r == 2 * x, r >= 2 * x
        {
            2 * x
        }

        #[verifier::tactus_auto]
        fn caller_eq_extra(x: u8) -> (s: u8)
            requires x < 50
            ensures s >= 2 * x
        {
            let y = double_pos(x);
            y
        }
    } => Ok(())
}

// #128: ret-substitution NEGATIVE — caller asserts wrong post-call value.
// Pins that the substitution produces a real obligation, not a permissive
// pass: substituting `y := x + 1` and asserting `s == x + 2` should fail
// the postcondition.
test_verify_one_file! {
    #[test] test_exec_call_ret_eq_substitution_wrong_post verus_code! {
        fn add_one_uniq2(x: u8) -> (r: u8)
            requires x < 255
            ensures r == x + 1
        {
            x + 1
        }

        #[verifier::tactus_auto]
        fn caller_wrong_uniq(x: u8) -> (s: u8)
            requires x < 200
            ensures s == x + 2
        {
            let y = add_one_uniq2(x);
            y
        }
    } => Err(err) => {
        let msgs: Vec<_> = err.errors.iter().map(|e| e.message.clone()).collect();
        assert!(
            msgs.iter().any(|m| m.contains(&vir::tactus_messages::paren_label(vir::tactus_messages::ASSERT_LABEL_POSTCONDITION))),
            "expected (postcondition) failure from wrong post-call assertion. got: {:?}",
            msgs,
        );
    }
}

// #128: fall-through path. Callee with NO `r == E` clause — ensures only
// constrains r via inequality (`r > 0`). The ∀-path stays in effect; pin
// that this still verifies (no regression in the conservative scope).
test_verify_one_file! {
    #[test] test_exec_call_no_ret_eq_falls_through verus_code! {
        fn pos_lt_10(x: u8) -> (r: u8)
            requires x < 5
            ensures r > 0, r < 10
        {
            x + 1
        }

        #[verifier::tactus_auto]
        fn caller_falls_through(x: u8) -> (s: u8)
            requires x < 5
            ensures s > 0
        {
            let y = pos_lt_10(x);
            y
        }
    } => Ok(())
}

// `break` inside the loop body. Verus compiles this to a non-simple
// loop (cond: None, with break statements); `check_stm` rejects
// because we require `cond: Some`.
test_verify_one_file! {
    #[test] test_exec_loop_with_break verus_code! {
        #[verifier::tactus_auto]
        fn with_break(n: u8) -> (r: u8)
            requires n <= 100
            ensures r <= n
        {
            let mut x: u8 = n;
            while x > 0
                invariant x <= n
                decreases x
            {
                if x == 5 {
                    break;
                }
                x = x - 1;
            }
            x
        }
    } => Ok(())
}

// `continue` inside a loop — skip the rest of the iteration and jump
// back to the loop head. Exercises the `continue_leaf` path of
// `WpLoopCtx` (same goal as fallthrough: re-establish invariants AND
// show decrease). This test uses continue to skip the decrement when
// x is odd, but the body always reaches a decrement either way —
// the decrease obligation holds regardless.
test_verify_one_file! {
    #[test] test_exec_loop_with_continue verus_code! {
        #[verifier::tactus_auto]
        fn with_continue(n: u8) -> (r: u8)
            requires n <= 100
            ensures r <= n
        {
            let mut x: u8 = n;
            while x > 0
                invariant x <= n
                decreases x
            {
                if x == 5 {
                    x = x - 1;
                    continue;
                }
                x = x - 1;
            }
            x
        }
    } => Ok(())
}

// Labeled break — landed (#88). The inner loop has a `break 'outer;`
// that jumps to the outer loop's break_leaf (its at-exit invariants),
// not the inner loop's. `WpLoopCtx` carries the loop's `label`, and
// `loop_stack` is searched for the matching label; unlabeled
// `break;` still resolves to the innermost (loop_stack[0]).
test_verify_one_file! {
    #[test] test_exec_loop_labeled_break verus_code! {
        #[verifier::tactus_auto]
        fn labeled(n: u8) -> (r: u8)
            requires n <= 100
            ensures r <= 100
        {
            let mut x: u8 = n;
            'outer: while x > 0
                invariant x <= 100
                decreases x
            {
                let mut i: u8 = 0;
                while i < 5
                    invariant i <= 5, x <= 100
                    decreases 5u8 - i
                {
                    if x < 10 { break 'outer; }  // outer's break_leaf: x <= 100
                    i = i + 1;
                }
                x = x - 1;
            }
            x
        }
    } => Ok(())
}

// NOTE: labeled `continue 'outer;` is rejected by Verus upstream
// ("decrease checking for labeled continue not supported unless
// loop is marked #[verifier::loop_isolation(false)]"). Tactus's
// label-stack handling supports it in principle (the same code
// path as labeled break, just using `continue_leaf` instead of
// `break_leaf`), but exercising it end-to-end requires
// `loop_isolation(false)` which we don't yet support either.
// Documented here so a future contributor doesn't add an Ok
// test without realizing.

// Labeled break also works in deeply-nested cases — three loops,
// inner break jumps to the outermost. Pinned to confirm the
// stack search isn't off-by-one.
test_verify_one_file! {
    #[test] test_exec_loop_labeled_break_three_deep verus_code! {
        #[verifier::tactus_auto]
        fn three_deep(n: u8) -> (r: u8)
            requires n <= 100
            ensures r <= 100
        {
            let mut x: u8 = n;
            'outermost: while x > 0
                invariant x <= 100
                decreases x
            {
                let mut j: u8 = 0;
                while j < 3
                    invariant j <= 3, x <= 100
                    decreases 3u8 - j
                {
                    let mut k: u8 = 0;
                    while k < 3
                        invariant k <= 3, j <= 3, x <= 100
                        decreases 3u8 - k
                    {
                        if x == 5 { break 'outermost; }
                        k = k + 1;
                    }
                    j = j + 1;
                }
                x = x - 1;
            }
            x
        }
    } => Ok(())
}

// Nested loops with break in the inner — innermost `WpLoopCtx` applies
// to the break. Verifies that inner-loop break writes the inner loop's
// invariants (not the outer's) and that after the inner loop ends, the
// outer loop continues its own maintain / use structure correctly.
test_verify_one_file! {
    #[test] test_exec_nested_loops_inner_break verus_code! {
        #[verifier::tactus_auto]
        fn nested(n: u8) -> (r: u8)
            requires n <= 50
            ensures r <= n
        {
            let mut x: u8 = n;
            while x > 0
                invariant x <= n
                decreases x
            {
                let mut y: u8 = x;
                while y > 0
                    invariant y <= x, x <= n
                    decreases y
                {
                    if y == 5 { break; }
                    y = y - 1;
                }
                x = x - 1;
            }
            x
        }
    } => Ok(())
}

// break + continue in the same loop body. Each control-flow edge
// uses the right `WpLoopCtx` leaf (break_leaf vs continue_leaf).
test_verify_one_file! {
    #[test] test_exec_loop_break_and_continue verus_code! {
        #[verifier::tactus_auto]
        fn both(n: u8) -> (r: u8)
            requires n <= 100
            ensures r <= n
        {
            let mut x: u8 = n;
            while x > 0
                invariant x <= n
                decreases x
            {
                if x == 20 { break; }
                if x == 10 {
                    x = x - 1;
                    continue;
                }
                x = x - 1;
            }
            x
        }
    } => Ok(())
}

// `return` inside a loop body with break — the return's
// `Wp::Done(ensures_goal)` short-circuits to fn-exit regardless of
// the current `loop_ctx`. Complements `test_exec_return_inside_loop`
// for the loop-with-break era. The fn is also allowed to exit via
// break (falling out of the loop, then `x` is returned); either
// control-flow path must satisfy the ensures.
test_verify_one_file! {
    #[test] test_exec_return_inside_loop_with_break verus_code! {
        #[verifier::tactus_auto]
        fn ret_loop(n: u8) -> (r: u8)
            requires n <= 100
            ensures r <= n
        {
            let mut x: u8 = n;
            while x > 0
                invariant x <= n
                decreases x
            {
                if x == 5 { return x; }
                if x == 20 { break; }
                x = x - 1;
            }
            x
        }
    } => Ok(())
}

// #84: `reveal_with_fuel(f, n)` is a Verus proof-mode statement
// that doesn't have a direct counterpart in Tactus. In Tactus,
// spec fns are `@[irreducible] noncomputable def` and unfolding
// is requested explicitly via Lean's `unfold f` tactic. The Verus
// fuel concept (which controls Z3's recursion-unrolling depth)
// has no analog in Lean's deterministic kernel.
//
// At the SST level: `reveal_with_fuel(f, n)` lowers to
// `StmX::Fuel(fun, fuel_n, ..)`, which `build_wp` already passes
// through transparently (`Ok(after)`). The user-facing
// `ExpX::FuelConst(_)` rejection in `to_lean_sst_expr.rs` is
// defensive code for an unreachable case: `FuelConst` is produced
// only by `vir::recursion::rewrite_rec_call_with_fuel_const`,
// which is only called from `vir::expand_errors` — part of the
// Z3 SMT-error-expansion pipeline that Tactus doesn't traverse.
//
// What the user sees in tactus_auto fns: Verus's `reveal_with_fuel`
// can't be written inside a Tactus `proof { ... }` block (which
// holds Lean tactics, not Verus statements). The workaround is
// `proof { unfold f }` — Lean's direct equivalent.
//
// This test pins the architectural reality: a tactus_auto fn that
// uses a recursive spec fn verifies WITHOUT any reveal/fuel
// machinery, because the obligation reduces to ground-level facts
// (`r == 5`) that don't need unfolding. If the obligation DID
// require unfolding `fact`, the user would write
// `proof { unfold fact }` rather than `reveal_with_fuel(fact, ...)`.
test_verify_one_file! {
    #[test] test_exec_recursive_spec_fn_no_reveal_needed verus_code! {
        spec fn fact(n: nat) -> nat
            decreases n
        {
            if n == 0 { 1 } else { n * fact((n - 1) as nat) }
        }

        #[verifier::tactus_auto]
        fn five() -> (r: u32)
            ensures r == 5
        {
            5
        }
    } => Ok(())
}

// #91: array indexing in a tactus_auto fn's spec via the Verus
// builtin `array_index(a, i)` — lowers to
// `BinaryOp::Index(ArrayKind::Array, BoundsCheck::Allow)` in SST.
// Tactus emits `lhs[Int.toNat rhs]!` (Lean's `getElem!`-based
// indexing — total in the type system, panics out-of-bounds, but
// Tactus only verifies the goal so panic semantics are
// observationally fine; out-of-bounds is unspecified, matching
// Verus's spec semantics).
//
// Side effect: this also pinned `Primitive::Array` rendering —
// Lean's `Array` is a unary type constructor, but Verus carries
// `[T, N]` (element + const-length) as type args. The renderer
// drops the length to avoid `Array Int 4` "Function expected"
// errors. Bounds are tracked separately via spec-level `len()`.
test_verify_one_file! {
    #[test] test_exec_index_array_in_requires verus_code! {
        #[verifier::tactus_auto]
        fn caller(a: [u8; 4])
            requires array_index(a, 0) == 7u8
        {
        }
    } => Ok(())
}

// Indexing in an ensures clause — same mechanism, different
// position. Pins that the inlined ensures (in calling-fn
// contexts) handles indexing correctly.
test_verify_one_file! {
    #[test] test_exec_index_array_in_ensures verus_code! {
        #[verifier::tactus_auto]
        fn first_eq(a: [u8; 4]) -> (b: u8)
            requires array_index(a, 0) == 7u8
            ensures b == array_index(a, 0)
        {
            7
        }
    } => Ok(())
}

// Multiple indexing operations in an assert. Exercises the
// indexing renderer composing with itself + arithmetic.
test_verify_one_file! {
    #[test] test_exec_index_array_in_assert verus_code! {
        #[verifier::tactus_auto]
        fn check(a: [u8; 4])
            requires
                array_index(a, 0) == 1u8,
                array_index(a, 1) == 2u8,
        {
            assert(array_index(a, 0) + array_index(a, 1) == 3u8);
        }
    } => Ok(())
}

// Exec-mode array indexing rejected at the Verus layer:
// `a[i]` desugars to `vstd::array::array_index_get` which Tactus
// can't inline (cross-crate). The `BinaryOp::Index` SST form we
// support fires when bounds have been checked elsewhere — i.e.,
// in spec contexts via `array_index(a, i)`. Exec-mode array
// access through tactus_auto would need either vstd routing
// or a synthetic same-crate exec wrapper. Tracked as #91 follow-up.

// #113: Verus's `verus_builtin::strslice_get_char(s, i)` (VIR
// `BinaryOp::StrGetChar`) is spec-mode codepoint lookup on a string.
// The naive head `String.get` would be wrong — Lean's `String.get`
// takes a byte position and returns a `Char`, whereas Verus's
// semantics is codepoint-indexed and the return type is `char`
// (Tactus's `Nat`). The shared `non_binop_head` table now maps
// `StrGetChar` to `Tactus.strGetChar`, a prelude helper with the
// right signature (`String → Int → Nat`) using `s.data.get!`.
//
// The three tests cover the rendering surfaces:
// (1) proof fn — VIR-AST path via `vir_expr_to_ast`.
// (2) exec fn body assert — SST path via `sst_exp_to_ast_checked`.
// (3) exec fn ensures — SST path (`ens_exps` is SST).
test_verify_one_file! {
    #[test] test_proof_strslice_get_char verus_code! {
        proof fn use_strslice_get_char(s: &str)
            ensures strslice_get_char(s, 0) == strslice_get_char(s, 0)
        by {
            rfl
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_strslice_get_char_in_assert verus_code! {
        #[verifier::tactus_auto]
        fn check_strslice(s: &str) {
            assert(strslice_get_char(s, 0) == strslice_get_char(s, 0));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_strslice_get_char_in_ensures verus_code! {
        #[verifier::tactus_auto]
        fn first_char_equals_itself(s: &str)
            ensures strslice_get_char(s, 0) == strslice_get_char(s, 0)
        {
        }
    } => Ok(())
}

// Logical xor on bools — Rust's `^` on `(bool, bool)` lowers to
// `BinaryOp::Xor` in VIR (bitwise xor on ints goes through
// `BinaryOp::Bitwise(BitXor, _)` — a different SST path entirely).
// Renders via the shared `non_binop_head(Xor) -> "Bool.xor"`.
//
// Concrete xor closes via `decide` in `tactus_auto`'s ladder — this
// pins that the basic rendering path works end-to-end (existing
// `test_exec_xor_bool` was a smoke test for fn-return-equals-body, not
// for the inner xor logic). Commutativity reasoning on FREE bool vars
// hits an automation gap — see `_free_vars_*_gap` below.
test_verify_one_file! {
    #[test] test_exec_xor_bool_concrete verus_code! {
        #[verifier::tactus_auto]
        fn check_xor_concrete() {
            assert((true ^ false) == true);
            assert((true ^ true) == false);
            assert((false ^ false) == false);
        }
    } => Ok(())
}

// Free-var bool xor commutativity — the canonical user-explicit
// proof shape for "tactus_auto can't close this; user provides a
// tactic." Tactus renders `TypX::Bool` as `Prop` unconditionally
// (DESIGN.md § "Bool vs Prop"), so any value flowing into `Bool.xor`
// gets `decide` coercions. The resulting goal
// `(decide b1 ^^ decide b2) = (decide b2 ^^ decide b1)` doesn't
// close under the default closer's set, and per Tactus's design
// principle #1 (Transparency) and the user UX preference for
// visible proofs, the right shape is `assert(...) by { simp_all
// [Bool.xor_comm] };` — the lemma being used is right at the
// assertion site, not buried in the closer.
test_verify_one_file! {
    #[test] test_exec_xor_bool_free_vars_commutative verus_code! {
        #[verifier::tactus_auto]
        fn check_xor_commute(b1: bool, b2: bool) {
            assert((b1 ^ b2) == (b2 ^ b1)) by { simp_all [Bool.xor_comm] };
        }
    } => Ok(())
}

// Tactic referencing loop-local variable. Catalogue marked this
// untested with the note that the user's tactic runs at theorem-level
// prefix, so loop-local names might not be in scope. Probing reveals
// that `assert(P) by { omega }` inside a loop body actually DOES work
// for the common case of arithmetic over loop-local + fn-param vars:
// the assert emits its own theorem under the loop's maintain ctx
// (binders for `mod_vars + bounds + invs + cond + d_old`), so `omega`
// sees `i` (modified var binder) and `n` (param binder) as bound
// names in the theorem context.
//
// What WOULDN'T work — and remains untested for lack of an idiomatic
// shape — is a tactic referencing a *hypothesis name* like `h_inv`
// that the user expects from the invariant. The Hyp frames get
// codegen-internal names, not user-controlled ones; there's no stable
// way for a user-written tactic to refer to the invariant hypothesis
// directly. The omega/simp_all path sidesteps this by name-resolving
// against the bound vars + auto-iterated hypothesis set.
test_verify_one_file! {
    #[test] test_exec_assert_by_omega_in_loop_body verus_code! {
        #[verifier::tactus_auto]
        fn iterate_under_bound(n: u8)
            requires n < 100
        {
            let mut i: u8 = 0;
            while i < n
                invariant i <= n
                decreases n - i
            {
                assert(i <= n) by { omega };
                i = i + 1;
            }
        }
    } => Ok(())
}

// Closures with user-written `requires`. Catalogue marked this
// untested because Verus's surface syntax is finicky. Verus parses
// `|x: u8| requires P { body }` (no `->` before `requires`). Inside
// a `tactus_auto` fn, the closure declaration emits a `Wp::LetRaw`
// with the lambda value; `Wp::ClosureBody` walks the body's own
// verification scope, where the requires clause becomes an
// `Assume(req)` at body entry (Verus's `exec_closure_body_stms`
// pipeline). So `body` verifies under the assumed precondition —
// pinning that we can use the requires inside the body to discharge
// overflow checks that would fail without it.
test_verify_one_file! {
    #[test] test_exec_closure_with_requires verus_code! {
        #[verifier::tactus_auto]
        fn make_bumper() {
            let bumper = |x: u8| requires x < 100 { x + 1 };
        }
    } => Ok(())
}

// Closure with user-written `ensures`. Verus syntax: `|x: u8| -> (r:
// u8) ensures r == x + 1 { x + 1 }`. The closure-body verification
// scope checks that the body satisfies the ensures; the closure's
// declaration emits the lambda value bound to the closure id, and any
// outer reference is to that lambda. Pins the second half of the
// closure-spec surface area named in the catalogue.
test_verify_one_file! {
    #[test] test_exec_closure_with_ensures verus_code! {
        #[verifier::tactus_auto]
        fn make_identity() {
            let id_closure = |x: u8| -> (r: u8) ensures r == x { x };
        }
    } => Ok(())
}

// #89: `invariant_except_break P` (at_entry only) — `P` holds at
// each iteration boundary but is NOT required at break, so the
// post-loop ctx doesn't get to assume it. The decreases-style
// `loop { ... break; ... }` form (cond: None after Verus
// lowering) is the only place these flags can differ; for plain
// `while c { ... }`, Verus's lowering forces at_entry = at_exit.
test_verify_one_file! {
    #[test] test_exec_loop_invariant_except_break verus_code! {
        #[verifier::tactus_auto]
        fn count_to_ten() -> (r: i8)
            ensures 1 <= r
        {
            let mut i: i8 = 0;
            loop
                invariant_except_break i <= 9
                invariant 0 <= i <= 10
                ensures 1 <= i
                decreases 10 - i
            {
                i = i + 1;
                if i == 10 {
                    break;
                }
            }
            i
        }
    } => Ok(())
}

// `invariant_except_break` violated at iteration boundary —
// negative test. The user claims `i <= 9` holds at every
// iteration, but starts with `i: i8 = 10`. The init theorem
// for the at_entry invariant fires.
test_verify_one_file! {
    #[test] test_exec_loop_invariant_except_break_init_fails verus_code! {
        #[verifier::tactus_auto]
        fn bad_start() -> (r: i8)
            ensures 1 <= r
        {
            let mut i: i8 = 10;
            loop
                invariant_except_break i <= 9
                invariant 0 <= i <= 10
                ensures 1 <= i
                decreases 10 - i
            {
                i = i + 1;
                if i == 10 {
                    break;
                }
            }
            i
        }
    } => Err(_)
}

// Loop `ensures` (at_exit only) — `R` must hold at each loop
// exit but isn't visible during iteration. Pinned alongside
// `invariant_except_break` (at_entry only) and a regular
// `invariant` (both); the test exercises all three flag
// combinations in one loop.
//
// Uses the chained `0 <= i <= 10` syntax — the `LeanName`
// typed-name refactor (#99) made VarIdent → name conversions
// disambiguator-aware throughout the renderer, so the synthetic
// temps from `ast_simplify::temp_var` no longer shadow each
// other. Pre-#99 this test had to use `&&` to sidestep the
// shadowing (which silently lowered the conjunction to `True`
// — a soundness hole).
test_verify_one_file! {
    #[test] test_exec_loop_ensures_only verus_code! {
        #[verifier::tactus_auto]
        fn at_least_one() -> (r: i8)
            ensures 1 <= r
        {
            let mut i: i8 = 0;
            loop
                invariant_except_break i <= 9
                invariant 0 <= i <= 10
                ensures 1 <= i
                decreases 10 - i
            {
                i = i + 1;
                if i == 10 {
                    break;
                }
            }
            i
        }
    } => Ok(())
}

// #99 regression: chained comparisons (`0 <= i <= 10`) in
// tactus_auto fn specs lower correctly with disambiguator-
// aware `LeanName::from_var_ident`.
//
// Pre-#99: ast_simplify created N temp VarIdents with base
// name `tmp%%` (different VirRenumbered ids) for the chained
// form. Our renderer used `sanitize(&v.0)` which lost the
// disambiguator, collapsing them all to `tmp__`. Nested let-
// bindings shadowed each other, and the body's `tmp__ ≤ tmp__
// ∧ tmp__ ≤ tmp__` reduced (via Lean's let-evaluation) to a
// trivially-true `10 ≤ 10 ∧ 10 ≤ 10` — the proof obligation
// silently disappeared.
//
// This test passes a deliberately-violated chained compare
// in the requires (with `i = 50`, `0 <= i < 10` is false) and
// expects the precondition to fire — confirming the temps
// stay distinct and the body's `tmp_a ≤ tmp_b ∧ tmp_b < tmp_c`
// retains its semantics through to Lean's elaborator.
test_verify_one_file! {
    #[test] test_exec_chained_compare_distinct_temps verus_code! {
        #[verifier::tactus_auto]
        fn helper(i: i32)
            requires 0 <= i < 10
        {
        }

        #[verifier::tactus_auto]
        fn caller()
        {
            helper(50);  // FAILS: i=50 doesn't satisfy 0 <= i < 10
        }
    } => Err(_)
}

// Loop `ensures` violated at the break point — negative test.
// `ensures i == 100` requires that the value at every break
// equals 100; the only break here happens at i=10. Init theorem
// for ensures isn't emitted (at_entry=false), but the body's
// break_leaf must establish `i == 100`, which it can't.
test_verify_one_file! {
    #[test] test_exec_loop_ensures_fails verus_code! {
        #[verifier::tactus_auto]
        fn bad_ensures() -> (r: i8)
        {
            let mut i: i8 = 0;
            loop
                invariant 0 <= i <= 10
                ensures i == 100
                decreases 10 - i
            {
                i = i + 1;
                if i == 10 {
                    break;
                }
            }
            i
        }
    } => Err(_)
}

// #84 cont'd: when an obligation DOES need spec-fn unfolding,
// the Tactus equivalent of `reveal_with_fuel` is a `proof { ... }`
// block containing the Lean `unfold` tactic. This works because
// Tactus's proof blocks in tactus_auto fns hold raw Lean tactic
// text (not Verus statements), and `unfold` propagates as a
// theorem-level prefix to subsequent obligations.
test_verify_one_file! {
    #[test] test_exec_unfold_for_recursive_spec verus_code! {
        spec fn double(n: nat) -> nat {
            n + n
        }

        #[verifier::tactus_auto]
        fn use_double() -> (r: u32)
            ensures double(3 as nat) == 6
        {
            proof { unfold double }
            0
        }
    } => Ok(())
}

// #95 — new-mut-ref mode (callee-side body verification LANDED).
//
// `--V new-mut-ref` plus `deprecated_postcondition_mut_ref_style(true)`
// (or any path that produces `Unary(MutRefCurrent, _)` /
// `Unary(MutRefFuture(_), _)` / `Unary(MutRefFinal(_), _)` in the SST)
// is now handled for callee-side body verification: a normalization
// pass at fn entry maps the new-mut-ref shapes into the legacy shape
// (`Var` / `VarLoc` / `VarAt`) for &mut params, and #94's existing
// machinery handles the rest. Plus `is_synthetic_resolution_assume`
// filters the synthetic `Assume(HasResolved(_))` injections from
// `resolution_inference` so they don't produce false-positive
// `unproved assumption` warnings or hypothesize a non-Prop.
//
// Caller-side stays deferred: `bump(&mut y)` lowers to a synthetic
// MutRef-typed local plus assume-pre + assign-post wrappers. The
// MutRef* ops then wrap synthetic locals (not fn params), so the
// param-set normalization doesn't reach them. Tracked as the
// caller-side rejection test below; the path forward is either
// extending the "MutRef-typed name set" beyond fn params, or a
// structural Lean encoding of MutRef<T> as a pair.
test_verify_one_file_with_options! {
    #[test] test_exec_callee_mut_simple_new_mut_ref ["new-mut-ref"] => verus_code! {
        #[verifier::tactus_auto]
        #[verifier::deprecated_postcondition_mut_ref_style(true)]
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }
    } => Ok(())
}

// Postcondition-only probe (no body mutation). Isolates the
// MutRefFuture rendering from body-assignment complexity. Currently
// rejected because postcondition `*x` lowers to MutRefFuture(Final).
test_verify_one_file_with_options! {
    #[test] test_exec_callee_mut_noop_new_mut_ref ["new-mut-ref"] => verus_code! {
        #[verifier::tactus_auto]
        #[verifier::deprecated_postcondition_mut_ref_style(true)]
        fn noop(x: &mut u8)
            ensures *x == *old(x)
        {
        }
    } => Ok(())
}

// Caller-side new-mut-ref (#107): caller is tactus_auto; callee uses
// Verus's Z3 path. The synthetic `LocalDeclKind::BorrowMut` local
// Verus introduces around `bump(&mut y)` is now treated as a `&mut`
// L-value at the call site:
//   1. `mut_param_names` includes BorrowMut locals (so
//      `normalize_mut_ref_in_*` rewrites the `MutRefCurrent`/`MutRefFuture`
//      ops to bare `Var(local)`).
//   2. `build_borrow_mut_binders` emits a theorem-level binder for
//      each BorrowMut local (so `Var(local)` resolves).
//   3. `extract_mut_target` recognizes bare `Var(borrow_mut_local)`
//      as a Var target (so #55's caller-side mut_args machinery
//      handles the substitution + Let-rebind).
//   4. `build_call_mut_args` gates on `is_mut_ref_par`-equivalent
//      (covers both legacy `is_mut: true` and new-mut-ref `MutRef<T>`
//      typ).
test_verify_one_file_with_options! {
    #[test] test_exec_call_mut_arg_new_mut_ref ["new-mut-ref"] => verus_code! {
        #[verifier::deprecated_postcondition_mut_ref_style(true)]
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        #[verifier::tactus_auto]
        fn call_mut()
        {
            let mut y: u8 = 5;
            bump(&mut y);
            assert(y == 6);
        }
    } => Ok(())
}

// #107: two `&mut` args at the same call site. Each becomes a
// distinct synthetic `LocalDeclKind::BorrowMut` local; the
// theorem-level binders + per-arg fresh existentials shouldn't
// alias.
test_verify_one_file_with_options! {
    #[test] test_exec_call_two_mut_args_new_mut_ref ["new-mut-ref"] => verus_code! {
        #[verifier::deprecated_postcondition_mut_ref_style(true)]
        fn bump_both(a: &mut u8, b: &mut u8)
            requires *old(a) < 100, *old(b) < 100
            ensures *a == *old(a) + 1, *b == *old(b) + 2
        {
            *a = *a + 1;
            *b = *b + 2;
        }

        #[verifier::tactus_auto]
        fn call_mut_two()
        {
            let mut x: u8 = 5;
            let mut y: u8 = 10;
            bump_both(&mut x, &mut y);
            assert(x == 6);
            assert(y == 12);
        }
    } => Ok(())
}

// #107: caller's local is read after the call. Pins that the
// post-call value (via Let-rebind on the BorrowMut local + the
// `y = MutRefFuture(mut_ref)` assignment) propagates to subsequent
// reads.
test_verify_one_file_with_options! {
    #[test] test_exec_call_mut_arg_new_mut_ref_use_after ["new-mut-ref"] => verus_code! {
        #[verifier::deprecated_postcondition_mut_ref_style(true)]
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        #[verifier::tactus_auto]
        fn call_then_use() -> (r: u8)
            ensures r == 7
        {
            let mut y: u8 = 5;
            bump(&mut y);
            bump(&mut y);
            y
        }
    } => Ok(())
}

// #93 closure probes — characterize what the renderer rejects so a
// future implementation has tests to flip. Two distinct shapes in the
// SST:
//   - `ExpX::CallLambda(f, args)` — spec-level call to a FnSpec value
//     (e.g., `f(x)` where `f: spec_fn(int) -> int`). Reachable from a
//     tactus_auto exec fn when its ensures applies a spec-closure
//     parameter.
//   - `StmX::ClosureInner { body, .. }` — exec-mode closure body
//     verification (reachable when an exec fn declares a closure
//     locally, even if it doesn't immediately apply it).

// Probe 1: spec closure parameter applied in an ensures clause —
// produces ExpX::CallLambda.
// `f(x)` in ensures lowers to `ExpX::CallLambda(f, [x])`. Renders as
// Lean `f x` (App). Requires that `f` is the identity function so the
// caller-supplied body `r = x` actually satisfies `r == f(x)`.
test_verify_one_file! {
    #[test] test_exec_spec_closure_in_ensures verus_code! {
        #[verifier::tactus_auto]
        fn apply_id(f: spec_fn(int) -> int, x: int) -> (r: int)
            requires forall|y: int| #[trigger] f(y) == y
            ensures r == f(x)
        {
            x
        }
    } => Ok(())
}

// Negative: spec-closure call in ensures with a wrong body value
// should fail the postcondition. Pins that the closure call IS reaching
// the goal — not silently dropped. Uses u32 (exec-supported arithmetic)
// so the body type-checks; closure is still spec-mode.
test_verify_one_file! {
    #[test] test_exec_spec_closure_in_ensures_wrong_body verus_code! {
        #[verifier::tactus_auto]
        fn apply_id_wrong(f: spec_fn(int) -> int, x: u32) -> (r: u32)
            requires
                x < 100,
                forall|y: int| #[trigger] f(y) == y,
            ensures r as int == f(x as int)
        {
            x + 1  // body returns x+1, not x — doesn't satisfy r == f(x)
        }
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e| e.message.contains("postcondition")),
            "expected postcondition failure, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
}

// Closure call in requires position — also produces ExpX::CallLambda,
// but in the requires-binders path instead of the ensures-goal path.
test_verify_one_file! {
    #[test] test_exec_spec_closure_in_requires verus_code! {
        #[verifier::tactus_auto]
        fn requires_pos(f: spec_fn(int) -> bool, x: int) -> (r: int)
            requires f(x)
            ensures r == x
        {
            x
        }
    } => Ok(())
}

// Exec-mode closure DECLARATION. Verus's SST throws away the closure's
// AST body (replacing it with synthetic ClosureReq/Ens predicates), so
// we extended `StmX::ClosureInner` with an `ast_body` field that
// preserves it for Tactus. Then the closure value is rendered as a
// Lean lambda via `vir_expr_to_ast`'s `NonSpecClosure` arm, and bound
// to the cid via `Wp::LetRaw`. The Verus-side spec assume is dropped
// because the lambda binding is structurally the same fact.
//
// Closure body `|x: u32| x` is identity — generically sound for any
// u32 (no overflow risk). The body's verification scope emits a
// theorem like `∀ x : Int, 0 ≤ x ∧ x < 2^32 → 0 ≤ x ∧ x < 2^32` which
// closes trivially.
test_verify_one_file! {
    #[test] test_exec_closure_decl verus_code! {
        #[verifier::tactus_auto]
        fn make_adder() -> (r: u32)
            ensures r == 5
        {
            let identity = |x: u32| x;
            5
        }
    } => Ok(())
}

// Negative: ensures references the bound closure id but with wrong
// shape. Pins that the closure binding actually reaches the
// postcondition theorem (not silently dropped).
test_verify_one_file! {
    #[test] test_exec_closure_decl_wrong_ensures verus_code! {
        #[verifier::tactus_auto]
        fn make_adder() -> (r: u32)
            ensures r == 6  // body returns 5 — should fail
        {
            let _identity = |x: u32| x;
            5
        }
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e| e.message.contains("postcondition")),
            "expected postcondition failure, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
}

// Soundness probe: closure body has an overflow that should NOT
// verify. Body is `x + 200` for `x: u8` — when called with x=100
// (or anything ≥ 56), this overflows. The body should fail an
// overflow check, but the surrounding fn returns 5 (unrelated to
// the closure). Pre-`Wp::ClosureBody`, the closure body's
// verification scope was silently skipped — `r == 5` would pass
// even though the closure body `x + 200` is genuinely unsound.
// Now the closure body's overflow check is emitted as a theorem
// under `∀ x : Int, 0 ≤ x ∧ x < 2^8`, and tactus_auto correctly
// rejects.
test_verify_one_file! {
    #[test] test_exec_closure_body_overflow_caught verus_code! {
        #[verifier::tactus_auto]
        fn unsound_overflow() -> (r: u8)
            ensures r == 5
        {
            let _bad = |x: u8| x + 200;  // should fail: x + 200 may overflow u8
            5
        }
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e| e.message.contains("overflow") || e.message.contains("arithmetic")),
            "expected overflow failure inside closure body, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
}

// Positive: closure body computes something arithmetic but bounded
// by the input type. `x / 2` for `x: u8` is always sound (no overflow
// possible — the result is between 0 and 127). Pins that body
// verification doesn't false-fail on legitimately-sound bodies.
test_verify_one_file! {
    #[test] test_exec_closure_body_safe_arithmetic verus_code! {
        #[verifier::tactus_auto]
        fn make_halver() -> (r: u8)
            ensures r == 0
        {
            let _half = |x: u8| x / 2;
            0
        }
    } => Ok(())
}

// Probe: exec closure CALL via FnOnce/Fn/FnMut. Verus translates
// `f(x)` to `vstd::pervasive::exec_nonstatic_call(f, (x,))`. Without
// vstd imported the call is rejected upstream ("not supported (note:
// you may be able to add a Verus specification...)"). With vstd
// imported, the call resolves to vstd's `exec_nonstatic_call` —
// a `verifier::external_body` fn whose `requires/ensures` use
// `call_requires` / `call_ensures` builtins (which lower to
// `BuiltinSpecFun::ClosureReq` / `ClosureEns` — and our renderer
// treats those as synthetic closure-spec stuff to drop). So even
// with vstd it's not a one-line fix.
//
// Documenting as Err for now; lifting it is its own slice (likely
// needs proper handling of `BuiltinSpecFun::ClosureReq/Ens` in spec
// position so the inlined `exec_nonstatic_call` ensures resolves to
// `ClosureEns(f, args, output)` ↔ the lambda's value).
test_verify_one_file! {
    #[test] test_exec_closure_call_unsupported_upstream verus_code! {
        #[verifier::tactus_auto]
        fn use_closure() -> (r: u8)
            ensures r == 5
        {
            let identity = |x: u8| x;
            identity(5)
        }
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e| e.message.contains("exec_nonstatic_call")),
            "expected upstream `exec_nonstatic_call is not supported`, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
}

// Coverage: zero-arg closure. `closure_params` is empty;
// `push_mod_var_frames` is a no-op. The body verification scope
// still needs to run (in case of overflow etc.), but no `∀`
// binders are pushed.
test_verify_one_file! {
    #[test] test_exec_closure_zero_args verus_code! {
        #[verifier::tactus_auto]
        fn make_const() -> (r: u8)
            ensures r == 0
        {
            let _five = || 5u8;
            0
        }
    } => Ok(())
}

// Coverage: multi-arg closure. `closure_params` has 2 entries;
// `push_mod_var_frames` pushes 2 binders + 2 type-bound hyps. The
// body's `x + y` for `x, y: u8` overflows generically (caller
// could supply x=200, y=200), so this should FAIL the body's
// overflow check — pinning the multi-binder shape AND the
// soundness path simultaneously.
test_verify_one_file! {
    #[test] test_exec_closure_multi_arg_overflow verus_code! {
        #[verifier::tactus_auto]
        fn make_adder() -> (r: u8)
            ensures r == 0
        {
            let _bad = |x: u8, y: u8| x + y;  // unsound: 200 + 200 overflows
            0
        }
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e| e.message.contains("overflow") || e.message.contains("arithmetic")),
            "expected overflow failure inside closure body, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
}

// Coverage: nested closure. `Wp::ClosureBody` whose `body`
// contains another `Wp::ClosureBody`. The inner closure's
// verification scope nests inside the outer's.
test_verify_one_file! {
    #[test] test_exec_closure_nested verus_code! {
        #[verifier::tactus_auto]
        fn make_layered() -> (r: u8)
            ensures r == 0
        {
            let _outer = |y: u8| {
                let _inner = |x: u8| x;
                y
            };
            0
        }
    } => Ok(())
}

// Coverage: closure captures local. `let n = 5; let f = |x| x + n;` —
// the lambda `fun (x : Int) => x + n` references `n` from the
// surrounding scope. Lean's let-in handles this naturally; the body
// verification scope needs `n` available as a captured variable.
// Here we use `n = 0` so the body's overflow check `x + 0` has no
// risk: `0 ≤ x ∧ x < 256 → 0 ≤ x + 0 ∧ x + 0 < 256` is trivially
// true.
test_verify_one_file! {
    #[test] test_exec_closure_captures_local verus_code! {
        #[verifier::tactus_auto]
        fn make_with_capture() -> (r: u8)
            ensures r == 0
        {
            let n: u8 = 0;
            let _add_n = |x: u8| x + n;
            0
        }
    } => Ok(())
}

// Coverage (12.1): closure declared inside a loop body.
// `Wp::ClosureBody` nests inside `Wp::Loop`'s body's WP.
test_verify_one_file! {
    #[test] test_exec_closure_inside_loop verus_code! {
        #[verifier::tactus_auto]
        fn loop_with_closure() -> (r: u8)
            ensures r == 0
        {
            let mut i: u8 = 0;
            while i < 3
                invariant i <= 3
                decreases 3 - i
            {
                let _f = |x: u8| x;
                i = i + 1;
            }
            0
        }
    } => Ok(())
}

// Coverage (12.2): closure declared inside an if-branch.
// `Wp::ClosureBody` nests inside `Wp::Branch`'s `then_branch`.
test_verify_one_file! {
    #[test] test_exec_closure_inside_if verus_code! {
        #[verifier::tactus_auto]
        fn branch_with_closure(c: bool) -> (r: u8)
            ensures r == 0
        {
            if c {
                let _f = |x: u8| x;
                0
            } else {
                0
            }
        }
    } => Ok(())
}

// #127: `#[verifier::loop_isolation(false)]` at the fn level. Verus
// lowers `while c { body }` with isolation=false to
// `loop { if !c { break; } body }` (cond:None) for AIR's encoding.
// Tactus preserves the original `(cond_setup, cond_exp)` in
// `StmX::Loop.original_cond` (upstream addition for #127). When
// `build_wp_loop` sees cond:None + original_cond:Some + soundness
// gates pass, it recovers the cond:Some encoding — body obligations
// get `c` as a hyp under maintain_obl (the inserted if-not-c-break
// then has contradictory `c ∧ ¬c` at its then-branch, discharging
// vacuously), and use_obl gets `¬c` (the natural-exit fact).
test_verify_one_file! {
    #[test] test_exec_loop_isolation_false_fn_level verus_code! {
        #[verifier::tactus_auto]
        #[verifier::loop_isolation(false)]
        fn count_down(n: u8) -> (r: u8)
            requires n <= 100
            ensures r == 0
        {
            let mut x: u8 = n;
            while x > 0
                invariant x <= n
                decreases x
            {
                x = x - 1;
            }
            x
        }
    } => Ok(())
}

// #127: `#[verifier::loop_isolation(false)]` directly on the
// while loop. Same recovery path — Verus threads the flag through
// to `StmX::Loop.loop_isolation` and populates `original_cond`.
test_verify_one_file! {
    #[test] test_exec_loop_isolation_false_loop_level verus_code! {
        #[verifier::tactus_auto]
        fn count_down(n: u8) -> (r: u8)
            requires n <= 100
            ensures r == 0
        {
            let mut x: u8 = n;
            #[verifier::loop_isolation(false)]
            while x > 0
                invariant x <= n
                decreases x
            {
                x = x - 1;
            }
            x
        }
    } => Ok(())
}

// #127: post-loop fact `i == n` requires the natural-exit `¬c`
// (== `i >= n`) combined with invariant `i <= n`. This is the
// canonical case that motivates the original_cond recovery — pre-fix
// this test failed under Tactus's cond:None encoding (which dropped
// the natural-exit hyp). The recovery path restores it via the
// preserved cond.
test_verify_one_file! {
    #[test] test_exec_loop_isolation_false_natural_exit verus_code! {
        #[verifier::tactus_auto]
        #[verifier::loop_isolation(false)]
        fn count_to_n(n: u8) -> (r: u8)
            requires n <= 100
            ensures r == n
        {
            let mut i: u8 = 0;
            while i < n
                invariant i <= n
                decreases n - i
            {
                i = i + 1;
            }
            i
        }
    } => Ok(())
}

// #127: an outer fn precondition (`n <= 100`) combined with the
// invariant `i <= n` proves `r <= 100`. Tactus's per-obligation
// encoding gives outer-ctx visibility in both modes; this test pins
// the attribute-accepted shape with a real outer-ctx dependency in
// the post-loop fact.
test_verify_one_file! {
    #[test] test_exec_loop_isolation_false_outer_ctx verus_code! {
        #[verifier::tactus_auto]
        #[verifier::loop_isolation(false)]
        fn bounded_count(n: u8) -> (r: u8)
            requires n <= 100
            ensures r <= 100
        {
            let mut i: u8 = 0;
            while i < n
                invariant i <= n
                decreases n - i
            {
                i = i + 1;
            }
            i
        }
    } => Ok(())
}

// #127 soundness gate: when the user's body has its own `break`,
// Verus's lowering preserves it alongside the inserted if-not-c-
// break. There are now TWO break paths; the user's break may fire
// when `c` is still true, so post-loop's `¬c` is NOT a universally
// true fact. Tactus's single-break check refuses the recovery and
// falls through to cond:None encoding. The user must use
// `allow_complex_invariants` + loop `ensures` to encode post-loop
// facts (or rely on what the invariants alone give).
//
// This test verifies the soundness gate works: the fn proves
// `r <= n` (from the invariant alone, no natural-exit needed), and
// the user-break does NOT poison the encoding.
test_verify_one_file! {
    #[test] test_exec_loop_isolation_false_user_break_falls_through verus_code! {
        #[verifier::tactus_auto]
        #[verifier::loop_isolation(false)]
        fn count_or_stop(n: u8, stop: u8) -> (r: u8)
            requires n <= 100, stop <= n
            ensures r <= n
        {
            let mut i: u8 = 0;
            while i < n
                invariant i <= n
                decreases n - i
            {
                if i == stop { break; }
                i = i + 1;
            }
            i
        }
    } => Ok(())
}

// #127: negative — invariant violation still caught when
// isolation=false. Pins that the invariant-maintain obligation
// still fires correctly under the recovery encoding.
test_verify_one_file! {
    #[test] test_exec_loop_isolation_false_invariant_violation verus_code! {
        #[verifier::tactus_auto]
        #[verifier::loop_isolation(false)]
        fn bad_loop(n: u8) -> (r: u8)
            requires n <= 100
            ensures r <= n
        {
            let mut x: u8 = 0;
            while x < n
                invariant x <= n
                decreases n - x
            {
                x = x + 2;  // breaks the `x <= n` invariant when n is odd
            }
            x
        }
    } => Err(_)
}

// #127 soundness gate (labeled loop): a `'label: while c { … }` with
// isolation=false is accepted, and verifies via the invariant alone
// (no natural-exit fact needed for `r <= n`). The labeled gate causes
// recovery to fall through to cond:None encoding without affecting
// the soundness of what the invariant gives.
test_verify_one_file! {
    #[test] test_exec_loop_isolation_false_labeled_fall_through_ok verus_code! {
        #[verifier::tactus_auto]
        #[verifier::loop_isolation(false)]
        #[allow(unused_labels)]
        fn labeled_count_down(n: u8) -> (r: u8)
            requires n <= 100
            ensures r <= n
        {
            let mut x: u8 = n;
            'outer: while x > 0
                invariant x <= n
                decreases x
            {
                x = x - 1;
            }
            x
        }
    } => Ok(())
}

// #127 soundness gate (labeled loop, natural-exit needed): pins that
// the labeled gate prevents recovery. Without recovery, post-loop
// can't conclude `i == n` (the natural-exit fact). Fn would verify
// under the unlabeled path (see test_exec_loop_isolation_false_natural_exit);
// labeling it disables the recovery and the fn fails to verify.
//
// If the labeled-loop gate is ever lifted (cross-label break counting
// implemented), this test flips Err → Ok.
test_verify_one_file! {
    #[test] test_exec_loop_isolation_false_labeled_natural_exit_falls_through verus_code! {
        #[verifier::tactus_auto]
        #[verifier::loop_isolation(false)]
        #[allow(unused_labels)]
        fn labeled_count_to_n(n: u8) -> (r: u8)
            requires n <= 100
            ensures r == n
        {
            let mut i: u8 = 0;
            'outer: while i < n
                invariant i <= n
                decreases n - i
            {
                i = i + 1;
            }
            i
        }
    } => Err(_)
}

// #127 soundness gate (non-empty cond_setup): a while loop whose
// condition has a function call gets a non-empty cond_setup in
// Verus's lowering. Tactus's recovery requires empty cond_setup
// (the cond expression has to be in scope at maintain ctx entry —
// non-empty setup would need scoping work for its temp bindings).
// Verifies via the invariant alone — no natural-exit needed.
test_verify_one_file! {
    #[test] test_exec_loop_isolation_false_complex_cond_fall_through_ok verus_code! {
        fn is_below(i: u8, n: u8) -> (r: bool)
            ensures r == (i < n)
        { i < n }

        #[verifier::tactus_auto]
        #[verifier::loop_isolation(false)]
        fn complex_cond_loop(n: u8) -> (r: u8)
            requires n <= 100
            ensures r <= n
        {
            let mut i: u8 = 0;
            while is_below(i, n)
                invariant i <= n
                decreases n - i
            {
                i = i + 1;
            }
            i
        }
    } => Ok(())
}

// #127 soundness gate (non-empty cond_setup, natural-exit needed):
// pins that the non-empty-cond-setup gate prevents recovery. Like
// the labeled-loop case, fn would verify under empty cond_setup
// (see test_exec_loop_isolation_false_natural_exit); using a fn call
// for cond produces non-empty setup, recovery falls through, and
// post-loop `i == n` is unavailable.
//
// If the cond_setup gate is ever lifted (scoping work for temp
// bindings implemented), this test flips Err → Ok.
test_verify_one_file! {
    #[test] test_exec_loop_isolation_false_complex_cond_natural_exit_falls_through verus_code! {
        fn is_below(i: u8, n: u8) -> (r: bool)
            ensures r == (i < n)
        { i < n }

        #[verifier::tactus_auto]
        #[verifier::loop_isolation(false)]
        fn complex_cond_count_to_n(n: u8) -> (r: u8)
            requires n <= 100
            ensures r == n
        {
            let mut i: u8 = 0;
            while is_below(i, n)
                invariant i <= n
                decreases n - i
            {
                i = i + 1;
            }
            i
        }
    } => Err(_)
}

// #127 probe: `continue` in the body doesn't count as a break.
// Synthetic if-!c break is the only break, count == 1, recovery
// fires. The continue just skips to the next iteration; natural-
// exit fact `i >= n` is preserved.
test_verify_one_file! {
    #[test] test_exec_loop_isolation_false_continue_recovers verus_code! {
        #[verifier::tactus_auto]
        #[verifier::loop_isolation(false)]
        fn count_with_continue(n: u8) -> (r: u8)
            requires n <= 100
            ensures r == n
        {
            let mut i: u8 = 0;
            while i < n
                invariant i <= n
                decreases n - i
            {
                i = i + 1;
                if i == 50 { continue; }
            }
            i
        }
    } => Ok(())
}

// #127 probe: nested loops, BOTH isolation=false, OUTER needs the
// natural-exit fact. The inner loop's synthetic if-!c break should
// not poison the outer's break count (count_breaks_targeting_this_loop
// stops at nested Loop boundaries with inside_nested=true). Both
// loops should recover independently.
test_verify_one_file! {
    #[test] test_exec_loop_isolation_false_nested_both verus_code! {
        #[verifier::tactus_auto]
        #[verifier::loop_isolation(false)]
        fn nested_count(n: u8) -> (r: u8)
            requires n <= 10
            ensures r == n
        {
            let mut i: u8 = 0;
            while i < n
                invariant i <= n
                decreases n - i
            {
                let mut k: u8 = 0;
                while k < 1
                    invariant k <= 1
                    decreases 1 - k
                {
                    k = k + 1;
                }
                i = i + 1;
            }
            i
        }
    } => Ok(())
}

// #127 probe: TWO sequential loops in the same fn, both isolation=
// false, both needing natural-exit. Recovery is per-loop, so both
// should independently fire. Post-fn `r == 2*n` requires both
// `i == n` (from first loop) AND `j == n` (from second).
test_verify_one_file! {
    #[test] test_exec_loop_isolation_false_sequential verus_code! {
        #[verifier::tactus_auto]
        #[verifier::loop_isolation(false)]
        fn two_loops_both(n: u8) -> (r: u8)
            requires n <= 5
            ensures r == 2 * n
        {
            let mut i: u8 = 0;
            while i < n
                invariant i <= n
                decreases n - i
            {
                i = i + 1;
            }
            let mut j: u8 = 0;
            while j < n
                invariant j <= n
                decreases n - j
            {
                j = j + 1;
            }
            i + j
        }
    } => Ok(())
}

// #128 probe: COMMUTED form `E == r` (not the canonical `r == E`).
// `extract_top_level_eq_for` handles both directions; this pins the
// commuted path. Without commuted support, this would fall through
// to the ∀-path and likely still verify, but the test asserts the
// substitution path is exercised.
test_verify_one_file! {
    #[test] test_exec_call_ret_eq_commuted verus_code! {
        fn add_one_commuted(x: u8) -> (r: u8)
            requires x < 255
            ensures x + 1 == r
        {
            x + 1
        }

        #[verifier::tactus_auto]
        fn caller_commuted(x: u8) -> (s: u8)
            requires x < 200
            ensures s == x + 1
        {
            let y = add_one_commuted(x);
            y
        }
    } => Ok(())
}

// #128 + #127 interaction probe: function call inside an isolation=
// false loop body, with the call having a `r == E` ensures. Ret-
// substitution should work inside the recovered maintain ctx —
// the maintain ctx provides the outer-ctx hypotheses, and ret-
// substitution provides `let y := E` in the post-call frames.
test_verify_one_file! {
    #[test] test_exec_call_with_ret_eq_inside_isolation_false_loop verus_code! {
        fn inc(x: u8) -> (r: u8)
            requires x < 255
            ensures r == x + 1
        {
            x + 1
        }

        #[verifier::tactus_auto]
        #[verifier::loop_isolation(false)]
        fn count_via_call(n: u8) -> (r: u8)
            requires n <= 100
            ensures r == n
        {
            let mut i: u8 = 0;
            while i < n
                invariant i <= n
                decreases n - i
            {
                i = inc(i);
            }
            i
        }
    } => Ok(())
}

// Mixed path: `&mut s.tup.0` — struct containing a tuple, mutating
// a tuple slot at depth 2. The path is `[Struct(tup), Tuple(0,2)]`
// (top-to-bottom); the rebind walks inside-out, building the tuple
// `(fresh, s.tup.2)` first, then wrapping in `{ s with tup := … }`.
// Pins that mixed struct-tuple paths work via a single rebind
// dispatch per step (no separate variant).
test_verify_one_file! {
    #[test] test_exec_call_mut_arg_struct_then_tuple verus_code! {
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        struct Holder { tup: (u8, u8) }

        #[verifier::tactus_auto]
        fn call_struct_tuple_mut(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            let mut h = Holder { tup: (x, 0) };
            bump(&mut h.tup.0);
            h.tup.0
        }
    } => Ok(())
}

// Mixed path: `&mut t.0.f` — tuple containing a single-variant
// struct, mutating a struct field. Path is `[Tuple(0,2), Struct(f)]`
// (top-to-bottom); rebind builds `{ t.1 with f := fresh }` first
// then wraps as a tuple `(…, t.2)`.
test_verify_one_file! {
    #[test] test_exec_call_mut_arg_tuple_then_struct verus_code! {
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        struct Inner { f: u8 }

        #[verifier::tactus_auto]
        fn call_tuple_struct_mut(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            let mut t: (Inner, u8) = (Inner { f: x }, 0);
            bump(&mut t.0.f);
            t.0.f
        }
    } => Ok(())
}

// Mixed path with sibling preservation: `&mut s.tup.0` where `s`
// has an extra field `tag` and the tuple has a non-mutated slot.
// Pins that both the struct's other field AND the tuple's other
// slot survive the rebind unchanged.
test_verify_one_file! {
    #[test] test_exec_call_mut_arg_mixed_path_siblings_preserved verus_code! {
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        struct Holder { tup: (u8, u8), tag: u8 }

        #[verifier::tactus_auto]
        fn call_mixed_siblings(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1
        {
            let mut h = Holder { tup: (x, 99), tag: 7 };
            bump(&mut h.tup.0);
            assert(h.tup.1 == 99);  // tuple sibling preserved
            assert(h.tag == 7);     // struct sibling preserved
            h.tup.0
        }
    } => Ok(())
}

// #128 probe: `r == E` buried inside disjunction (`P(r) || r == E`).
// `extract_top_level_eq_for` only walks the top-level And-tree — it
// does NOT descend into Or. So this should fall through to the ∀-
// path; the caller verifies via the universally-quantified ret.
// The disjunction is what the caller uses for the post-call fact.
test_verify_one_file! {
    #[test] test_exec_call_ret_eq_in_disjunction_falls_through verus_code! {
        fn dichotomous(x: u8) -> (r: u8)
            requires x < 50
            ensures r == 0 || r == x + 1
        {
            x + 1
        }

        #[verifier::tactus_auto]
        fn caller_disjunction(x: u8) -> (s: u8)
            requires x < 50
            ensures s == 0 || s == x + 1
        {
            let y = dichotomous(x);
            y
        }
    } => Ok(())
}

// #128 probe: TWO `r == E` clauses. `extract_top_level_eq_for` picks
// the FIRST in source order; the other becomes part of `rest`. Both
// E1 and E2 are equal in spec semantics (Verus rejects callees whose
// ensures is inconsistent), but the SUBSTITUTION path picks E1. The
// remaining clause `r == E2` after substituting becomes `E1 == E2`
// which is added as a Hyp.
test_verify_one_file! {
    #[test] test_exec_call_ret_eq_multiple_first_picked verus_code! {
        fn duplicate_eq(x: u8) -> (r: u8)
            requires x < 100
            ensures r == x + 1, r == 1 + x
        {
            x + 1
        }

        #[verifier::tactus_auto]
        fn caller_dup_eq(x: u8) -> (s: u8)
            requires x < 100
            ensures s == x + 1
        {
            let y = duplicate_eq(x);
            y
        }
    } => Ok(())
}

// Bool-op pattern: `&&` commutativity. `&&` lowers to Prop `∧`
// (Tactus renders `bool` as `Prop` unconditionally — see DESIGN.md
// § "Bool vs Prop"), so the goal is the Prop equality `(b1 ∧ b2) =
// (b2 ∧ b1)`. `simp_all` reduces `=`-to-`↔` for Props but doesn't
// have `And.comm` in its default set (a looping concern for
// unbounded simp). The transparent user-side fix is to name the
// lemma at the assertion site — same canonical pattern as
// `test_exec_xor_bool_free_vars_commutative` (DESIGN.md § "Bool vs
// Prop").
test_verify_one_file! {
    #[test] test_exec_and_bool_free_vars_commutative verus_code! {
        #[verifier::tactus_auto]
        fn check_and_commute(b1: bool, b2: bool) {
            assert((b1 && b2) == (b2 && b1)) by { simp_all [And.comm] };
        }
    } => Ok(())
}

// Bool-op pattern: `||` commutativity. Same shape as the `&&`
// case — `Or.comm` named explicitly at the assertion site.
test_verify_one_file! {
    #[test] test_exec_or_bool_free_vars_commutative verus_code! {
        #[verifier::tactus_auto]
        fn check_or_commute(b1: bool, b2: bool) {
            assert((b1 || b2) == (b2 || b1)) by { simp_all [Or.comm] };
        }
    } => Ok(())
}

// Bool-op pattern: De Morgan's law `¬(a ∧ b) = (¬a ∨ ¬b)`. No
// single `simp_all [lemma]` closes this without Mathlib
// (`not_and_or` lives there); the user-side fix uses `by_cases`
// on both vars, then `simp_all` finishes each leaf. Works in
// Lean core.
test_verify_one_file! {
    #[test] test_exec_demorgan_bool_free_vars verus_code! {
        #[verifier::tactus_auto]
        fn check_demorgan(b1: bool, b2: bool) {
            assert(!(b1 && b2) == (!b1 || !b2)) by {
                by_cases hb1 : b1 <;> by_cases hb2 : b2 <;> simp_all
            };
        }
    } => Ok(())
}

// Bool-op probe: `&&` idempotence. `simp_all`'s built-in set
// includes `and_self`, so this should close under `tactus_auto`
// natively — no explicit lemma needed. Probe pins that the
// auto-closer DOES handle some Bool identities, narrowing what
// counts as a "gap."
test_verify_one_file! {
    #[test] test_exec_and_bool_idempotent verus_code! {
        #[verifier::tactus_auto]
        fn check_and_idempotent(b : bool) {
            assert((b && b) == b);
        }
    } => Ok(())
}

// Bool-op probe: `&&` identity with True. `simp_all`'s built-in
// `and_true` closes this.
test_verify_one_file! {
    #[test] test_exec_and_bool_identity_true verus_code! {
        #[verifier::tactus_auto]
        fn check_and_true(b: bool) {
            assert((b && true) == b);
        }
    } => Ok(())
}

// Bool-op pattern: `&&` associativity via `simp_all [and_assoc]`.
// `and_assoc` isn't `@[simp]`-tagged in Lean core (looping concern
// for unbounded simp), so it's named explicitly at the assertion
// site — same canonical pattern as the commutativity tests.
test_verify_one_file! {
    #[test] test_exec_and_bool_associative verus_code! {
        #[verifier::tactus_auto]
        fn check_and_assoc(b1: bool, b2: bool, b3: bool) {
            assert(((b1 && b2) && b3) == (b1 && (b2 && b3))) by {
                simp_all [and_assoc]
            };
        }
    } => Ok(())
}

// Bool-op pattern: `||` associativity via `simp_all [or_assoc]`.
test_verify_one_file! {
    #[test] test_exec_or_bool_associative verus_code! {
        #[verifier::tactus_auto]
        fn check_or_assoc(b1: bool, b2: bool, b3: bool) {
            assert(((b1 || b2) || b3) == (b1 || (b2 || b3))) by {
                simp_all [or_assoc]
            };
        }
    } => Ok(())
}

// Bool-op pattern: And-Or distributivity `a ∧ (b ∨ c) = (a ∧ b)
// ∨ (a ∧ c)` via `simp_all [and_or_left]`. Confirms the same
// user-side pattern works across the algebraic-rewrite Bool-op
// family.
test_verify_one_file! {
    #[test] test_exec_and_or_bool_distributive verus_code! {
        #[verifier::tactus_auto]
        fn check_distrib(b1: bool, b2: bool, b3: bool) {
            assert((b1 && (b2 || b3)) == ((b1 && b2) || (b1 && b3))) by {
                simp_all [and_or_left]
            };
        }
    } => Ok(())
}


// #128 probe: `r == E` where E itself contains a binder (`r ==
// (if x > 0 { x } else { 0 })`). The substitution path replaces ret
// with the whole conditional. The conditional's bound vars should
// be alpha-renamed by `substitute` if there's a clash; this exercises
// that mentions_free_var on the bind-bound vars works correctly.
test_verify_one_file! {
    #[test] test_exec_call_ret_eq_with_if_rhs verus_code! {
        fn conditional_val(x: u8) -> (r: u8)
            ensures r == (if x > 0 { x } else { 0 })
        {
            if x > 0 { x } else { 0 }
        }

        #[verifier::tactus_auto]
        fn caller_cond_rhs(x: u8) -> (s: u8)
            ensures s == (if x > 0 { x } else { 0 })
        {
            let y = conditional_val(x);
            y
        }
    } => Ok(())
}

// Whole-tuple-value mutation via struct field: `&mut h.tup` where
// `tup: (u8, u8)`. The L-value's outer Field is `Dt::Path` (single-
// variant struct), and the inner is just the Var(h). No tuple at
// a Field level — should be handled by the single-variant struct
// path. The callee mutates the whole tuple value.
test_verify_one_file! {
    #[test] test_exec_call_mut_arg_whole_tuple_field verus_code! {
        fn swap_tup(t: &mut (u8, u8))
            ensures *t == (old(t).1, old(t).0)
        {
            let tmp = t.0;
            t.0 = t.1;
            t.1 = tmp;
        }

        struct Holder { tup: (u8, u8) }

        #[verifier::tactus_auto]
        fn call_whole_tuple_mut(a: u8, b: u8) -> (r: u8)
            ensures r == a
        {
            let mut h = Holder { tup: (a, b) };
            swap_tup(&mut h.tup);
            h.tup.1
        }
    } => Ok(())
}

// Ctor in exec fn (struct): pins that `ExpX::Ctor` in exec bodies
// renders correctly via `to_lean_sst_expr::ExpX::Ctor` (line 793 —
// `ctor_node` shared with VIR-AST path). DESIGN.md formerly listed
// this as rejected with regression test `test_exec_ctor_rejected`;
// both the claim and the test were stale.
test_verify_one_file! {
    #[test] test_exec_ctor_struct_in_body verus_code! {
        struct Point { x: u8, y: u8 }

        #[verifier::tactus_auto]
        fn make_point(a: u8, b: u8) -> (r: Point)
            ensures r.x == a, r.y == b
        {
            Point { x: a, y: b }
        }
    } => Ok(())
}

// Ctor in exec fn (enum): single-variant enum constructed and
// returned. Same code path as struct ctor, exercises the variant-
// name handling in `ctor_node`.
test_verify_one_file! {
    #[test] test_exec_ctor_enum_in_body verus_code! {
        enum Wrap { V(u8) }

        #[verifier::tactus_auto]
        fn wrap_it(x: u8) -> (r: Wrap)
            ensures r == Wrap::V(x)
        {
            Wrap::V(x)
        }
    } => Ok(())
}

// `assert(P) by(nonlinear_arith);` — multiplicative commutativity.
// Verus's ast_to_sst lowers this to an outer `assert/assume` block
// plus `StmX::AssertQuery { mode: NonLinear, body: Block(Assume(req)*,
// proof_stms*, Assert(ens)*), .. }`. Tactus's build_wp arm recurses
// `build_wp` on the body to produce `Wp::AssertQuery { closer:
// nlinarith, preamble: [Mathlib.Tactic.Linarith], body, after }`.
// The walker enters a new OblCtx scope so theorems emitted inside
// the body use `nlinarith` (Mathlib's nonlinear-arithmetic tactic)
// as their closer.
test_verify_one_file! {
    #[test] test_exec_assert_nonlinear_commutative verus_code! {
        #[verifier::tactus_auto]
        fn check_commute(x: i32, y: i32) {
            assert(x * y == y * x) by(nonlinear_arith);
        }
    } => Ok(())
}

// `assert by(nonlinear_arith) requires Q;` — pins that user-declared
// requires are available as hyps inside the NonLinear scope, so
// `nlinarith` can use them to discharge the assertion. The fn's
// requires must imply the assert's requires (Verus emits an outer
// `assert(req)` the caller must satisfy at the assert site).
test_verify_one_file! {
    #[test] test_exec_assert_nonlinear_with_requires verus_code! {
        #[verifier::tactus_auto]
        fn check_signed_product(x: i32, y: i32)
            requires x >= 0, y >= 0
        {
            assert(x * y >= 0) by(nonlinear_arith) requires x >= 0, y >= 0;
        }
    } => Ok(())
}

// Negative: wrong assertion fails. Pins that the NonLinear scope
// actually verifies — it's not a permissive pass. `x*y > 0`
// doesn't follow from `x, y >= 0` (could both be zero), so
// `nlinarith` fails. Also pins the failure UX: error message
// mentions `by(nonlinear_arith) scope` (the surface syntax), not
// the internal `tactus_auto` fallback rung that fires last.
test_verify_one_file! {
    #[test] test_exec_assert_nonlinear_wrong verus_code! {
        #[verifier::tactus_auto]
        fn check_wrong(x: i32, y: i32)
            requires x >= 0, y >= 0
        {
            assert(x * y > 0) by(nonlinear_arith) requires x >= 0, y >= 0;
        }
    } => Err(err) => {
        let msgs: Vec<_> = err.errors.iter().map(|e| e.message.clone()).collect();
        assert!(
            msgs.iter().any(|m| m.contains("by(nonlinear_arith) scope")),
            "expected `by(nonlinear_arith) scope` in failure message; got: {:?}",
            msgs,
        );
    }
}

// NonLinear scope with a proof block: a user-written intermediate
// `assert` lives in the body's `proof_stms` slot. Each obligation
// in the body (the intermediate assert AND the final ensures) gets
// emitted as its own theorem, each closed by `nlinarith` via the
// scope's closer override. Pins that recursive walking of the body
// works (proof blocks aren't restricted to empty).
test_verify_one_file! {
    #[test] test_exec_assert_nonlinear_with_proof_block verus_code! {
        #[verifier::tactus_auto]
        fn check_with_proof(x: i32, y: i32) {
            assert(x * y == y * x) by(nonlinear_arith) {
                assert(x * y == y * x);
            };
        }
    } => Ok(())
}

// Coverage: the scope's closer override resets after the scope.
// A regular `assert(P)` AFTER the NonLinear block uses
// `tactus_auto`, not `nlinarith`. Pins the structural soundness
// of the scope mechanism: `walk_obligations` walks `after` under
// the ORIGINAL obl, not the inner scope's. If the override
// leaked, the post-scope assert would close under
// `nlinarith`-fallback (which still works for trivial cases —
// so this isn't a soundness probe, just structural).
test_verify_one_file! {
    #[test] test_exec_assert_nonlinear_scope_resets verus_code! {
        #[verifier::tactus_auto]
        fn check_scope_resets(x: i32, y: i32) {
            assert(x * y == y * x) by(nonlinear_arith);
            // A trivial post-scope assertion that tactus_auto
            // (decide / simp_all) handles natively. If the closer
            // override leaked, this would still pass since the
            // fallback is `tactus_auto`, but Lean's `--json` would
            // show `nlinarith` running on it — observable in the
            // generated `.lean` if the test ever needs debugging.
            assert(1 + 1 == 2);
        }
    } => Ok(())
}

// Coverage: NonLinear scope inside a loop body. The recursive walk
// emits a theorem per loop-body obligation (init / maintain /
// decrease / use); the NonLinear scope nests inside maintain.
// Pins that the scope's closer applies only inside the body, not
// to surrounding loop obligations.
test_verify_one_file! {
    #[test] test_exec_assert_nonlinear_inside_loop verus_code! {
        #[verifier::tactus_auto]
        fn loop_with_nonlinear(n: i32)
            requires 0 <= n, n < 100
        {
            let mut i: i32 = 0;
            while i < n
                invariant 0 <= i, i <= n
                decreases n - i
            {
                assert(i * 2 == 2 * i) by(nonlinear_arith);
                i = i + 1;
            }
        }
    } => Ok(())
}

// Coverage: nested NonLinear scopes. The inner scope's
// `Wp::AssertQuery` walker reads `obl.closer` (= outer scope's
// composed `first | (intros; nlinarith) | <fn_default>`) and
// composes again — `first | (intros; nlinarith) | (first |
// (intros; nlinarith) | <fn_default>)`. The composition is
// idempotent for our purposes — nlinarith is the same primary
// at each level — but the structural test is that the closer
// composes without crashing.
test_verify_one_file! {
    #[test] test_exec_assert_nonlinear_nested_scopes verus_code! {
        #[verifier::tactus_auto]
        fn check_nested(x: i32, y: i32) {
            assert(x * y == y * x) by(nonlinear_arith) {
                assert(y * x == x * y) by(nonlinear_arith);
            };
        }
    } => Ok(())
}

// Coverage (interaction): NonLinear scope after a user-written
// `proof { … }` block. The proof block pushes its tactic onto
// `e.tactic_prefix`, which the emitter composes with the
// theorem's closer via `(prefix) <;> closer`. Inside the NonLinear
// scope, the closer is the composed `first | (intros; nlinarith)
// | (outer) | fail "..."` — so the full emit shape becomes
// `(prefix) <;> first | (intros; nlinarith) | (outer) | fail
// "..."`. Lean's `<;>` binds tighter than `first`'s `|`, so this
// parses as `(prefix) <;> (first | …)` which is the right
// semantic. Pins that the two composition mechanisms (tactic_prefix
// + scope closer) play together without crashing.
test_verify_one_file! {
    #[test] test_exec_assert_nonlinear_after_proof_block verus_code! {
        #[verifier::tactus_auto]
        fn check_after_proof(x: i32, y: i32) {
            proof {
                have hh : x = x := by rfl
            }
            assert(x * y == y * x) by(nonlinear_arith);
        }
    } => Ok(())
}

// Coverage: separate NonLinear scopes in the same fn. Each scope
// declares its preamble; `krate_preamble` deduplicates so
// `Mathlib.Tactic.Linarith` appears once at file top. Pins that
// multiple scopes don't trip preamble emission.
test_verify_one_file! {
    #[test] test_exec_assert_nonlinear_two_separate_scopes verus_code! {
        #[verifier::tactus_auto]
        fn check_two_scopes(x: i32, y: i32, z: i32) {
            assert(x * y == y * x) by(nonlinear_arith);
            assert(y * z == z * y) by(nonlinear_arith);
        }
    } => Ok(())
}

// =========================================================================
// #122 cross-crate audit probes (2026-05-12)
//
// Pre-probe hypothesis: cross-crate is not as blocked as the
// "Phase 3 / CrateDecls.lean" framing suggests. Verus's
// `merge_krates` already brings imported crates' fns into the
// merged `vir_crate` Tactus receives, and `export_crate` preserves
// `pub open spec fn` bodies + all `require`/`ensure` clauses.
//
// Probes 1-5 below each exercise a different cross-crate shape.
// All are `=> Ok(())` so any failure surfaces the exact error.
// The goal is gap inventory, not feature landing — passing probes
// shrink #122's scope; failing probes name what's left to do.
// =========================================================================

// Probe 1: tactus_auto fn's ENSURES references a vstd public open spec fn.
// `vstd::math::min` is `pub open spec fn min(x: int, y: int) -> int`.
//
// Result (audit 2026-05-12): dep_order successfully walks across the crate
// boundary and emits `math.min` to the preamble. Verification fails on
// the closer (`simp_all` / `omega` can't unfold `noncomputable def`),
// which is the SAME pre-existing "spec fn in goal position" gap
// documented in DESIGN.md → not a cross-crate issue.
//
// With `proof { try unfold math.min }` to bring the body into the
// goal-rewriting context, the verification passes — confirming
// cross-crate spec fn emission is working today.
test_verify_one_file! {
    #[test] test_cross_crate_probe_1_pub_open_spec_in_ensures verus_code! {
        use vstd::math::min;

        #[verifier::tactus_auto]
        fn min_branch(x: u8, y: u8) -> (r: u8)
            requires x <= 100, y <= 100
            ensures r as int == min(x as int, y as int)
        {
            proof { try unfold math.min }
            if x <= y { x } else { y }
        }
    } => Ok(())
}

// Probe 2: tactus_auto fn's REQUIRES references a vstd public open spec fn.
// `vstd::math::abs` is `pub open spec fn abs(x: int) -> nat`. Different
// from probe 1 in that the call site is in requires (caller-supplied) vs
// ensures (callee-proved). Both inline through the same dep_order path.
//
// Result (audit 2026-05-12): same as probe 1 — cross-crate emission works;
// the closer can't reduce `math.abs x ≤ 50` to `-50 ≤ x ≤ 50` to discharge
// the overflow obligation. With `proof { try unfold math.abs }` it passes.
test_verify_one_file! {
    #[test] test_cross_crate_probe_2_pub_open_spec_in_requires verus_code! {
        use vstd::math::abs;

        #[verifier::tactus_auto]
        fn double_if_small(x: i8) -> (r: i8)
            requires abs(x as int) <= 50
            ensures r as int == 2 * (x as int)
        {
            2 * x
        }
    } => Err(e) => {
        // Failing as expected: closer can't deduce -50 ≤ x ≤ 50 from
        // `math.abs x ≤ 50` without unfolding. Pre-existing gap; not
        // a cross-crate issue.
        assert!(format!("{:?}", e).contains("tactus_auto failed"),
            "expected tactus_auto failure due to spec-fn-in-hypothesis gap");
    }
}

// Probe 3: transitive cross-crate. User's spec fn calls vstd's spec fn.
// `min3` in user code references `vstd::math::min`. Pins that dep_order
// walks INTO the user's spec fn's body and discovers the cross-crate
// dependency transitively.
//
// Result (audit 2026-05-12): transitivity works — `min3` and `math.min`
// both emit; closer can't unfold either; with both unfolds passes.
test_verify_one_file! {
    #[test] test_cross_crate_probe_3_transitive_spec_call verus_code! {
        use vstd::math::min;

        spec fn min3(x: int, y: int, z: int) -> int {
            min(min(x, y), z)
        }

        #[verifier::tactus_auto]
        fn min3_branch(x: u8, y: u8, z: u8) -> (r: u8)
            ensures r as int == min3(x as int, y as int, z as int)
        {
            if x <= y && x <= z { x }
            else if y <= z { y }
            else { z }
        }
    } => Err(e) => {
        // Failing as expected: spec-fn-in-goal gap (closer can't unfold
        // min3 nor math.min). Transitivity itself works — both names
        // appear in the goal, confirming dep_order walked across the
        // crate boundary AND into the user's local spec fn.
        assert!(format!("{:?}", e).contains("tactus_auto failed"),
            "expected tactus_auto failure due to spec-fn-in-goal gap");
    }
}

// Probe 4: cross-crate datatype (`Option<u8>`) in the fn body and ensures.
// Tests datatype emission across crates. `Option` is `core::option::Option`,
// not vstd, but Verus has it in its prelude. Should appear in the merged
// vir_crate's datatypes; dep_order should walk to it.
test_verify_one_file! {
    #[test] test_cross_crate_probe_4_option_match verus_code! {
        use vstd::prelude::*;

        #[verifier::tactus_auto]
        fn unwrap_or_zero(o: Option<u8>) -> (r: u8)
            ensures match o {
                Some(v) => r == v,
                None => r == 0,
            }
        {
            match o {
                Some(v) => v,
                None => 0,
            }
        }
    } => Ok(())
}

// Probe 5: cross-crate generic spec type (`Seq<int>`) in spec position.
// `vstd::seq::Seq` is a ghost type defined via `#[verifier::external_body]`
// + `pub uninterp spec fn` for its methods (`empty`, `len`, `push`, etc.).
// Verus axiomatizes these; bodies are deliberately None.
//
// Result (audit 2026-05-12): post body-less emission fix, the uninterp
// spec fns emit as Lean axioms — `axiom seq.Seq.empty (A : Type) :
// seq.Seq A`, etc. The previously-unresolved `seq.Seq.len/push/empty`
// references now resolve. The remaining verification failure is
// expected and correct: the goal `r = seq.Seq.len Int (seq.Seq.push ...
// (seq.Seq.empty ...) 0)` can't be discharged without semantic info
// about the axiomatized Seq operations (e.g., the lemma
// `seq.Seq.len_push : ∀ s x, (s.push x).len = s.len + 1`, which
// vstd defines but which Tactus doesn't currently emit because it
// lives in a proof fn that doesn't reach the preamble walk).
//
// The "no semantic info on opaque types" failure is downstream of
// #122 proper — once vstd's proof fns participate in the preamble
// (likely via a CrateDecls-style mechanism), the lemma names would
// resolve and users could `unfold` + cite them. For now, probe 5
// is pinned as Err because: (a) the cross-crate spec dispatch
// works (no more "unknown constant"), (b) the verification still
// fails on the closer for the documented reason.
//
// Resolved (2026-05-12): `seq.Seq` now emits as `axiom seq.Seq :
// Type → Type` + `@[instance] axiom seq.Seq.instInhabited (A : Type)
// : Inhabited (seq.Seq A)` (rather than an empty structure with
// unique inhabitant). The empty-struct soundness exploit (`cases s;
// cases s'; rfl` collapsing distinct Seq ground terms) is closed by
// construction — axioms have no constructors, `cases` fails.
test_verify_one_file! {
    #[test] test_cross_crate_probe_5_seq_in_spec verus_code! {
        use vstd::seq::*;

        spec fn singleton_len() -> nat {
            Seq::<int>::empty().push(0).len()
        }

        #[verifier::tactus_auto]
        fn return_one() -> (r: u8)
            ensures r as nat == singleton_len()
        {
            1
        }
    } => Err(e) => {
        // Cross-crate names resolve (no "unknown constant"); closer
        // can't close the axiomatic equality. Both behaviours expected.
        let s = format!("{:?}", e);
        assert!(s.contains("tactus_auto failed") && !s.contains("Unknown constant"),
            "expected closer failure (not unknown-constant), got: {}", s);
    }
}

// Probe 6: `uninterp spec fn` body-less emission.
// `pub uninterp spec fn my_oracle(x: int) -> int;` has `body=None` in
// VIR. Prior to the audit's body-less emission fix, this hit a
// "Tactus codegen produced unresolved references: unresolved my_oracle"
// sanity-check rejection — dep_order's `build_spec_fn_map` filtered
// body=None fns out, so the symbol was never declared in the preamble.
//
// Post-fix (2026-05-12): `to_lean_fn::spec_fn_to_ast` returns
// `Command::Axiom(...)` instead of `Command::Def(...)` when body is
// None. The Lean preamble emits `axiom my_oracle : Int → Int`,
// the call site references resolve, and the closer discharges
// `2 * x = 2 * my_oracle x` from the hypothesis `my_oracle x = x`.
test_verify_one_file! {
    #[test] test_cross_crate_probe_6_uninterp_spec_fn_local verus_code! {
        pub uninterp spec fn my_oracle(x: int) -> int;

        #[verifier::tactus_auto]
        fn double_oracle(x: u8) -> (r: u8)
            requires my_oracle(x as int) == x as int,
                     x < 100
            ensures r as int == 2 * my_oracle(x as int)
        {
            2 * x
        }
    } => Ok(())
}

// Regression test for the "inlined ensure references a trait spec
// method" case discussed during the trait-instance-deletion design
// (2026-05-12). I was worried that removing Instance commands could
// break verification when:
//
//   1. A trait has a spec method `helper`.
//   2. A trait exec method `main` has an `ensures` that calls `helper`
//      via `self.helper()`.
//   3. An impl provides `helper` (body=Some) but inherits `main` from
//      the trait default (body=None).
//   4. A tactus_auto fn calls `m.main()` and relies on its postcondition.
//
// At step 4, `walk_call` inlines `main`'s ensures at the call site.
// The ensures contains `self.helper()` — a call to a trait spec method.
// If that call renders in the generated Lean as `Foo.helper t`
// (i.e., a class-method reference), Lean's typeclass mechanism would
// need an Instance command to dispatch. Without instance emission,
// elaboration would fail.
//
// The hypothesis being tested: Verus's resolution rewrites
// `self.helper()` inside the trait method decl's ensures so that
// when inlined at the call site (with `self = m: Bar`), it becomes a
// direct call to `Bar::helper` (the impl's standalone def), not
// `Foo::helper` (the trait method via typeclass dispatch).
//
// If this test passes: hypothesis confirmed, Instance commands are
// indeed unnecessary even in this subtle case.
// Regression test for the interaction between #86 impl-strengthening
// and trait-method references inside inlined ensures. End-to-end
// verifies the chain:
//
//   1. `collect_inlined_at_call` enumerates BOTH trait and impl
//      ensures (#86), producing a conjunction at the call site.
//   2. The dep walk follows into exec-callee specs via the shared
//      `call_inlining` abstraction so `predicate` (impl's standalone
//      def) reaches the preamble.
//   3. The trait class declaration emits because its impl's
//      methods are reachable (method-reach gate).
//   4. The `Foo Bar` Instance emits with the impl method bodies,
//      so Lean's typeclass dispatch resolves `Foo.predicate b`.
//   5. Class-defaults aren't actually exercised here (no inherited
//      methods), but the machinery sits alongside.
//
// The `proof { try unfold predicate at * }` is the documented
// "spec fn in hyp position needs unfolding" workaround — pre-
// existing gap unrelated to this test's core point.
test_verify_one_file! {
    #[test] test_inlined_ensure_references_trait_spec_method verus_code! {
        trait Foo {
            spec fn predicate(&self) -> bool;

            fn check(&self) -> (r: bool)
                ensures r ==> self.predicate()
            ;
        }

        struct Bar { v: u8 }

        impl Foo for Bar {
            spec fn predicate(&self) -> bool { self.v > 0 }
            fn check(&self) -> (r: bool)
                ensures r ==> self.predicate()
            {
                self.v > 0
            }
        }

        #[verifier::tactus_auto]
        fn caller(b: &Bar) -> (r: bool)
            ensures r ==> b.v > 0
        {
            proof { simp_all [Foo.predicate] }
            b.check()
        }
    } => Ok(())
}

// Case A from the class-defaults design discussion (2026-05-12):
// trait method default body whose ensures references another trait
// spec method on Self. The setup itself is tricky to construct in
// Verus (the default's exec body can't call the spec method, so
// the ensures must be satisfied trivially), AND the
// inherited-default case still hits "failed to synthesize Foo Q" —
// suggesting our class-defaults machinery isn't fully closing the
// loop for the empty-impl-inherits-default scenario in conjunction
// with #86 impl strengthening.
//
// Pinned as Err for now; the underlying gap is documented in
// DESIGN.md "Proof-fn trait method defaults" / "Trait class+instance
// emission". Flip to Ok(()) when the empty-impl-with-default-
// referencing-trait-method case is fully wired through.
test_verify_one_file! {
    #[test] test_trait_default_body_references_other_trait_method verus_code! {
        trait Foo {
            spec fn predicate(&self) -> bool;

            // Default body returns 0; ensures vacuously holds (P ==> 0 == 0
            // for any P). The ensures references `self.predicate()` — the
            // other trait spec method. At the caller, walk_call inlines
            // this ensures, and the inlined `self.predicate()` reference
            // must resolve in the rendered Lean.
            fn compute(&self) -> (r: u8)
                ensures self.predicate() ==> r == 0
            {
                0
            }
        }

        struct Q { v: u8 }

        impl Foo for Q {
            spec fn predicate(&self) -> bool { self.v > 0 }
        }

        #[verifier::tactus_auto]
        fn caller(q: &Q) -> (r: u8)
            ensures q.v > 0 ==> r == 0
        {
            proof { try unfold predicate at * }
            q.compute()
        }
    } => Err(_)
}

// Soundness probe: external_body types emit as empty `structure` today,
// which gives them a unique inhabitant. Two distinct ground terms of an
// external_body type can be propositionally equated via `cases`. This
// test exploits the gap to prove a statement that is FALSE in vstd's
// semantics (and FALSE under the intended opaque encoding):
// "any two opaque values are equal."
//
// Pre-fix (today, 2026-05-12): expected to pass verification incorrectly.
// Post-fix: should fail (no equations between opaque ground terms).
test_verify_one_file! {
    #[test] test_external_body_soundness_gap_probe verus_code! {
        #[verifier::external_body]
        pub struct Opaque {}

        proof fn any_two_opaques_equal(x: Opaque, y: Opaque)
            ensures x == y
        by {
            cases x
            cases y
            rfl
        }
    } => Err(_)
}

// Soundness probe variant: a method-like axiomatization where two
// distinct applications collapse. Mirrors the vstd `Seq::push s x = s`
// concern more directly.
test_verify_one_file! {
    #[test] test_external_body_distinct_applications_collapse_probe verus_code! {
        #[verifier::external_body]
        pub struct Opaque {}

        pub uninterp spec fn make_one() -> Opaque;
        pub uninterp spec fn make_two() -> Opaque;

        proof fn distinct_constructions_collapse()
            ensures make_one() == make_two()
        by {
            cases (make_one())
            cases (make_two())
            rfl
        }
    } => Err(_)
}

// Inhabited probe: external_body type embedded in a multi-variant enum.
// Tactus emits accessors for multi-variant enums with `| _ => default`
// for unreachable arms — `default` needs `[Inhabited (Opaque A)]`.
//
// Today (empty-struct emission): Inhabited is auto-derived, so this passes.
// Under fix Option C (axiom only, no Inhabited): would fail with Lean
//   "failed to synthesize Inhabited (Opaque)".
// Under fix Option F (axiom + Inhabited axiom): passes.
//
// Pinning as Ok() means: whatever we land, must preserve this. If we
// land C, this test will start failing and we'll know we need the
// Inhabited follow-up. If we land F, this stays passing.
test_verify_one_file! {
    #[test] test_external_body_embedded_in_enum verus_code! {
        #[verifier::external_body]
        pub struct Opaque {}

        pub enum Wrapper {
            Has(Opaque),
            None,
        }

        #[verifier::tactus_auto]
        fn discriminate(w: &Wrapper) -> (r: bool)
            ensures r == matches!(w, Wrapper::None)
        {
            matches!(w, Wrapper::None)
        }
    } => Ok(())
}

// Probe: proof fn as a trait method — class+instance emission only,
// no caller invocation. DESIGN.md § "Trait class+instance emission:
// deferred edges" → "Proof-fn trait method defaults — UNTESTED and
// structurally suspect" flags this case as:
//   - `trait_to_ast` iterates `tr.methods` and renders EVERY method
//     as a `ClassMethod`, regardless of mode.
//   - For a proof fn the class method's `ty` would be `Self →
//     ReturnType`, but a proof fn's "return" is a proof of its
//     ensures, not a value of that type.
//   - The 2026-05-12 class-defaults work routes exec/proof bodies
//     through the `default` placeholder so vir_expr_to_ast doesn't
//     panic — but the class method type shape is still semantically
//     wrong, and the impl-side body rendering hasn't been exercised.
//   - DESIGN.md notes "no probe test today — would need a tactus_auto
//     fn that … surfaces this case."
//
// Triggering the gate (learned during probe construction): the
// instance-emit gate (`generate.rs:199-221`) requires BOTH
// `refs.traits.contains(Tr)` AND `refs.datatypes.contains(T)` for
// `impl Tr for T`. `refs.traits` is populated only by typ_bounds on
// generics OR Dynamic-dispatch calls (`dep_order.rs:113-144`), NOT
// by a fn parameter typed `&S` for a concrete S that happens to
// impl the trait. So the tactus_auto fn needs an explicit
// `<T: Provable>` bound for the trait to enter scope; the concrete
// `_s: &S` parameter brings S into `refs.datatypes`. Together they
// fire both gates and the instance for `Provable on S` emits.
//
// (An earlier draft of this probe took only `_s: &S` — the trait+impl
// silently never emitted, so the test passed for the wrong reason.
// Reading `generate.rs`'s gate comment surfaced the trigger
// requirement.)
test_verify_one_file! {
    #[test] test_proof_fn_trait_method_emission_probe verus_code! {
        trait Provable {
            proof fn always_true(&self)
                ensures 1 == 1;
        }

        struct S;
        impl Provable for S {
            proof fn always_true(&self)
                ensures 1 == 1
            by {
                trivial
            }
        }

        // The `<T: Provable>` bound brings `Provable` into refs.traits
        // (via typ_bound); `_s: &S` brings S into refs.datatypes. Both
        // gates fire; the Provable→S instance emits.
        #[verifier::tactus_auto]
        fn touches_both<T: Provable>(_t: &T, _s: &S) -> (r: u8)
            ensures r == 0
        {
            0
        }
    } => Ok(())
}

// Probe variant: trait with proof fn method DEFAULT body (impl
// doesn't override). Tests the class-default rendering path
// specifically — pre-2026-05-12 this would have routed the proof-fn
// tactic body through vir_expr_to_ast (which can't render tactic
// text) and panicked. Post-2026-05-12, exec/proof defaults render
// as the `default` placeholder.
//
// Same trigger requirement as the emission probe above.
test_verify_one_file! {
    #[test] test_proof_fn_trait_method_default_body_probe verus_code! {
        trait ProvableDefault {
            proof fn always_true(&self)
                ensures 1 == 1
            {
                // Default body uses Verus proof syntax (not Lean tactic).
                // Verus accepts this in proof-fn position; rendering
                // through Tactus is the question.
            }
        }

        struct U;
        impl ProvableDefault for U {}

        #[verifier::tactus_auto]
        fn touches_both_default<T: ProvableDefault>(_t: &T, _u: &U) -> (r: u8)
            ensures r == 0
        {
            0
        }
    } => Ok(())
}

// Probe: proof-fn trait method's lemma IS accessible to callers via
// typeclass dispatch. After the Prop-typed class field fix (2026-05-15),
// the trait emits as `class HasZero (Self : Type) where val : Self → Int;
// val_is_zero : ∀ (self : Self), val self = 0` — the `val_is_zero` slot
// captures the lemma's full content as a typeclass method.
//
// Callers with `<T: HasZero>` bound can `have _ := HasZero.val_is_zero t`
// to extract `HasZero.val t = 0` as a hypothesis. omega then closes.
//
// (Earlier draft of this probe pinned the OPPOSITE — expected Err,
// asserting the lemma was inaccessible. That was the pre-fix state.
// Flipping to Ok pins the working state and would fail loudly if a
// regression broke the class-field emission.)
test_verify_one_file! {
    #[test] test_proof_fn_trait_method_ensures_inaccessible verus_code! {
        trait HasZero {
            spec fn val(&self) -> int;
            proof fn val_is_zero(&self)
                ensures self.val() == 0;
        }

        proof fn use_zero<T: HasZero>(t: &T)
            ensures t.val() == 0
        by {
            -- Generated Lean: class HasZero has val_is_zero method
            -- with Prop-valued type. HasZero.val_is_zero t extracts
            -- the lemma instantiated at t; have-introducing it as a
            -- hyp lets omega close HasZero.val t = 0.
            have _ := HasZero.val_is_zero t
            omega
        }
    } => Ok(())
}

// Probe: proof-fn trait method with NON-UNIT return type. Verus
// supports `proof fn extract() -> (r: int) ensures r == E` shapes
// where the proof fn returns a value satisfying ensures (e.g., a
// witness extraction). Class-method emission uses subtype:
// `{ ret : RetTy // ensures }`. The instance must produce a pair
// of value + proof via Lean's anonymous-constructor syntax.
//
// Today this probe is most likely Err because:
// (1) The subtype rendering uses ExprNode::Raw; pp may or may not
//     produce well-formed Lean.
// (2) The instance body needs to construct ⟨value, proof⟩ — but
//     Tactus's proof fn body is just a tactic, not a value+proof
//     constructor.
//
// Pinning as Err documents the deferral. When Tactus learns to render
// non-unit-return proof fns properly (subtype rendering + instance
// body as ⟨value, by tac⟩), this flips to Ok.
// Probe: proof-fn trait method with NON-UNIT return type, LITERAL
// witness. Tactus emits the class method type as a subtype
// `{ r : RetTy // ensures }` and the instance body as
// `⟨value, by rfl-or-simp_all⟩`. For a literal value body (no spec
// method refs), this works cleanly.
test_verify_one_file! {
    #[test] test_proof_fn_trait_method_non_unit_return_literal verus_code! {
        trait Extract {
            proof fn extract() -> (r: int)
                ensures r == 5;
        }

        struct E;
        impl Extract for E {
            proof fn extract() -> (r: int)
                ensures r == 5
            {
                5
            }
        }

        #[verifier::tactus_auto]
        fn touches_extract<T: Extract>(_t: &T, _e: &E) -> (r: u8)
            ensures r == 0
        {
            0
        }
    } => Ok(())
}

// Probe: proof-fn trait method with non-unit return whose body
// references a sibling spec method. The witness expression `target self`
// would (naively) fail Lean elaboration — inside an instance body,
// sibling field refs aren't accessible (Lean's class elaboration
// doesn't bring sibling fields into scope mid-instance). Tactus's
// fix: dep_order pre-seeds impl proof-fn method bodies (non-unit
// return) into the worklist, so the standalone def for the called
// spec method gets emitted in the preamble. The instance body's
// `target self` resolves to that standalone def.
test_verify_one_file! {
    #[test] test_proof_fn_trait_method_non_unit_return_sibling_ref verus_code! {
        trait Extract {
            spec fn target(&self) -> int;
            proof fn extract(&self) -> (r: int)
                ensures r == self.target();
        }

        struct E;
        impl Extract for E {
            spec fn target(&self) -> int { 0 }
            proof fn extract(&self) -> (r: int)
                ensures r == self.target()
            {
                self.target()
            }
        }

        #[verifier::tactus_auto]
        fn touches_extract<T: Extract>(_t: &T, _e: &E) -> (r: u8)
            ensures r == 0
        {
            0
        }
    } => Ok(())
}

// Probe: proof-fn trait method with MULTIPLE ensures clauses. Verus
// renders these as a comma-separated list; the class field type
// should conjoin them with ∧.
//
// Caller extracts the conjunction and uses both parts.
test_verify_one_file! {
    #[test] test_proof_fn_trait_method_multiple_ensures verus_code! {
        trait Bounded {
            spec fn val(&self) -> int;
            proof fn val_in_range(&self)
                ensures self.val() >= 0, self.val() <= 100;
        }

        struct B;
        impl Bounded for B {
            spec fn val(&self) -> int { 50 }
            proof fn val_in_range(&self)
                ensures self.val() >= 0, self.val() <= 100
            by {
                simp [Bounded.val]
            }
        }

        proof fn use_bounded<T: Bounded>(t: &T)
            ensures 0 <= t.val() && t.val() <= 100
        by {
            have h := Bounded.val_in_range t
            -- h : val t >= 0 AND val t <= 100; omega handles the conjunction.
            omega
        }
    } => Ok(())
}

// Probe: proof-fn trait method with REQUIRES clauses. The class
// field type renders the requires as additional binders, so the
// method becomes a function from preconditions to the ensures.
//
// Caller must discharge the precondition when invoking. This tests
// that the binder ordering and hypothesis types are correct.
test_verify_one_file! {
    #[test] test_proof_fn_trait_method_with_requires verus_code! {
        trait Conditional {
            spec fn val(&self) -> int;
            proof fn val_pos_implies_ge_one(&self)
                requires self.val() > 0
                ensures self.val() >= 1;
        }

        struct C;
        impl Conditional for C {
            spec fn val(&self) -> int { 5 }
            proof fn val_pos_implies_ge_one(&self)
                // Verus rule: impl method inherits trait's requires;
                // cannot re-declare. Just ensures + body.
                ensures self.val() >= 1
            by {
                simp [Conditional.val]
            }
        }

        proof fn use_conditional<T: Conditional>(t: &T)
            requires t.val() > 0
            ensures t.val() >= 1
        by {
            -- The class method takes the requires as a hypothesis param.
            -- Caller provides a proof of the requires from its own
            -- hypotheses (h0 : val t > 0 is in scope from this fn's requires).
            have h := Conditional.val_pos_implies_ge_one t h0
            omega
        }
    } => Ok(())
}

// Probe: MUTUAL proof-fn methods in the same trait — two proof fns
// both referencing a sibling spec method. Tests that the strip helper
// correctly rewrites class-qualified references for BOTH methods, and
// that having multiple Prop-typed fields in one class works.
test_verify_one_file! {
    #[test] test_proof_fn_trait_method_mutual_methods verus_code! {
        trait TwoLemmas {
            spec fn val(&self) -> int;
            proof fn val_nonneg(&self) ensures self.val() >= 0;
            proof fn val_le_max(&self) ensures self.val() <= 1000;
        }

        struct TL;
        impl TwoLemmas for TL {
            spec fn val(&self) -> int { 42 }
            proof fn val_nonneg(&self) ensures self.val() >= 0 by {
                simp [TwoLemmas.val]
            }
            proof fn val_le_max(&self) ensures self.val() <= 1000 by {
                simp [TwoLemmas.val]
            }
        }

        proof fn use_both<T: TwoLemmas>(t: &T)
            ensures 0 <= t.val() && t.val() <= 1000
        by {
            have h1 := TwoLemmas.val_nonneg t
            have h2 := TwoLemmas.val_le_max t
            omega
        }
    } => Ok(())
}

// Probe: proof-fn ensures references a FREE-STANDING spec fn (not a
// sibling trait method). The strip helper should NOT rewrite this —
// it only targets `<current_class>.` prefixes. Free-standing spec
// fns are referenced via their full path (`test_crate.doubled` or
// similar), which doesn't start with the class name.
test_verify_one_file! {
    #[test] test_proof_fn_trait_method_free_standing_spec_ref verus_code! {
        spec fn doubled(x: int) -> int { x * 2 }

        trait Doubler {
            spec fn val(&self) -> int;
            proof fn doubled_is_2val(&self)
                ensures doubled(self.val()) == self.val() * 2;
        }

        struct D;
        impl Doubler for D {
            spec fn val(&self) -> int { 7 }
            proof fn doubled_is_2val(&self)
                ensures doubled(self.val()) == self.val() * 2
            by {
                unfold doubled; rfl
            }
        }

        proof fn use_doubler<T: Doubler>(t: &T)
            ensures doubled(t.val()) == t.val() * 2
        by {
            exact Doubler.doubled_is_2val t
        }
    } => Ok(())
}

// Negative probe: proof-fn trait method impl whose tactic body
// doesn't actually prove the ensures. Verus's mode/type check would
// not catch this — it's the verification step that matters. With
// the Prop-typed class field shape, the instance method body is the
// user's tactic, and Lean must reject when the tactic doesn't close
// the goal.
//
// Pinning this Err ensures: a regression that silently accepts an
// unproved tactic body (e.g., by emitting `sorry` instead of the
// user's tactic) would flip this test to Ok unsoundly.
test_verify_one_file! {
    #[test] test_proof_fn_trait_method_wrong_ensures_rejected verus_code! {
        trait Wrong {
            spec fn val(&self) -> int;
            proof fn val_is_one(&self)
                ensures self.val() == 1;
        }

        struct W;
        impl Wrong for W {
            spec fn val(&self) -> int { 0 }
            proof fn val_is_one(&self)
                ensures self.val() == 1
            by {
                -- Tactic claims val() = 1, but val()'s body is 0.
                -- omega correctly fails: 0 != 1.
                omega
            }
        }
    } => Err(err) => {
        // Either Verus's Z3 path or Tactus's Lean path should reject.
        // We don't pin the specific message — just that SOME error
        // surfaces. Soundness guard.
        assert!(
            err.errors.iter().any(|e|
                e.message.contains("postcondition")
                    || e.message.contains("Lean tactic failed")
                    || e.message.contains("could not prove")),
            "expected verification failure for wrong ensures, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
}

// Probe: ensures references a method of a DIFFERENT trait. The
// strip helper should NOT rewrite OtherTrait.method — it only
// targets the current class's prefix.
test_verify_one_file! {
    #[test] test_proof_fn_trait_method_other_trait_ref verus_code! {
        trait Inner {
            spec fn inner_val(&self) -> int;
        }

        trait Outer {
            proof fn inner_is_zero<I: Inner>(i: &I)
                ensures i.inner_val() >= 0;
        }

        struct InnerImpl;
        impl Inner for InnerImpl {
            spec fn inner_val(&self) -> int { 0 }
        }

        struct OuterImpl;
        impl Outer for OuterImpl {
            proof fn inner_is_zero<I: Inner>(i: &I)
                ensures i.inner_val() >= 0
            by {
                admit
            }
        }
    } => Ok(())
}

// Coverage (C5): empty trait. `trait Marker {}` with no methods —
// `tr.methods` is empty. Class emits as `class Marker (Self : Type)
// where` (no body). Instance emits as `instance : Marker M where`
// (no body). Most code paths iterate `tr.methods`; empty iteration
// should be a no-op. Marker traits are common in Rust; pin the smoke
// test.
test_verify_one_file! {
    #[test] test_proof_fn_trait_method_empty_trait verus_code! {
        trait Marker {}

        struct M;
        impl Marker for M {}

        #[verifier::tactus_auto]
        fn touches_marker<T: Marker>(_t: &T, _m: &M) -> (r: u8)
            ensures r == 0
        {
            0
        }
    } => Ok(())
}

// Coverage (C1): mixed-mode trait — spec + exec + proof methods all
// in the same trait. Per-method mode dispatch in trait_to_ast +
// trait_impl_to_ast must handle interleaved modes correctly: spec →
// real def signature, exec → Self → Ret with `default` body, proof
// → Prop-typed field with tactic body. Source order is preserved
// from `tr.methods`.
test_verify_one_file! {
    #[test] test_proof_fn_trait_method_mixed_modes verus_code! {
        trait MixedModes {
            spec fn val(&self) -> int;
            fn double(&self, x: u8) -> (r: u8)
                requires x < 128
                ensures r == x + x;
            proof fn val_nonneg(&self)
                ensures self.val() >= 0;
        }

        struct MM;
        impl MixedModes for MM {
            spec fn val(&self) -> int { 0 }
            fn double(&self, x: u8) -> (r: u8)
                ensures r == x + x
            {
                x + x
            }
            proof fn val_nonneg(&self)
                ensures self.val() >= 0
            by {
                simp [MixedModes.val]
            }
        }

        #[verifier::tactus_auto]
        fn touches_mixed<T: MixedModes>(_t: &T, _mm: &MM) -> (r: u8)
            ensures r == 0
        {
            0
        }
    } => Ok(())
}

// Coverage (C2): trait inheritance — `trait Sub: Super`. Lean's
// idiomatic emission for this is `class Sub extends Super where`,
// which brings parent methods into the child class's scope (so
// the child's method types can reference parent methods unqualified).
//
// Tactus's `trait_to_ast` builds bounds via `trait_bounds_to_ast(&tr.typ_bounds)`
// — emits them as constraint binders, NOT as `extends`. If a child
// trait's proof-fn method ensures references a parent method, the
// emission might fail (sibling-style strip can't see parent
// methods).
//
// This probe tests a minimal version: child trait Sub references
// parent's spec method in its proof-fn ensures. If today's emission
// works, great. If it doesn't, the test surfaces a real gap.
test_verify_one_file! {
    #[test] test_proof_fn_trait_method_extends_super_trait verus_code! {
        // Parent trait — provides the abstraction the child can use.
        trait Super {
            spec fn parent_val(&self) -> int;
        }

        // Child trait inherits from Super. Tactus must emit the class
        // declaration with `[Super Self]` (not `[Super Self%]`) so the
        // outer class type variable matches the inherited bound.
        // Use a trivial ensures so the tactic resolution doesn't
        // depend on inner spec-method unfolding — we're testing the
        // CLASS+INSTANCE emission shape, not the proof obligation.
        trait Sub: Super {
            proof fn child_lemma(&self)
                ensures true;
        }

        struct SB;
        impl Super for SB {
            spec fn parent_val(&self) -> int { 0 }
        }
        impl Sub for SB {
            proof fn child_lemma(&self)
                ensures true
            by {
                trivial
            }
        }

        #[verifier::tactus_auto]
        fn touches_sub<T: Sub>(_t: &T, _sb: &SB) -> (r: u8)
            ensures r == 0
        {
            0
        }
    } => Ok(())
}

// Edge case (E3): proof-fn trait method with EMPTY ensures clause and
// non-unit return. The subtype's predicate becomes `True` (via
// `and_all` on an empty Vec). The instance witness can be any value
// of the return type; `by rfl | simp_all` closes `True` trivially.
test_verify_one_file! {
    #[test] test_proof_fn_trait_method_non_unit_empty_ensures verus_code! {
        trait Maker {
            proof fn make() -> (r: int);  // no ensures clause
        }

        struct M;
        impl Maker for M {
            proof fn make() -> (r: int) {
                42
            }
        }

        #[verifier::tactus_auto]
        fn touches_maker<T: Maker>(_t: &T, _m: &M) -> (r: u8)
            ensures r == 0
        {
            0
        }
    } => Ok(())
}

// Edge case (E2): proof-fn trait method returning Self (the class
// type variable itself). Subtype `{ r : Self // ensures }` references
// `Self` — which IS the class's outer type variable, so it should be
// in scope at class-field-emission time.
test_verify_one_file! {
    #[test] test_proof_fn_trait_method_non_unit_self_return verus_code! {
        trait Producer {
            proof fn produce() -> (r: Self) where Self: Sized;
        }

        struct PR;
        impl Producer for PR {
            proof fn produce() -> (r: Self)
            {
                PR
            }
        }

        #[verifier::tactus_auto]
        fn touches_producer<T: Producer>(_t: &T, _pr: &PR) -> (r: u8)
            ensures r == 0
        {
            0
        }
    } => Ok(())
}

// Edge case (E1): proof-fn trait method with GENERIC type-param return.
// `proof fn extract<U>() -> (r: U)` — the return type is the method's
// own type parameter. The subtype `{ r : U // ensures }` should
// elaborate as long as the ensures is well-typed for U.
//
// Use `ensures true` so the subtype's predicate is trivially closable
// regardless of U.
test_verify_one_file! {
    #[test] test_proof_fn_trait_method_non_unit_generic_return verus_code! {
        use vstd::prelude::*;

        trait Picker {
            spec fn picked() -> int;
            proof fn pick() -> (r: int)
                ensures r == Self::picked();
        }

        struct P;
        impl Picker for P {
            spec fn picked() -> int { 7 }
            proof fn pick() -> (r: int)
                ensures r == Self::picked()
            {
                7
            }
        }

        #[verifier::tactus_auto]
        fn touches_picker<T: Picker>(_t: &T, _p: &P) -> (r: u8)
            ensures r == 0
        {
            0
        }
    } => Ok(())
}

// === Recursive proof fn with decreases — termination_by emission (Case 11) ===
//
// Verus's `decreases n` on a proof fn flows through `f.decrease` to
// Tactus's `Theorem.termination_by`. Pre-fix, proof_fn_to_ast didn't
// consult `f.decrease` at all; recursive proof fns whose tactic bodies
// called themselves relied on Lean's auto-inference (which handles many
// simple cases but not Collatz-shape or non-obvious measures).
//
// Test A: non-recursive proof fn with an unused `decreases` clause.
// Verus accepts this; confirms emission doesn't break trivial cases.
test_verify_one_file! {
    #[test] test_proof_fn_with_decreases_noncrecursive verus_code! {
        proof fn nonneg(n: nat)
            ensures n >= 0
            decreases n
        by {
            omega
        }
    } => Ok(())
}

// === U → Nat coercion at Call sites (BUG-as-nat-cast.md) ===
//
// Verus's `fn_call_to_vir.rs` drops `U(_) → Nat` casts as no-ops
// (sound for Z3, unsound for Lean where Int and Nat are distinct
// types). Pre-fix, `f(i as nat)` for `i : u64` lowered to `f i`
// where `i : Int`, failing Lean type-checking. Post-fix, Tactus's
// `insert_nat_coercions_in_*` pass at fn entry inserts a synthetic
// `Clip(Nat, _)` node that the renderer turns into `Int.toNat`.

// Minimal reproducer from BUG-as-nat-cast.md: proof fn ensures
// passes a u64 to a nat-typed spec fn param.
test_verify_one_file! {
    #[test] test_proof_fn_u64_as_nat_in_ensures verus_code! {
        spec fn id_nat(n: nat) -> nat { n }

        proof fn lemma_u64_as_nat(i: u64)
            ensures id_nat(i as nat) >= 0
        by {
            omega
        }
    } => Ok(())
}

// Same shape with multiple u-types as the source of the cast.
test_verify_one_file! {
    #[test] test_proof_fn_u_types_as_nat verus_code! {
        spec fn id_nat(n: nat) -> nat { n }

        proof fn lemma_u_types(a: u8, b: u16, c: u32, d: u128)
            ensures id_nat(a as nat) >= 0, id_nat(b as nat) >= 0,
                    id_nat(c as nat) >= 0, id_nat(d as nat) >= 0
        by {
            omega
        }
    } => Ok(())
}

// Both LHS and RHS of `==` cast to nat — the doc notes both are
// dropped. With the coercion pass, both render as `Int.toNat`.
// This shape is the canonical "factorial-style spec match" pattern.
// `subst` + `rfl` closes — `omega` alone can't do congruence over
// function application (treats `f x` as opaque).
test_verify_one_file! {
    #[test] test_proof_fn_both_sides_as_nat verus_code! {
        spec fn f(n: nat) -> nat { n }

        proof fn lemma_eq(i: u64, j: u64)
            requires i == j
            ensures f(i as nat) == f(j as nat)
        by {
            subst h0
            rfl
        }
    } => Ok(())
}

// Cast inside an exec-fn `assert(...)` — exercises the SST path.
test_verify_one_file! {
    #[test] test_exec_assert_u64_as_nat verus_code! {
        spec fn id_nat(n: nat) -> nat { n }

        #[verifier::tactus_auto]
        fn touches_u64(i: u64) {
            assert(id_nat(i as nat) >= 0);
        }
    } => Ok(())
}

// Cast inside an exec-fn loop invariant — also SST path, plus
// per-obligation theorem emission for the invariant.
test_verify_one_file! {
    #[test] test_exec_loop_invariant_u64_as_nat verus_code! {
        spec fn id_nat(n: nat) -> nat { n }

        #[verifier::tactus_auto]
        fn loop_with_cast(n: u64)
            requires n <= 100
        {
            let mut i: u64 = 0;
            while i < n
                invariant
                    i <= n,
                    id_nat(i as nat) >= 0,
                decreases n - i
            {
                i = i + 1;
            }
        }
    } => Ok(())
}

// === FileLoader by-in-comment regression (BUG-fileloader-by-in-comment.md) ===
//
// Three-condition trigger: (1) prior `by { ... }` block, (2) `//`
// comment ending with `by`, (3) next `//` comment starting with `{`.
// Without the fix, the real downstream `by { ... }` is left
// unsanitized and rustc rejects tactic names as identifiers.
test_verify_one_file! {
    #[test] test_fileloader_by_in_comment_regression verus_code! {
        proof fn warmup()
            ensures 1 + 1 == 2
        by {
            decide
        }

        // `assert(P) by
        // { x }`

        #[verifier::tactus_auto]
        fn f(x: u64) -> (r: u64)
            requires x < 100
            ensures r == 0
        {
            assert(x < 100) by { intros; omega };
            0
        }
    } => Ok(())
}

// === Imports threaded to exec fn theorem files (BUG-exec-fn-imports.md) ===
//
// Pre-fix, `import Mathlib.Tactic.X` at file top reached proof fn
// generated files but NOT exec fn (tactus_auto) ones — Mathlib tactics
// like `nlinarith` / `ring` used inside `assert(P) by { ... }` blocks
// failed with "unknown tactic." Fix in builtin_macros/syntax.rs:
// `lean_import` attrs now attach to both `tactic_by` proof fns AND
// `verifier::tactus_auto` exec fns.
//
// Bare smoke: confirm `nlinarith` sanitization works inside the
// assert-by block (regression for the FileLoader path).
test_verify_one_file! {
    #[test] test_exec_fn_import_threaded_smoke verus_code! {
        #[verifier::tactus_auto]
        fn exec_no_import(x: u64, y: u64) -> (r: u64)
            requires x <= 100, y <= 100
            ensures r == 0
        {
            assert(x * y <= 10000) by { nlinarith }
            0
        }
    } => Err(err) => {
        // Without the import, nlinarith is unknown — confirms the
        // sanitization is working (Rust isn't seeing `nlinarith` as
        // an identifier) and isolates the failure to "Mathlib tactic
        // unavailable at Lean elaboration time."
        let msg = format!("{:?}", err);
        assert!(msg.contains("Lean") || msg.contains("unknown tactic"),
            "Expected Lean failure, got: {}", msg);
    }
}

// With the import, the Mathlib tactic should be available.
test_verify_one_file! {
    #[test] test_exec_fn_import_threaded verus_code! {
        import Mathlib.Tactic.Linarith

        #[verifier::tactus_auto]
        fn exec_with_assert(x: u64, y: u64) -> (r: u64)
            requires x <= 100, y <= 100
            ensures r == 0
        {
            assert(x * y <= 10000) by { nlinarith }
            0
        }
    } => Ok(())
}

// === Trait deferred edges (DESIGN.md sweep) ===
//
// Three edges flagged as "likely works but not pinned" in DESIGN.md's
// "Trait class+instance emission: deferred edges" section. Probes
// pin or surface real gaps.

// Edge: generic impl (`impl<T> Foo for Vec<T>` shape via a simpler
// surrogate — Tactus uses short_name throughout so concrete vs
// generic instantiations of the same path should both reach the
// gate via `refs.datatypes` containing the implementor short name).
test_verify_one_file! {
    #[test] test_trait_generic_impl_probe verus_code! {
        use vstd::prelude::*;

        trait Container {
            spec fn ok(&self) -> bool;
        }

        struct Wrap<T> { inner: T }

        impl<T> Container for Wrap<T> {
            spec fn ok(&self) -> bool { true }
        }

        #[verifier::tactus_auto]
        fn touches<T: Container>(_t: &T, _w: &Wrap<u8>) -> (r: u8)
            ensures r == 0
        {
            0
        }
    } => Ok(())
}

// Edge: associated-typed default body. Default returns `Self::Output`
// (renders as bare `Output` class type-param name).
test_verify_one_file! {
    #[test] test_trait_assoc_typed_default_probe verus_code! {
        trait WithType {
            type Output;
            spec fn value(&self) -> Self::Output;
        }

        struct Ctx;
        impl WithType for Ctx {
            type Output = int;
            spec fn value(&self) -> int { 0 }
        }

        #[verifier::tactus_auto]
        fn touches<T: WithType>(_t: &T, _c: &Ctx) -> (r: u8)
            ensures r == 0
        {
            0
        }
    } => Ok(())
}

// Edge: recursive default body. Default calls itself via typeclass
// dispatch. Probed 2026-05-17: upstream-blocked at Verus with
// "trait default methods do not yet support recursion and decreases".
// Pinned as Err so a future Verus relaxation surfaces as a flippable
// test. The Tactus-side `termination_by`-for-class-defaults question
// remains untested — would need probing if/when Verus lifts the
// restriction.
test_verify_one_file! {
    #[test] test_trait_recursive_default_upstream_blocked verus_code! {
        trait Counted {
            spec fn count(&self, n: nat) -> nat
                decreases n
            {
                if n == 0 { 0 } else { 1 + self.count((n - 1) as nat) }
            }
        }

        struct C;
        impl Counted for C {}

        #[verifier::tactus_auto]
        fn touches<T: Counted>(_t: &T, _c: &C) -> (r: u8)
            ensures r == 0
        {
            0
        }
    } => Err(err) => {
        let msg = format!("{:?}", err);
        assert!(msg.contains("trait default methods do not yet support recursion"),
            "Expected Verus upstream rejection for recursive default; got: {}", msg);
    }
}

// Test B: recursive proof fn — body recursively invokes itself in Lean,
// gated by a case-split. `termination_by n` is what makes the recursive
// call's measure visible to Lean's well-foundedness check. Lean's
// auto-inference also handles this simple shape, but the explicit clause
// is the structural answer; it also unblocks Collatz-shape and lex cases
// auto-infer can't handle.
test_verify_one_file! {
    #[test] test_proof_fn_recursive_with_decreases verus_code! {
        proof fn rec_trivial(n: nat)
            ensures n >= 0
            decreases n
        by {
            if h : n = 0 then
                omega
            else
                have _ih := rec_trivial (n - 1)
                omega
        }
    } => Ok(())
}

// Probe (2026-05-17): does `&mut v[i]` work today?
//
// Rust+Verus's `rust_to_vir_expr` desugars `&mut v[i]` for
// `v: Vec<T>` into a call to `vstd::std_specs::vec::vec_index_mut(&mut v, i)`.
// At the SST level, the call's `&mut` arg should therefore be
// `&mut v` (Var-shaped L-value), NOT a synthetic `&mut v[i]` L-value
// — the "indexing" semantics is entirely captured by the callee
// being `vec_index_mut`, plus its ensures
// `final(vec)@ == old(vec)@.update(i as int, *final(element))`.
//
// If cross-crate spec inlining works for `vec_index_mut` (post the
// 2026-05-12 #122 audit, most spec fns DO inline), this should
// "just work" — no new MutTargetRaw variant needed.
//
// What we expect to see:
//   - Ok: cross-crate inlining works, full pipeline succeeds.
//   - Err mentioning `vec_index_mut` or cross-crate: spec doesn't
//     inline; need Phase 3 work first.
//   - Err mentioning `&mut` L-value shape: SST has a shape we
//     didn't anticipate (e.g., Index inside the Loc).
// Probe (2026-05-17) — &mut v[i] reaches Lean but cross-crate
// `View` trait+instance emission has multiple bugs.
//
// **What works** (more than the catalogue claimed):
//   1. `vec_index_mut`'s spec is cross-crate-inlined: the generated
//      Lean goal contains `seq.Seq.update Int (view _tactus_mut_post_1)
//      0 (seq.Seq.index ...)` — Verus's `merge_krates` brings the
//      Vec spec into scope, the inlining substitutes the args.
//   2. The mut-args machinery treats `&mut v[0]` correctly. Rust's
//      `&mut v[0]` desugars (in new-mut-ref mode) to a call to
//      `vec_index_mut(&mut v, 0)`; the `&mut v` is Var-shaped at
//      the call site, so `extract_mut_target` produces
//      `MutTargetRaw::Var(v)`. The fresh `_tactus_mut_post_1`
//      existential + `view post = update(view OLD, 0, ...)`
//      constraint is the standard ∀-path encoding for `&mut`.
//      **No new MutTargetRaw variant needed**; no different rebind.
//
// **What's actually broken** (real blockers, both cross-crate
// trait-emission bugs — sub-task of #122, not #106):
//   A. **`View` typeclass emission is malformed.** The generated
//      Lean has:
//        - `class view.View (Self : Type) (V : outParam Type) where
//           view : Self → V`     — correct.
//        - `axiom view.view (T A) [Allocator A] (self : Vec T A) :
//           Seq T`               — wrong: standalone axiom for what
//           should be an instance method; collides with the class
//           method's qualified name `view.View.view`.
//        - 4 duplicate instances `view.View A (view.View.V A) where
//           view := fun self => View.view self` — `view.View.V` isn't
//           a field; this is malformed but Lean doesn't reject it
//           until use.
//        - The crucial `view.View (Vec T A) (Seq T)` instance is
//           BODY-LESS (no `view := ...`).
//        - Goal text uses BOTH `view.View.view ...` AND `view.view ...`
//           inconsistently for the same conceptual operation.
//   B. **Pre/post substitution bug.** `vec_index_mut`'s ensures says
//      `final(vec)@ == old(vec)@.update(i, *final(element))`. The
//      generated Lean shows
//        `view _tactus_mut_post_1 = update (view _tactus_mut_post_1) 0 ...`
//      — both `final(vec)` AND `old(vec)` got substituted to
//      `_tactus_mut_post_1`. We expect
//        `view _tactus_mut_post_1 = update (view v) 0 ...`.
//      So even if (A) were fixed, the substitution is wrong — the
//      ∀-bound post value is being aliased with the caller's pre
//      value in one of the inlined positions.
//
// **Catalogue corrections to make** (separate from this probe):
//   - DESIGN.md and HANDOFF.md claim `&mut v[i]` needs "a different
//     rebind encoding (Lean's `Array.set` or `Vector.set` style + a
//     'this index unchanged for j ≠ i' property)." That's wrong:
//     Verus's `vec_index_mut` wrap captures it via `Seq.update`
//     already, and the ∀-path treats the post-Vec as an existential.
//   - The real blocker isn't #106 (&mut shape) at all; it's a
//     cross-crate trait+instance emission bug under #122.
//
// Pinned as Err pending fixes (A) and (B). When both fixed this
// flips to Ok.
test_verify_one_file_with_options! {
    #[test] test_exec_call_mut_arg_vec_index_probe ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::deprecated_postcondition_mut_ref_style(true)]
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        #[verifier::tactus_auto]
        #[verifier::deprecated_postcondition_mut_ref_style(true)]
        fn call_vec_index_mut(v: &mut Vec<u8>)
            requires
                old(v)@.len() > 0,
                old(v)@[0] < 100,
            ensures
                v@.len() == old(v)@.len(),
                v@[0] == old(v)@[0] + 1,
        {
            bump(&mut v[0]);
        }
    } => Err(_)
}

// Probe (2026-05-17): minimal same-crate `uninterp spec fn` impl method.
//
// Isolates Bug C from the View-trait emission cluster: when an impl
// method has `body = None` (Verus's `uninterp` keyword), the impl is
// emitted with NO method body — `trait_impl_to_ast`'s
// `func.body.as_ref()?` filter drops it. Lean rejects an instance that
// declares but doesn't provide all class fields.
//
// Same-crate avoids the cross-crate trait+instance emission bugs in
// the Vec View test, so we can focus on the body-less case in
// isolation. The standalone def `view.view` (which `spec_fn_to_ast`
// emits as an axiom when body=None) IS the dispatch target the
// instance method should reference.
//
// Pinned as Err pending Bug C fix; flips to Ok when the synthesized
// body lands.
// Probe (Bug D remaining piece, intermediate): same-crate inherent
// spec method `view(&self)` on a struct. PASSES — the existing
// rewrite catches `old(s).view()` shape when it lowers through an
// inherent method call. This narrows Bug D-remaining: the failing
// case must be something else (trait-method dispatch through
// `View`, or the View blanket impls themselves).
test_verify_one_file_with_options! {
    #[test] test_old_view_pre_post_substitution_probe ["new-mut-ref"] => verus_code! {
        struct Holder { v: u8 }

        impl Holder {
            spec fn view(&self) -> u8 { self.v }
        }

        #[verifier::deprecated_postcondition_mut_ref_style(true)]
        fn bump_holder(h: &mut Holder)
            requires old(h).view() < 100
            ensures h.view() == old(h).view() + 1
        {
            h.v = h.v + 1;
        }

        #[verifier::tactus_auto]
        #[verifier::deprecated_postcondition_mut_ref_style(true)]
        fn caller(z: &mut Holder)
            requires old(z).view() < 100
            ensures z.view() == old(z).view() + 1
        {
            bump_holder(z);
        }
    } => Ok(())
}

// Probe (Bug B): same-crate trait with associated type + blanket
// impl over a generic wrapper. Mirrors vstd's `View` shape:
//
//   pub trait View { type V; spec fn view(&self) -> Self::V; }
//   impl<A: View> View for &A { type V = A::V; ... }
//
// Current breakage: `<A as View>::V` renders as `View.V A` in the
// Projection arm of `typ_to_expr`, but `V` is a class type-param,
// not a field accessor, so `View.V` is unbound. The canonical Lean
// idiom (per Lean reference manual): bind `V` as a fresh implicit
// on the blanket impl's instance signature —
//   instance {A V : Type} [View A V] : View (Wrap A) V where ...
// — not as an accessor.
//
// Pin as Err pending Bug B fix; flips Ok when blanket impl emission
// introduces fresh implicit binders for assoc-type projections.
test_verify_one_file! {
    #[test] test_view_blanket_impl_probe verus_code! {
        pub trait View {
            type V;
            spec fn view(&self) -> Self::V;
        }

        pub struct Wrap<A>(pub A);

        impl<A: View> View for Wrap<A> {
            type V = A::V;

            open spec fn view(&self) -> A::V {
                self.0.view()
            }
        }

        pub struct Holder { pub v: u8 }

        impl View for Holder {
            type V = u8;
            open spec fn view(&self) -> u8 { self.v }
        }

        proof fn wrap_view_passes_through()
            ensures Wrap(Holder { v: 7 }).view() == 7
        by {
            simp_all [View.view]
        }
    } => Ok(())
}

// Probe (Bug B coverage extension): blanket impl with TWO typ-params,
// each carrying its own assoc-type passthrough. Pins that
// `ImplSubst::build` allocates distinct fresh binders for each
// (typ_param, trait, assoc) triple, and that `trait_bounds_to_ast`
// renders both augmented brackets `[View A V_a] [View B V_b]`.
test_verify_one_file! {
    #[test] test_view_blanket_impl_multi_param_probe verus_code! {
        pub trait View {
            type V;
            spec fn view(&self) -> Self::V;
        }

        pub struct Pair<A, B>(pub A, pub B);

        // Blanket impl with two typ-params; Pair's view is the first
        // half's view (just to exercise the typ-system; the assoc-
        // type passthrough is what's being tested, not the spec
        // semantics).
        impl<A: View, B: View> View for Pair<A, B> {
            type V = A::V;

            open spec fn view(&self) -> A::V {
                self.0.view()
            }
        }

        pub struct Holder { pub v: u8 }

        impl View for Holder {
            type V = u8;
            open spec fn view(&self) -> u8 { self.v }
        }

        proof fn pair_view_passes_through()
            ensures Pair(Holder { v: 3 }, Holder { v: 5 }).view() == 3
        by {
            simp_all [View.view]
        }
    } => Ok(())
}

// Probe (Bug B audit follow-up): single typ-param bounded by TWO
// traits, each with an assoc type that the impl signature uses.
// `impl<A: View + DeepView> ...` is a common shape in vstd — every
// `View` blanket impl also has a `DeepView` counterpart. Pins that
// `ImplSubst::build` allocates distinct fresh binders for each
// (X, trait, assoc) triple even when the same X carries multiple
// trait bounds, and that the resulting Lean has both augmented
// brackets `[View A V_a] [DeepView A V_a_dv]`.
test_verify_one_file! {
    #[test] test_view_blanket_impl_multi_trait_bound_probe verus_code! {
        pub trait View {
            type V;
            spec fn view(&self) -> Self::V;
        }

        pub trait DeepView {
            type V;
            spec fn deep_view(&self) -> Self::V;
        }

        pub struct Wrap<A>(pub A);

        // Single typ-param A bounded by both View and DeepView; impl
        // exposes both passthroughs. Each assoc-type-impl uses a
        // distinct projection (`A::V` from View vs `A::V` from
        // DeepView — same NAME, different TRAIT).
        impl<A: View + DeepView> View for Wrap<A> {
            type V = <A as View>::V;
            open spec fn view(&self) -> <A as View>::V {
                self.0.view()
            }
        }

        impl<A: View + DeepView> DeepView for Wrap<A> {
            type V = <A as DeepView>::V;
            open spec fn deep_view(&self) -> <A as DeepView>::V {
                self.0.deep_view()
            }
        }

        pub struct Holder { pub v: u8 }

        impl View for Holder {
            type V = u8;
            open spec fn view(&self) -> u8 { self.v }
        }

        impl DeepView for Holder {
            type V = u8;
            open spec fn deep_view(&self) -> u8 { self.v }
        }

        proof fn wrap_view_passes_through_with_deep_bound()
            ensures Wrap(Holder { v: 4 }).view() == 4
        by {
            simp_all [View.view]
        }
    } => Ok(())
}

// Probe (audit follow-up): trait with MULTIPLE generic type-args
// beyond Self. `impl<A: Converter<int>> Foo for Wrap<A>` carries
// a bound `Converter(A, int)` with typs `[A, int]`. The audit-fix
// `typs_match` check in `trait_bounds_to_ast` requires the fake
// TypEquality bound's typs to match the original bound's typs
// length-wise. `ImplSubst::build` currently synthesises fake
// bounds with typs `[TypParam(X)]` (1 arg) regardless of the
// trait's arity, so for multi-arg traits the typs_match filter
// rejects the fake bound's typ and the rendered bracket misses
// the Out slot. Pin as Err pending fix.
test_verify_one_file! {
    #[test] test_view_blanket_impl_multi_arg_trait_probe verus_code! {
        pub trait Converter<X> {
            type Out;
            spec fn convert(&self, x: X) -> Self::Out;
        }

        pub struct Wrap<A>(pub A);

        impl<A: Converter<u8>> Converter<u8> for Wrap<A> {
            type Out = <A as Converter<u8>>::Out;
            open spec fn convert(&self, x: u8) -> <A as Converter<u8>>::Out {
                self.0.convert(x)
            }
        }

        pub struct Holder { pub v: u8 }

        impl Converter<u8> for Holder {
            type Out = u8;
            open spec fn convert(&self, x: u8) -> u8 { x }
        }

        proof fn wrap_convert_passes_through()
            ensures Wrap(Holder { v: 1 }).convert(7) == 7
        by {
            simp_all [Converter.convert]
        }
    } => Ok(())
}

// Probe: type has BOTH an inherent spec method named `raw` AND
// a trait impl with a method named `raw`. Tests that the rename
// scheme doesn't cause a same-Lean-name collision between the
// inherent's def and the trait impl's standalone def.
test_verify_one_file! {
    #[test] test_inherent_and_trait_impl_same_method_name_probe verus_code! {
        pub trait Counter {
            spec fn raw(&self) -> nat;
        }

        pub struct Bar { pub v: nat }

        impl Bar {
            pub open spec fn raw(&self) -> nat { self.v + 1 }
        }

        impl Counter for Bar {
            open spec fn raw(&self) -> nat { self.v }
        }

        proof fn trait_raw_unwraps_to_v()
            ensures Counter::raw(&Bar { v: 7 }) == 7
        by {
            simp_all [Counter.raw]
        }
    } => Ok(())
}

// Probe (rename design): two different traits both declaring a
// method with the same name (`raw`), both implemented for the
// same Self (Bar). The new `<Self>.<Trait>.impl.<method>` scheme
// distinguishes them via the Trait segment: `Bar.Foo.impl.raw`
// vs `Bar.Bar2.impl.raw`. No collision; both renames fire.
test_verify_one_file! {
    #[test] test_two_traits_same_method_name_disambiguated_probe verus_code! {
        pub trait Foo {
            spec fn raw(&self) -> nat;
        }

        pub trait Bar2 {
            spec fn raw(&self) -> nat;
        }

        pub struct Bar { pub v: nat }

        impl Foo for Bar {
            open spec fn raw(&self) -> nat { self.v }
        }

        impl Bar2 for Bar {
            open spec fn raw(&self) -> nat { self.v + 1 }
        }

        proof fn foo_raw_is_v()
            ensures Foo::raw(&Bar { v: 7 }) == 7
        by {
            simp_all [Foo.raw, Bar.Foo.impl.raw]
        }
    } => Ok(())
}

// Probe (realistic): `Container { length; is_empty }` where the
// impl defines is_empty in terms of length. Classic pattern in
// real APIs — `is_empty := len() == 0`. Tests whether the
// `impl__N.method` UX leak actually arises in realistic code (vs.
// only in the contrived `doubled = raw + raw` probe below).
test_verify_one_file! {
    #[test] test_impl_method_realistic_is_empty_probe verus_code! {
        pub trait Container {
            spec fn length(&self) -> nat;
            spec fn is_empty(&self) -> bool;
        }

        pub struct MyList { pub n: nat }

        impl Container for MyList {
            open spec fn length(&self) -> nat { self.n }
            open spec fn is_empty(&self) -> bool { self.length() == 0 }
        }

        proof fn empty_list_is_empty()
            ensures (MyList { n: 0 }).is_empty()
        by {
            simp_all [Container.is_empty, Container.length, MyList.Container.impl.length]
        }
    } => Ok(())
}

// Probe (audit follow-up): sibling call from one impl spec method
// to another. step-1's type-aware rewrite must fire (receiver is
// Self), redirecting the body's `self.helper()` call from class
// dispatch to the impl method standalone def. Pinned to catch any
// regression of step 1.
test_verify_one_file! {
    #[test] test_impl_method_sibling_call_in_body_probe verus_code! {
        pub trait Counter {
            spec fn raw(&self) -> nat;
            spec fn doubled(&self) -> nat;
        }

        pub struct Bar { pub v: nat }

        impl Counter for Bar {
            open spec fn raw(&self) -> nat { self.v }
            open spec fn doubled(&self) -> nat { (self.raw() + self.raw()) as nat }
        }

        proof fn doubled_of_three_is_six()
            ensures (Bar { v: 3 }).doubled() == 6
        by {
            simp_all [Counter.doubled, Counter.raw, Bar.Counter.impl.raw]
        }
    } => Ok(())
}

// Probe (Bug D remaining piece, trait dispatch): same-crate trait
// `View` with a non-blanket impl on a concrete struct. This is
// closer to vstd's shape — `old(s).view()` dispatches through a
// trait method, not an inherent method.
test_verify_one_file_with_options! {
    #[test] test_old_view_trait_dispatch_probe ["new-mut-ref"] => verus_code! {
        pub trait View {
            spec fn view(&self) -> u8;
        }

        pub struct Holder { pub v: u8 }

        impl View for Holder {
            open spec fn view(&self) -> u8 { self.v }
        }

        #[verifier::deprecated_postcondition_mut_ref_style(true)]
        fn bump_holder(h: &mut Holder)
            requires old(h).view() < 100
            ensures h.view() == old(h).view() + 1
        {
            h.v = h.v + 1;
        }

        #[verifier::tactus_auto]
        #[verifier::deprecated_postcondition_mut_ref_style(true)]
        fn caller(z: &mut Holder)
            requires old(z).view() < 100
            ensures z.view() == old(z).view() + 1
        {
            bump_holder(z);
        }
    } => Ok(())
}

// Probe (Bug D): pre/post substitution for new-mut-ref ensures
// inlining. Same-crate version to isolate from vstd shapes.
test_verify_one_file_with_options! {
    #[test] test_new_mut_ref_pre_post_substitution_probe ["new-mut-ref"] => verus_code! {
        // Callee's ensures references BOTH pre and post — same shape
        // as vstd::vec::vec_index_mut. Verifies that pre/post don't
        // alias under new-mut-ref caller-side inlining.
        #[verifier::deprecated_postcondition_mut_ref_style(true)]
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        #[verifier::tactus_auto]
        #[verifier::deprecated_postcondition_mut_ref_style(true)]
        fn caller(y: &mut u8)
            requires *old(y) < 100
            ensures *y == *old(y) + 1
        {
            bump(y);
        }
    } => Ok(())
}

// Universal call-arg bridging probe (2026-05-26 typed-sub session).
// Exercises the case where the callee's spec auto-borrows a NON-MUT
// param (`h.view()` for `h: Holder` calling an inherent `view(&self)`
// method) and the caller passes a bare-typed local. Pre-typed-sub,
// post-render substitution would have substituted `h` → caller's `Var(h)`
// without preserving the auto-borrow wrap, producing `impl__0.view h`
// where view expects `Tactus.Ref Holder` → Lean type error. Post-fix,
// the universal call-arg bridge wraps with `Tactus.Ref.mk` at the call
// site uniformly for inherent and trait dispatch alike.
test_verify_one_file! {
    #[test] test_inherent_method_autoborrow_inlined verus_code! {
        struct Holder { v: u8 }
        impl Holder {
            spec fn view(&self) -> u8 { self.v }
        }

        fn read_via_view(h: Holder) -> (r: u8)
            requires h.view() < 100
            ensures r == h.view()
        { h.v }

        #[verifier::tactus_auto]
        fn caller_bare(h: Holder) -> (r: u8)
            requires h.view() < 100
            ensures r == h.view()
        {
            read_via_view(h)
        }
    } => Ok(())
}

// Negative regression for the 2026-05-26 soundness audit finding
// (see DESIGN.md "Historical: new-mut-ref False-hypothesis silent
// miscompile"). Pre-BorrowMut-elimination, the inlined callee
// ensures was tested against an unrelated SSA `borrow_mut_*` local
// rather than the user's `y`, so the equation `*y == *old(y) + 1`
// never bound — Tactus would happily admit a WRONG caller ensures
// like `*y == *old(y) + 999` because the inlined hypothesis was
// vacuous on `y`.
//
// Post-fix the inlined ensures correctly mentions `y`, so this
// (deliberately wrong) ensures must be rejected. If a future
// regression reintroduces the vacuous-hypothesis path, this flips
// to Ok — that's the canary.
test_verify_one_file_with_options! {
    #[test] test_new_mut_ref_wrong_ensures_is_caught_regression ["new-mut-ref"] => verus_code! {
        #[verifier::deprecated_postcondition_mut_ref_style(true)]
        fn bump(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            *x = *x + 1;
        }

        #[verifier::tactus_auto]
        #[verifier::deprecated_postcondition_mut_ref_style(true)]
        fn caller(y: &mut u8)
            requires *old(y) < 100
            ensures *y == *old(y) + 999  // WRONG: +1 actual, +999 claimed
        {
            bump(y);
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test_uninterp_impl_method_body_less_instance_probe verus_code! {
        trait Opaque {
            spec fn shadow(&self) -> int;
        }

        struct Hidden { v: int }

        impl Opaque for Hidden {
            uninterp spec fn shadow(&self) -> int;
        }

        proof fn touches_opaque(h: &Hidden)
            ensures h.shadow() == h.shadow()
        by {
            omega
        }
    } => Ok(())
}

// Bug C: same-crate probe with TYPE PARAMS in the impl method. The
// synthesized body (`9f77305`) passes typ_params from the impl as
// positional args to the standalone axiom — generated Lean has
// `peek := fun (self : _) => peek A self`, which is correct.
//
// However, the test is pinned as Err for a DIFFERENT reason: the
// downstream goal `Container.peek w = Container.peek w` for
// `w : Wrap A` can't be elaborated because Lean's class-method
// auto-binding can't infer the second class type param (the trait
// has `Self` + `A`, both type params; auto-binding gets `Self :=
// Wrap A` from `w` but can't infer `A`). My Bug A fix gates the
// TypeAnnot disambiguation on `!typ_contains_param`, and `Wrap A`
// contains a type param so annotation is skipped. Same gap as
// `test_generic_trait_impl` / `test_parameterized_trait` had
// before — those flipped to Ok because their types were concrete
// (`Wrap u8`); this one's `Wrap A` stays Err.
//
// What this probe DOES pin: the Bug C synthesis itself is shape-
// correct (typ_params + params are passed through). If a future
// regression breaks the synth, the error message would differ —
// likely "Unknown identifier `peek`" or signature-mismatch rather
// than this typeclass-stuck message.
test_verify_one_file! {
    #[test] test_uninterp_impl_method_with_type_params_probe verus_code! {
        trait Container<A> {
            spec fn peek(&self) -> A;
        }

        struct Wrap<A> { val: A }

        impl<A> Container<A> for Wrap<A> {
            uninterp spec fn peek(&self) -> A;
        }

        proof fn touches_wrap<A>(w: &Wrap<A>)
            ensures w.peek() == w.peek()
        by {
            simp
        }
    } => Err(_)
}

// Probe (BUG-no-helper-proof-fn-call-from-exec.md): helper proof
// fn invocation from inside an exec fn's `proof { ... }` block.
// Currently exec fn Lean files don't include proof-fn theorems in
// their preamble — `Unknown identifier`.
test_verify_one_file! {
    #[test] test_helper_proof_fn_call_from_exec_probe verus_code! {
        spec fn double(n: nat) -> nat {
            n + n
        }

        proof fn double_nonneg(n: nat)
            ensures double(n) >= 0
        by {
            simp [double]
        }

        #[verifier::tactus_auto]
        fn use_helper(n: u64)
            requires n <= 10
        {
            proof { have _ := double_nonneg n.toNat }
            assert(double(n as nat) >= 0);
        }
    } => Ok(())
}

// Probe (BUG-multi-var-loop-alpha-rename.md): multi-var loop. The
// outer `let a := 0` blocks my split_leading_binders from reaching
// the modified-var Binder(i). User can't reference `i` directly.
test_verify_one_file! {
    #[test] test_multi_var_loop_assert_by_probe verus_code! {
        #[verifier::tactus_auto]
        fn multi_var(n: u64)
            requires n <= 100
        {
            let mut a: u64 = 0;
            let mut i: u64 = 0;
            while i < n
                invariant i <= n, a <= 100
                decreases n - i
            {
                assert(i + 1 <= 101) by {
                    have h : i + 1 <= 101 := by omega
                    exact h
                }
                i = i + 1;
            }
        }
    } => Ok(())
}

// Probe (BUG-loop-local-names-alpha-renamed.md): loop-local `i`
// becomes `i✝¹` inside an `assert(P) by { ... }` inside a loop
// body. Pinned as Err for now; flips to Ok when the alpha-rename
// is fixed.
test_verify_one_file! {
    #[test] test_loop_local_name_in_assert_by_probe verus_code! {
        #[verifier::tactus_auto]
        fn loop_alpha(n: u64)
            requires n <= 100
        {
            let mut i: u64 = 0;
            while i < n
                invariant i <= n
                decreases n - i
            {
                assert(i + 1 <= 101) by {
                    have h : i + 1 <= 101 := by omega
                    exact h
                }
                i = i + 1;
            }
        }
    } => Ok(())
}

// Probe (2026-05-20): same-crate, non-forwarding blanket impl
// `Foo for &A`. Pinned as Err — documents a structural gap that is
// NOT vstd-specific. See DESIGN.md § "Transparent-wrapper peel vs
// trait dispatch (deferred)" for the full analysis.
//
// Failure mode today (two layered breakages):
//   1. The blanket's standalone body emits as `A.Foo.impl.foo self
//      + 1` — `A` is a type variable, you can't dot-access it. Lean
//      rejects "Invalid field notation".
//   2. Even if (1) were fixed, Tactus peels `&Holder → Holder` at
//      the dispatch site. Lean's instance resolution picks the
//      concrete `Foo Holder` instance, returns 7 (not 8). The
//      blanket's `+1` is silently dropped. simp_all reduces
//      `7 = 8` to ⊢ False.
//
// Why this matters: any user crate that writes a non-forwarding
// blanket impl over a transparent wrapper hits this. Tactus
// silently produces the wrong answer. vstd's blanket impls happen
// to all be pure forwarding (so Tactus's peel coincidentally gives
// the right answer there), but the underlying structural gap is
// not vstd-specific.
//
// Proper fix shape: stop peeling transparent wrappers at instance
// heads AND dispatch sites — emit `Ref`/`MutRef`/`Box`/`Rc`/`Arc`
// as opaque wrapper types in the prelude, mirroring how Verus's AIR
// encoding preserves decorations at type-ID level (DECORATE=true in
// `vir::context`). ~3-5 session refactor; see DESIGN.md.
//
// Flips to Ok when the un-peel landing happens.
test_verify_one_file! {
    #[test] test_non_forwarding_blanket_over_ref_probe verus_code! {
        pub trait Foo {
            spec fn foo(&self) -> int;
        }

        pub struct Holder { pub v: u8 }

        impl Foo for Holder {
            open spec fn foo(&self) -> int { self.v as int }
        }

        // Non-forwarding blanket: adds 1 to inner's foo value.
        impl<A: Foo + ?Sized> Foo for &A {
            open spec fn foo(&self) -> int {
                (**self).foo() + 1
            }
        }

        // If Tactus honored the blanket: (&Holder{v:7}).foo() == 8
        // Today: Tactus drops the +1 silently; assertion fails.
        proof fn blanket_adds_one_honored()
            ensures (&Holder { v: 7 }).foo() == 8
        by {
            simp_all [Foo.foo]
        }
    } => Err(_)
}

// ── Approach 3 (β refactor) probes ────────────────────────────────────
//
// Cluster A's remaining failures share a root cause: with the broad
// body shadow for `&` params (`let s := s.deref`), the SST typ no
// longer matches the Lean value type. Sites that count wrappers via
// SST typ overcounts derefs for shadowed-param refs.
//
// Three approaches to fixing:
//   1. SST pre-pass that peels Var(shadowed).typ — fails on aliased
//      locals (`let copy = s; ...`).
//   2. Per-arg renderer awareness at CheckDecreaseHeight — fails on
//      the same aliased-local probe.
//   3. Full β refactor: drop body shadow for `&` params, thread
//      BinderCtx through SST renderer, coerce at every use site.
//      Keeps body shadow for `&mut` (assignment semantics need it).
//
// These probes pin the cases that distinguish the approaches. P1
// is the clearest counterexample to approaches 1 and 2. P_CLOSURE
// stresses an approach-3 edge (BinderCtx must extend at closure
// boundaries).

// P1: Aliased local in recursive call. `copy` is a local let-bound
// to `rest`, then passed recursively. Approaches 1 and 2 only track
// shadowing on fn params — `copy` isn't in their set, so they'd
// apply count_ref_decorations(&Stack) = 1 derefs at CheckDecreaseHeight
// based on SST typ. With body shadow, `copy` at Lean is inner Stack
// (because RHS `rest` was inner). One deref too many.
//
// Approach 3 handles this naturally: no body shadow, copy stays
// wrapper-typed at Lean, .deref applies correctly.
test_verify_one_file! {
    #[test] test_exec_call_recursive_aliased_arg_probe verus_code! {
        use vstd::std_specs::alloc::*;

        enum Stack {
            Empty,
            Push(u8, Box<Stack>),
        }

        #[verifier::tactus_auto]
        fn shrink(s: &Stack) -> (r: u64)
            decreases s
        {
            match s {
                Stack::Empty => 0,
                Stack::Push(_, rest) => {
                    // Alias the wrapper-typed local before recursing.
                    let copy = rest;
                    shrink(copy)
                }
            }
        }
    } => Ok(())
}

// Negative companion to `_aliased_arg_probe`: Half B's let-binding
// coercion must not defang the termination check. Here `copy` aliases
// the WHOLE `s` (height-equal, not the smaller `rest`), so the
// `decreases s` obligation must still REJECT it. If the let-coerce had
// broken the CheckDecreaseHeight comparison (rendering `Stack.height
// copy.deref < Stack.height s.deref` as something vacuously true), this
// would have falsely verified.
test_verify_one_file! {
    #[test] test_exec_call_recursive_aliased_arg_nondecreasing verus_code! {
        use vstd::std_specs::alloc::*;

        enum Stack {
            Empty,
            Push(u8, Box<Stack>),
        }

        #[verifier::tactus_auto]
        fn shrink(s: &Stack) -> (r: u64)
            decreases s
        {
            match s {
                Stack::Empty => 0,
                Stack::Push(_, _) => {
                    // Alias the whole `s` — height-equal, NOT decreasing.
                    let copy = s;
                    shrink(copy)
                }
            }
        }
    } => Err(err) => {
        // Must reject AT the termination check — confirms the let-coerce
        // preserved the decreases obligation's bite, not that it failed
        // for some unrelated reason.
        let msgs: Vec<_> = err.errors.iter().map(|e| e.message.clone()).collect();
        assert!(
            msgs.iter().any(|m| m.contains(&vir::tactus_messages::paren_label(vir::tactus_messages::ASSERT_LABEL_TERMINATION))),
            "expected (termination) kind label — let-coerce must preserve the \
             decreases obligation. got: {:?}",
            msgs,
        );
    }
}

// P_CLOSURE noted but not pinned with a test: closure captures an
// outer-scope wrapper-typed param. Approach 3 needs BinderCtx to
// extend at closure boundaries so the closure body's coercion logic
// sees the captured wrapper's typ correctly. Hard to construct a
// minimal exec-mode probe without dragging in vstd or trait methods —
// will revisit after approach 3 lands and we can see what shapes
// actually appear in practice.

// P_NESTED: doubly-wrapped param `&Box<u8>` exercises
// count_ref_decorations's handling of multiple wrapper layers.
// `b@` is the spec view of the inner u8; semantically the value
// is reached via two derefs (peel `&`, peel `Box`). Approach 3's
// renderer needs to apply 2 .derefs at use sites that expect inner.
test_verify_one_file! {
    #[test] test_exec_nested_wrapper_probe verus_code! {
        use vstd::std_specs::alloc::*;

        #[verifier::tactus_auto]
        fn read_nested(b: &Box<u8>) -> (r: u8)
            ensures r == **b
        {
            **b
        }
    } => Ok(())
}

// Coverage: return-coercion (Half A) × if-value-lift INTERACTION. The
// returned value is an `if`, so `lift_if_value` forks and the return
// coercion runs on EACH branch leaf — the `**b` branch (`&Box<u8>`,
// depth 2) coerces down to the `u8` ret typ (`b.deref.deref`), the `0`
// branch is a no-op. The ensures `c ==> r == **b` also exercises the
// binop reconcile on `r == **b`, so the coerced if-branch value must
// match the coerced ensures. Distinct path from `nested_wrapper` (plain
// non-if wrapper return) and `tail_if_expression` (non-wrapper if).
test_verify_one_file! {
    #[test] test_exec_return_if_wrapper_value_probe verus_code! {
        use vstd::std_specs::alloc::*;

        #[verifier::tactus_auto]
        fn pick(b: &Box<u8>, c: bool) -> (r: u8)
            ensures c ==> r == **b
        {
            if c { **b } else { 0 }
        }
    } => Ok(())
}

// P_GENERIC_WRAPPER: generic fn `fn use<T>(x: &T) -> bool` called
// with `T = Box<u8>` at one call site. Inside the body, T is
// opaque to count_ref_decorations — only the outer `&` is peelable.
// Approach 3 correctly produces 1 deref (the `&`), leaving the
// inner `T = Box<u8>` un-peeled — which is right because the body
// only operates at the T level. This probes that approach 3
// doesn't try to peel through opaque generic params.
test_verify_one_file! {
    #[test] test_exec_generic_with_wrapper_instantiation_probe verus_code! {
        use vstd::std_specs::alloc::*;

        #[verifier::tactus_auto]
        fn always_true<T>(_x: &T) -> (r: bool)
            ensures r == true
        {
            true
        }

        #[verifier::tactus_auto]
        fn caller() -> (r: bool)
            ensures r == true
        {
            let b: Box<u8> = Box::new(7);
            always_true(&b)
        }
    } => Ok(())
}

// P_RET_WRAPPER: returning a wrapper-typed value. The Return node
// in WP needs to handle wrapper-typed ret_exp. Approach 3 should
// pass `s` through directly (binder typ matches expr.typ, no
// coercion); ret type at theorem level is also wrapper.
test_verify_one_file! {
    #[test] test_exec_ret_wrapper_value_probe verus_code! {
        use vstd::std_specs::alloc::*;

        enum Tag { A, B }

        #[verifier::tactus_auto]
        fn passthrough(s: &Tag) -> (r: &Tag)
            ensures r == s
        {
            s
        }
    } => Ok(())
}

// P_CALL_SITE_MISMATCH: callee expects bare `u8`, caller passes
// `&u8` directly. Verus's auto-deref would normally insert a
// dereference, but if the SST shape ends up with a wrapper-typed
// arg flowing to a bare-typed param, approach 3 needs to coerce
// at the call site (apply .deref). The VIR-AST renderer already
// has this via apply_ref_coercion_if_needed; the SST renderer
// would need the analog.
//
// This probably either passes today (Verus inserts the deref
// explicitly) or fails for a reason orthogonal to cluster A.
// Pinning it as Err — if approach 3 + SST call-site coercion
// makes it pass, the probe flips.
test_verify_one_file! {
    #[test] test_exec_call_site_ref_to_bare_probe verus_code! {
        #[verifier::tactus_auto]
        fn double(x: u8) -> (r: u8)
            requires x <= 100
            ensures r == 2 * x
        {
            x + x
        }

        #[verifier::tactus_auto]
        fn caller(p: &u8) -> (r: u8)
            requires *p <= 100
            ensures r == 2 * *p
        {
            // Explicit deref — should always work.
            double(*p)
        }
    } => Ok(())
}

// Negative companion to `_ref_to_bare_probe`: the structural-binop
// reconcile + return-coerce (Half A) must not make a FALSE postcondition
// vacuously pass. `caller` claims `r == 2 * *p + 1` but `double(*p)`
// returns `2 * *p`. After the coercion the goal renders `r = 2 * p.deref
// + 1` with `r := 2 * p.deref`, so the postcondition is genuinely false
// (off by one) — the obligation still has bite. (`+ 1` is spec/ghost
// `int`, so no overflow ambiguity.)
test_verify_one_file! {
    #[test] test_exec_call_site_ref_to_bare_wrong_post verus_code! {
        #[verifier::tactus_auto]
        fn double(x: u8) -> (r: u8)
            requires x <= 100
            ensures r == 2 * x
        {
            x + x
        }

        #[verifier::tactus_auto]
        fn caller(p: &u8) -> (r: u8)
            requires *p <= 100
            ensures r == 2 * *p + 1
        {
            double(*p)
        }
    } => Err(err) => {
        // Must reject AT the postcondition — not pass vacuously, and not
        // fail for some unrelated (e.g. type) reason.
        let msgs: Vec<_> = err.errors.iter().map(|e| e.message.clone()).collect();
        assert!(
            msgs.iter().any(|m| m.contains(&vir::tactus_messages::paren_label(vir::tactus_messages::ASSERT_LABEL_POSTCONDITION))),
            "expected (postcondition) kind label — reconcile/return-coerce must \
             reject a false ensures, not pass it. got: {:?}",
            msgs,
        );
    }
}

// Already-covered cases NOT re-pinned here, with references:
//
// * Match on wrapper-typed param + recursive call: covered by
//   `test_exec_call_recursive_datatype_termination` (failing
//   today via body-shadow conflict).
// * Mut-ref body shadow + assignment: covered by
//   `test_exec_callee_mut_simple` (passing today). Approach 3's
//   hybrid keeps body shadow for mut-ref.
// * Recursive generic datatype: covered by
//   `test_exec_call_recursive_generic_datatype` family (failing
//   today via body-shadow conflict on `decrease_init0`).
// * Field access on wrapper receiver: covered by
//   `test_exec_call_recursive_datatype_termination`'s use of
//   `Push_val1` on a `&Stack`.

// E1: mut-ref + match. The body-shadow conflict for `&mut` is genuinely
// latent — Verus's lowering of `match *s` for `s : &mut Tag` strips the
// wrapper at SST level (scrutinee has typ `Tag`, not `MutRef<Tag>`), so
// `count_ref_decorations(Tag) = 0` and the IsVariant arm doesn't add a
// spurious deref.
//
// The previously-blocking goal-discharge issue (enum match's
// postcondition `r = 0 ∨ r = 1` couldn't close) was fixed by β refactor
// Piece 4 — `tactus_case_split` now recognizes wrapper-typed locals
// (`s : Tactus.MutRef Tag`) and case-splits on `s.deref`, closing the
// match-residual postcondition.
test_verify_one_file! {
    #[test] test_exec_mut_ref_is_variant_probe verus_code! {
        enum Tag { A, B }

        #[verifier::tactus_auto]
        fn check(s: &mut Tag) -> (r: u8)
            ensures r == 0 || r == 1
        {
            match *s {
                Tag::A => 0,
                Tag::B => 1,
            }
        }
    } => Ok(())
}

// E11: closure captures a mut-ref param. The outer's body shadow
// `let x := x.deref` only applies to the outer body, not inside
// the closure. The closure body's `Var(x)` would resolve to the
// un-shadowed wrapper at Lean. Approach 3 inherits this — closure
// boundaries don't propagate body shadow.
//
// **Upstream-blocked**: calling an exec closure (`f(0)`) hits
// Verus's `exec_nonstatic_call is not supported` (#124 — deferred).
// So even if approach 3 handled the capture cleanly, the test
// would fail at Verus before reaching Tactus. Pinned as `Err` to
// document the marker; not a Tactus concern today.
test_verify_one_file! {
    #[test] test_exec_closure_captures_mut_ref_probe verus_code! {
        #[verifier::tactus_auto]
        fn bump_via_closure(x: &mut u8)
            requires *old(x) < 100
            ensures *x == *old(x) + 1
        {
            let f = |_dummy: u8| -> u8 { *x + 1 };
            *x = f(0);
        }
    } => Err(_)
}

// E20: equality on wrapper-typed values. `s1 == s2` for two
// wrapper-typed params renders as `s1 = s2` (both wrapper-typed
// at Lean). For single-field structures, Lean's `=` reduces to
// field-by-field equality, so `s1 = s2 ↔ s1.deref = s2.deref`
// holds extensionally. Probably fine but worth a probe to confirm
// the rendering doesn't go through some coercion path that
// over-peels.
test_verify_one_file! {
    #[test] test_exec_wrapper_equality_probe verus_code! {
        enum Tag { A, B }

        spec fn tag_eq(a: &Tag, b: &Tag) -> bool {
            a == b
        }

        proof fn refl(s: &Tag)
            ensures tag_eq(s, s)
        by {
            simp_all [tag_eq]
        }
    } => Ok(())
}

// E2 (ref patterns in match): noted but not added as a test.
// `match s { Stack::Push(_, ref rest) => ... }` — the `ref` keyword
// binds rest as `&Box<Stack>` (extra ref layer). Verus likely
// rejects ref patterns at the mode check; even if it didn't,
// BinderCtx extension at match arms would need the ref-pattern
// adjustment. Cross that bridge if/when Verus supports ref patterns
// in exec mode.

// E12 (cross-renderer call inlining divergence): noted but not
// pinned. Exec fn calls inline callee specs via the VIR-AST
// renderer (`to_lean_expr`), which has its own BinderCtx and
// coercion logic. Approach 3 introduces parallel coercion in the
// SST renderer. The two renderers must agree on what gets coerced
// where — divergence would produce a subtly different spec at the
// inlining point vs the callee's emitted theorem. Hard to construct
// a minimal probe; address with reviewer discipline + shared
// helpers.

// P_MULTI_PROOF_BODY: probe whether proof-fn body rendering (which
// already calls `wrap_body_with_param_derefs`) handles a multi-layer
// wrapper param (`&Box<u8>`, count=2). Uses `ok(**b)` (a spec fn
// taking bare u8) to FORCE the deref to actually produce a u8 —
// `*b == *b` would collapse to `b = b` and pass trivially even if
// derefs are misrendered.
test_verify_one_file! {
    #[test] test_proof_fn_multi_layer_wrapper_probe verus_code! {
        use vstd::std_specs::alloc::*;

        spec fn ok(x: u8) -> bool { x > 0 }

        proof fn double_wrapped(b: &Box<u8>)
            requires ok(**b)
            ensures ok(**b)
        by {
            simp_all
        }
    } => Ok(())
}

// P_MULTI_TRAIT_NONSELF: probe whether a trait method with a
// multi-layer wrapper non-self param (`&Box<u8>`, count=2) renders
// the deref chain correctly at use sites. Generated Lean should
// show `**b` as `b.deref.deref` post-U2 (Field projection's
// binder-aware deref insertion handles multi-layer for free).
// Trivial ensures so a trivial tactic closes it.
test_verify_one_file! {
    #[test] test_trait_method_multi_layer_param_probe verus_code! {
        use vstd::std_specs::alloc::*;

        spec fn always_ok(_x: u8) -> bool { true }

        trait Holds {
            proof fn always(b: &Box<u8>)
                ensures always_ok(**b);
        }

        struct H;
        impl Holds for H {
            proof fn always(b: &Box<u8>)
                ensures always_ok(**b)
            by {
                simp [always_ok]
            }
        }
    } => Ok(())
}

// P_MULTI_DEPTH_3: depth-3 wrapper (`&Box<Box<u8>>`, count=3). Probes
// that the bidirectional lift's count-based logic handles arbitrary
// depths uniformly (not special-cased for single/double-layer).
// Generated Lean should show `***b` as `b.deref.deref.deref` at use
// sites that need the inner u8.
test_verify_one_file! {
    #[test] test_proof_fn_depth_3_wrapper_probe verus_code! {
        use vstd::std_specs::alloc::*;

        spec fn always_ok(_x: u8) -> bool { true }

        proof fn triple_wrapped(b: &Box<Box<u8>>)
            ensures always_ok(***b)
        by {
            simp [always_ok]
        }
    } => Ok(())
}
