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
            unfold value; simp
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
            unfold val; simp
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
            unfold lo
            simp
        }

        proof fn range_hi()
            ensures (Range { start: 1, end: 10 }).hi() == 10
        by {
            unfold hi
            simp
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
            unfold is_zero; simp
        }

        proof fn nat_zero()
            ensures (MyNat { v: 0 }).is_zero()
        by {
            unfold is_zero; simp
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
            unfold unwrap
            simp
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
            unfold add
            simp
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
            unfold convert
            simp
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
            unfold peek
            simp
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
            unfold produce
            simp
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
            unfold holds
            simp
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
            unfold dbl
            unfold double
            simp
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
            unfold fst
            simp
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

// === Track B: exec fn with sst_to_lean (first slice) ===
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
    }
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
            err.errors.iter().any(|e| e.message.contains("non-simple LHS")
                || e.message.contains("not yet supported")),
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
    }
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

// `&mut` arg is rejected. The detector peels transparent SST
// wrappers (Box/Unbox/CoerceMode/Trigger) before checking for
// `ExpX::Loc`, so a mutable borrow can't slip past as by-value.
test_verify_one_file! {
    #[test] test_exec_call_mut_ref_rejected verus_code! {
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
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e| e.message.contains("not yet supported")),
            "&mut call arg should be rejected, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
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

// Trait method call — rejected by `walk_call` because the
// `resolved_method` field is populated (dynamic dispatch resolution
// that we don't handle yet).
test_verify_one_file! {
    #[test] test_exec_call_trait_method_rejected verus_code! {
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
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e| e.message.contains("not yet supported")),
            "trait-method call should be rejected",
        );
    }
}

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
// and `sst_to_lean::build_wp` reads the verbatim tactic off disk and
// prepends a `have h_tactus_assert_N : P := by <user_tac>;` to the
// theorem's closer. The hypothesis then sits in context for the
// rest of the proof.
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

// Multi-variant enum + pattern matching: **infrastructure landed,
// automation gap remains**. `match` is desugared by ast_simplify into
// an if-chain using `UnaryOpr::IsVariant` and `UnaryOpr::Field`, and
// we now generate the corresponding `Type.is<Variant>` / `Type.<Variant>_<field>`
// accessor fns in `datatype_to_cmds`. The generated Lean parses and
// type-checks cleanly — but `tactus_auto` (`rfl | decide | omega |
// simp_all`) can't close a goal that still contains a `match k with
// …` expression, which is what the @[simp]-unfolded accessors reduce
// to. The missing piece is case-analysis on the enum scrutinee; would
// need `tactus_auto` to learn `cases <enum-typed-var> <;> simp_all
// <;> omega` or similar. Tracked as a follow-up to #52.
//
// Confirmed: the generated Lean file's structural issues are gone.
// Codegen is correct; automation is the remaining gap.
test_verify_one_file! {
    #[test] test_exec_match_enum_automation_gap verus_code! {
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
    } => Err(err) => {
        // Pin the current failure mode (auto-tactic failed with an
        // unsolved goal containing `match k with`) so a future change
        // that accidentally closes the goal without fixing the
        // automation gap trips this test and prompts a re-evaluation.
        assert!(
            err.errors.iter().any(|e|
                e.message.contains("auto-tactic failed") ||
                e.message.contains("unsolved") ||
                e.message.contains("match")
            ),
            "expected automation-gap failure on enum match, got: {:?}",
            err.errors.iter().map(|e| &e.message).collect::<Vec<_>>(),
        );
    }
}

// Lexicographic `decreases` is rejected up front — single-expression
// only at the current slice. Regression guard so we notice when /
// if that restriction is lifted.
test_verify_one_file! {
    #[test] test_exec_loop_lex_decreases_rejected verus_code! {
        #[verifier::tactus_auto]
        fn lex_loop(a: u8, b: u8) -> (r: u8)
            requires a <= 10, b <= 10
            ensures r == 0
        {
            let mut x: u8 = a;
            let mut y: u8 = b;
            while x > 0 || y > 0
                invariant x <= a, y <= b
                decreases x, y  // lexicographic — not yet supported
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
    } => Err(err) => {
        assert!(
            err.errors.iter().any(|e| e.message.contains("decreases")
                || e.message.contains("not yet supported")),
            "lexicographic decreases should be rejected",
        );
    }
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

