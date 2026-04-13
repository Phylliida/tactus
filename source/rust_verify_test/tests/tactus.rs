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
