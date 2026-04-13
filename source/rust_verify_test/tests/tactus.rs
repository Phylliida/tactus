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
