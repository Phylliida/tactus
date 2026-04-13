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

        #[verifier::tactic]
        proof fn lemma_double_pos(x: nat)
            requires x > 0
            ensures double(x) > x
        {
            unfold(double);
            omega();
        }
    } => Ok(())
}

// === Wrong proof correctly rejected ===

test_verify_one_file! {
    #[test] test_wrong_proof_rejected verus_code! {
        #[verifier::tactic]
        proof fn wrong(x: nat)
            ensures x + 1 == x
        {
            omega();
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "Expected at least one error for wrong proof");
    }
}

// === add_comm with omega ===

test_verify_one_file! {
    #[test] test_add_comm verus_code! {
        #[verifier::tactic]
        proof fn add_comm(a: int, b: int)
            ensures a + b == b + a
        {
            omega();
        }
    } => Ok(())
}

// === Multiple requires and ensures (conjunction with ∧) ===

test_verify_one_file! {
    #[test] test_multiple_requires_ensures verus_code! {
        #[verifier::tactic]
        proof fn bounds(x: int, y: int)
            requires
                x > 0,
                y > 0,
            ensures
                x + y > 0,
                x + y > 1,
        {
            constructor();
            omega();
            omega();
        }
    } => Ok(())
}

// === Implies ===

test_verify_one_file! {
    #[test] test_implies verus_code! {
        #[verifier::tactic]
        proof fn pos_add(x: int)
            requires x > 0
            ensures x + 1 > 1
        {
            omega();
        }
    } => Ok(())
}

// === Spec fn with if-then-else ===

test_verify_one_file! {
    #[test] test_spec_ite verus_code! {
        spec fn abs(x: int) -> int {
            if x >= 0 { x } else { -x }
        }

        #[verifier::tactic]
        proof fn abs_nonneg(x: int)
            ensures abs(x) >= 0
        {
            unfold(abs);
            omega();
        }
    } => Ok(())
}

// === by { } syntax (DESIGN.md canonical form) ===

test_verify_one_file! {
    #[test] test_by_syntax verus_code! {
        spec fn double(x: nat) -> nat {
            x + x
        }

        proof fn lemma_double_by(x: nat)
            requires x > 0
            ensures double(x) > x
        by {
            unfold(double);
            omega();
        }
    } => Ok(())
}

// === by { } syntax with wrong proof (rejected) ===

test_verify_one_file! {
    #[test] test_by_syntax_rejected verus_code! {
        proof fn wrong_by(x: nat)
            ensures x + 1 == x
        by {
            omega();
        }
    } => Err(err) => {
        assert!(err.errors.len() >= 1, "Expected Lean to reject wrong proof");
    }
}

// === Recursive spec fn with termination_by ===

test_verify_one_file! {
    #[test] test_recursive_triangle verus_code! {
        spec fn triangle(n: nat) -> nat
            decreases n
        {
            if n == 0 { 0 } else { (n + triangle((n - 1) as nat)) as nat }
        }

        #[verifier::tactic]
        proof fn triangle_zero()
            ensures triangle(0) == 0
        {
            unfold(triangle);
            simp();
        }
    } => Ok(())
}
