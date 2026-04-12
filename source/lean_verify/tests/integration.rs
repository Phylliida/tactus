//! End-to-end integration tests: generate Lean, invoke Lean, verify.
//!
//! These tests directly construct Lean text and invoke Lean to verify it.
//! This tests the full pipeline output without needing to construct VIR AST.
//! The VIR → Lean translation is tested separately via unit tests.
//!
//! Requires Lean 4 on PATH.
//! Run: nix-shell -p lean4 --run "cargo test -p lean_verify --test integration"

use lean_verify::lean_process::check_lean_stdin;
use lean_verify::prelude::TACTUS_PRELUDE;

fn check(lean: &str) {
    eprintln!("=== Generated Lean ===\n{}\n=== End ===", lean);
    match check_lean_stdin(lean) {
        Ok(r) => {
            for d in &r.diagnostics {
                eprintln!("[{}] {}", d.severity, d.data);
            }
            assert!(r.success, "Lean verification failed");
        }
        Err(e) => eprintln!("Lean not available, skipping: {}", e),
    }
}

fn check_fails(lean: &str) {
    match check_lean_stdin(lean) {
        Ok(r) => {
            assert!(!r.success, "Expected Lean to reject this");
            assert!(r.diagnostics.iter().any(|d| d.severity == "error"));
        }
        Err(e) => eprintln!("Lean not available, skipping: {}", e),
    }
}

fn with_prelude(body: &str) -> String {
    format!("{}{}", TACTUS_PRELUDE, body)
}

#[test]
fn test_double_and_lemma() {
    check(&with_prelude(r#"
@[irreducible] noncomputable def double (x : Nat) : Nat :=
  x + x

theorem lemma_double_pos (x : Nat) (h0 : x > 0) :
    double x > x := by
  unfold double
  omega
"#));
}

#[test]
fn test_add_comm() {
    check(&with_prelude(r#"
theorem add_comm (a : Int) (b : Int) :
    a + b = b + a := by
  omega
"#));
}

#[test]
fn test_wrong_proof_fails() {
    check_fails(&with_prelude(r#"
theorem wrong (x : Nat) :
    x + 1 = x := by
  omega
"#));
}

#[test]
fn test_recursive_factorial() {
    check(&with_prelude(r#"
@[irreducible] noncomputable def factorial (n : Nat) : Nat :=
  if n = 0 then 1 else n * factorial (n - 1)
termination_by n

theorem factorial_pos (n : Nat) :
    factorial n > 0 := by
  induction n with
  | zero => unfold factorial; simp
  | succ n ih =>
    unfold factorial
    split
    next h => omega
    next h => exact Nat.mul_pos (by omega) ih
"#));
}

#[test]
fn test_multiple_requires_ensures() {
    check(&with_prelude(r#"
theorem bounds (x : Int) (y : Int) (h0 : x > 0) (h1 : y > 0) :
    x + y > 0 ∧ x + y > 1 := by
  constructor <;> omega
"#));
}

#[test]
fn test_forall_quantifier() {
    check(&with_prelude(r#"
theorem forall_add_comm :
    ∀ (x y : Int), x + y = y + x := by
  intro x y
  omega
"#));
}

#[test]
fn test_implies() {
    check(&with_prelude(r#"
theorem pos_add (x : Int) (h0 : x > 0) :
    x + 1 > 1 := by
  omega
"#));
}
