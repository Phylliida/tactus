//! End-to-end tests: generate Lean, invoke Lean, verify.
//!
//! Run: nix-shell -p lean4 --run "cargo test -p lean_verify --test integration"

use lean_verify::lean_process::check_lean_stdin;
use lean_verify::prelude::TACTUS_PRELUDE;

fn verify(lean: &str) {
    let full = format!("{}{}", TACTUS_PRELUDE, lean);
    match check_lean_stdin(&full) {
        Ok(r) => {
            for d in &r.diagnostics { eprintln!("[{}] {}", d.severity, d.data); }
            assert!(r.success, "Lean verification failed");
        }
        Err(e) => eprintln!("Lean not available, skipping: {}", e),
    }
}

fn reject(lean: &str) {
    let full = format!("{}{}", TACTUS_PRELUDE, lean);
    match check_lean_stdin(&full) {
        Ok(r) => {
            assert!(!r.success, "Expected Lean to reject this");
            assert!(r.diagnostics.iter().any(|d| d.severity == "error"));
        }
        Err(e) => eprintln!("Lean not available, skipping: {}", e),
    }
}

#[test]
fn test_double_and_lemma() {
    verify(r#"
@[irreducible] noncomputable def double (x : Nat) : Nat := x + x

theorem lemma_double_pos (x : Nat) (h0 : x > 0) : double x > x := by
  unfold double; omega
"#);
}

#[test]
fn test_add_comm() {
    verify("theorem add_comm (a : Int) (b : Int) : a + b = b + a := by omega\n");
}

#[test]
fn test_wrong_proof_fails() {
    reject("theorem wrong (x : Nat) : x + 1 = x := by omega\n");
}

#[test]
fn test_recursive_factorial() {
    verify(r#"
@[irreducible] noncomputable def factorial (n : Nat) : Nat :=
  if n = 0 then 1 else n * factorial (n - 1)
termination_by n

theorem factorial_pos (n : Nat) : factorial n > 0 := by
  induction n with
  | zero => unfold factorial; simp
  | succ n ih =>
    unfold factorial; split
    next h => omega
    next h => exact Nat.mul_pos (by omega) ih
"#);
}

#[test]
fn test_multiple_requires_ensures() {
    verify(r#"
theorem bounds (x : Int) (y : Int) (h0 : x > 0) (h1 : y > 0) :
    x + y > 0 ∧ x + y > 1 := by
  constructor <;> omega
"#);
}

#[test]
fn test_forall_quantifier() {
    verify(r#"
theorem forall_add_comm : ∀ (x y : Int), x + y = y + x := by
  intro x y; omega
"#);
}

#[test]
fn test_implies() {
    verify("theorem pos_add (x : Int) (h0 : x > 0) : x + 1 > 1 := by omega\n");
}
