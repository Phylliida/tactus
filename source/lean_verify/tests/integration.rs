//! End-to-end integration tests: generate Lean from IR, invoke Lean, verify.
//!
//! These tests require Lean 4 to be installed and on PATH.
//! Run with: nix-shell -p lean4 --run "cargo test -p lean_verify --test integration"

use lean_verify::ir::*;
use lean_verify::lean_process::check_lean_stdin;
use lean_verify::to_lean_fn::generate_lean_file;

fn nat() -> Typ {
    Typ::Int(IntRange::Nat)
}

fn int() -> Typ {
    Typ::Int(IntRange::Int)
}

/// The core end-to-end test:
/// spec fn double(x: nat) -> nat { x + x }
/// proof fn lemma_double_pos(x: nat) requires x > 0 ensures double(x) > x by { unfold double; omega }
#[test]
fn test_double_and_lemma() {
    let items = vec![
        Item::SpecFn(SpecFn {
            name: vec!["double".into()],
            typ_params: vec![],
            params: vec![Param { name: "x".into(), typ: nat() }],
            ret_typ: nat(),
            body: Expr::Binary(
                BinOp::Add,
                Box::new(Expr::Var("x".into())),
                Box::new(Expr::Var("x".into())),
            ),
            is_open: false,
            decreases: vec![],
        }),
        Item::ProofFn(ProofFn {
            name: vec!["lemma_double_pos".into()],
            typ_params: vec![],
            params: vec![Param { name: "x".into(), typ: nat() }],
            requires: vec![Expr::Binary(
                BinOp::Gt,
                Box::new(Expr::Var("x".into())),
                Box::new(Expr::IntLit("0".into())),
            )],
            ensures: vec![Expr::Binary(
                BinOp::Gt,
                Box::new(Expr::Call("double".into(), vec![Expr::Var("x".into())])),
                Box::new(Expr::Var("x".into())),
            )],
            named_return: None,
            tactic_body: "unfold double\nomega".into(),
        }),
    ];

    let lean = generate_lean_file(&items, &[]);
    eprintln!("=== Generated Lean ===\n{}\n=== End ===", lean);

    match check_lean_stdin(&lean) {
        Ok(result) => {
            for d in &result.diagnostics {
                eprintln!("[{}] {}", d.severity, d.data);
            }
            assert!(result.success, "Lean should verify double + lemma_double_pos");
        }
        Err(e) => {
            eprintln!("Lean not available, skipping: {}", e);
        }
    }
}

/// Test: proof fn add_comm(a: int, b: int) ensures a + b == b + a by { omega }
#[test]
fn test_add_comm() {
    let items = vec![
        Item::ProofFn(ProofFn {
            name: vec!["add_comm".into()],
            typ_params: vec![],
            params: vec![
                Param { name: "a".into(), typ: int() },
                Param { name: "b".into(), typ: int() },
            ],
            requires: vec![],
            ensures: vec![Expr::Binary(
                BinOp::Eq,
                Box::new(Expr::Binary(
                    BinOp::Add,
                    Box::new(Expr::Var("a".into())),
                    Box::new(Expr::Var("b".into())),
                )),
                Box::new(Expr::Binary(
                    BinOp::Add,
                    Box::new(Expr::Var("b".into())),
                    Box::new(Expr::Var("a".into())),
                )),
            )],
            named_return: None,
            tactic_body: "omega".into(),
        }),
    ];

    let lean = generate_lean_file(&items, &[]);
    eprintln!("=== Generated Lean ===\n{}\n=== End ===", lean);

    match check_lean_stdin(&lean) {
        Ok(result) => {
            for d in &result.diagnostics {
                eprintln!("[{}] {}", d.severity, d.data);
            }
            assert!(result.success, "Lean should verify a + b = b + a");
        }
        Err(e) => {
            eprintln!("Lean not available, skipping: {}", e);
        }
    }
}

/// Test: intentionally wrong proof should fail
#[test]
fn test_wrong_proof_fails() {
    let items = vec![
        Item::ProofFn(ProofFn {
            name: vec!["wrong".into()],
            typ_params: vec![],
            params: vec![Param { name: "x".into(), typ: nat() }],
            requires: vec![],
            ensures: vec![Expr::Binary(
                BinOp::Eq,
                Box::new(Expr::Binary(
                    BinOp::Add,
                    Box::new(Expr::Var("x".into())),
                    Box::new(Expr::IntLit("1".into())),
                )),
                Box::new(Expr::Var("x".into())),
            )],
            named_return: None,
            // omega can't prove x + 1 = x (it's false!)
            tactic_body: "omega".into(),
        }),
    ];

    let lean = generate_lean_file(&items, &[]);
    eprintln!("=== Generated Lean ===\n{}\n=== End ===", lean);

    match check_lean_stdin(&lean) {
        Ok(result) => {
            assert!(!result.success, "Lean should reject x + 1 = x");
            assert!(
                result.diagnostics.iter().any(|d| d.severity == "error"),
                "Should have error diagnostic"
            );
        }
        Err(e) => {
            eprintln!("Lean not available, skipping: {}", e);
        }
    }
}

/// Test: spec fn with if-then-else (recursive, with termination)
#[test]
fn test_recursive_spec_fn() {
    let items = vec![
        Item::SpecFn(SpecFn {
            name: vec!["factorial".into()],
            typ_params: vec![],
            params: vec![Param { name: "n".into(), typ: nat() }],
            ret_typ: nat(),
            body: Expr::If(
                Box::new(Expr::Binary(
                    BinOp::Eq,
                    Box::new(Expr::Var("n".into())),
                    Box::new(Expr::IntLit("0".into())),
                )),
                Box::new(Expr::IntLit("1".into())),
                Box::new(Expr::Binary(
                    BinOp::Mul,
                    Box::new(Expr::Var("n".into())),
                    Box::new(Expr::Call(
                        "factorial".into(),
                        vec![Expr::Binary(
                            BinOp::Sub,
                            Box::new(Expr::Var("n".into())),
                            Box::new(Expr::IntLit("1".into())),
                        )],
                    )),
                )),
            ),
            is_open: false,
            decreases: vec![Expr::Var("n".into())],
        }),
        Item::ProofFn(ProofFn {
            name: vec!["factorial_pos".into()],
            typ_params: vec![],
            params: vec![Param { name: "n".into(), typ: nat() }],
            requires: vec![],
            ensures: vec![Expr::Binary(
                BinOp::Gt,
                Box::new(Expr::Call("factorial".into(), vec![Expr::Var("n".into())])),
                Box::new(Expr::IntLit("0".into())),
            )],
            named_return: None,
            tactic_body: "induction n with\n| zero => unfold factorial; simp\n| succ n ih =>\n  unfold factorial\n  split\n  next h => omega\n  next h => exact Nat.mul_pos (by omega) ih".into(),
        }),
    ];

    let lean = generate_lean_file(&items, &[]);
    eprintln!("=== Generated Lean ===\n{}\n=== End ===", lean);

    match check_lean_stdin(&lean) {
        Ok(result) => {
            for d in &result.diagnostics {
                eprintln!("[{}] {}", d.severity, d.data);
            }
            assert!(
                result.success,
                "Lean should verify factorial > 0 by induction"
            );
        }
        Err(e) => {
            eprintln!("Lean not available, skipping: {}", e);
        }
    }
}

/// Test: multiple requires and ensures
#[test]
fn test_multiple_requires_ensures() {
    let items = vec![
        Item::ProofFn(ProofFn {
            name: vec!["bounds".into()],
            typ_params: vec![],
            params: vec![
                Param { name: "x".into(), typ: int() },
                Param { name: "y".into(), typ: int() },
            ],
            requires: vec![
                Expr::Binary(
                    BinOp::Gt,
                    Box::new(Expr::Var("x".into())),
                    Box::new(Expr::IntLit("0".into())),
                ),
                Expr::Binary(
                    BinOp::Gt,
                    Box::new(Expr::Var("y".into())),
                    Box::new(Expr::IntLit("0".into())),
                ),
            ],
            ensures: vec![
                Expr::Binary(
                    BinOp::Gt,
                    Box::new(Expr::Binary(
                        BinOp::Add,
                        Box::new(Expr::Var("x".into())),
                        Box::new(Expr::Var("y".into())),
                    )),
                    Box::new(Expr::IntLit("0".into())),
                ),
                Expr::Binary(
                    BinOp::Gt,
                    Box::new(Expr::Binary(
                        BinOp::Add,
                        Box::new(Expr::Var("x".into())),
                        Box::new(Expr::Var("y".into())),
                    )),
                    Box::new(Expr::IntLit("1".into())),
                ),
            ],
            named_return: None,
            tactic_body: "constructor <;> omega".into(),
        }),
    ];

    let lean = generate_lean_file(&items, &[]);
    eprintln!("=== Generated Lean ===\n{}\n=== End ===", lean);

    match check_lean_stdin(&lean) {
        Ok(result) => {
            for d in &result.diagnostics {
                eprintln!("[{}] {}", d.severity, d.data);
            }
            assert!(result.success, "Lean should verify bounds lemma");
        }
        Err(e) => {
            eprintln!("Lean not available, skipping: {}", e);
        }
    }
}
