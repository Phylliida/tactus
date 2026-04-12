//! Translate Tactus IR functions to Lean 4 definitions and theorems.

use crate::ir::{Expr, Item, Param, ProofFn, SpecFn};
use crate::prelude::TACTUS_PRELUDE;
use crate::to_lean_expr::expr_to_lean;
use crate::to_lean_type::typ_to_lean;

/// Generate a complete Lean file from a list of items.
///
/// Items must be in dependency order (callees before callers).
/// The caller is responsible for topological sorting.
pub fn generate_lean_file(items: &[Item], imports: &[String]) -> String {
    let mut out = String::new();

    // Prelude
    out.push_str(TACTUS_PRELUDE);

    // User-specified imports
    for imp in imports {
        out.push_str(&format!("import {}\n", imp));
    }
    if !imports.is_empty() {
        out.push('\n');
    }

    // Items
    for item in items {
        match item {
            Item::SpecFn(f) => out.push_str(&spec_fn_to_lean(f)),
            Item::ProofFn(f) => out.push_str(&proof_fn_to_lean(f)),
        }
        out.push('\n');
    }

    out
}

/// Translate a spec fn to a Lean `noncomputable def`.
pub fn spec_fn_to_lean(f: &SpecFn) -> String {
    let mut out = String::new();

    // @[irreducible] for non-open spec fns
    if !f.is_open {
        out.push_str("@[irreducible] ");
    }
    out.push_str("noncomputable def ");

    // Name (use last segment for now)
    let name = lean_fn_name(&f.name);
    out.push_str(&name);

    // Type parameters
    for tp in &f.typ_params {
        out.push_str(&format!(" ({} : Type*)", tp));
    }

    // Parameters
    for p in &f.params {
        out.push_str(&format!(" ({} : {})", p.name, typ_to_lean(&p.typ)));
    }

    // Return type
    out.push_str(&format!(" : {} :=\n", typ_to_lean(&f.ret_typ)));

    // Body
    out.push_str(&format!("  {}\n", expr_to_lean(&f.body)));

    // Termination annotation for recursive functions
    if !f.decreases.is_empty() {
        if f.decreases.len() == 1 {
            out.push_str(&format!(
                "termination_by {}\n",
                expr_to_lean(&f.decreases[0])
            ));
        } else {
            let parts: Vec<String> = f.decreases.iter().map(expr_to_lean).collect();
            out.push_str(&format!("termination_by ({})\n", parts.join(", ")));
        }
    }

    out
}

/// Translate a proof fn to a Lean `theorem`.
pub fn proof_fn_to_lean(f: &ProofFn) -> String {
    let mut out = String::new();

    out.push_str("theorem ");

    // Name
    let name = lean_fn_name(&f.name);
    out.push_str(&name);

    // Type parameters
    for tp in &f.typ_params {
        out.push_str(&format!(" ({} : Type*)", tp));
    }

    // Parameters
    for p in &f.params {
        out.push_str(&format!(" ({} : {})", p.name, typ_to_lean(&p.typ)));
    }

    // Requires → hypotheses
    for (i, req) in f.requires.iter().enumerate() {
        out.push_str(&format!(" (h{} : {})", subscript(i), expr_to_lean(req)));
    }

    // Goal: ensures (conjoined if multiple)
    let goal = ensures_to_lean(&f.ensures, &f.named_return);
    out.push_str(&format!(" :\n    {} := by\n", goal));

    // Tactic body (verbatim, indented 2 spaces)
    for line in f.tactic_body.lines() {
        if line.trim().is_empty() {
            out.push('\n');
        } else {
            out.push_str(&format!("  {}\n", line));
        }
    }

    out
}

/// Construct the Lean goal from ensures clauses.
fn ensures_to_lean(ensures: &[Expr], named_return: &Option<(String, crate::ir::Typ)>) -> String {
    if ensures.is_empty() {
        return "True".to_string();
    }

    // If there's a named return, wrap ensures in a let or universal
    // For now, just emit the ensures directly (named return handling is Phase 2)
    let _ = named_return;

    if ensures.len() == 1 {
        expr_to_lean(&ensures[0])
    } else {
        // Conjoin: E₁ ∧ E₂ ∧ ... ∧ Eₙ
        let parts: Vec<String> = ensures.iter().map(expr_to_lean).collect();
        parts.join(" ∧ ")
    }
}

/// Generate a Unicode subscript index for hypothesis names.
fn subscript(i: usize) -> String {
    if i == 0 {
        "₀".to_string()
    } else {
        let digits = ["₀", "₁", "₂", "₃", "₄", "₅", "₆", "₇", "₈", "₉"];
        let mut result = String::new();
        let mut n = i;
        let mut parts = Vec::new();
        while n > 0 {
            parts.push(digits[n % 10]);
            n /= 10;
        }
        parts.reverse();
        for p in parts {
            result.push_str(p);
        }
        result
    }
}

/// Convert a fully-qualified name to a Lean identifier.
fn lean_fn_name(segments: &[String]) -> String {
    if segments.len() == 1 {
        segments[0].clone()
    } else {
        // Use dot-separated path for namespaced names
        segments.join(".")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::*;

    fn nat() -> Typ {
        Typ::Int(IntRange::Nat)
    }

    fn int() -> Typ {
        Typ::Int(IntRange::Int)
    }

    #[test]
    fn test_spec_fn_double() {
        let f = SpecFn {
            name: vec!["double".into()],
            typ_params: vec![],
            params: vec![Param {
                name: "x".into(),
                typ: nat(),
            }],
            ret_typ: nat(),
            body: Expr::Binary(
                BinOp::Add,
                Box::new(Expr::Var("x".into())),
                Box::new(Expr::Var("x".into())),
            ),
            is_open: false,
            decreases: vec![],
        };

        let lean = spec_fn_to_lean(&f);
        assert!(lean.contains("@[irreducible]"));
        assert!(lean.contains("noncomputable def double"));
        assert!(lean.contains("(x : Nat)"));
        assert!(lean.contains(": Nat :="));
        assert!(lean.contains("x + x"));
    }

    #[test]
    fn test_open_spec_fn() {
        let f = SpecFn {
            name: vec!["double".into()],
            typ_params: vec![],
            params: vec![Param {
                name: "x".into(),
                typ: nat(),
            }],
            ret_typ: nat(),
            body: Expr::Binary(
                BinOp::Add,
                Box::new(Expr::Var("x".into())),
                Box::new(Expr::Var("x".into())),
            ),
            is_open: true,
            decreases: vec![],
        };

        let lean = spec_fn_to_lean(&f);
        assert!(!lean.contains("@[irreducible]"));
        assert!(lean.contains("noncomputable def double"));
    }

    #[test]
    fn test_recursive_spec_fn() {
        let f = SpecFn {
            name: vec!["triangle".into()],
            typ_params: vec![],
            params: vec![Param {
                name: "n".into(),
                typ: nat(),
            }],
            ret_typ: nat(),
            body: Expr::If(
                Box::new(Expr::Binary(
                    BinOp::Eq,
                    Box::new(Expr::Var("n".into())),
                    Box::new(Expr::IntLit("0".into())),
                )),
                Box::new(Expr::IntLit("0".into())),
                Box::new(Expr::Binary(
                    BinOp::Add,
                    Box::new(Expr::Var("n".into())),
                    Box::new(Expr::Call(
                        "triangle".into(),
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
        };

        let lean = spec_fn_to_lean(&f);
        assert!(lean.contains("noncomputable def triangle"));
        assert!(lean.contains("if n = 0 then 0 else"));
        assert!(lean.contains("triangle (n - 1)"));
        assert!(lean.contains("termination_by n"));
    }

    #[test]
    fn test_proof_fn() {
        let f = ProofFn {
            name: vec!["lemma_double_pos".into()],
            typ_params: vec![],
            params: vec![Param {
                name: "x".into(),
                typ: nat(),
            }],
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
        };

        let lean = proof_fn_to_lean(&f);
        assert!(lean.contains("theorem lemma_double_pos"));
        assert!(lean.contains("(x : Nat)"));
        assert!(lean.contains("(h₀ : x > 0)"));
        assert!(lean.contains("double x > x := by"));
        assert!(lean.contains("  unfold double"));
        assert!(lean.contains("  omega"));
    }

    #[test]
    fn test_proof_fn_multiple_ensures() {
        let f = ProofFn {
            name: vec!["lemma_add_comm".into()],
            typ_params: vec![],
            params: vec![
                Param { name: "a".into(), typ: int() },
                Param { name: "b".into(), typ: int() },
            ],
            requires: vec![],
            ensures: vec![
                Expr::Binary(
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
                ),
                Expr::Binary(
                    BinOp::Eq,
                    Box::new(Expr::Binary(
                        BinOp::Mul,
                        Box::new(Expr::Var("a".into())),
                        Box::new(Expr::Var("b".into())),
                    )),
                    Box::new(Expr::Binary(
                        BinOp::Mul,
                        Box::new(Expr::Var("b".into())),
                        Box::new(Expr::Var("a".into())),
                    )),
                ),
            ],
            named_return: None,
            tactic_body: "constructor <;> omega".into(),
        };

        let lean = proof_fn_to_lean(&f);
        assert!(lean.contains("∧"), "Multiple ensures should use conjunction");
        assert!(lean.contains("constructor <;> omega"));
    }

    #[test]
    fn test_generate_lean_file() {
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
        assert!(lean.contains("set_option"));
        assert!(lean.contains("noncomputable def double"));
        assert!(lean.contains("theorem lemma_double_pos"));
        // Spec fn should come before proof fn
        let def_pos = lean.find("noncomputable def double").unwrap();
        let thm_pos = lean.find("theorem lemma_double_pos").unwrap();
        assert!(def_pos < thm_pos, "spec fn should precede proof fn");
    }

    #[test]
    fn test_subscripts() {
        assert_eq!(subscript(0), "₀");
        assert_eq!(subscript(1), "₁");
        assert_eq!(subscript(9), "₉");
        assert_eq!(subscript(10), "₁₀");
        assert_eq!(subscript(42), "₄₂");
    }
}
