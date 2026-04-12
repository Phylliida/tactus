//! Translate Tactus IR expressions to Lean 4 expression syntax.

use crate::ir::{BinOp, Expr, IntRange, Typ, UnOp};
use crate::to_lean_type::typ_to_lean;

/// Translate a Tactus expression to Lean 4 expression text.
pub fn expr_to_lean(expr: &Expr) -> String {
    match expr {
        Expr::Bool(true) => "True".to_string(),
        Expr::Bool(false) => "False".to_string(),
        Expr::IntLit(n) => {
            // Negative literals need parentheses in Lean
            if n.starts_with('-') {
                format!("({})", n)
            } else {
                n.clone()
            }
        }
        Expr::Var(name) => lean_safe_name(name),
        Expr::Binary(op, lhs, rhs) => {
            let l = expr_to_lean_parens(lhs, needs_parens_lhs(op));
            let r = expr_to_lean_parens(rhs, needs_parens_rhs(op));
            let op_str = binop_to_lean(op, &**lhs);
            format!("{} {} {}", l, op_str, r)
        }
        Expr::Unary(op, inner) => {
            let inner_str = expr_to_lean_parens(inner, true);
            match op {
                UnOp::Not => format!("¬{}", inner_str),
                UnOp::Neg => format!("-{}", inner_str),
            }
        }
        Expr::Call(name, args) => {
            if args.is_empty() {
                lean_safe_name(name)
            } else {
                let arg_strs: Vec<String> = args.iter().map(|a| expr_to_lean_parens(a, true)).collect();
                format!("{} {}", lean_safe_name(name), arg_strs.join(" "))
            }
        }
        Expr::If(cond, then_e, else_e) => {
            format!(
                "if {} then {} else {}",
                expr_to_lean(cond),
                expr_to_lean(then_e),
                expr_to_lean(else_e)
            )
        }
        Expr::Let(name, val, body) => {
            format!(
                "let {} := {}; {}",
                lean_safe_name(name),
                expr_to_lean(val),
                expr_to_lean(body)
            )
        }
        Expr::Forall(binders, body) => {
            let binder_strs: Vec<String> = binders
                .iter()
                .map(|(name, typ)| format!("({} : {})", lean_safe_name(name), typ_to_lean(typ)))
                .collect();
            format!("∀ {}, {}", binder_strs.join(" "), expr_to_lean(body))
        }
        Expr::Exists(binders, body) => {
            let binder_strs: Vec<String> = binders
                .iter()
                .map(|(name, typ)| format!("({} : {})", lean_safe_name(name), typ_to_lean(typ)))
                .collect();
            format!("∃ {}, {}", binder_strs.join(" "), expr_to_lean(body))
        }
    }
}

/// Translate a binary operator to its Lean syntax.
///
/// For EuclideanDiv/Mod on Int, uses Int.ediv/Int.emod.
/// For Nat, uses standard / and %.
fn binop_to_lean(op: &BinOp, _lhs: &Expr) -> &'static str {
    // TODO: For EuclideanDiv/Mod, check if operands are Int or Nat
    // and emit Int.ediv/Int.emod for Int. For now, use / and % which
    // are correct for Nat and close enough for Phase 1.
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::EuclideanDiv => "/",
        BinOp::EuclideanMod => "%",
        BinOp::Eq => "=",
        BinOp::Ne => "≠",
        BinOp::Le => "≤",
        BinOp::Lt => "<",
        BinOp::Ge => "≥",
        BinOp::Gt => ">",
        BinOp::And => "∧",
        BinOp::Or => "∨",
        BinOp::Implies => "→",
    }
}

/// Wrap expression in parens if needed.
fn expr_to_lean_parens(expr: &Expr, parens_needed: bool) -> String {
    if parens_needed && needs_outer_parens(expr) {
        format!("({})", expr_to_lean(expr))
    } else {
        expr_to_lean(expr)
    }
}

/// Does this expression need parentheses when used as an operand?
fn needs_outer_parens(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Binary(..) | Expr::If(..) | Expr::Let(..) | Expr::Forall(..) | Expr::Exists(..)
    )
}

/// Does the LHS of this operator need parentheses?
fn needs_parens_lhs(op: &BinOp) -> bool {
    // Implications and logical ops are right-associative in Lean
    matches!(op, BinOp::Implies)
}

/// Does the RHS of this operator need parentheses?
fn needs_parens_rhs(_op: &BinOp) -> bool {
    true // Conservative: always parenthesize RHS of binary ops
}

/// Make a name safe for Lean (avoid Lean keywords, handle special chars).
fn lean_safe_name(name: &str) -> String {
    // Lean reserved words that might conflict with Verus identifiers
    const LEAN_KEYWORDS: &[&str] = &[
        "def", "theorem", "lemma", "example", "abbrev", "instance", "class",
        "structure", "inductive", "where", "with", "match", "do", "return",
        "if", "then", "else", "let", "have", "show", "by", "at", "fun",
        "forall", "exists", "Type", "Prop", "Sort", "import", "open",
        "namespace", "section", "end", "variable", "universe",
    ];

    let clean = name.replace('@', "_").replace('#', "_");

    if LEAN_KEYWORDS.contains(&clean.as_str()) {
        format!("«{}»", clean) // Lean's escaped identifier syntax
    } else {
        clean
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::IntRange;

    #[test]
    fn test_literals() {
        assert_eq!(expr_to_lean(&Expr::Bool(true)), "True");
        assert_eq!(expr_to_lean(&Expr::Bool(false)), "False");
        assert_eq!(expr_to_lean(&Expr::IntLit("42".into())), "42");
        assert_eq!(expr_to_lean(&Expr::IntLit("-7".into())), "(-7)");
    }

    #[test]
    fn test_variable() {
        assert_eq!(expr_to_lean(&Expr::Var("x".into())), "x");
    }

    #[test]
    fn test_binary_arithmetic() {
        let expr = Expr::Binary(
            BinOp::Add,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::IntLit("1".into())),
        );
        assert_eq!(expr_to_lean(&expr), "x + 1");
    }

    #[test]
    fn test_binary_comparison() {
        let expr = Expr::Binary(
            BinOp::Gt,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::IntLit("0".into())),
        );
        assert_eq!(expr_to_lean(&expr), "x > 0");
    }

    #[test]
    fn test_nested_binary() {
        // x + x > x — Lean handles precedence, no parens needed on LHS of >
        let double_x = Expr::Binary(
            BinOp::Add,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::Var("x".into())),
        );
        let expr = Expr::Binary(
            BinOp::Gt,
            Box::new(double_x),
            Box::new(Expr::Var("x".into())),
        );
        assert_eq!(expr_to_lean(&expr), "x + x > x");
    }

    #[test]
    fn test_function_call() {
        let expr = Expr::Call(
            "double".into(),
            vec![Expr::Var("x".into())],
        );
        assert_eq!(expr_to_lean(&expr), "double x");
    }

    #[test]
    fn test_if_then_else() {
        let expr = Expr::If(
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
        );
        assert_eq!(
            expr_to_lean(&expr),
            "if n = 0 then 0 else n + triangle (n - 1)"
        );
    }

    #[test]
    fn test_forall() {
        let expr = Expr::Forall(
            vec![("x".into(), Typ::Int(IntRange::Nat))],
            Box::new(Expr::Binary(
                BinOp::Ge,
                Box::new(Expr::Binary(
                    BinOp::Mul,
                    Box::new(Expr::Var("x".into())),
                    Box::new(Expr::Var("x".into())),
                )),
                Box::new(Expr::IntLit("0".into())),
            )),
        );
        assert_eq!(expr_to_lean(&expr), "∀ (x : Nat), x * x ≥ 0");
    }

    #[test]
    fn test_implies() {
        let expr = Expr::Binary(
            BinOp::Implies,
            Box::new(Expr::Binary(
                BinOp::Gt,
                Box::new(Expr::Var("x".into())),
                Box::new(Expr::IntLit("0".into())),
            )),
            Box::new(Expr::Binary(
                BinOp::Gt,
                Box::new(Expr::Binary(
                    BinOp::Mul,
                    Box::new(Expr::Var("x".into())),
                    Box::new(Expr::Var("x".into())),
                )),
                Box::new(Expr::IntLit("0".into())),
            )),
        );
        assert_eq!(expr_to_lean(&expr), "(x > 0) → (x * x > 0)");
    }

    #[test]
    fn test_not() {
        let expr = Expr::Unary(
            UnOp::Not,
            Box::new(Expr::Var("b".into())),
        );
        assert_eq!(expr_to_lean(&expr), "¬b");
    }

    #[test]
    fn test_lean_keyword_escaping() {
        assert_eq!(lean_safe_name("def"), "«def»");
        assert_eq!(lean_safe_name("x"), "x");
        assert_eq!(lean_safe_name("my_var"), "my_var");
    }
}
