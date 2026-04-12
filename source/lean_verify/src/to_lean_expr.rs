//! Translate VIR expressions to Lean 4 expression syntax.

use std::fmt::Write;
use vir::ast::*;
use crate::to_lean_type::write_typ;

/// Lean operator precedence levels (higher = tighter binding).
const PREC_IMPLIES: u8 = 25;
const PREC_OR: u8 = 30;
const PREC_AND: u8 = 35;
const PREC_CMP: u8 = 50;
const PREC_ADD: u8 = 65;
const PREC_MUL: u8 = 70;
const PREC_ATOM: u8 = 255;

fn binop_prec(op: &BinaryOp) -> u8 {
    match op {
        BinaryOp::Implies => PREC_IMPLIES,
        BinaryOp::Or => PREC_OR,
        BinaryOp::And => PREC_AND,
        BinaryOp::Eq(_) | BinaryOp::Ne => PREC_CMP,
        BinaryOp::Inequality(_) => PREC_CMP,
        BinaryOp::Arith(ArithOp::Add(_) | ArithOp::Sub(_)) => PREC_ADD,
        BinaryOp::Arith(ArithOp::Mul(_) | ArithOp::EuclideanDiv(_) | ArithOp::EuclideanMod(_)) => PREC_MUL,
        _ => PREC_CMP,
    }
}

fn expr_prec(expr: &ExprX) -> u8 {
    match expr {
        ExprX::Const(_) | ExprX::Var(_) | ExprX::ConstVar(..) => PREC_ATOM,
        ExprX::Call(..) => PREC_ATOM,
        ExprX::Binary(op, _, _) => binop_prec(op),
        ExprX::Unary(..) => PREC_MUL + 1,
        _ => 0,
    }
}

/// Write a VIR expression as Lean 4 syntax.
pub fn write_expr(out: &mut String, expr: &ExprX) {
    match expr {
        ExprX::Const(c) => write_const(out, c),

        ExprX::Var(ident) => write_name(out, &ident.0),

        ExprX::ConstVar(fun, _) => {
            write_fn_ref(out, fun);
        }

        ExprX::Binary(op, lhs, rhs) => {
            let p = binop_prec(op);
            write_expr_prec(out, &lhs.x, p, true);
            out.push(' ');
            write_binop(out, op);
            out.push(' ');
            write_expr_prec(out, &rhs.x, p, false);
        }

        ExprX::BinaryOpr(BinaryOpr::ExtEq(_, _), lhs, rhs) => {
            // ExtEq → Lean = (function extensionality is built into Lean 4)
            write_expr_prec(out, &lhs.x, PREC_CMP, true);
            out.push_str(" = ");
            write_expr_prec(out, &rhs.x, PREC_CMP, false);
        }

        ExprX::Unary(op, inner) => match op {
            UnaryOp::Not => {
                out.push('¬');
                write_expr_prec(out, &inner.x, PREC_ATOM, true);
            }
            _ => { let _ = write!(out, "sorry /- unary {:?} -/", op); }
        },

        ExprX::Call(target, args, _) => {
            match target {
                CallTarget::Fun(_, fun, _, _, _, _) => write_fn_ref(out, fun),
                _ => out.push_str("sorry /- call -/"),
            }
            for arg in args.iter() {
                out.push(' ');
                write_expr_prec(out, &arg.x, PREC_ATOM, true);
            }
        }

        ExprX::If(cond, then_e, else_e) => {
            out.push_str("if ");
            write_expr(out, &cond.x);
            out.push_str(" then ");
            write_expr(out, &then_e.x);
            if let Some(else_e) = else_e {
                out.push_str(" else ");
                write_expr(out, &else_e.x);
            }
        }

        ExprX::Quant(quant, binders, body) => {
            match quant.quant {
                air::ast::Quant::Forall => out.push_str("∀ "),
                air::ast::Quant::Exists => out.push_str("∃ "),
            }
            for (i, b) in binders.iter().enumerate() {
                if i > 0 { out.push(' '); }
                out.push('(');
                write_name(out, &b.name.0);
                out.push_str(" : ");
                write_typ(out, &b.a);
                out.push(')');
            }
            out.push_str(", ");
            write_expr(out, &body.x);
        }

        ExprX::Choose { params, cond, body: _ } => {
            out.push_str("Classical.choose (show ∃ ");
            for (i, b) in params.iter().enumerate() {
                if i > 0 { out.push(' '); }
                out.push('(');
                write_name(out, &b.name.0);
                out.push_str(" : ");
                write_typ(out, &b.a);
                out.push(')');
            }
            out.push_str(", ");
            write_expr(out, &cond.x);
            out.push_str(" from sorry)");
        }

        ExprX::WithTriggers { body, .. } => {
            // Drop triggers — Lean doesn't use them
            write_expr(out, &body.x);
        }

        ExprX::Block(stmts, final_expr) => {
            for stmt in stmts.iter() {
                write_stmt(out, &stmt.x);
            }
            if let Some(e) = final_expr {
                write_expr(out, &e.x);
            }
        }

        _ => { let _ = write!(out, "sorry /- unhandled -/"); }
    }
}

fn write_expr_prec(out: &mut String, expr: &ExprX, parent_prec: u8, is_left: bool) {
    let child_prec = expr_prec(expr);
    let needs_parens = child_prec < parent_prec || (child_prec == parent_prec && !is_left);
    if needs_parens { out.push('('); }
    write_expr(out, expr);
    if needs_parens { out.push(')'); }
}

fn write_const(out: &mut String, c: &Constant) {
    match c {
        Constant::Bool(true) => out.push_str("True"),
        Constant::Bool(false) => out.push_str("False"),
        Constant::Int(n) => {
            let s = n.to_string();
            if s.starts_with('-') {
                let _ = write!(out, "({})", s);
            } else {
                out.push_str(&s);
            }
        }
        _ => { let _ = write!(out, "sorry /- const -/"); }
    }
}

fn write_binop(out: &mut String, op: &BinaryOp) {
    out.push_str(match op {
        BinaryOp::And => "∧",
        BinaryOp::Or => "∨",
        BinaryOp::Implies => "→",
        BinaryOp::Eq(_) => "=",
        BinaryOp::Ne => "≠",
        BinaryOp::Inequality(InequalityOp::Le) => "≤",
        BinaryOp::Inequality(InequalityOp::Lt) => "<",
        BinaryOp::Inequality(InequalityOp::Ge) => "≥",
        BinaryOp::Inequality(InequalityOp::Gt) => ">",
        BinaryOp::Arith(ArithOp::Add(_)) => "+",
        BinaryOp::Arith(ArithOp::Sub(_)) => "-",
        BinaryOp::Arith(ArithOp::Mul(_)) => "*",
        BinaryOp::Arith(ArithOp::EuclideanDiv(_)) => "/",
        BinaryOp::Arith(ArithOp::EuclideanMod(_)) => "%",
        _ => "sorry /- op -/",
    });
}

fn write_stmt(out: &mut String, stmt: &StmtX) {
    match stmt {
        StmtX::Expr(e) => {
            write_expr(out, &e.x);
            out.push_str("; ");
        }
        StmtX::Decl { .. } => {
            // Decl uses Place (exec-level), skip for now
            out.push_str("sorry /- decl -/; ");
        }
    }
}

fn write_fn_ref(out: &mut String, fun: &Fun) {
    let name = fun.path.segments.last().map(|s| s.as_str()).unwrap_or("?");
    write_name(out, name);
}

fn write_name(out: &mut String, name: &str) {
    let clean = name.replace('@', "_").replace('#', "_");
    if is_lean_keyword(&clean) {
        let _ = write!(out, "«{}»", clean);
    } else {
        out.push_str(&clean);
    }
}

fn is_lean_keyword(s: &str) -> bool {
    matches!(s,
        "def" | "theorem" | "lemma" | "example" | "abbrev" | "instance" | "class"
        | "structure" | "inductive" | "where" | "with" | "match" | "do" | "return"
        | "if" | "then" | "else" | "let" | "have" | "show" | "by" | "at" | "fun"
        | "forall" | "exists" | "Type" | "Prop" | "Sort" | "import" | "open"
        | "namespace" | "section" | "end" | "variable" | "universe"
    )
}

/// Convenience: return expression as String.
pub fn expr_to_lean(expr: &ExprX) -> String {
    let mut s = String::new();
    write_expr(&mut s, expr);
    s
}
