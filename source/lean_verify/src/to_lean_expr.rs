//! Translate VIR expressions to Lean 4 expression syntax.

use vir::ast::*;
use crate::to_lean_type::{write_typ, write_todo};

// Lean operator precedence (higher = tighter binding).
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
        BinaryOp::Eq(_) | BinaryOp::Ne | BinaryOp::Inequality(_) => PREC_CMP,
        BinaryOp::Arith(ArithOp::Add(_) | ArithOp::Sub(_)) => PREC_ADD,
        BinaryOp::Arith(ArithOp::Mul(_) | ArithOp::EuclideanDiv(_) | ArithOp::EuclideanMod(_)) => PREC_MUL,
        _ => PREC_CMP,
    }
}

fn expr_prec(expr: &ExprX) -> u8 {
    match expr {
        ExprX::Const(_) | ExprX::Var(_) | ExprX::ConstVar(..) | ExprX::Call(..) => PREC_ATOM,
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
        ExprX::ConstVar(fun, _) => write_fn_ref(out, fun),

        ExprX::Binary(op, lhs, rhs) => {
            let p = binop_prec(op);
            write_expr_prec(out, &lhs.x, p, true);
            out.push(' ');
            write_binop(out, op);
            out.push(' ');
            write_expr_prec(out, &rhs.x, p, false);
        }

        ExprX::BinaryOpr(BinaryOpr::ExtEq(_, _), lhs, rhs) => {
            write_expr_prec(out, &lhs.x, PREC_CMP, true);
            out.push_str(" = ");
            write_expr_prec(out, &rhs.x, PREC_CMP, false);
        }

        ExprX::Unary(UnaryOp::Not, inner) => {
            out.push('¬');
            write_expr_prec(out, &inner.x, PREC_ATOM, true);
        }

        ExprX::Unary(UnaryOp::Clip { range, .. }, inner) => {
            // `as nat` / `as int` / `as u32` etc.
            // Check source type to decide if conversion is needed or if it's identity.
            let src_is_nat = matches!(&*inner.typ, TypX::Int(
                IntRange::Nat | IntRange::U(_) | IntRange::USize | IntRange::Char
            ));
            let dst_is_nat = matches!(range,
                IntRange::Nat | IntRange::U(_) | IntRange::USize | IntRange::Char
            );
            if src_is_nat == dst_is_nat {
                // Same signedness family — identity in spec mode
                write_expr(out, &inner.x);
            } else if dst_is_nat {
                // Int → Nat: Int.toNat (truncates negative to 0)
                out.push_str("Int.toNat ");
                write_expr_prec(out, &inner.x, PREC_ATOM, true);
            } else {
                // Nat → Int: implicit coercion (↑) in Lean
                write_expr(out, &inner.x);
            }
        }

        ExprX::Unary(UnaryOp::CoerceMode { .. }, inner) => {
            // Ghost/Tracked mode coercions are transparent in spec
            write_expr(out, &inner.x);
        }

        ExprX::Call(target, args, _) => {
            match target {
                CallTarget::Fun(_, fun, _, _, _, _) => write_fn_ref(out, fun),
                _ => write_todo(out, "call target"),
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
            out.push_str(match quant.quant {
                air::ast::Quant::Forall => "∀ ",
                air::ast::Quant::Exists => "∃ ",
            });
            write_binders(out, binders);
            out.push_str(", ");
            write_expr(out, &body.x);
        }

        ExprX::Choose { params, cond, body: _ } => {
            out.push_str("Classical.choose (show ∃ ");
            write_binders(out, params);
            out.push_str(", ");
            write_expr(out, &cond.x);
            out.push_str(" from sorry)");
        }

        ExprX::WithTriggers { body, .. } => write_expr(out, &body.x),

        ExprX::Block(stmts, final_expr) => {
            for stmt in stmts.iter() {
                match &stmt.x {
                    StmtX::Expr(e) => { write_expr(out, &e.x); out.push_str("; "); }
                    StmtX::Decl { .. } => { write_todo(out, "decl"); out.push_str("; "); }
                }
            }
            if let Some(e) = final_expr {
                write_expr(out, &e.x);
            }
        }

        ExprX::Ghost { expr, .. } | ExprX::ProofInSpec(expr) => write_expr(out, &expr.x),
        ExprX::Loc(expr) => write_expr(out, &expr.x),
        ExprX::VarLoc(ident) => write_name(out, &ident.0),
        ExprX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner) => write_expr(out, &inner.x),

        ExprX::ReadPlace(place, _) => write_place(out, &place.x),

        ExprX::UnaryOpr(UnaryOpr::Field(field_opr), inner) => {
            write_expr_prec(out, &inner.x, PREC_ATOM, true);
            out.push('.');
            out.push_str(&field_opr.field);
        }
        ExprX::UnaryOpr(UnaryOpr::IsVariant { variant, .. }, inner) => {
            write_expr_prec(out, &inner.x, PREC_ATOM, true);
            out.push_str(".is");
            out.push_str(variant);
        }
        // Remaining UnaryOpr that are genuinely transparent in spec mode
        ExprX::UnaryOpr(UnaryOpr::CustomErr(_), inner) => write_expr(out, &inner.x),

        ExprX::Header(_) => {} // skip header expressions (requires/ensures markers)

        _ => write_todo(out, "expr"),
    }
}

/// Write expression, adding parens if needed by precedence.
fn write_expr_prec(out: &mut String, expr: &ExprX, parent_prec: u8, is_left: bool) {
    let child_prec = expr_prec(expr);
    let needs_parens = child_prec < parent_prec || (child_prec == parent_prec && !is_left);
    if needs_parens { out.push('('); }
    write_expr(out, expr);
    if needs_parens { out.push(')'); }
}

/// Write `(name₁ : Type₁) (name₂ : Type₂) ...` binder list.
pub(crate) fn write_binders(out: &mut String, binders: &VarBinders<Typ>) {
    for (i, b) in binders.iter().enumerate() {
        if i > 0 { out.push(' '); }
        out.push('(');
        write_name(out, &b.name.0);
        out.push_str(" : ");
        write_typ(out, &b.a);
        out.push(')');
    }
}

fn write_const(out: &mut String, c: &Constant) {
    match c {
        Constant::Bool(true) => out.push_str("True"),
        Constant::Bool(false) => out.push_str("False"),
        Constant::Int(n) => {
            let s = n.to_string();
            if s.starts_with('-') {
                out.push('('); out.push_str(&s); out.push(')');
            } else {
                out.push_str(&s);
            }
        }
        _ => write_todo(out, "const"),
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
        _ => "sorry /- TODO: op -/",
    });
}

fn write_fn_ref(out: &mut String, fun: &Fun) {
    write_name(out, fun.path.segments.last().map(|s| s.as_str()).unwrap_or("_"));
}

/// Write a name, escaping Lean keywords.
pub(crate) fn write_name(out: &mut String, name: &str) {
    if is_lean_keyword(name) {
        out.push('«'); out.push_str(name); out.push('»');
    } else {
        for c in name.chars() {
            match c { '@' | '#' => out.push('_'), _ => out.push(c) }
        }
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

/// Write a VIR place as Lean syntax (for ReadPlace).
fn write_place(out: &mut String, place: &PlaceX) {
    match place {
        PlaceX::Local(ident) => write_name(out, &ident.0),
        PlaceX::Field(field_opr, base) => {
            write_place(out, &base.x);
            out.push('.');
            out.push_str(&field_opr.field);
        }
        PlaceX::DerefMut(inner) => write_place(out, &inner.x),
        PlaceX::ModeUnwrap(inner, _) => write_place(out, &inner.x),
        _ => write_todo(out, "place"),
    }
}

/// Convenience: return expression as String.
pub fn expr_to_lean(expr: &ExprX) -> String {
    let mut s = String::new();
    write_expr(&mut s, expr);
    s
}
