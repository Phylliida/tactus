//! Translate VIR expressions to Lean 4 expression syntax.

use vir::ast::*;
use crate::to_lean_type::{write_typ, write_todo, short_name};

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
        ExprX::Const(_) | ExprX::Var(_) | ExprX::ConstVar(..) => PREC_ATOM,
        // A call with args (e.g., `f x`) is NOT atomic — it needs parens when
        // used as an argument to another call: `g (f x)` not `g f x`.
        ExprX::Call(_, args, _) => if args.is_empty() { PREC_ATOM } else { 0 },
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
            // `as nat` / `as int` etc. In spec mode, VIR uses mathematical Int/Nat,
            // so clips between same-signedness families are identity.
            // For fixed-width clips (U(32), I(64)), modular arithmetic would apply
            // in exec mode — but spec mode just checks the range as a separate obligation.
            let src_is_nat = matches!(&*inner.typ, TypX::Int(
                IntRange::Nat | IntRange::U(_) | IntRange::USize | IntRange::Char
            ));
            let dst_is_nat = matches!(range,
                IntRange::Nat | IntRange::U(_) | IntRange::USize | IntRange::Char
            );
            if src_is_nat == dst_is_nat {
                write_expr(out, &inner.x);
            } else if dst_is_nat {
                out.push_str("Int.toNat ");
                write_expr_prec(out, &inner.x, PREC_ATOM, true);
            } else {
                // Nat → Int: implicit coercion in Lean
                write_expr(out, &inner.x);
            }
        }

        // Transparent unary ops: mode coercions, trigger annotations
        ExprX::Unary(UnaryOp::CoerceMode { .. }, inner) => write_expr(out, &inner.x),
        ExprX::Unary(UnaryOp::Trigger(_), inner) => write_expr(out, &inner.x),

        ExprX::Call(target, args, _) => {
            match target {
                CallTarget::Fun(kind, fun, _, _, _, _) => {
                    match kind {
                        // Concrete dispatch: use resolved impl function
                        CallTargetKind::DynamicResolved { resolved, .. } => {
                            write_fn_ref(out, resolved);
                        }
                        // Generic dispatch: emit TraitName.method for class resolution
                        CallTargetKind::Dynamic => {
                            write_trait_method_ref(out, fun);
                        }
                        _ => write_fn_ref(out, fun),
                    }
                }
                CallTarget::FnSpec(inner) => write_expr_prec(out, &inner.x, PREC_ATOM, true),
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
                    StmtX::Decl { pattern, init, .. } => {
                        out.push_str("let ");
                        write_pattern(out, &pattern.x);
                        if let Some(place) = init {
                            out.push_str(" := ");
                            write_place(out, &place.x);
                        }
                        out.push_str("; ");
                    }
                }
            }
            if let Some(e) = final_expr {
                write_expr(out, &e.x);
            }
        }

        // Spec closure: |x, y| body → fun x y => body
        ExprX::Closure(params, body) => {
            out.push_str("fun ");
            for (i, p) in params.iter().enumerate() {
                if i > 0 { out.push(' '); }
                out.push('(');
                write_name(out, &p.name.0);
                out.push_str(" : ");
                write_typ(out, &p.a);
                out.push(')');
            }
            out.push_str(" => ");
            write_expr(out, &body.x);
        }

        // Construct datatype: Struct { field: val } → { field := val } or ⟨val1, val2⟩
        ExprX::Ctor(dt, variant, fields, update) => {
            if update.is_some() {
                write_todo(out, "Ctor with update (..)");
            } else {
                write_ctor(out, dt, variant, fields);
            }
        }

        // Match expression
        ExprX::Match(place, arms) => {
            out.push_str("match ");
            write_place(out, &place.x);
            out.push_str(" with");
            for arm in arms.iter() {
                out.push_str(" | ");
                write_pattern(out, &arm.x.pattern.x);
                out.push_str(" => ");
                write_expr(out, &arm.x.body.x);
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
        ExprX::UnaryOpr(UnaryOpr::CustomErr(_), inner) => write_expr(out, &inner.x),

        ExprX::Header(_) => {} // skip header expressions (requires/ensures markers)

        ExprX::Assign { .. } => write_todo(out, "Assign"),
        ExprX::Loop { .. } => write_todo(out, "Loop"),
        ExprX::Return(_) => write_todo(out, "Return"),
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
    write_name(out, short_name(&fun.path));
}

/// Write a trait method reference as `TraitName.method` for Lean class dispatch.
fn write_trait_method_ref(out: &mut String, fun: &Fun) {
    let segs = &fun.path.segments;
    if segs.len() >= 2 {
        write_name(out, segs[segs.len() - 2].as_str());
        out.push('.');
        write_name(out, segs[segs.len() - 1].as_str());
    } else {
        write_fn_ref(out, fun);
    }
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

/// Write a VIR pattern as Lean syntax.
fn write_pattern(out: &mut String, pat: &PatternX) {
    match pat {
        PatternX::Wildcard(_) => out.push('_'),
        PatternX::Var(binding) => write_name(out, &binding.name.0),
        PatternX::Constructor(dt, variant, pats) => {
            write_dt_variant(out, dt, variant);
            for p in pats.iter() {
                out.push(' ');
                // Wrap non-trivial patterns in parens
                let needs_parens = matches!(&p.a.x, PatternX::Constructor(..));
                if needs_parens { out.push('('); }
                write_pattern(out, &p.a.x);
                if needs_parens { out.push(')'); }
            }
        }
        PatternX::Or(left, right) => {
            write_pattern(out, &left.x);
            out.push_str(" | ");
            write_pattern(out, &right.x);
        }
        PatternX::Expr(e) => write_expr(out, &e.x),
        PatternX::MutRef(inner) | PatternX::ImmutRef(inner) => write_pattern(out, &inner.x),
        _ => write_todo(out, "pattern"),
    }
}

/// Write a Ctor expression as Lean syntax.
/// Positional fields ("0", "1", ...): `Type.Variant val1 val2`
/// Named fields: `Type.Variant val1 val2` (field order from VIR)
/// No fields: `Type.Variant`
fn write_ctor(out: &mut String, dt: &Dt, variant: &Ident, fields: &Binders<Expr>) {
    write_dt_variant(out, dt, variant);
    for f in fields.iter() {
        out.push(' ');
        write_expr_prec(out, &f.a.x, PREC_ATOM, true);
    }
}

/// Write datatype variant name: Type.Variant, or Type.mk for structs (where variant == type name).
fn write_dt_variant(out: &mut String, dt: &Dt, variant: &Ident) {
    match dt {
        Dt::Path(path) => {
            let type_name = short_name(path);
            out.push_str(type_name);
            out.push('.');
            // Structs: VIR uses type name as variant, Lean uses `mk`
            if variant.as_str() == type_name { out.push_str("mk"); }
            else { write_name(out, variant); }
        }
        Dt::Tuple(_) => write_name(out, variant),
    }
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
        // Temporary: evaluate expression and return as a place
        PlaceX::Temporary(expr) => write_expr(out, &expr.x),
        // WithExpr: evaluate side-effect expr, then return place
        PlaceX::WithExpr(_, place) => write_place(out, &place.x),
        _ => write_todo(out, "place"),
    }
}

/// Convenience: return expression as String.
pub fn expr_to_lean(expr: &ExprX) -> String {
    let mut s = String::new();
    write_expr(&mut s, expr);
    s
}
