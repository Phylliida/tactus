//! Pretty-printer for `lean_ast` nodes.
//!
//! Precedence is enforced at render time, not by callers. Every `write_expr`
//! call takes the *parent* precedence; children wrap themselves in parens
//! iff their own precedence is strictly lower. Associativity is encoded by
//! having left-/right-assoc operators pass `p` on the associative side and
//! `p + 1` on the other side, so same-precedence children don't parenthesize
//! when Lean would parse them correctly.
//!
//! Indentation is minimal — just enough for readability of multi-line
//! goals/bodies. Tactus-generated Lean is consumed by the kernel, not
//! reviewed by hand in the common case; debuggable on-disk artifacts are
//! about structure, not aesthetics.

use crate::lean_ast::*;

// ── Precedence ─────────────────────────────────────────────────────────
//
// Numbers roughly follow Lean 4's standard operator precedences. What
// matters is relative ordering, not the absolute number.

const PREC_IFF: u16 = 20;
const PREC_IMPLIES: u16 = 25;
const PREC_OR: u16 = 30;
const PREC_AND: u16 = 35;
const PREC_NOT: u16 = 40;
const PREC_CMP: u16 = 50;
const PREC_ADD: u16 = 65;
const PREC_MUL: u16 = 70;
const PREC_APP: u16 = 1024;
const PREC_ATOM: u16 = u16::MAX;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Assoc { Left, Right, None_ }

fn binop_info(op: BinOp) -> (u16, Assoc) {
    match op {
        BinOp::Iff => (PREC_IFF, Assoc::Right),
        BinOp::Implies => (PREC_IMPLIES, Assoc::Right),
        BinOp::Or => (PREC_OR, Assoc::Right),
        BinOp::And => (PREC_AND, Assoc::Right),
        BinOp::Eq | BinOp::Ne
        | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => (PREC_CMP, Assoc::None_),
        BinOp::Add | BinOp::Sub => (PREC_ADD, Assoc::Left),
        BinOp::Mul | BinOp::Div | BinOp::Mod => (PREC_MUL, Assoc::Left),
        BinOp::Xor => (PREC_CMP, Assoc::None_), // treat as non-assoc comparison-y
        // Bitwise: Lean uses custom operators at ~65/70 range.
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => (PREC_ADD, Assoc::Left),
        BinOp::Shr | BinOp::Shl => (PREC_ADD, Assoc::Left),
    }
}

fn binop_symbol(op: BinOp) -> &'static str {
    match op {
        BinOp::And => "∧",
        BinOp::Or => "∨",
        BinOp::Implies => "→",
        BinOp::Iff => "↔",
        BinOp::Xor => "xor",
        BinOp::Eq => "=",
        BinOp::Ne => "≠",
        BinOp::Lt => "<",
        BinOp::Le => "≤",
        BinOp::Gt => ">",
        BinOp::Ge => "≥",
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::BitAnd => "&&&",
        BinOp::BitOr => "|||",
        BinOp::BitXor => "^^^",
        BinOp::Shr => ">>>",
        BinOp::Shl => "<<<",
    }
}

fn expr_prec(node: &ExprNode) -> u16 {
    match node {
        ExprNode::Var(_) | ExprNode::Lit(_) | ExprNode::LitBool(_)
        | ExprNode::LitStr(_) | ExprNode::LitChar(_)
        | ExprNode::ArrayLit(_) | ExprNode::StructUpdate { .. }
        | ExprNode::Raw(_) => PREC_ATOM,
        ExprNode::FieldProj { .. } => PREC_ATOM,
        ExprNode::BinOp { op, .. } => binop_info(*op).0,
        ExprNode::UnOp { op: UnOp::Not, .. } => PREC_NOT,
        ExprNode::UnOp { op: UnOp::Neg, .. } => PREC_MUL + 1,
        ExprNode::UnOp { op: UnOp::BitNot, .. } => PREC_APP,
        ExprNode::App { args, .. } => if args.is_empty() { PREC_ATOM } else { PREC_APP },
        ExprNode::TypeAnnot { .. } => 0, // always parenthesized when inside anything
        ExprNode::If { .. } | ExprNode::Match { .. }
        | ExprNode::Let { .. } | ExprNode::Lambda { .. }
        | ExprNode::Forall { .. } | ExprNode::Exists { .. } => 0,
    }
}

// ── Public entry points ────────────────────────────────────────────────

pub fn pp_command(cmd: &Command) -> String {
    let mut out = String::new();
    write_command(&mut out, cmd);
    out
}

pub fn pp_commands(cmds: &[Command]) -> String {
    let mut out = String::new();
    for cmd in cmds {
        write_command(&mut out, cmd);
    }
    out
}

pub fn pp_expr(e: &Expr) -> String {
    let mut out = String::new();
    write_expr(&mut out, e, 0);
    out
}

// ── Command writers ─────────────────────────────────────────────────────

fn write_command(out: &mut String, cmd: &Command) {
    match cmd {
        Command::Raw(s) => {
            out.push_str(s);
            if !s.ends_with('\n') { out.push('\n'); }
        }
        Command::Import(path) => {
            out.push_str("import ");
            out.push_str(path);
            out.push('\n');
        }
        Command::SetOption { name, value } => {
            out.push_str("set_option ");
            out.push_str(name);
            out.push(' ');
            out.push_str(value);
            out.push('\n');
        }
        Command::NamespaceOpen(name) => {
            out.push_str("namespace ");
            out.push_str(name);
            out.push('\n');
        }
        Command::NamespaceClose(name) => {
            out.push_str("end ");
            out.push_str(name);
            out.push('\n');
        }
        Command::Mutual(cmds) => {
            out.push_str("mutual\n");
            for c in cmds { write_command(out, c); }
            out.push_str("end\n\n");
        }
        Command::Def(d) => write_def(out, d),
        Command::Theorem(t) => write_theorem(out, t),
        Command::Datatype(dt) => write_datatype(out, dt),
        Command::Class(c) => write_class(out, c),
        Command::Instance(i) => write_instance(out, i),
    }
}

fn write_def(out: &mut String, d: &Def) {
    for attr in &d.attrs {
        out.push_str("@[");
        out.push_str(attr);
        out.push_str("] ");
    }
    if d.noncomputable {
        out.push_str("noncomputable ");
    }
    out.push_str("def ");
    out.push_str(&d.name);
    write_binders(out, &d.binders);
    out.push_str(" : ");
    write_expr(out, &d.ret_ty, 0);
    out.push_str(" :=\n  ");
    write_expr(out, &d.body, 0);
    out.push('\n');
    if let Some(t) = &d.termination_by {
        out.push_str("termination_by ");
        write_expr(out, t, 0);
        out.push('\n');
    }
}

fn write_theorem(out: &mut String, t: &Theorem) {
    out.push_str("theorem ");
    out.push_str(&t.name);
    write_binders(out, &t.binders);
    out.push_str(" :\n    ");
    write_expr(out, &t.goal, 0);
    out.push_str(" := by\n");
    write_tactic_block(out, &t.tactic, "  ");
}

fn write_datatype(out: &mut String, dt: &Datatype) {
    match &dt.kind {
        DatatypeKind::Structure { fields } => {
            out.push_str("structure ");
            out.push_str(&dt.name);
            for tp in &dt.typ_params {
                out.push_str(" (");
                out.push_str(tp);
                out.push_str(" : Type)");
            }
            out.push_str(" where\n");
            for f in fields {
                out.push_str("  ");
                out.push_str(&f.name);
                out.push_str(" : ");
                write_expr(out, &f.ty, 0);
                out.push('\n');
            }
        }
        DatatypeKind::Inductive { variants } => {
            out.push_str("inductive ");
            out.push_str(&dt.name);
            for tp in &dt.typ_params {
                out.push_str(" (");
                out.push_str(tp);
                out.push_str(" : Type)");
            }
            out.push_str(" where\n");
            for v in variants {
                out.push_str("  | ");
                out.push_str(&v.name);
                for f in &v.fields {
                    out.push_str(" (");
                    out.push_str(&f.name);
                    out.push_str(" : ");
                    write_expr(out, &f.ty, 0);
                    out.push(')');
                }
                out.push('\n');
            }
        }
    }
}

fn write_class(out: &mut String, c: &Class) {
    out.push_str("class ");
    out.push_str(&c.name);
    write_binders(out, &c.typ_params);
    write_binders(out, &c.bounds);
    out.push_str(" where\n");
    for m in &c.methods {
        out.push_str("  ");
        out.push_str(&m.name);
        out.push_str(" : ");
        write_expr(out, &m.ty, 0);
        out.push('\n');
    }
}

fn write_instance(out: &mut String, i: &Instance) {
    out.push_str("noncomputable instance");
    write_binders(out, &i.binders);
    out.push_str(" : ");
    write_expr(out, &i.target, 0);
    out.push_str(" where\n");
    for m in &i.methods {
        out.push_str("  ");
        out.push_str(&m.name);
        out.push_str(" := ");
        write_expr(out, &m.body, 0);
        out.push('\n');
    }
}

fn write_binders(out: &mut String, binders: &[Binder]) {
    for b in binders {
        out.push(' ');
        let (lo, hi) = match b.kind {
            BinderKind::Explicit | BinderKind::OutParam => ('(', ')'),
            BinderKind::Implicit => ('{', '}'),
            BinderKind::Instance => ('[', ']'),
        };
        out.push(lo);
        if let Some(name) = &b.name {
            out.push_str(name);
            out.push_str(" : ");
        }
        if matches!(b.kind, BinderKind::OutParam) {
            out.push_str("outParam ");
        }
        write_expr(out, &b.ty, 0);
        out.push(hi);
    }
}

// ── Tactic writers ──────────────────────────────────────────────────────

fn write_tactic_block(out: &mut String, t: &Tactic, indent: &str) {
    match t {
        Tactic::Raw(body) => {
            // Preserve the user's formatting verbatim; indent each line.
            for line in body.lines() {
                if line.trim().is_empty() {
                    out.push('\n');
                } else {
                    out.push_str(indent);
                    out.push_str(line);
                    out.push('\n');
                }
            }
        }
        Tactic::Named(name) => {
            out.push_str(indent);
            out.push_str(name);
            out.push('\n');
        }
        Tactic::Seq(ts) => {
            for inner in ts { write_tactic_block(out, inner, indent); }
        }
    }
}

// ── Expression writer ──────────────────────────────────────────────────

fn write_expr(out: &mut String, e: &Expr, parent_prec: u16) {
    let my_prec = expr_prec(&e.node);
    let needs_parens = my_prec < parent_prec;
    if needs_parens { out.push('('); }
    write_expr_body(out, &e.node);
    if needs_parens { out.push(')'); }
}

fn write_expr_body(out: &mut String, node: &ExprNode) {
    match node {
        ExprNode::Var(s) => out.push_str(s),
        ExprNode::Lit(s) => {
            if s.starts_with('-') {
                out.push('(');
                out.push_str(s);
                out.push(')');
            } else {
                out.push_str(s);
            }
        }
        ExprNode::LitBool(true) => out.push_str("True"),
        ExprNode::LitBool(false) => out.push_str("False"),
        ExprNode::LitStr(s) => {
            out.push('"');
            for c in s.chars() {
                match c {
                    '"' => out.push_str("\\\""),
                    '\\' => out.push_str("\\\\"),
                    '\n' => out.push_str("\\n"),
                    '\r' => out.push_str("\\r"),
                    '\t' => out.push_str("\\t"),
                    c => out.push(c),
                }
            }
            out.push('"');
        }
        ExprNode::LitChar(c) => {
            out.push('\'');
            out.push(*c);
            out.push('\'');
        }
        ExprNode::Raw(s) => out.push_str(s),

        ExprNode::BinOp { op, lhs, rhs } => {
            let (p, assoc) = binop_info(*op);
            let (lp, rp) = match assoc {
                Assoc::Left => (p, p + 1),
                Assoc::Right => (p + 1, p),
                Assoc::None_ => (p + 1, p + 1),
            };
            write_expr(out, lhs, lp);
            out.push(' ');
            out.push_str(binop_symbol(*op));
            out.push(' ');
            write_expr(out, rhs, rp);
        }

        ExprNode::UnOp { op, arg } => {
            out.push_str(match op {
                UnOp::Not => "¬",
                UnOp::Neg => "-",
                UnOp::BitNot => "~~~",
            });
            // Unary ops tuck tight — emit arg at prec APP so any non-atom
            // arg (including another UnOp) parenthesizes.
            write_expr(out, arg, PREC_APP);
        }

        ExprNode::App { head, args } => {
            if args.is_empty() {
                write_expr(out, head, PREC_ATOM);
            } else {
                write_expr(out, head, PREC_APP);
                for a in args {
                    out.push(' ');
                    write_expr(out, a, PREC_APP + 1);
                }
            }
        }

        ExprNode::Let { name, value, body } => {
            out.push_str("let ");
            out.push_str(name);
            out.push_str(" := ");
            write_expr(out, value, 0);
            out.push_str(";\n    ");
            write_expr(out, body, 0);
        }
        ExprNode::Lambda { binders, body } => {
            out.push_str("fun");
            write_binders(out, binders);
            out.push_str(" => ");
            write_expr(out, body, 0);
        }
        ExprNode::Forall { binders, body } => {
            out.push('∀');
            write_binders(out, binders);
            out.push_str(", ");
            write_expr(out, body, 0);
        }
        ExprNode::Exists { binders, body } => {
            out.push('∃');
            write_binders(out, binders);
            out.push_str(", ");
            write_expr(out, body, 0);
        }

        ExprNode::If { cond, then_, else_ } => {
            out.push_str("if ");
            write_expr(out, cond, 0);
            out.push_str(" then ");
            write_expr(out, then_, 0);
            out.push_str(" else ");
            write_expr(out, else_, 0);
        }

        ExprNode::Match { scrutinee, arms } => {
            out.push_str("match ");
            write_expr(out, scrutinee, 0);
            out.push_str(" with");
            for arm in arms {
                out.push_str(" | ");
                write_pattern(out, &arm.pattern);
                out.push_str(" => ");
                write_expr(out, &arm.body, 0);
            }
        }

        ExprNode::TypeAnnot { expr, ty } => {
            out.push('(');
            write_expr(out, expr, 0);
            out.push_str(" : ");
            write_expr(out, ty, 0);
            out.push(')');
        }

        ExprNode::FieldProj { expr, field } => {
            write_expr(out, expr, PREC_ATOM);
            out.push('.');
            out.push_str(field);
        }

        ExprNode::StructUpdate { base, updates } => {
            out.push_str("{ ");
            write_expr(out, base, 0);
            out.push_str(" with ");
            for (i, (name, val)) in updates.iter().enumerate() {
                if i > 0 { out.push_str(", "); }
                out.push_str(name);
                out.push_str(" := ");
                write_expr(out, val, 0);
            }
            out.push_str(" }");
        }

        ExprNode::ArrayLit(elts) => {
            out.push('[');
            for (i, e) in elts.iter().enumerate() {
                if i > 0 { out.push_str(", "); }
                write_expr(out, e, 0);
            }
            out.push(']');
        }
    }
}

fn write_pattern(out: &mut String, p: &Pattern) {
    match p {
        Pattern::Var(s) => out.push_str(s),
        Pattern::Wildcard => out.push('_'),
        Pattern::Ctor { name, args } => {
            out.push_str(name);
            for a in args {
                out.push(' ');
                let needs = matches!(a, Pattern::Ctor { args, .. } if !args.is_empty());
                if needs { out.push('('); }
                write_pattern(out, a);
                if needs { out.push(')'); }
            }
        }
        Pattern::Or(l, r) => {
            write_pattern(out, l);
            out.push_str(" | ");
            write_pattern(out, r);
        }
        Pattern::Binding { name, sub } => {
            out.push_str(name);
            out.push('@');
            write_pattern(out, sub);
        }
        Pattern::Lit(node) => write_expr_body(out, node),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(s: &str) -> Expr { Expr::new(ExprNode::Var(s.into())) }
    fn lit(n: i64) -> Expr { Expr::new(ExprNode::Lit(n.to_string())) }
    fn bin(op: BinOp, l: Expr, r: Expr) -> Expr {
        Expr::new(ExprNode::BinOp { op, lhs: Box::new(l), rhs: Box::new(r) })
    }

    #[test]
    fn mul_binds_tighter_than_add() {
        // a + b * c → "a + b * c" (no parens; mul is inside)
        let e = bin(BinOp::Add, var("a"), bin(BinOp::Mul, var("b"), var("c")));
        assert_eq!(pp_expr(&e), "a + b * c");
    }

    #[test]
    fn add_inside_mul_parenthesizes() {
        // (a + b) * c → "(a + b) * c"
        let e = bin(BinOp::Mul, bin(BinOp::Add, var("a"), var("b")), var("c"));
        assert_eq!(pp_expr(&e), "(a + b) * c");
    }

    #[test]
    fn sub_is_left_associative() {
        // a - b - c = (a - b) - c, no parens needed on left
        let e = bin(BinOp::Sub, bin(BinOp::Sub, var("a"), var("b")), var("c"));
        assert_eq!(pp_expr(&e), "a - b - c");
    }

    #[test]
    fn sub_right_nested_needs_parens() {
        // a - (b - c) — subtraction is left-assoc, so right child at same prec parenthesizes
        let e = bin(BinOp::Sub, var("a"), bin(BinOp::Sub, var("b"), var("c")));
        assert_eq!(pp_expr(&e), "a - (b - c)");
    }

    #[test]
    fn implies_is_right_associative() {
        // a → b → c = a → (b → c), no parens
        let e = bin(BinOp::Implies, var("a"), bin(BinOp::Implies, var("b"), var("c")));
        assert_eq!(pp_expr(&e), "a → b → c");
    }

    #[test]
    fn implies_left_nested_needs_parens() {
        // (a → b) → c — left child at same prec on right-assoc op parenthesizes
        let e = bin(BinOp::Implies, bin(BinOp::Implies, var("a"), var("b")), var("c"));
        assert_eq!(pp_expr(&e), "(a → b) → c");
    }

    #[test]
    fn and_binds_tighter_than_implies() {
        // a ∧ b → c = (a ∧ b) → c (∧ at 35 tighter than → at 25)
        let e = bin(BinOp::Implies, bin(BinOp::And, var("a"), var("b")), var("c"));
        assert_eq!(pp_expr(&e), "a ∧ b → c");
    }

    #[test]
    fn implies_inside_and_needs_parens() {
        // a ∧ (b → c) — ∧ is tighter, so the implication child needs parens
        let e = bin(BinOp::And, var("a"), bin(BinOp::Implies, var("b"), var("c")));
        assert_eq!(pp_expr(&e), "a ∧ (b → c)");
    }

    #[test]
    fn negative_literal_parenthesizes() {
        let e = Expr::new(ExprNode::Lit("-5".into()));
        assert_eq!(pp_expr(&e), "(-5)");
    }

    #[test]
    fn app_binds_tightest() {
        // f x + 1 — application + literal at add prec, no parens
        let e = bin(
            BinOp::Add,
            Expr::new(ExprNode::App {
                head: Box::new(var("f")),
                args: vec![var("x")],
            }),
            lit(1),
        );
        assert_eq!(pp_expr(&e), "f x + 1");
    }

    #[test]
    fn app_of_app_is_left_assoc() {
        // f g x — `App(App(f, [g]), [x])` emits the same as `App(f, [g, x])`.
        let nested = Expr::new(ExprNode::App {
            head: Box::new(var("f")),
            args: vec![var("g")],
        });
        let e = Expr::new(ExprNode::App {
            head: Box::new(nested),
            args: vec![var("x")],
        });
        assert_eq!(pp_expr(&e), "f g x");
    }

    #[test]
    fn app_arg_is_app_parenthesizes() {
        // f (g x) — inner app as an arg needs parens
        let inner = Expr::new(ExprNode::App {
            head: Box::new(var("g")),
            args: vec![var("x")],
        });
        let e = Expr::new(ExprNode::App {
            head: Box::new(var("f")),
            args: vec![inner],
        });
        assert_eq!(pp_expr(&e), "f (g x)");
    }

    #[test]
    fn simple_def_renders() {
        let d = Def {
            attrs: vec!["irreducible".into()],
            noncomputable: true,
            name: "double".into(),
            binders: vec![Binder {
                name: Some("x".into()),
                ty: var("Nat"),
                kind: BinderKind::Explicit,
            }],
            ret_ty: var("Nat"),
            body: bin(BinOp::Add, var("x"), var("x")),
            termination_by: None,
            span: None,
        };
        let expected = "@[irreducible] noncomputable def double (x : Nat) : Nat :=\n  x + x\n";
        assert_eq!(pp_command(&Command::Def(d)), expected);
    }

    #[test]
    fn theorem_with_named_tactic() {
        let t = Theorem {
            name: "foo".into(),
            binders: vec![Binder {
                name: Some("x".into()),
                ty: var("Nat"),
                kind: BinderKind::Explicit,
            }],
            goal: bin(BinOp::Eq, var("x"), var("x")),
            tactic: Tactic::Named("rfl".into()),
            span: None,
        };
        let out = pp_command(&Command::Theorem(t));
        assert!(out.contains("theorem foo (x : Nat)"));
        assert!(out.contains("x = x := by"));
        assert!(out.contains("  rfl"));
    }
}
