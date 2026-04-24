//! AST-level sanity checks on the generated command stream.
//!
//! These run in debug builds only (gated via `debug_assertions`) and catch
//! classes of codegen bug that would otherwise only surface as cryptic
//! Lean errors — or, worse, ship silently if the test proof happens to
//! paper over them.
//!
//! # The check
//!
//! For every `Command::Theorem`, `Command::Def`, and `Command::Instance`
//! we emit, walk the body/goal and verify every `Var(x)` reference is:
//!
//! 1. A **local** bound by an enclosing binder (theorem/def params,
//!    `let`, lambda, ∀/∃, match-arm pattern), or
//! 2. Defined by an earlier top-level `Command` in the same file, or
//! 3. A **Lean/Mathlib built-in** on our allowlist (`Nat`, `Int`, …), or
//! 4. A **dotted name** like `Classical.arbitrary` or `Nat.succ`
//!    (delegated trust to Lean resolution), or
//! 5. An **underscore** (`_`, an inference placeholder).
//!
//! Anything else is a violation: the generator likely lost track of a
//! dependency. This was the bug behind the tuple regression — `pair`
//! was referenced but never defined, because dep_order's walker skipped
//! it.
//!
//! # Why not check tactic bodies?
//!
//! `Tactic::Raw` is user-authored Lean we don't parse. `Tactic::Named`
//! references tactics (like `omega`, `tactus_auto`) that are macros, not
//! term-level definitions, and don't fit into the same "is it defined"
//! model. We only check term positions.

use std::collections::HashSet;
use crate::lean_ast::*;

/// A single unresolved reference.
#[derive(Debug)]
pub struct Violation {
    /// Human-readable context — usually the name of the theorem/def.
    pub context: String,
    /// The identifier that couldn't be resolved.
    pub name: String,
}

/// Walk `cmds` in order and collect every unresolved reference.
///
/// Returns an empty vec on success.
pub fn check_references(cmds: &[Command]) -> Vec<Violation> {
    let mut defined: HashSet<String> = HashSet::new();
    let mut violations: Vec<Violation> = Vec::new();

    for cmd in cmds {
        visit(cmd, &mut defined, &mut violations);
    }
    violations
}

fn visit(cmd: &Command, defined: &mut HashSet<String>, violations: &mut Vec<Violation>) {
    match cmd {
        // Commands that introduce no term references and add no names we need to track:
        Command::Raw(_)
        | Command::Import(_)
        | Command::SetOption { .. }
        | Command::NamespaceOpen(_)
        | Command::NamespaceClose(_) => {}

        // A Def adds its own name (supports self-recursion) and checks its
        // body against that name + params.
        Command::Def(d) => {
            defined.insert(d.name.clone());
            let mut scope = scope_from_binders(&d.binders);
            check_expr(&d.ret_ty, defined, &mut scope, violations, &d.name);
            check_expr(&d.body, defined, &mut scope, violations, &d.name);
            for t in &d.termination_by {
                check_expr(t, defined, &mut scope, violations, &d.name);
            }
        }

        Command::Theorem(t) => {
            let mut scope = scope_from_binders(&t.binders);
            for b in &t.binders {
                check_expr(&b.ty, defined, &mut scope, violations, &t.name);
            }
            check_expr(&t.goal, defined, &mut scope, violations, &t.name);
        }

        Command::Datatype(dt) => {
            defined.insert(dt.name.clone());
        }

        Command::Class(c) => {
            defined.insert(c.name.clone());
            // Method type signatures can reference types — check them.
            let mut scope = scope_from_binders(&c.typ_params);
            for b in &c.bounds { check_expr(&b.ty, defined, &mut scope, violations, &c.name); }
            for m in &c.methods {
                check_expr(&m.ty, defined, &mut scope, violations, &c.name);
            }
        }

        Command::Instance(i) => {
            let mut scope = scope_from_binders(&i.binders);
            check_expr(&i.target, defined, &mut scope, violations, "instance");
            for m in &i.methods {
                check_expr(&m.body, defined, &mut scope, violations, "instance");
            }
        }

        Command::Mutual(inner) => {
            // Predefine every name in the group so members can reference each other.
            for c in inner {
                if let Command::Def(d) = c { defined.insert(d.name.clone()); }
            }
            for c in inner { visit(c, defined, violations); }
        }
    }
}

fn scope_from_binders(binders: &[Binder]) -> HashSet<String> {
    binders.iter().filter_map(|b| b.name.clone()).collect()
}

fn check_expr(
    e: &Expr,
    defined: &HashSet<String>,
    scope: &mut HashSet<String>,
    violations: &mut Vec<Violation>,
    context: &str,
) {
    match &e.node {
        ExprNode::Var(name) => {
            if !name_resolves(name, defined, scope) {
                violations.push(Violation {
                    context: context.to_string(),
                    name: name.clone(),
                });
            }
        }

        // Literals, strings, etc. are never references.
        ExprNode::Lit(_) | ExprNode::LitBool(_)
        | ExprNode::LitStr(_) | ExprNode::LitChar(_)
        | ExprNode::Raw(_) => {}

        // Binders introduce local scope.
        ExprNode::Let { name, value, body } => {
            check_expr(value, defined, scope, violations, context);
            let shadowed = !scope.insert(name.clone());
            check_expr(body, defined, scope, violations, context);
            if !shadowed { scope.remove(name); }
        }
        ExprNode::Lambda { binders, body }
        | ExprNode::Forall { binders, body }
        | ExprNode::Exists { binders, body } => {
            // Check binder types under the outer scope, then push bound names.
            for b in binders { check_expr(&b.ty, defined, scope, violations, context); }
            let added: Vec<String> = binders.iter().filter_map(|b| {
                b.name.as_ref().and_then(|n| {
                    if scope.insert(n.clone()) { Some(n.clone()) } else { None }
                })
            }).collect();
            check_expr(body, defined, scope, violations, context);
            for n in &added { scope.remove(n); }
        }

        ExprNode::Match { scrutinee, arms } => {
            check_expr(scrutinee, defined, scope, violations, context);
            for arm in arms {
                let added = pattern_binds(&arm.pattern);
                let pushed: Vec<String> = added.iter()
                    .filter(|n| scope.insert((*n).clone()))
                    .cloned()
                    .collect();
                check_expr(&arm.body, defined, scope, violations, context);
                for n in &pushed { scope.remove(n); }
            }
        }

        // Compound expressions: recurse into children.
        ExprNode::BinOp { lhs, rhs, .. } => {
            check_expr(lhs, defined, scope, violations, context);
            check_expr(rhs, defined, scope, violations, context);
        }
        ExprNode::UnOp { arg, .. } => {
            check_expr(arg, defined, scope, violations, context);
        }
        ExprNode::App { head, args } => {
            check_expr(head, defined, scope, violations, context);
            for a in args { check_expr(a, defined, scope, violations, context); }
        }
        ExprNode::If { cond, then_, else_ } => {
            check_expr(cond, defined, scope, violations, context);
            check_expr(then_, defined, scope, violations, context);
            if let Some(e) = else_ { check_expr(e, defined, scope, violations, context); }
        }
        ExprNode::TypeAnnot { expr, ty } => {
            check_expr(expr, defined, scope, violations, context);
            check_expr(ty, defined, scope, violations, context);
        }
        ExprNode::FieldProj { expr, .. } => {
            check_expr(expr, defined, scope, violations, context);
        }
        ExprNode::StructUpdate { base, updates } => {
            check_expr(base, defined, scope, violations, context);
            for (_, v) in updates { check_expr(v, defined, scope, violations, context); }
        }
        ExprNode::ArrayLit(elts) | ExprNode::Anon(elts) => {
            for e in elts { check_expr(e, defined, scope, violations, context); }
        }
        ExprNode::Index { base, idx } => {
            check_expr(base, defined, scope, violations, context);
            check_expr(idx, defined, scope, violations, context);
        }
        ExprNode::SpanMark { inner, .. } => {
            check_expr(inner, defined, scope, violations, context);
        }
    }
}

/// Collect the names a pattern introduces into scope. Skips literal/ctor
/// names (those reference other things, they don't bind).
fn pattern_binds(p: &Pattern) -> Vec<String> {
    let mut out = Vec::new();
    collect_pattern_binders(p, &mut out);
    out
}

fn collect_pattern_binders(p: &Pattern, out: &mut Vec<String>) {
    match p {
        Pattern::Var(n) => out.push(n.clone()),
        Pattern::Wildcard | Pattern::Lit(_) => {}
        Pattern::Ctor { args, .. } => {
            for a in args { collect_pattern_binders(a, out); }
        }
        Pattern::Or(l, r) => {
            collect_pattern_binders(l, out);
            collect_pattern_binders(r, out);
        }
        Pattern::Binding { name, sub } => {
            out.push(name.clone());
            collect_pattern_binders(sub, out);
        }
    }
}

/// Decide whether a bare-identifier `Var(name)` resolves.
fn name_resolves(name: &str, defined: &HashSet<String>, scope: &HashSet<String>) -> bool {
    if name == "_" { return true; }
    if scope.contains(name) || defined.contains(name) { return true; }
    // Dotted names: trust Lean/Mathlib resolution. The generator uses
    // dots for namespaced identifiers; if we typo one, Lean will catch it.
    if name.contains('.') { return true; }
    // Keyword-quoted names (our sanitizer wraps Lean keywords in `«…»`)
    // always pass — they're not valid raw identifiers anyway.
    if name.starts_with('«') { return true; }
    // Lean / Mathlib built-in type and value names we expect callers to
    // reference without an explicit import chain through our command stream.
    matches!(name,
        "Type" | "Prop" | "Sort"
        | "Nat" | "Int" | "Bool" | "Real" | "Float" | "String" | "Char"
        | "List" | "Array" | "Option" | "Prod" | "Sum" | "Unit" | "Empty"
        | "And" | "Or" | "Not" | "Iff"
        | "True" | "False"
        // `default` resolves via the `Inhabited` typeclass — auto-derived
        // for primitive types. Used as the fallback value in synthesized
        // accessor functions for multi-variant inductives.
        | "default"
        | "()"
        // Tactus prelude axioms / defs / macros — resolved by the
        // `Command::Raw` block in the preamble, not by our own
        // declarations, so the sanity check needs them explicitly.
        | "arch_word_bits" | "arch_word_bits_valid"
        | "usize_hi" | "isize_hi"
        | "tactus_peel"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(s: &str) -> Expr { Expr::new(ExprNode::Var(s.into())) }

    #[test]
    fn known_builtins_pass() {
        let thm = Theorem {
            name: "t".into(),
            binders: vec![],
            goal: Expr::new(ExprNode::BinOp {
                op: BinOp::Eq,
                lhs: Box::new(var("Nat")),
                rhs: Box::new(var("Nat")),
            }),
            tactic: Tactic::Named("rfl".into()),
        };
        assert!(check_references(&[Command::Theorem(thm)]).is_empty());
    }

    #[test]
    fn undefined_reference_flagged() {
        // Theorem references `missing_fn`, which is never defined.
        let thm = Theorem {
            name: "t".into(),
            binders: vec![],
            goal: Expr::new(ExprNode::App {
                head: Box::new(var("missing_fn")),
                args: vec![var("x")],
            }),
            tactic: Tactic::Named("sorry".into()),
        };
        let v = check_references(&[Command::Theorem(thm)]);
        assert_eq!(v.len(), 2); // missing_fn + x
        assert!(v.iter().any(|vi| vi.name == "missing_fn"));
    }

    #[test]
    fn earlier_def_is_resolved() {
        // Def `f` first, then Theorem references `f`.
        let d = Def {
            attrs: vec![],
            name: "f".into(),
            binders: vec![Binder {
                name: Some("x".into()), ty: var("Nat"), kind: BinderKind::Explicit,
            }],
            ret_ty: var("Nat"),
            body: var("x"),
            termination_by: vec![],
        };
        let t = Theorem {
            name: "t".into(),
            binders: vec![Binder {
                name: Some("n".into()), ty: var("Nat"), kind: BinderKind::Explicit,
            }],
            goal: Expr::new(ExprNode::App {
                head: Box::new(var("f")),
                args: vec![var("n")],
            }),
            tactic: Tactic::Named("rfl".into()),
        };
        let violations = check_references(&[Command::Def(d), Command::Theorem(t)]);
        assert!(violations.is_empty(), "expected no violations, got {:?}", violations);
    }

    #[test]
    fn let_binder_shadows_reference() {
        // `let x := 5; x + x` — `x` is bound, should resolve.
        let body = Expr::new(ExprNode::Let {
            name: "x".into(),
            value: Box::new(Expr::new(ExprNode::Lit("5".into()))),
            body: Box::new(Expr::new(ExprNode::BinOp {
                op: BinOp::Add,
                lhs: Box::new(var("x")),
                rhs: Box::new(var("x")),
            })),
        });
        let d = Def {
            attrs: vec![], name: "ten".into(), binders: vec![],
            ret_ty: var("Nat"), body, termination_by: vec![],
        };
        assert!(check_references(&[Command::Def(d)]).is_empty());
    }

    #[test]
    fn forall_binder_scopes_body() {
        let goal = Expr::new(ExprNode::Forall {
            binders: vec![Binder {
                name: Some("k".into()), ty: var("Nat"), kind: BinderKind::Explicit,
            }],
            body: Box::new(Expr::new(ExprNode::BinOp {
                op: BinOp::Eq,
                lhs: Box::new(var("k")),
                rhs: Box::new(var("k")),
            })),
        });
        let t = Theorem {
            name: "t".into(), binders: vec![], goal,
            tactic: Tactic::Named("rfl".into()),
        };
        assert!(check_references(&[Command::Theorem(t)]).is_empty());
    }

    #[test]
    fn mutual_group_resolves_cross_references() {
        // `mutual def f := g   def g := f end` — would fail without
        // predefining names across the group.
        let d1 = Def {
            attrs: vec![], name: "f".into(), binders: vec![], ret_ty: var("Nat"),
            body: var("g"), termination_by: vec![],
        };
        let d2 = Def {
            attrs: vec![], name: "g".into(), binders: vec![], ret_ty: var("Nat"),
            body: var("f"), termination_by: vec![],
        };
        let m = Command::Mutual(vec![Command::Def(d1), Command::Def(d2)]);
        assert!(check_references(&[m]).is_empty());
    }

    #[test]
    fn dotted_names_pass_through() {
        // `Classical.arbitrary` should be accepted without explicit definition.
        let t = Theorem {
            name: "t".into(), binders: vec![],
            goal: var("Classical.arbitrary"),
            tactic: Tactic::Named("sorry".into()),
        };
        assert!(check_references(&[Command::Theorem(t)]).is_empty());
    }
}
