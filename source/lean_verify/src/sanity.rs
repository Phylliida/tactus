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

        // Curried-form def: name in scope (self-recursion), `ty`
        // and equations checked under the pre-colon binders' scope
        // (e.g., implicit `{A : Type}` for generic datatypes — #108)
        // plus each equation's pattern-bound names.
        Command::DefCurried(d) => {
            defined.insert(d.name.clone());
            let mut scope = scope_from_binders(&d.binders);
            for b in &d.binders {
                check_expr(&b.ty, defined, &mut scope, violations, &d.name);
            }
            check_expr(&d.ty, defined, &mut scope, violations, &d.name);
            for arm in &d.equations {
                let mut arm_scope = scope.clone();
                for n in pattern_binds(&arm.pattern) { arm_scope.insert(n); }
                check_expr(&arm.body, defined, &mut arm_scope, violations, &d.name);
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
            // Predefine every declarable name in the group BEFORE
            // visiting any member, so cross-references inside the
            // group resolve. For Def / DefCurried this is the usual
            // self-recursion + mutual-recursion pattern. For
            // Datatype (#109): an SCC of mutually recursive
            // inductives references each other in their variants'
            // field types — `inductive Tree where | Branch (f :
            // Forest) → Tree` looks up `Forest` mid-declaration,
            // which fails the sanity check unless `Forest` is
            // already in `defined` when Tree's body is visited.
            for c in inner {
                match c {
                    Command::Def(d) => { defined.insert(d.name.clone()); }
                    Command::DefCurried(d) => { defined.insert(d.name.clone()); }
                    Command::Datatype(dt) => { defined.insert(dt.name.clone()); }
                    _ => {}
                }
            }
            for c in inner { visit(c, defined, violations); }
        }
    }
}

fn scope_from_binders(binders: &[Binder]) -> HashSet<String> {
    binders.iter().filter_map(|b| b.name.as_ref().map(|n| n.as_str().to_string())).collect()
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
            if !name_resolves(name.as_str(), defined, scope) {
                violations.push(Violation {
                    context: context.to_string(),
                    name: name.as_str().to_string(),
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
            let shadowed = !scope.insert(name.as_str().to_string());
            check_expr(body, defined, scope, violations, context);
            if !shadowed { scope.remove(name.as_str()); }
        }
        ExprNode::Lambda { binders, body }
        | ExprNode::Forall { binders, body }
        | ExprNode::Exists { binders, body } => {
            // Check binder types under the outer scope, then push bound names.
            for b in binders { check_expr(&b.ty, defined, scope, violations, context); }
            let added: Vec<String> = binders.iter().filter_map(|b| {
                b.name.as_ref().and_then(|n| {
                    let s = n.as_str().to_string();
                    if scope.insert(s.clone()) { Some(s) } else { None }
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
        ExprNode::ArrayLit(elts) | ExprNode::Anon(elts) | ExprNode::Tuple(elts) => {
            for e in elts { check_expr(e, defined, scope, violations, context); }
        }
        ExprNode::Index { base, idx, bang: _ } => {
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
        Pattern::Var(n) => out.push(n.as_str().to_string()),
        Pattern::Wildcard | Pattern::Lit(_) => {}
        Pattern::Ctor { args, .. } => {
            for a in args { collect_pattern_binders(a, out); }
        }
        Pattern::Or(l, r) => {
            collect_pattern_binders(l, out);
            collect_pattern_binders(r, out);
        }
        Pattern::Binding { name, sub } => {
            out.push(name.as_str().to_string());
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
    // Tactus prelude axioms / defs / macros / tactic-syntax names —
    // resolved by the `Command::Raw` preamble that ships TactusPrelude.lean,
    // not by our own emitted declarations. Auto-derived from the prelude
    // text (#118) so adding a new def/axiom/macro/syntax/elab in
    // TactusPrelude.lean automatically updates the allowlist — no
    // hand-sync chore. (Convention 4 in `expr_shared.rs`'s "Reserved
    // identifier conventions": bare names in TactusPrelude.lean.)
    if cached_prelude_names().contains(name) { return true; }
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
        // `Inhabited` typeclass referenced by the manual instance Tactus
        // emits for indexed-style inductives (cross-instantiation
        // recursion — see `to_lean_fn::datatype_inhabited_instance_cmd`).
        // Parameter-style datatypes use `deriving Inhabited` which is
        // a string in the Datatype's `derives` field and bypasses name
        // resolution entirely; only the indexed-style path needs this.
        | "Inhabited"
        | "()"
    )
}

/// Cached set of top-level names defined in `TactusPrelude.lean`.
///
/// Resolved lazily on first use via `extract_prelude_names`. Used by
/// `name_resolves` to allow generated AST nodes to reference prelude
/// names (axioms, defs, tactic syntaxes/macros/elabs) without each
/// being explicitly hardcoded — the previous design required a manual
/// `matches!` arm update every time a prelude def landed.
fn cached_prelude_names() -> &'static HashSet<String> {
    use std::sync::OnceLock;
    static CACHE: OnceLock<HashSet<String>> = OnceLock::new();
    CACHE.get_or_init(|| extract_prelude_names(crate::prelude::TACTUS_PRELUDE))
}

/// Parse `TactusPrelude.lean` text and extract top-level names that
/// generated code may reference.
///
/// Recognised forms (one per line; the prelude has been simple enough
/// for line-based parsing to suffice):
/// * `axiom NAME : ...` — e.g., `arch_word_bits`.
/// * `def NAME ...` / `noncomputable def NAME ...` — e.g., `usize_hi`.
///   `noncomputable` may also follow other modifiers (`private`, `abbrev`)
///   if added later; we accept any leading-keyword soup that ends with
///   `def `.
/// * `syntax "NAME" ...` — e.g., `tactus_first`. The double-quoted
///   string literal is the introduced tactic name.
/// * `macro "NAME" ...` — e.g., `tactus_auto`.
/// * `elab "NAME" ...` — e.g., `tactus_case_split`.
///
/// Lines starting with `--` (comments) are skipped. `attribute`,
/// `import`, `set_option`, `open`, `macro_rules` introduce no names
/// of their own and are silently passed over.
///
/// **Why parse at runtime instead of build-time?** The prelude is
/// ~150 lines and the parse runs at most once per process via
/// `OnceLock`. Build-time codegen (build.rs) would add a dependency
/// graph entry without saving meaningful work. Robustness: if the
/// prelude grows enough that line-based parsing misses a form, the
/// regression surfaces as a sanity-check false positive on the
/// referenced name — easy to diagnose.
fn extract_prelude_names(prelude: &str) -> HashSet<String> {
    let mut names = HashSet::new();
    for raw in prelude.lines() {
        let line = raw.trim_start();
        if line.starts_with("--") || line.is_empty() { continue; }

        // axiom NAME : …  /  def NAME …  /  noncomputable def NAME …
        let after_kw = line.strip_prefix("axiom ")
            .or_else(|| line.strip_prefix("noncomputable def "))
            .or_else(|| line.strip_prefix("def "));
        if let Some(rest) = after_kw {
            let name: String = rest.chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            if !name.is_empty() {
                names.insert(name);
            }
            continue;
        }

        // syntax "NAME" …  /  macro "NAME" …  /  elab "NAME" …
        for prefix in &["syntax \"", "macro \"", "elab \""] {
            if let Some(rest) = line.strip_prefix(*prefix) {
                if let Some(end) = rest.find('"') {
                    let name = &rest[..end];
                    if !name.is_empty() {
                        names.insert(name.to_string());
                    }
                }
                break;
            }
        }
    }
    names
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(s: &str) -> Expr { Expr::new(ExprNode::Var(crate::lean_name::LeanName::lit(s))) }

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
            requires_preamble: Vec::new(),
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
            requires_preamble: Vec::new(),
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
                name: Some(crate::lean_name::LeanName::lit("x")), ty: var("Nat"), kind: BinderKind::Explicit,
            }],
            ret_ty: var("Nat"),
            body: var("x"),
            termination_by: vec![],
        };
        let t = Theorem {
            name: "t".into(),
            binders: vec![Binder {
                name: Some(crate::lean_name::LeanName::lit("n")), ty: var("Nat"), kind: BinderKind::Explicit,
            }],
            goal: Expr::new(ExprNode::App {
                head: Box::new(var("f")),
                args: vec![var("n")],
            }),
            tactic: Tactic::Named("rfl".into()),
            requires_preamble: Vec::new(),
        };
        let violations = check_references(&[Command::Def(d), Command::Theorem(t)]);
        assert!(violations.is_empty(), "expected no violations, got {:?}", violations);
    }

    #[test]
    fn let_binder_shadows_reference() {
        // `let x := 5; x + x` — `x` is bound, should resolve.
        let body = Expr::new(ExprNode::Let {
            name: crate::lean_name::LeanName::lit("x"),
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
                name: Some(crate::lean_name::LeanName::lit("k")), ty: var("Nat"), kind: BinderKind::Explicit,
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
            requires_preamble: Vec::new(),
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
            requires_preamble: Vec::new(),
        };
        assert!(check_references(&[Command::Theorem(t)]).is_empty());
    }

    /// Pin the prelude-name extractor against the actual `TactusPrelude.lean`.
    ///
    /// If a contributor adds a new top-level def/axiom/macro/syntax/elab
    /// to TactusPrelude.lean, this test confirms it lands in the allowlist
    /// without a corresponding `sanity.rs` edit. If a contributor introduces
    /// a new prelude-form syntax our parser doesn't recognise (e.g.,
    /// multi-line `def NAME\n  : Ty := …`), this test is the most natural
    /// place to fail loudly.
    #[test]
    fn extract_prelude_names_recognises_current_prelude() {
        let names = extract_prelude_names(crate::prelude::TACTUS_PRELUDE);
        // Axioms.
        assert!(names.contains("arch_word_bits"),
            "expected `arch_word_bits` in extracted prelude names; got {:?}", names);
        assert!(names.contains("arch_word_bits_valid"));
        // noncomputable defs.
        assert!(names.contains("usize_hi"));
        assert!(names.contains("isize_hi"));
        // syntax-introduced tactic names.
        assert!(names.contains("tactus_first"));
        assert!(names.contains("tactus_peel"));
        // macro-introduced tactic names.
        assert!(names.contains("tactus_auto"));
        assert!(names.contains("tactus_usize_bound"));
        // elab-introduced tactic names.
        assert!(names.contains("tactus_case_split"));
    }

    #[test]
    fn extract_prelude_names_skips_non_definition_lines() {
        // `import`, `set_option`, `attribute`, `open`, comments, blank
        // lines — none introduces a top-level name we should allowlist.
        let synthetic = r#"
            import Lean
            set_option maxHeartbeats 800000
            -- This is a comment
            -- axiom not_a_real_axiom : Nat
            open Classical in
            attribute [instance] Classical.propDecidable
            macro_rules
              | `(tactic| tactus_first $[| $ts:tacticSeq]*) => `(tactic| skip)
        "#;
        let names = extract_prelude_names(synthetic);
        assert!(names.is_empty(),
            "non-definition lines shouldn't introduce names; got {:?}", names);
    }

    #[test]
    fn extract_prelude_names_handles_each_form() {
        let synthetic = r#"
            axiom my_axiom : Nat
            def my_def : Int := 0
            noncomputable def my_ncdef : Int := 1
            syntax "my_syntax" : tactic
            macro "my_macro" : tactic => `(tactic| skip)
            elab "my_elab" : tactic => do return
        "#;
        let names = extract_prelude_names(synthetic);
        for expected in &["my_axiom", "my_def", "my_ncdef",
                          "my_syntax", "my_macro", "my_elab"] {
            assert!(names.contains(*expected),
                "expected `{}` in {:?}", expected, names);
        }
    }

    /// Pin which multi-line def shapes the parser handles, and which it
    /// misses. DESIGN.md catalogue flagged the line-based parser as a
    /// concern for "future prelude growth"; this test makes the actual
    /// failure surface concrete:
    ///
    /// * `def name\n  : Type := body` — works (name is on the same
    ///   line as `def`, so line-1 extraction succeeds).
    /// * `def name {A : Type}\n  [Inhabited A] : T A := body` — works
    ///   (same reason; the implicit-binder section on line 1 doesn't
    ///   matter because take_while on `name {A : ...` stops at `{`).
    /// * `def name :=\n  body` — works (name on line 1, body wraps).
    /// * `noncomputable\ndef name : T := body` — MISSES (line 1 is
    ///   bare `noncomputable` with no name; line 2 has `def name` but
    ///   the parser handles `noncomputable def NAME` as a single-line
    ///   prefix only; on line 2 alone, `def name` does match the bare
    ///   `def NAME` form, so this case ACTUALLY works through that
    ///   fallback).
    /// * `def\n  name : T := body` — MISSES (line 1 is bare `def`, no
    ///   space-after-def matches; line 2 doesn't match any prefix).
    ///
    /// The single failure mode is bare `def\n` separated from the
    /// name. That's unidiomatic Lean (no one writes it that way), but
    /// pinning it makes the actual failure surface concrete instead of
    /// the DESIGN.md guess.
    #[test]
    fn extract_prelude_names_multi_line_def_shapes() {
        // Cases that should work:
        let works_a = "def my_a\n  : Int := 0";
        let works_b = "def my_b {A : Type}\n  [Inhabited A] : Int := 0";
        let works_c = "def my_c :=\n  0";
        let works_d = "noncomputable\ndef my_d : Int := 0";
        for (label, src) in &[("a", works_a), ("b", works_b),
                              ("c", works_c), ("d", works_d)] {
            let names = extract_prelude_names(src);
            let expected = format!("my_{}", label);
            assert!(names.contains(&expected),
                "case {}: expected `{}` in {:?}", label, expected, names);
        }

        // The single failure mode: bare `def\n` separated from name.
        let fails = "def\n  my_e : Int := 0";
        let names = extract_prelude_names(fails);
        assert!(!names.contains("my_e"),
            "bare `def\\n` followed by name on next line is not handled \
             by the line-based parser; if this case starts working, \
             update extract_prelude_names docs");
    }

    /// Regression guard: every name the old hardcoded allowlist had
    /// should still be accepted via the auto-derived path. Catches any
    /// future TactusPrelude.lean refactor that removes one of these
    /// without realising the sanity-check depended on it.
    #[test]
    fn cached_prelude_names_includes_legacy_allowlist() {
        let cached = cached_prelude_names();
        for legacy in &["arch_word_bits", "arch_word_bits_valid",
                        "usize_hi", "isize_hi",
                        "tactus_peel", "tactus_usize_bound"] {
            assert!(cached.contains(*legacy),
                "legacy allowlist name `{}` missing from auto-derived set; \
                 did TactusPrelude.lean change?", legacy);
        }
    }

    /// Pin that `name_resolves` accepts a prelude-defined name. Catches
    /// regressions where the wiring between `cached_prelude_names`
    /// and `name_resolves` breaks (e.g., someone re-introducing the
    /// hardcoded `matches!` arm without removing the cache lookup, or
    /// vice versa).
    #[test]
    fn name_resolves_accepts_prelude_name() {
        let defined = HashSet::new();
        let scope = HashSet::new();
        assert!(name_resolves("arch_word_bits", &defined, &scope));
        assert!(name_resolves("usize_hi", &defined, &scope));
        assert!(name_resolves("tactus_peel", &defined, &scope));
        // Sanity: a made-up name is still rejected.
        assert!(!name_resolves("not_a_prelude_name_xyz", &defined, &scope));
    }
}
