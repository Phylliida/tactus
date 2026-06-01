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

        // Axiom: declares a constant. Adds the name to `defined` so
        // downstream references resolve. Binder types may reference
        // earlier top-level names; check them.
        Command::Axiom(a) => {
            defined.insert(a.name.clone());
            let mut scope = scope_from_binders(&a.binders);
            for b in &a.binders {
                check_expr(&b.ty, defined, &mut scope, violations, &a.name);
            }
            check_expr(&a.ret_ty, defined, &mut scope, violations, &a.name);
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
            // Method type signatures + default bodies can reference
            // types and other class methods — check them under the
            // class's typ_params scope.
            let mut scope = scope_from_binders(&c.typ_params);
            for b in &c.bounds { check_expr(&b.ty, defined, &mut scope, violations, &c.name); }
            // Methods can reference each other in defaults (standard
            // typeclass-self-reference pattern). Predefine each
            // method's name in scope before checking any default
            // body, so cross-method references inside defaults
            // resolve.
            for m in &c.methods {
                scope.insert(m.name.clone());
            }
            for m in &c.methods {
                check_expr(&m.ty, defined, &mut scope, violations, &c.name);
                if let Some(default) = &m.default {
                    check_expr(default, defined, &mut scope, violations, &c.name);
                }
                for t in &m.termination_by {
                    check_expr(t, defined, &mut scope, violations, &c.name);
                }
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
                    Command::Axiom(a) => { defined.insert(a.name.clone()); }
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
        // ByBlock contains opaque tactic text (not LExpr references)
        // — the sanity check doesn't validate Lean tactic syntax,
        // matching how `Tactic::Raw` in theorem bodies is treated.
        ExprNode::Lit(_) | ExprNode::LitBool(_)
        | ExprNode::LitStr(_) | ExprNode::LitChar(_)
        | ExprNode::Raw(_) | ExprNode::ByBlock { .. } => {}

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
            // Dependent binders: check each binder's type under the
            // scope WITH all prior binders bound, then add this binder
            // to scope before the next one. Required for shapes like
            // `∀ (self : Self) (h : P self), ...` where `(h : P self)`
            // references `self` introduced by the first binder.
            let mut added: Vec<String> = Vec::new();
            for b in binders {
                check_expr(&b.ty, defined, scope, violations, context);
                if let Some(n) = &b.name {
                    let s = n.as_str().to_string();
                    if scope.insert(s.clone()) { added.push(s); }
                }
            }
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

        ExprNode::Subtype { name, ty, pred } => {
            // `{ name : ty // pred }` — `ty` is in outer scope;
            // `pred` is in scope extended by `name`.
            check_expr(ty, defined, scope, violations, context);
            let n = name.as_str().to_string();
            let pushed = scope.insert(n.clone());
            check_expr(pred, defined, scope, violations, context);
            if pushed { scope.remove(&n); }
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
        // `Nonempty` typeclass — the `[Nonempty T]` binder Tactus
        // synthesises for fns/instances/lemmas that `choose` over a
        // type-param T (Lean's `Classical.epsilon` requires it). See
        // `nonempty.rs`.
        | "Nonempty"
        // `sizeOf` — Lean's auto-derived size measure (`SizeOf`
        // typeclass). Used in `termination_by sizeOf <arg>` clauses
        // emitted for recursive height fns where the arg's structural
        // recursion would otherwise fail Lean's WF inference (e.g.,
        // recursive datatypes whose recursive field is wrapper-typed
        // like `Box<Self>` — Lean's structural analyzer doesn't see
        // through the wrapper's `.deref` projection).
        | "sizeOf"
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
#[path = "tests/sanity.rs"]
mod tests;
