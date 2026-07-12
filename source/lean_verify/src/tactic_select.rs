//! Deterministic-floor tactic selection (S1 of the squeeze-and-pin arc,
//! `DESIGN-transparent-automation.md`; measured basis:
//! `MEASUREMENT-brick1-rung-attribution.md`).
//!
//! When an obligation theorem's goal — hypotheses included, since
//! `emit_split` wraps them into the goal as binder types and
//! implications — lies entirely inside the LINEAR INTEGER ARITHMETIC
//! fragment, the emitter selects `omega` (or `tactus_peel <;> omega`
//! for ∀/let/→-wrapped goals) instead of the `tactus_auto` search
//! gate.
//!
//! Safety argument (why selection cannot lose passes): `omega` is a
//! DECISION PROCEDURE for the fragment — complete. Any in-fragment
//! goal that `tactus_auto` closed (through whichever rung) is
//! therefore closed by `omega` directly. Goals needing a broadcast
//! axiom or a spec-fn unfolding necessarily mention an out-of-fragment
//! head (the axiom's subject — `Seq.len`, a spec fn, …), so they can
//! never be misclassified into the fragment. The classification is
//! purely syntactic and total: unknown node kinds fall out of the
//! fragment, never into it.
//!
//! Guiding rule served (Danielle, 2026-07-11): every injected tactic
//! carries its own specification, readable at the site — `omega`'s
//! name IS its spec, and the fragment check is exactly that spec.
//!
//! v1 scope notes:
//! - `Bool` is OUT of the fragment (omega is Int/Nat only; Bool-valued
//!   equalities fall to `simp`-class reasoning). `True`/`False` goals
//!   are likewise left to the default closer.
//! - `ite` is OUT (omega does not split; that's the
//!   `(repeat split) <;> omega` shape — a candidate v2 selection).
//! - `Int.toNat` is IN (omega handles it natively; it appears in
//!   emitted usize-cast goals — both `e.toNat` field-proj and
//!   `Int.toNat e` application forms).
//! - Broadcast `have` prefixes stay attached even when omega is
//!   selected (harmless: omega ignores non-arithmetic hypotheses);
//!   trimming them is a v2 nicety.

use crate::lean_ast::{BinOp, Binder, Expr, ExprNode, UnOp};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Selection {
    /// Bare arithmetic goal: `omega`.
    Omega,
    /// Arithmetic goal behind leading ∀ / `let` / `→` wrappers:
    /// `tactus_peel <;> omega` (peel intros the spine, omega closes).
    PeelOmega,
}

impl Selection {
    pub(crate) fn tactic_text(self) -> &'static str {
        match self {
            Selection::Omega => "omega",
            Selection::PeelOmega => "tactus_peel <;> omega",
        }
    }
}

/// Names that are known to be Int/Nat-valued (term layer) or
/// let-bound propositions (prop layer) in the current scope. A bare
/// `Var` is admitted as an integer TERM atom ONLY if it is in
/// `int_vars` — never merely because it "looks like a variable". This
/// is the load-bearing invariant: a global reference such as a
/// nullary spec fn (`test_crate.pair`, which renders as a bare `Var`,
/// not an `App`) is NOT a local integer, so `pair = pair` must fall
/// out of the arithmetic fragment rather than be handed to omega.
/// (Regression exposed by the bootstrap merge: the package-check path
/// emits that obligation as a `theorem := by <closer>` — which S1
/// classifies — whereas the islands path emitted it as a `Prop` def
/// that selection never saw. Being global-blind here fixes it for
/// both paths.)
#[derive(Default, Clone)]
struct Env {
    int_vars: std::collections::HashSet<String>,
    prop_vars: std::collections::HashSet<String>,
}

/// Classify a fully-wrapped obligation goal. `binders` are the
/// theorem's binders (fn params, requires-hypotheses — whose TYPES are
/// the hypothesis propositions — and any extras). Returns `None` when
/// the goal is not certainly in the fragment.
pub(crate) fn select_deterministic(goal: &Expr, binders: &[Binder]) -> Option<Selection> {
    let mut used = std::collections::HashSet::new();
    collect_var_names(goal, &mut used);

    // Seed the typing environment: every Int/Nat-typed binder is a
    // known integer term variable. (Built from ALL binders, not just
    // used ones — harmless, and a hypothesis over a param needs the
    // param present regardless of goal mentions.)
    let mut env = Env::default();
    for b in binders {
        if let Some(name) = &b.name {
            if frag_type(&b.ty) {
                env.int_vars.insert(name.as_str().to_string());
            }
        }
    }

    // Every binder the goal mentions must itself be in-fragment: an
    // Int/Nat variable, or a hypothesis whose proposition is
    // in-fragment. Binders the goal never mentions (opaque receivers,
    // type params) are irrelevant.
    for b in binders {
        let Some(name) = &b.name else { continue };
        if !used.contains(name.as_str()) {
            continue;
        }
        if !frag_type(&b.ty) && !frag_hyp(&b.ty, &env) {
            return None;
        }
    }

    let mut wrapped = false;
    if frag_prop(goal, true, &mut wrapped, &mut env) {
        Some(if wrapped { Selection::PeelOmega } else { Selection::Omega })
    } else {
        None
    }
}

fn collect_var_names(e: &Expr, out: &mut std::collections::HashSet<String>) {
    match &e.node {
        ExprNode::Var(n) => {
            out.insert(n.as_str().to_string());
        }
        _ => e.for_each_child(|c| collect_var_names(c, out)),
    }
}

/// Is `ty` an arithmetic scalar type?
fn frag_type(ty: &Expr) -> bool {
    matches!(&ty.node, ExprNode::Var(n) if matches!(n.as_str(), "Int" | "Nat"))
}

/// Is `ty` an in-fragment hypothesis PROPOSITION (a requires-binder's
/// type)? Must be proposition-shaped at the top — a comparison,
/// connective, or negation — so bare opaque type names (`Tactus.Ref`,
/// type params, `Bool`) are rejected rather than sliding through the
/// prop walk. The inner check uses the current `env` so operands
/// resolve against the known integer variables (a hypothesis over an
/// unknown global is rejected).
fn frag_hyp(ty: &Expr, env: &Env) -> bool {
    let mut env = env.clone();
    let mut wrapped = false;
    match &ty.node {
        ExprNode::SpanMark { inner, .. } => frag_hyp(inner, &env),
        ExprNode::BinOp { op, .. } => matches!(
            op,
            BinOp::And | BinOp::Or | BinOp::Iff | BinOp::Implies
            | BinOp::Eq | BinOp::Ne
            | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
        ) && frag_prop(ty, false, &mut wrapped, &mut env),
        ExprNode::UnOp { op: UnOp::Not, .. } => {
            frag_prop(ty, false, &mut wrapped, &mut env)
        }
        _ => false,
    }
}

/// Two-layer fragment check — omega's actual domain:
/// * TERM layer: Int/Nat-valued — vars, literals, +,-,neg, *literal,
///   /literal, %literal, toNat atoms.
/// * PROP layer: comparisons over TERMS, Eq/Ne over TERMS (NOT over
///   props — propositional equality like `r = (x > 0)` is rfl/simp
///   territory, omega rejects it; the v1 bug this layering fixes),
///   connectives over props, ¬, and spine wrappers.
///
/// `let`-bound variables carry their layer: a var bound to a PROP
/// (`let r := x > 0; …`) is a prop atom — admissible as a conjunct
/// (peel's zeta-substitution turns it back into the comparison) but
/// NOT as an Eq operand.
///
/// `spine` is true while on the leading spine (∀ bodies, `let` bodies,
/// `→` right-hand sides) — positions `tactus_peel` can intro. Wrappers
/// are only admitted on the spine; `wrapped` records one was seen.
fn frag_prop(
    e: &Expr,
    spine: bool,
    wrapped: &mut bool,
    env: &mut Env,
) -> bool {
    match &e.node {
        ExprNode::SpanMark { inner, .. } => frag_prop(inner, spine, wrapped, env),

        // A bare var in prop position must be a let-bound prop atom
        // (peel substitutes it back into its comparison). Term-typed
        // vars are not props; Bool params were already rejected by the
        // binder check (Bool is out of the fragment).
        ExprNode::Var(n) => env.prop_vars.contains(n.as_str()),
        ExprNode::LitBool(_) => false, // True/False goals: out (v1)

        ExprNode::BinOp { op, lhs, rhs } => match op {
            BinOp::And | BinOp::Or | BinOp::Iff => {
                frag_prop(lhs, false, wrapped, env)
                    && frag_prop(rhs, false, wrapped, env)
            }
            // `→` continues the spine on the right; the left is a
            // hypothesis peel will intro.
            BinOp::Implies => {
                if spine {
                    *wrapped = true;
                }
                frag_prop(lhs, false, wrapped, env)
                    && frag_prop(rhs, spine, wrapped, env)
            }
            // Comparisons and equality: TERM operands only.
            BinOp::Eq | BinOp::Ne
            | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                frag_term(lhs, env) && frag_term(rhs, env)
            }
            _ => false,
        },

        ExprNode::UnOp { op: UnOp::Not, arg } => {
            frag_prop(arg, false, wrapped, env)
        }

        // Wrappers: admitted on the spine only.
        ExprNode::Forall { binders, body } => {
            if !spine {
                return false;
            }
            *wrapped = true;
            for b in binders {
                if frag_type(&b.ty) {
                    // Int/Nat quantified var — enters scope as a term.
                    if let Some(name) = &b.name {
                        env.int_vars.insert(name.as_str().to_string());
                    }
                } else if !frag_hyp(&b.ty, env) {
                    // Not an int var and not a hypothesis prop → out.
                    return false;
                }
            }
            frag_prop(body, true, wrapped, env)
        }
        ExprNode::Let { name, value, body } => {
            if !spine {
                return false;
            }
            *wrapped = true;
            if frag_term(value, env) {
                // Term-bound: the var is a known integer term.
                env.int_vars.insert(name.as_str().to_string());
            } else if frag_prop(value, false, &mut false, env) {
                env.prop_vars.insert(name.as_str().to_string());
            } else {
                return false;
            }
            frag_prop(body, true, wrapped, env)
        }

        _ => false,
    }
}

/// TERM layer: Int/Nat-valued expressions omega treats as linear
/// arithmetic atoms/terms.
fn frag_term(e: &Expr, env: &Env) -> bool {
    match &e.node {
        ExprNode::SpanMark { inner, .. } => frag_term(inner, env),
        ExprNode::TypeAnnot { expr, ty } => {
            frag_type(ty) && frag_term(expr, env)
        }
        // A bare Var is a term atom ONLY if it is a KNOWN integer local
        // (binder / ∀-Int-binder / term-let). Globals — including
        // nullary spec fns that render as bare `Var` (`test_crate.pair`)
        // — are NOT locals, so they fall out of the fragment. This is
        // the load-bearing conservatism: omega would treat an unknown
        // atom as a free variable and might close `pair = pair` by
        // chance, but `pair`'s VALUE (a Seq) makes that unsound in
        // general, and the goal wants rfl/simp, not omega.
        ExprNode::Var(n) => env.int_vars.contains(n.as_str()),
        ExprNode::Lit(_) => true,
        ExprNode::BinOp { op, lhs, rhs } => match op {
            BinOp::Add | BinOp::Sub => {
                frag_term(lhs, env) && frag_term(rhs, env)
            }
            // Linear only: multiplication by a literal.
            BinOp::Mul => {
                (is_lit(lhs) || is_lit(rhs))
                    && frag_term(lhs, env)
                    && frag_term(rhs, env)
            }
            // omega supports div/mod by integer literals.
            BinOp::Div | BinOp::Mod => is_lit(rhs) && frag_term(lhs, env),
            _ => false,
        },
        ExprNode::UnOp { op: UnOp::Neg, arg } => frag_term(arg, env),
        // omega-native cast atoms: `e.toNat` / `Int.toNat e`.
        ExprNode::FieldProj { expr, field } if field == "toNat" => {
            frag_term(expr, env)
        }
        ExprNode::App { head, args } => {
            matches!(&head.node,
                ExprNode::Var(n) if matches!(n.as_str(), "Int.toNat" | "Int.natAbs"))
                && args.len() == 1
                && frag_term(&args[0], env)
        }
        _ => false,
    }
}

fn is_lit(e: &Expr) -> bool {
    match &e.node {
        ExprNode::Lit(_) => true,
        ExprNode::UnOp { op: UnOp::Neg, arg } => is_lit(arg),
        ExprNode::TypeAnnot { expr, .. } => is_lit(expr),
        _ => false,
    }
}

#[cfg(test)]
#[path = "tests/tactic_select.rs"]
mod tests;
