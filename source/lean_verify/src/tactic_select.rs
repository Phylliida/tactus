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

/// Classify a fully-wrapped obligation goal. `binders` are the
/// theorem's binders (fn params, requires-hypotheses — whose TYPES are
/// the hypothesis propositions — and any extras). Returns `None` when
/// the goal is not certainly in the fragment.
pub(crate) fn select_deterministic(goal: &Expr, binders: &[Binder]) -> Option<Selection> {
    // Over-approximate the goal's free variables by every Var name
    // that occurs anywhere in it (ignoring binding structure). Extra
    // names only force MORE binder-type checks — conservative.
    let mut used = std::collections::HashSet::new();
    collect_var_names(goal, &mut used);

    // Every binder the goal mentions must itself be in-fragment:
    // an Int/Nat variable, or a hypothesis whose proposition is
    // in-fragment. Binders the goal never mentions (opaque receivers,
    // type params) are irrelevant.
    for b in binders {
        let Some(name) = &b.name else { continue };
        if !used.contains(name.as_str()) {
            continue;
        }
        if !frag_type(&b.ty) && !frag_hyp(&b.ty) {
            return None;
        }
    }

    let mut wrapped = false;
    if frag(goal, true, &mut wrapped) {
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
/// type params, `Bool`) are rejected rather than sliding through
/// `frag`'s bare-Var admission (which is meant for TERM variables).
fn frag_hyp(ty: &Expr) -> bool {
    match &ty.node {
        ExprNode::SpanMark { inner, .. } => frag_hyp(inner),
        ExprNode::BinOp { op, .. } => matches!(
            op,
            BinOp::And | BinOp::Or | BinOp::Iff | BinOp::Implies
            | BinOp::Eq | BinOp::Ne
            | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
        ) && frag(ty, false, &mut false),
        ExprNode::UnOp { op: UnOp::Not, .. } => frag(ty, false, &mut false),
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
fn frag(e: &Expr, spine: bool, wrapped: &mut bool) -> bool {
    let mut prop_vars = std::collections::HashSet::new();
    frag_prop(e, spine, wrapped, &mut prop_vars)
}

fn frag_prop(
    e: &Expr,
    spine: bool,
    wrapped: &mut bool,
    prop_vars: &mut std::collections::HashSet<String>,
) -> bool {
    match &e.node {
        ExprNode::SpanMark { inner, .. } => frag_prop(inner, spine, wrapped, prop_vars),

        // A bare var in prop position must be a let-bound prop atom
        // (peel substitutes it back into its comparison). Term-typed
        // vars are not props; Bool params were already rejected by the
        // binder check (Bool is out of the fragment).
        ExprNode::Var(n) => prop_vars.contains(n.as_str()),
        ExprNode::LitBool(_) => false, // True/False goals: out (v1)

        ExprNode::BinOp { op, lhs, rhs } => match op {
            BinOp::And | BinOp::Or | BinOp::Iff => {
                frag_prop(lhs, false, wrapped, prop_vars)
                    && frag_prop(rhs, false, wrapped, prop_vars)
            }
            // `→` continues the spine on the right; the left is a
            // hypothesis peel will intro.
            BinOp::Implies => {
                if spine {
                    *wrapped = true;
                }
                frag_prop(lhs, false, wrapped, prop_vars)
                    && frag_prop(rhs, spine, wrapped, prop_vars)
            }
            // Comparisons and equality: TERM operands only.
            BinOp::Eq | BinOp::Ne
            | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                frag_term(lhs, prop_vars) && frag_term(rhs, prop_vars)
            }
            _ => false,
        },

        ExprNode::UnOp { op: UnOp::Not, arg } => {
            frag_prop(arg, false, wrapped, prop_vars)
        }

        // Wrappers: admitted on the spine only.
        ExprNode::Forall { binders, body } => {
            if !spine {
                return false;
            }
            *wrapped = true;
            binders.iter().all(|b| frag_type(&b.ty) || frag_hyp(&b.ty))
                && frag_prop(body, true, wrapped, prop_vars)
        }
        ExprNode::Let { name, value, body } => {
            if !spine {
                return false;
            }
            *wrapped = true;
            if frag_term(value, prop_vars) {
                // Term-bound: the var stays a term atom.
            } else if frag_prop(value, false, &mut false, prop_vars) {
                prop_vars.insert(name.as_str().to_string());
            } else {
                return false;
            }
            frag_prop(body, true, wrapped, prop_vars)
        }

        _ => false,
    }
}

/// TERM layer: Int/Nat-valued expressions omega treats as linear
/// arithmetic atoms/terms.
fn frag_term(e: &Expr, prop_vars: &std::collections::HashSet<String>) -> bool {
    match &e.node {
        ExprNode::SpanMark { inner, .. } => frag_term(inner, prop_vars),
        ExprNode::TypeAnnot { expr, ty } => {
            frag_type(ty) && frag_term(expr, prop_vars)
        }
        // A prop-bound let var is NOT a term.
        ExprNode::Var(n) => !prop_vars.contains(n.as_str()),
        ExprNode::Lit(_) => true,
        ExprNode::BinOp { op, lhs, rhs } => match op {
            BinOp::Add | BinOp::Sub => {
                frag_term(lhs, prop_vars) && frag_term(rhs, prop_vars)
            }
            // Linear only: multiplication by a literal.
            BinOp::Mul => {
                (is_lit(lhs) || is_lit(rhs))
                    && frag_term(lhs, prop_vars)
                    && frag_term(rhs, prop_vars)
            }
            // omega supports div/mod by integer literals.
            BinOp::Div | BinOp::Mod => is_lit(rhs) && frag_term(lhs, prop_vars),
            _ => false,
        },
        ExprNode::UnOp { op: UnOp::Neg, arg } => frag_term(arg, prop_vars),
        // omega-native cast atoms: `e.toNat` / `Int.toNat e`.
        ExprNode::FieldProj { expr, field } if field == "toNat" => {
            frag_term(expr, prop_vars)
        }
        ExprNode::App { head, args } => {
            matches!(&head.node,
                ExprNode::Var(n) if matches!(n.as_str(), "Int.toNat" | "Int.natAbs"))
                && args.len() == 1
                && frag_term(&args[0], prop_vars)
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
