//! Layer 7 — replay Verus's `#[verifier::inline]` spec-fn inlining on the
//! VIR-AST, so VIR-AST-rendered spec expressions agree with SST-rendered ones.
//!
//! ## The divergence this closes
//!
//! Verus's `sst_elaborate` inlines a spec-fn call when
//! `attrs.inline && kind.inline_okay()` (the `#[verifier::inline]` attribute),
//! substituting the callee's body. That pass runs on the **SST**, so exec-fn
//! goals — which Tactus renders from the SST — see `#[inline]` fns *unfolded*
//! (e.g. `m@.contains_key(k)` arrives as `m@.dom().contains(k)`). But Tactus
//! renders proof-fn goals and broadcast-lemma clauses from the **VIR-AST**,
//! where the call stays *folded* (`map_lib.contains_key m k`). A broadcast lemma
//! stated over the folded form then can't match an exec goal stated over the
//! unfolded form, and `tactus_auto`'s `simp_all` can't bridge them (it won't
//! delta-reduce a `noncomputable def`).
//!
//! `#[inline]` is the *only* axis on which SST- and VIR-AST-rendered spec
//! expressions diverge: default / `open` / `closed` spec fns stay folded on
//! *both* paths (hence the documented "spec fn in goal position needs `unfold`"
//! workflow), `#[verifier::opaque]` is `@[irreducible]` everywhere, and the
//! uninterp vstd primitives have no body to unfold. So mirroring `sst_elaborate`
//! here closes the divergence class entirely, for every `#[inline]` fn in any
//! crate, in proof fns and broadcast lemmas alike — not a `contains_key`
//! point-fix. This is the second member of the existing pattern "replay the
//! Verus AST→SST transforms that affect spec-expression shape" (the first being
//! the `ExprX::Multi` arm's replay of `ast_simplify`'s chained-compare
//! expansion). See DESIGN § "Cross-crate `HashMap::contains_key` deep-view-body
//! arc" layer 7.
//!
//! ## What the pass does
//!
//! One krate-level VIR-AST→VIR-AST transform, run before dep_order and all
//! rendering so there is a single inlined source of truth:
//! * inline every `#[inline]` call in every function's
//!   require / ensure / returns / decrease / body, recursively (bottom-up;
//!   `#[inline]` fns are non-recursive by Verus's well-formedness check); and
//! * **drop** the inline-able *inherent* (`Static`) fns from the function list —
//!   once their calls are inlined they get no Lean `def`, exactly as Verus emits
//!   no SMT symbol for them. An inline *trait-impl* method keeps its def: the
//!   trait `instance` references it as a method field, so dropping it would
//!   leave Lean's instance "fields missing" (see `can_drop`).

use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{
    CallTarget, CallTargetKind, Expr, ExprX, Exprs, Fun, Function, FunctionKind, FunctionX, Ident,
    Idents, KrateX, PlaceX, SpannedTyped, Typ, Typs, VirErr,
};
use vir::ast_visitor::{map_expr_typ_visitor, map_expr_visitor};
use vir::def::Spanned;
use vir::sst_util::subst_typ;

/// Mirror of Verus's `FunctionKind::inline_okay` (`pub(crate)` there): inlining
/// is only safe for statically-resolved targets, never a trait method *decl*
/// (whose default body might be overridden by an impl). Exhaustive (no `_`) so a
/// new Verus `FunctionKind` variant is a compile error here rather than silently
/// defaulting to non-inline — the upstream-robustness convention.
fn inline_okay(kind: &FunctionKind) -> bool {
    match kind {
        FunctionKind::Static | FunctionKind::TraitMethodImpl { .. } => true,
        FunctionKind::TraitMethodDecl { .. } | FunctionKind::ForeignTraitMethodImpl { .. } => false,
    }
}

/// A spec fn whose *calls* we inline: marked `#[verifier::inline]`, inline-okay
/// (mirroring Verus's `sst_elaborate`), with a **binder-free** body we can
/// substitute into without variable capture. A binder-bodied `#[inline]` fn
/// (none exist in vstd today) is left folded — which is *sound* (it would fail
/// to close, never falsely pass), as opposed to a naive substitution that could
/// silently capture.
fn can_inline_call(f: &FunctionX) -> bool {
    f.attrs.inline && inline_okay(&f.kind) && f.body.as_ref().map_or(false, |b| !body_blocks_inlining(b))
}

/// Whether to also *drop* the fn's standalone def. Only `Static` (inherent)
/// inline fns become fully dead once their calls are inlined. A `TraitMethodImpl`
/// inline method must keep its def: the trait `instance` references it as a
/// method field (`view := …`), so dropping it leaves Lean's instance with a
/// "fields missing" error. Inlining its *calls* is still correct and faithful;
/// only the emission of its def is preserved.
///
/// Drop-safety: the only references this pass doesn't rewrite are ones held
/// *outside* function clauses/bodies — reveal-group members, datatype
/// invariant fns, assoc-type-impl values. An `#[inline]` fn appears in none of
/// these: it's always-transparent (never broadcast/revealed → not a reveal-group
/// member), it's `Static` (never a `TraitMethodImpl`, so not an instance method
/// or assoc-type value), and Tactus emits no datatype-invariant fns. A surviving
/// reference would, regardless, fail *loud* (Lean "unknown constant"), never
/// silently mis-resolve.
fn can_drop(f: &FunctionX) -> bool {
    can_inline_call(f) && matches!(f.kind, FunctionKind::Static)
}

/// Does the body contain anything that makes naive `Var`-substitution unsafe —
/// a node that binds variables (capture risk) or a non-trivial block (which
/// `unwrap_trivial_block` can't peel into expression position)? If so we refuse
/// to inline (keeping the call folded — *sound*: it fails to close, never
/// falsely passes) rather than build full hygienic VIR-AST substitution for a
/// shape vstd never produces. The binder list errs conservative: anything that
/// introduces a scope is flagged, so widening the inline-able set later can't
/// silently re-open the capture hole.
fn body_blocks_inlining(e: &Expr) -> bool {
    let found = std::cell::Cell::new(false);
    // Read-only scan via the map visitor; the cloned (tiny) inline body is
    // discarded. `fe` is `Fn`, so interior mutability carries the flag out.
    let _ = map_expr_visitor(e, &|node: &Expr| {
        let blocks = match &node.x {
            ExprX::Quant(..)
            | ExprX::Closure(..)
            | ExprX::NonSpecClosure { .. }
            | ExprX::Choose { .. }
            | ExprX::Match(..)
            | ExprX::AssertBy { .. }      // binds `vars` (assert-forall)
            | ExprX::OpenInvariant(..)    // binds the opened invariant value
            | ExprX::Loop { .. } => true, // not expected in a spec body; refuse if seen
            // A `{ … }` block: refuse if it carries ANY statement. A `Decl`
            // binds; and `unwrap_trivial_block` only peels statement-free
            // blocks, so a `{ s; e }` body can't be safely spliced into
            // expression position regardless. A spec-fn body `{ expr }` is
            // `Block([], Some(expr))` — empty, so it inlines.
            ExprX::Block(stmts, _) => !stmts.is_empty(),
            _ => false,
        };
        if blocks {
            found.set(true);
        }
        Ok(node.clone())
    });
    found.get()
}

/// Build a transformed krate where every `#[inline]` call is inlined in every
/// function's clauses/body, and the inline-able fns are dropped (no Lean def).
/// Identity (modulo a clone) for crates with no `#[inline]` fns.
pub fn inline_marked_in_krate(krate: &KrateX) -> KrateX {
    // Common case (most crates have no `#[verifier::inline]` fns): skip the deep
    // per-clause rebuild — a shallow KrateX clone (Arc-sharing the function
    // bodies) is enough. The `attrs.inline &&` short-circuit in `can_inline_call`
    // keeps this scan cheap (no body walk for the overwhelming non-inline
    // majority). (This pass re-runs per checked fn; that's acceptable —
    // verification is Lean-I/O-bound, and this is pure-Rust work over a pruned
    // krate. Memoize if a profile ever says otherwise.)
    if !krate.functions.iter().any(|f| can_inline_call(&f.x)) {
        return krate.clone();
    }

    let fn_map: HashMap<&Fun, &FunctionX> =
        krate.functions.iter().map(|f| (&f.x.name, &f.x)).collect();

    let mut new_functions: Vec<Function> = Vec::with_capacity(krate.functions.len());
    for f in krate.functions.iter() {
        if can_drop(&f.x) {
            continue; // dropped: all its calls are inlined; no def emitted (matches Verus)
        }
        let nx = inline_in_function(&f.x, &fn_map);
        new_functions.push(Spanned::new(f.span.clone(), nx));
    }

    let mut new_krate = krate.clone();
    new_krate.functions = new_functions;
    new_krate
}

fn inline_in_function(f: &FunctionX, fn_map: &HashMap<&Fun, &FunctionX>) -> FunctionX {
    let map_clauses = |es: &Exprs| -> Exprs {
        Arc::new(es.iter().map(|e| inline_calls(e, fn_map)).collect::<Vec<Expr>>())
    };
    let mut nf = f.clone();
    nf.require = map_clauses(&f.require);
    nf.ensure = (map_clauses(&f.ensure.0), map_clauses(&f.ensure.1));
    nf.returns = f.returns.as_ref().map(|e| inline_calls(e, fn_map));
    nf.decrease = map_clauses(&f.decrease);
    nf.body = f.body.as_ref().map(|e| inline_calls(e, fn_map));
    nf
}

/// Inline every `#[inline]` call in `expr`, recursively (bottom-up). Terminates
/// because `#[inline]` fns are non-recursive (Verus well-formedness enforces
/// `decrease.len() == 0` and rejects recursion), so the inline call graph is a
/// DAG — same termination assumption `sst_elaborate` itself relies on.
fn inline_calls(expr: &Expr, fn_map: &HashMap<&Fun, &FunctionX>) -> Expr {
    // `map_expr_visitor` applies `fe` post-order, so a Call's args are already
    // inlined when we see it; returning the substituted body (itself inlined,
    // to catch inline calls inside the body) replaces the call node.
    map_expr_visitor(expr, &|e: &Expr| -> Result<Expr, VirErr> {
        if let ExprX::Call(CallTarget::Fun(kind, fun, typs, ..), args, _) = &e.x {
            // Mirror sst_elaborate: a DynamicResolved call inlines its resolved
            // target; everything else inlines the static `fun`.
            let (eff_fun, eff_typs) = match kind {
                CallTargetKind::DynamicResolved { resolved, typs, .. } => (resolved, typs),
                _ => (fun, typs),
            };
            if let Some(f) = fn_map.get(eff_fun) {
                if can_inline_call(f) {
                    let body = unwrap_trivial_block(f.body.as_ref().expect("can_inline_call ⇒ body present"));
                    let substituted = substitute_body(body, &f.typ_params, eff_typs, f, args);
                    // Re-stamp the inlined result with the *call site's* span and
                    // type — mirroring sst_elaborate (`SpannedTyped::new(&exp.span,
                    // &exp.typ, …)`). The call site's type may carry reference
                    // decorations (e.g. `&V` where the surrounding context borrows
                    // the result) that the callee's bare return type (`V`) lacks;
                    // preserving it keeps use-site `.mk`/`.deref` coercions firing.
                    let retyped = SpannedTyped::new(&e.span, &e.typ, substituted.x.clone());
                    return Ok(inline_calls(&retyped, fn_map));
                }
            }
        }
        Ok(e.clone())
    })
    .expect("inline_calls callback never errors")
}

/// Peel a spec-fn body's trivial `{ expr }` wrapper — `Block([], Some(inner))`
/// with no declarations is just `inner`. Avoids carrying a stray block node
/// into the inlined site (which would muddle use-site coercion depth). Only
/// peels decl-free blocks; `can_inline` already guarantees no `Decl`s.
fn unwrap_trivial_block(e: &Expr) -> &Expr {
    match &e.x {
        ExprX::Block(stmts, Some(inner)) if stmts.is_empty() => unwrap_trivial_block(inner),
        _ => e,
    }
}

/// Substitute the callee's type params → `typs` and value params → `args` into
/// `body`. `body` is binder-free (guaranteed by `can_inline`), so direct
/// `Var`-replacement is capture-free.
fn substitute_body(body: &Expr, typ_params: &Idents, typs: &Typs, f: &FunctionX, args: &Exprs) -> Expr {
    // Length invariants Verus's own `sst_elaborate` asserts. They hold for every
    // call Verus's resolution produces (Static and DynamicResolved alike); a
    // mismatch would otherwise silently `zip`-truncate, leaving an
    // un-substituted `TypParam`/`Var` dangling in the goal. Fail loud instead.
    assert_eq!(typ_params.len(), typs.len(),
        "inline fn typ_params/typ_args length mismatch — Verus resolution invariant violated");
    assert_eq!(f.params.len(), args.len(),
        "inline fn params/args length mismatch — Verus resolution invariant violated");

    // 1. Type substitution (`K` ↦ `u8`, …) on every Typ embedded in the body.
    let typ_substs: HashMap<Ident, Typ> =
        typ_params.iter().cloned().zip(typs.iter().cloned()).collect();
    let body = map_expr_typ_visitor(body, &|t: &Typ| Ok(subst_typ(&typ_substs, t)))
        .expect("typ subst callback never errors");

    // 2. Value substitution (param `Var` → arg). Keyed by the param's name
    //    string, matching Tactus's by-name VarIdent convention; params within a
    //    single fn have distinct names, and a body's param references carry the
    //    same name as the param binding.
    let val_substs: HashMap<String, Expr> = f
        .params
        .iter()
        .map(|p| p.x.name.0.to_string())
        .zip(args.iter().cloned())
        .collect();
    map_expr_visitor(&body, &|e: &Expr| -> Result<Expr, VirErr> {
        // A param is referenced as a plain `Var` (by-value params, e.g. `k`), a
        // staged `VarAt`, or a whole-local place read `ReadPlace(Local(p))`
        // (by-reference receivers, e.g. `self`) — each reads the param's value
        // and is replaced wholesale with the corresponding arg expr. A param
        // appearing inside a *nested* place (`ReadPlace(Field(Local(p)))`,
        // `*p`) is NOT substitutable to an arbitrary arg expr at the VIR-AST
        // Place/Expr boundary; such a body would leave the param dangling →
        // caught loud by the sanity check (`unresolved p`). No vstd `#[inline]`
        // fn does field/deref access on a param (all use whole-receiver method
        // calls), so this doesn't arise today.
        let referenced = match &e.x {
            ExprX::Var(v) | ExprX::VarLoc(v) | ExprX::VarAt(v, _) => Some(v),
            ExprX::ReadPlace(place, _) => match &place.x {
                PlaceX::Local(v) => Some(v),
                _ => None,
            },
            _ => None,
        };
        if let Some(v) = referenced {
            if let Some(arg) = val_substs.get(&v.0.to_string()) {
                return Ok(arg.clone());
            }
        }
        Ok(e.clone())
    })
    .expect("value subst callback never errors")
}

#[cfg(test)]
mod tests {
    use super::*;
    use vir::ast::{Path, PathX};

    fn dummy_path() -> Path {
        Arc::new(PathX { krate: None, segments: Arc::new(vec![]) })
    }

    // `inline_okay` is the gate that lets blanket-impl `#[inline]` methods
    // (`TraitMethodImpl`) be inlined while a trait method *decl* (whose default
    // body might be overridden) is never inlined — mirroring Verus's own
    // `FunctionKind::inline_okay`. It also underpins `can_drop` (drop only
    // `Static`). The richer behaviour (self-as-`ReadPlace` substitution,
    // trivial-block peel, typ-preservation, Static-drop vs TraitMethodImpl-keep)
    // is exercised end-to-end by `test_cross_crate_map_contains_key`,
    // `test_cross_crate_set_contains`, and `test_exec_call_mut_arg_vec_index`.
    #[test]
    fn inline_okay_matches_verus() {
        assert!(inline_okay(&FunctionKind::Static));
        assert!(inline_okay(&FunctionKind::TraitMethodImpl {
            method: Arc::new(vir::ast::FunX { path: dummy_path() }),
            impl_path: dummy_path(),
            trait_path: dummy_path(),
            trait_typ_args: Arc::new(vec![]),
            inherit_body_from: None,
        }));
        assert!(!inline_okay(&FunctionKind::TraitMethodDecl {
            trait_path: dummy_path(),
            has_default: true,
        }));
    }
}
