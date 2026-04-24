//! Weakest-precondition VC generation from SST → Lean AST.
//!
//! Takes an exec fn's `FuncCheckSst` (from `FunctionSst::exec_proof_check`)
//! and produces a `Theorem` AST node whose goal is the WP of the body and
//! whose tactic body is `tactus_auto`.
//!
//! # Pipeline
//!
//! `exec_fn_theorems_to_ast` runs the pipeline:
//!
//! 1. `WpCtx::new` validates `reqs` / `ens_exps` via `check_exp` and
//!    constructs the shared context (fn_map, type_map, ret_name,
//!    ensures_goal).
//! 2. `build_wp(&check.body, Wp::Done(ensures_goal), &ctx)` walks the
//!    SST body right-to-left, producing a `Wp<'a>` tree where each
//!    compound node carries its own continuation by construction. Any
//!    unsupported SST form returns `Err` and bubbles up.
//! 3. `lower_wp(&body_wp, &ctx)` interprets the `Wp` tree into a Lean
//!    `LExpr` goal.
//! 4. Emission wraps the goal in a `Theorem` with either `tactus_auto`
//!    (flat goals) or `tactus_peel; all_goals tactus_auto` (when the
//!    WP introduces nested ∀/∧ structure — see `Wp::needs_peel`).
//!
//! # The `Wp` DSL
//!
//! `Wp<'a>` is a small algebra of WP-shaped operations:
//!
//!   * `Done(LExpr)` — terminator leaf; no continuation slot. Built
//!     from the fn's ensures at top level, `I ∧ D < _tactus_d_old`
//!     inside a loop body, or `let <ret> := e; ensures_goal` from a
//!     `return` statement.
//!   * `Let(x, rhs, after)` — `let x := rhs; <after>`. Lowering uses
//!     `lift_if_value` so an `ExpX::If` RHS lifts to goal level.
//!   * `Assert(P, after)` — `P ∧ <after>`.
//!   * `Assume(P, after)` — `P → <after>`.
//!   * `Branch { cond, then_branch, else_branch }` —
//!     `(c → then_branch) ∧ (¬c → else_branch)`. Each branch carries
//!     its own continuation; no shared-rest parameter.
//!   * `Loop { cond, invs, decrease, modified_vars, body, after }` —
//!     lowered to `I ∧ maintain_clause ∧ havoc_continuation`. `body`
//!     is built with its own `Done(I ∧ D < _tactus_d_old)`
//!     terminator; `after` is the post-loop continuation.
//!   * `Call { callee, args, dest, after }` — `requires(subst) ∧ ∀ ret,
//!     bound(ret) → ensures_using_ret(subst) → let dest := ret;
//!     <after>`. Inlines the callee's `require`/`ensure` via
//!     `lean_ast::substitute` (capture-avoiding).
//!
//! Three structural properties the DSL gets for free:
//!
//!   * **Continuation is type-level.** `Done` has no slot for a
//!     continuation, so "discard after Return" is enforced by the
//!     type system rather than by a positional convention.
//!   * **`Return` is fn-exit by construction.** Walk's `Return` arm
//!     ignores its `after` parameter and writes `Done(let <ret> := e;
//!     ctx.ensures_goal)`. No way to accidentally write to a loop's
//!     local terminator.
//!   * **Composition is structural.** Loops and calls compose like
//!     any other node; recursion into them is a normal tree walk,
//!     no special-case dispatcher.
//!
//! `build_wp` folds right-to-left over `StmX::Block` so each
//! statement's `after` is the already-built Wp for the rest of the
//! block. `Return` terminates a branch by dropping `after`.
//!
//! # Loop obligations (conjunctive WP)
//!
//! A loop contributes three pieces to the goal of the enclosing
//! theorem — conjoined inline rather than split into separate
//! theorems:
//!
//! ```
//! lower(Wp::Loop{ cond, invs, decrease, modified_vars, body, after })
//!   = I                                                      -- init
//!     ∧ (∀ mod_vars, bounds → I ∧ cond →
//!         let _tactus_d_old := D; lower(body))               -- maintain
//!     ∧ (∀ mod_vars, bounds → I ∧ ¬cond →
//!         lower(after))                                      -- havoc
//! ```
//!
//! where `body` has `Done(I ∧ D < _tactus_d_old)` as its own
//! terminator, so `lower(body)` naturally produces the maintain
//! clause's inner goal. The Lean `let _tactus_d_old := D; ...`
//! wrapper puts the pre-body `D` in scope; references to `D` *inside*
//! the body see post-body values via let-shadowing from intervening
//! assignments.
//!
//! Non-modified surrounding state stays in scope via the outer
//! `let`/`∀` nesting already built by the enclosing `lower_wp`
//! frames. Only `mod_vars` — variables the loop body writes to —
//! get the fresh universal quantification.
//!
//! # Mutation
//!
//! Simple mutation (`let mut x = …; x = …;`) needs no rename pass:
//! `StmX::Assign { is_init: false }` emits `Wp::Let(x, e, body)` just
//! like an init, and Lean's let-shadowing gives us SSA semantics
//! naturally. This also works across if-branches — an inner branch's
//! `let x := …` only shadows within its implication, so the outer
//! `x` remains in scope for the other branch and the code after the
//! if. Loops break this trick because the loop body's mutations
//! can't tunnel out through shadowing; they'll need a real rename
//! pass when we get there.

use std::collections::{HashMap, HashSet};

use vir::sst::{
    BndX, Dest, Exp, ExpX, FuncCheckSst, FunctionSst, LoopInv, Par, Stm, StmX,
};
use vir::ast::{
    AssertQueryMode, Fun, FunctionX, KrateX, TactusKind, Typ, UnaryOp, UnaryOpr, VarIdent,
};
use crate::lean_ast::{
    and_all, substitute, Binder as LBinder, BinderKind, Expr as LExpr, Tactic, Theorem,
};
use crate::to_lean_expr::vir_expr_to_ast;
use crate::to_lean_sst_expr::{sst_exp_to_ast, sst_exp_to_ast_checked, type_bound_predicate};
use crate::to_lean_type::{lean_name, sanitize, typ_to_expr};

/// Lookup table from callee `Fun` to its VIR-AST `FunctionX`. Used by
/// `Wp::Call` lowering to inline a callee's `requires` / `ensures`
/// at the call site. Callee's spec lives on `FunctionX` (VIR-AST),
/// not on its `FunctionSst`, so the map points at the AST form.
pub type FnMap<'a> = HashMap<&'a Fun, &'a FunctionX>;

/// Shared context threaded through the WP builder. Collects the
/// per-verification-unit state that nearly every walker / builder
/// needs — the callee lookup, the local declaration types, the fn's
/// ensures goal (where `return` terminates), and the declared return
/// var name (if any). Future additions — source spans, current-fn
/// name, etc. — plug into this struct instead of growing every
/// function signature.
/// The break / continue goal leaves in scope inside a loop body.
/// Threaded through `build_wp` as `Option<&WpLoopCtx>` — `None`
/// outside any loop (break/continue rejected), `Some(...)` inside a
/// loop's body. Inner loops shadow outer loops for unlabeled
/// break/continue (the innermost applies). Labeled break/continue
/// would need a stack; not yet supported.
///
/// The two leaves differ in what they need to prove:
/// * `continue_leaf` — on body fallthrough or `continue`, re-establish
///   the loop invariants AND show the decrease measure decreased.
///   Currently `I ∧ D < _tactus_d_old`.
/// * `break_leaf` — on `break`, establish the loop's at-exit
///   invariants (which the use clause will assume). Currently just
///   `I` since we only accept all-both invariants (at_entry = at_exit
///   = true). The decrease obligation doesn't apply on break — the
///   loop is terminating, not iterating.
pub struct WpLoopCtx {
    pub break_leaf: LExpr,
    pub continue_leaf: LExpr,
}

pub struct WpCtx<'a> {
    pub fn_map: FnMap<'a>,
    pub type_map: HashMap<&'a VarIdent, &'a Typ>,
    /// Declared return-var name (`-> (r: T)`), or `None` for unit
    /// returns. Used by `Wp::Done` leaves produced from `Return`
    /// statements to bind the returned value before jumping to the
    /// fn's ensures.
    pub ret_name: Option<&'a str>,
    /// Conjoined ensures clauses — what `Return` terminates at. For
    /// the top-level walk this is passed as the initial `after`; an
    /// explicit `return e` discards its textual continuation and
    /// writes `Done(let ret := e; ensures_goal)`.
    pub ensures_goal: LExpr,
}

impl<'a> WpCtx<'a> {
    /// Build the context for verifying `check` against `krate`.
    ///
    /// Validates `check.reqs` and `check.post_condition.ens_exps`
    /// up front via `check_exp`. If any expression uses an SST form
    /// we don't support, returns `Err(reason)` before constructing
    /// anything — in particular before the infallible
    /// `sst_exp_to_ast` call that renders `ensures_goal`, which
    /// would otherwise panic.
    ///
    /// The precondition "ens_exps is supported" thus lives in the
    /// type signature rather than in a docstring: you can only get
    /// a `WpCtx` by passing validation.
    pub fn new(krate: &'a KrateX, check: &'a FuncCheckSst) -> Result<Self, String> {
        for req in check.reqs.iter() {
            check_exp(req)?;
        }
        for ens in check.post_condition.ens_exps.iter() {
            check_exp(ens)?;
        }
        let fn_map = krate.functions.iter().map(|f| (&f.x.name, &f.x)).collect();
        let type_map = check.local_decls.iter().map(|d| (&d.ident, &d.typ)).collect();
        let ret_name = check.post_condition.dest.as_ref().map(|v| v.0.as_str());
        let ensures_goal = and_all(
            check.post_condition.ens_exps.iter().map(sst_exp_to_ast).collect()
        );
        Ok(Self { fn_map, type_map, ret_name, ensures_goal })
    }
}

// ── Support check (helpers) ────────────────────────────────────────────
//
// The main validation is fused into `build_wp` below — a single pass
// that both checks shape constraints and builds the `Wp` tree. The
// helpers here are the reusable bits.

// Callee param iteration is just `callee.params.iter()`. Our `FnMap`
// sees the POST-simplify `FunctionX` (see `verifier.rs`'s
// `vir_crate_simplified`), so for zero-arg fns the params list
// includes Verus's injected `no%param` dummy — matched positionally
// by a `Const(0)` dummy arg at the call site. Both sides align, so
// we can zip directly; the dummy param's substitution binds a name
// nothing references, inert.

/// The set of SST expression wrappers we treat as semantically
/// transparent — i.e., they don't emit any Lean code of their own
/// and peeling through them is safe. Centralised here so adding a
/// new transparent wrapper is one edit, not four parallel ones.
///
/// Callers: [`contains_loc`] (for `&mut` detection),
/// [`lift_if_value`] (for if-value lifting; it additionally peels
/// `Loc`), [`to_lean_sst_expr::render_checked_decrease_arg`] (for
/// the Bind(Let) peel in `CheckDecreaseHeight` args).
///
/// If Verus adds a new transparent wrapper (e.g., a new `UnaryOpr`
/// or `Unary` variant that's effectively inert at the SST level),
/// extending this one function also extends the peel semantics of
/// all callers uniformly.
pub(crate) fn peel_transparent(e: &Exp) -> &Exp {
    match &e.x {
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner)
        | ExpX::Unary(UnaryOp::CoerceMode { .. } | UnaryOp::Trigger(_), inner) => {
            peel_transparent(inner)
        }
        _ => e,
    }
}

/// Does this expression — or any transparently-wrapped inner — use
/// `ExpX::Loc`? `Loc` marks an L-value (`&mut` argument site).
/// We peel transparent wrappers via [`peel_transparent`] so a
/// mutable borrow buried under them is still detected rather than
/// silently accepted as by-value.
fn contains_loc(e: &Exp) -> bool {
    matches!(&peel_transparent(e).x, ExpX::Loc(_))
}

/// Validate an SST expression — `sst_exp_to_ast_checked` does both
/// validation AND rendering in a single pass, so we just call it and
/// discard the rendered result. Used by `build_wp` at the points
/// where it encounters expressions that `lower_wp` will later
/// re-render via the infallible wrapper (at which point validation
/// is known to have passed).
fn check_exp(e: &Exp) -> Result<(), String> {
    sst_exp_to_ast_checked(e).map(|_| ())
}

// ── Theorem builder ────────────────────────────────────────────────────

/// Build the Lean `Theorem`s for an exec fn body check.
///
/// Returns a `Vec` because future slices may want to split obligations
/// into separate theorems (e.g., for per-loop diagnostics); today it's
/// always length 1 — loops contribute conjuncts to the main goal
/// rather than their own top-level theorems.
///
/// Returns `Err` if any part of `check` uses an SST form we don't know
/// how to emit. Validation and AST construction share a single pass
/// (`build_wp` + `sst_exp_to_ast_checked`), so the "validate-first"
/// precondition is enforced by construction — there's no way to
/// produce a `Wp` tree without having already cleared the shape
/// checks.
pub fn exec_fn_theorems_to_ast<'a>(
    krate: &'a KrateX,
    fn_sst: &'a FunctionSst,
    check: &'a FuncCheckSst,
) -> Result<Vec<Theorem>, String> {
    // `WpCtx::new` validates reqs / ens_exps before rendering them.
    let ctx = WpCtx::new(krate, check)?;

    let name = format!("_tactus_body_{}", lean_name(&fn_sst.x.name.path));
    let mut binders = build_param_binders(fn_sst);
    binders.extend(build_req_binders(check));

    // Build the whole WP tree from the body, with the fn's ensures
    // as the natural continuation at the leaves. `Return` statements
    // inside the body replace their local `after` with the same
    // ensures goal (via `ctx.ensures_goal`). Initial loop_ctx is
    // `None` — break/continue are rejected outside any loop.
    let body_wp = build_wp(
        &check.body,
        Wp::Done(ctx.ensures_goal.clone()),
        &ctx,
        None,
    )?;
    let has_loop_or_call = body_wp.needs_peel();
    // Two-pass: collect `have` clauses from every `Wp::AssertByTactus`
    // node in the tree, then lower the tree to the goal LExpr. The
    // haves prepend to the closer so each user tactic discharges its
    // assert obligation AND introduces a hypothesis that `simp_all`
    // / `omega` can pick up during the rest of the proof. Splitting
    // the walk from `lower_wp` keeps lowering a pure function of the
    // tree — no shared-mutable side channel needed.
    let user_haves = collect_tactus_haves(&body_wp);
    let goal = lower_wp(&body_wp, &ctx);
    let closer = if has_loop_or_call { loop_tactic() } else { simple_tactic() };
    let tactic = prepend_user_haves(user_haves, closer);
    Ok(vec![Theorem { name, binders, goal, tactic }])
}

/// Collected tactic prefix extracted from a `Wp::AssertByTactus` node.
/// `wrap` distinguishes the two Tactus surface forms — see the
/// variant's doc for the semantic split.
struct TactusHave {
    /// `Some((hypothesis_name, rendered_P))` for assert-by: emission
    /// wraps as `have <name> : <P> := by <tac>`. `None` for proof
    /// blocks: emission emits `<tac>` raw.
    wrap: Option<(String, LExpr)>,
    tactic_text: String,
}

/// Walk the Wp tree and extract one `TactusHave` per
/// `Wp::AssertByTactus` node, in structural order. The resulting
/// list is consumed by `prepend_user_haves` to build the theorem's
/// prefix. `lower_wp` stays pure — the Tactus tactic info is
/// extracted up-front rather than collected via a mutable side
/// channel during lowering.
fn collect_tactus_haves(wp: &Wp<'_>) -> Vec<TactusHave> {
    let mut out = Vec::new();
    collect_tactus_haves_into(wp, &mut out);
    out
}

fn collect_tactus_haves_into(wp: &Wp<'_>, out: &mut Vec<TactusHave>) {
    match wp {
        Wp::Done(_) => {}
        Wp::Let(_, _, body) | Wp::Assert(_, body) | Wp::Assume(_, body) => {
            collect_tactus_haves_into(body, out);
        }
        Wp::AssertByTactus { cond, tactic_text, body } => {
            let wrap = cond.map(|c| {
                let idx = out.len();
                (format!("h_tactus_assert_{}", idx), sst_exp_to_ast(c))
            });
            out.push(TactusHave { wrap, tactic_text: tactic_text.clone() });
            collect_tactus_haves_into(body, out);
        }
        Wp::Branch { then_branch, else_branch, .. } => {
            collect_tactus_haves_into(then_branch, out);
            collect_tactus_haves_into(else_branch, out);
        }
        Wp::Loop { body, after, .. } => {
            collect_tactus_haves_into(body, out);
            collect_tactus_haves_into(after, out);
        }
        Wp::Call { after, .. } => {
            collect_tactus_haves_into(after, out);
        }
    }
}

/// Prepend collected Tactus user tactics to the normal theorem
/// `closer`. Two forms per `TactusHave`:
///
/// * `wrap = Some((name, cond))` (assert-by form): emit
///   `have <name> : <cond> := by <user_tac>` so the user's tactic
///   discharges the proof obligation for `<cond>` AND the proved
///   hypothesis <name> is in scope for the rest of the proof.
/// * `wrap = None` (proof-block form): emit `<user_tac>` raw — the
///   user's own `have` / `unfold` / etc. run at theorem-tactic
///   level, affecting outer context and goal.
///
/// No-op when the collector is empty — theorems with no Tactus
/// assert-by / proof-block keep their single-tactic form unchanged.
fn prepend_user_haves(haves: Vec<TactusHave>, closer: Tactic) -> Tactic {
    if haves.is_empty() {
        return closer;
    }
    let mut body = String::new();
    for h in &haves {
        match &h.wrap {
            Some((name, cond)) => {
                let cond_text = crate::lean_pp::pp_expr(cond);
                body.push_str(&format!("have {name} : {cond_text} := by\n"));
                for line in h.tactic_text.lines() {
                    body.push_str("  ");
                    body.push_str(line);
                    body.push('\n');
                }
            }
            None => {
                for line in h.tactic_text.lines() {
                    body.push_str(line);
                    body.push('\n');
                }
            }
        }
    }
    // Splice the closer's textual form after the haves.
    match closer {
        Tactic::Named(n) => body.push_str(&n),
        Tactic::Raw(s) => body.push_str(&s),
    }
    Tactic::Raw(body)
}

/// Atomic `tactus_auto` for straight-line exec fn theorems — their
/// goals are a single chain of `let` / `→` / `∧` that omega handles
/// directly.
fn simple_tactic() -> Tactic {
    Tactic::Named("tactus_auto".to_string())
}

/// Loop theorems have a conjunctive shape `init ∧ maintain ∧ use` per
/// loop; nested / sequential loops produce nested conjunctions of the
/// same shape. The goal can therefore be arbitrarily deeply structured,
/// so we delegate to `tactus_peel` (defined in `TactusPrelude.lean`) —
/// a recursive macro that strips one layer of `∧` or one `∀` / `→`
/// per call and bottoms out at arithmetic leaves. `all_goals
/// tactus_auto` then closes each leaf. No hardcoded depth — the
/// recursion follows the goal's structure, so deeply-nested loops
/// work the same as shallow ones.
fn loop_tactic() -> Tactic {
    Tactic::Raw("tactus_peel; all_goals tactus_auto".to_string())
}

// ── Binder builders ────────────────────────────────────────────────────

/// Function params + their type-bound hypotheses. Shared across all
/// theorems emitted for a given fn (init / maintain / use all start
/// from these).
fn build_param_binders(fn_sst: &FunctionSst) -> Vec<LBinder> {
    let mut out: Vec<LBinder> = Vec::new();
    // Type parameters first, so value params can reference them in
    // their types (`x : T`). Mirrors `to_lean_fn::fn_binders`'
    // ordering so proof fns and exec fns present a consistent
    // binder shape for the same fn signature.
    for tp in fn_sst.x.typ_params.iter() {
        out.push(LBinder {
            name: Some(tp.to_string()),
            ty: LExpr::var("Type"),
            kind: BinderKind::Explicit,
        });
    }
    for p in fn_sst.x.pars.iter().filter(|p| !is_synthetic_param(p)) {
        let name = sanitize(&p.x.name.0);
        out.push(LBinder {
            name: Some(name.clone()),
            ty: typ_to_expr(&p.x.typ),
            kind: BinderKind::Explicit,
        });
        if let Some(pred) = type_bound_predicate(&LExpr::var(name.clone()), &p.x.typ) {
            out.push(LBinder {
                name: Some(format!("h_{}_bound", name)),
                ty: pred,
                kind: BinderKind::Explicit,
            });
        }
    }
    out
}

/// `(h_req<i> : <req_i>)` for each requires clause.
fn build_req_binders(check: &FuncCheckSst) -> Vec<LBinder> {
    check.reqs.iter().enumerate().map(|(i, req)| LBinder {
        name: Some(format!("h_req{}", i)),
        ty: sst_exp_to_ast(req),
        kind: BinderKind::Explicit,
    }).collect()
}

// ── WP DSL ─────────────────────────────────────────────────────────────
//
// `Wp<'a>` is a small algebra of WP-shaped operations. Each non-`Done`
// node carries its own continuation by construction — no separate
// "rest" parameter, no separate "terminator" parameter. Lowering
// (`lower_wp`) is a straightforward tree walk; construction
// (`build_wp`) threads each statement's continuation through at walk
// time.
//
// Compared to the earlier `BodyItem` + `build_goal_with_terminator`
// design:
//
//   * Continuation is type-level, not positional. Can't accidentally
//     compose after a `Return` because `Done` has no slot for more.
//   * `Return` is cleanly "terminator-at-fn-exit" rather than
//     "terminator-in-current-scope" — an early return always writes
//     the fn's ensures goal, even when nested inside a loop. The
//     earlier code passed the loop's local goal through as the
//     terminator, which was incorrect for true fn-exit semantics
//     (harmless in practice because we don't exercise return-in-loop
//     yet, but the DSL shape gets this right by construction).
//   * `Loop` / `Call` compose like any other node — each has `body`
//     and/or `after` sub-Wps, recursion is structural.
//   * `needs_peel` is one line per variant, based on the node's own
//     shape rather than a post-hoc traversal looking for
//     `BodyItem::Loop` / `Call`.
//
// Adding a new WP form means adding a constructor + an arm in
// `build_wp` (where construction happens) and `lower_wp` (where it
// lowers to LExpr). No changes needed to a central dispatcher.

/// A WP program. Each compound node carries its own continuation,
/// so composition is structural and `Return` is naturally a
/// terminator.
#[derive(Clone)]
enum Wp<'a> {
    /// Terminal leaf — the goal at this point in the program. Built
    /// from the fn's ensures (top-level), from the loop's local
    /// `I ∧ D < d_old` (loop-body terminator), or from a `return`
    /// statement's `let <ret> := e; ensures`.
    Done(LExpr),

    /// `let x := e; <body>`. If `e` contains an `ExpX::If`, the
    /// lowering pass lifts it out via `lift_if_value` — this keeps
    /// the Wp tree shape intact while giving omega a tractable goal.
    Let(&'a str, &'a Exp, Box<Wp<'a>>),

    /// `P ∧ <body>`.
    Assert(&'a Exp, Box<Wp<'a>>),

    /// `P → <body>`.
    Assume(&'a Exp, Box<Wp<'a>>),

    /// User-written Lean tactic inside a `tactus_auto` fn.
    ///
    /// Two surface forms produce this node, distinguished by `cond`:
    /// * `Some(P)` — `assert(P) by { tac }`. Emission prepends
    ///   `have h_N : P := by <tac>` to the theorem's closer; the
    ///   user's tactic discharges the obligation for P, and the
    ///   proved hypothesis h_N is available for the rest of the
    ///   proof via `simp_all` / `omega`.
    /// * `None` — `proof { tac }`. Emission prepends `<tac>` raw;
    ///   the user's own `have` statements inside become theorem-
    ///   level hypotheses, and `unfold` / `simp` / etc. affect the
    ///   outer goal. No wrapping, no synthesized condition.
    ///
    /// In both cases `body` is the post-block continuation, and the
    /// body's `lower_wp` passes through unchanged — the tactic
    /// content is extracted up-front by `collect_tactus_haves` and
    /// prepended to the closer, not woven into the goal.
    AssertByTactus {
        cond: Option<&'a Exp>,
        tactic_text: String,
        body: Box<Wp<'a>>,
    },

    /// `(c → then_branch) ∧ (¬c → else_branch)`. Both branches
    /// carry their own continuations up to the next join — the
    /// outer WP builder doesn't split continuations textually,
    /// because each branch already has the right continuation
    /// embedded in its Wp sub-tree.
    Branch {
        cond: &'a Exp,
        then_branch: Box<Wp<'a>>,
        else_branch: Box<Wp<'a>>,
    },

    /// Loop. `body` is the body's Wp built with its own local
    /// `Done(I ∧ D < _tactus_d_old)` terminator; `after` is the
    /// post-loop continuation (built with the enclosing scope's
    /// `after`). Lowering wraps `body` with the `let _tactus_d_old
    /// := D` binding and the maintain quantifier, and wraps `after`
    /// with the havoc quantifier.
    ///
    /// `cond` is `Some(c)` for a simple `while c { … }` with no
    /// breaks (the body runs while `c` holds; exit is via `!c`).
    /// `cond` is `None` for the break-lowered form Verus produces
    /// for `while c { … break; … }` (the body sees `if !c { break; }`
    /// inserted by Verus; exit is only via `break`). The maintain
    /// clause's `I ∧ cond →` guard is dropped in the `None` case,
    /// and the use clause's `I ∧ ¬cond →` becomes just `I →`.
    Loop {
        cond: Option<&'a Exp>,
        invs: &'a [LoopInv],
        decrease: &'a Exp,
        modified_vars: Vec<(&'a VarIdent, &'a Typ)>,
        body: Box<Wp<'a>>,
        after: Box<Wp<'a>>,
    },

    /// Direct function call. `after` is the post-call continuation.
    /// Lowering inlines the callee's require/ensure via
    /// `lean_ast::substitute` and wraps `after` under `∀ ret, bound →
    /// ensures → let dest := ret; after`.
    Call {
        callee: &'a FunctionX,
        /// Borrow the SST's arg slice directly — no `Vec<&Exp>`
        /// allocation. `StmX::Call::args` is `Arc<Vec<Exp>>`, so
        /// `&args[..]` gives us a `&'a [Exp]` with the same
        /// lifetime as the rest of the Wp.
        args: &'a [Exp],
        /// Type arguments from the call site, one per `callee.typ_params`.
        /// Used at lowering time to substitute each `TypParam(id)` in
        /// the callee's require/ensure with the call site's concrete
        /// type. Empty slice when the callee is non-generic.
        typ_args: &'a [Typ],
        /// Caller's destination variable (`let x = foo(…)` → `Some("x")`;
        /// `foo(…);` → `None`). Only the name is needed — lowering emits
        /// `let dest := ret` inside the `∀ ret`, and `ret` already has
        /// its type-bound hypothesis from `type_bound_predicate`.
        dest: Option<&'a VarIdent>,
        after: Box<Wp<'a>>,
    },
}

impl<'a> Wp<'a> {
    /// Does lowering this Wp produce a goal shape that needs
    /// structural peeling (nested `∀` / `∧` beyond what omega can
    /// chase directly)? Flat Let/Assert/Assume/Branch chains over
    /// arithmetic don't; Loops and Calls do because they introduce
    /// quantifiers and conjunctive splits. `Branch` by itself is
    /// peel-free (just two implications under a conjunction) — only
    /// needs peel when a sub-branch does.
    fn needs_peel(&self) -> bool {
        match self {
            Wp::Done(_) => false,
            Wp::Let(_, _, body) | Wp::Assert(_, body) | Wp::Assume(_, body) => body.needs_peel(),
            Wp::AssertByTactus { body, .. } => body.needs_peel(),
            Wp::Branch { then_branch, else_branch, .. } => {
                then_branch.needs_peel() || else_branch.needs_peel()
            }
            Wp::Loop { .. } | Wp::Call { .. } => true,
        }
    }
}

// ── WP lowering ────────────────────────────────────────────────────────

/// Interpret a `Wp` tree into a Lean `LExpr`. Each node has a
/// corresponding WP rule; see the variant docs on `Wp` for details.
fn lower_wp(wp: &Wp<'_>, ctx: &WpCtx<'_>) -> LExpr {
    match wp {
        Wp::Done(leaf) => leaf.clone(),
        Wp::Let(name, rhs, body) => {
            // If `rhs` has an `ExpX::If` (possibly under transparent
            // wrappers), lift it to goal level: `let x := if c then
            // a else b; rest` becomes `(c → let x := a; rest) ∧ (¬c →
            // let x := b; rest)`. Omega can chase each branch
            // separately; it can't see inside a value-position if.
            let body_lowered = lower_wp(body, ctx);
            lift_if_value(rhs, &|rhs_ast| {
                LExpr::let_bind(sanitize(name), rhs_ast, body_lowered.clone())
            })
        }
        Wp::Assert(e, body) => LExpr::and(sst_exp_to_ast(e), lower_wp(body, ctx)),
        Wp::Assume(e, body) => LExpr::implies(sst_exp_to_ast(e), lower_wp(body, ctx)),
        // The user tactic is NOT in the goal — it's extracted
        // up-front by `collect_tactus_haves` and prepended to the
        // closer (as `have h : P := by tac` for assert-by when
        // `cond = Some(_)`, or raw when `cond = None` for proof
        // blocks). Here we just pass through. Keeps `lower_wp` a
        // pure function of the Wp tree + ctx.
        Wp::AssertByTactus { cond: _, tactic_text: _, body } => lower_wp(body, ctx),
        Wp::Branch { cond, then_branch, else_branch } => {
            let c = sst_exp_to_ast(cond);
            LExpr::and(
                LExpr::implies(c.clone(), lower_wp(then_branch, ctx)),
                LExpr::implies(LExpr::not(c), lower_wp(else_branch, ctx)),
            )
        }
        Wp::Loop { cond, invs, decrease, modified_vars, body, after } => {
            lower_loop(*cond, invs, decrease, modified_vars, body, after, ctx)
        }
        Wp::Call { callee, args, typ_args, dest, after } => {
            lower_call(callee, args, typ_args, *dest, after, ctx)
        }
    }
}

/// Lower a `Wp::Loop` to the three-part conjunction
/// `I ∧ maintain ∧ havoc_continuation` — see DESIGN.md "Loop
/// obligations (conjunctive WP)" for the shape and rationale.
///
/// `body` was built with `Done(I ∧ D < _tactus_d_old)` as its
/// terminator (see `build_wp_loop`), so `lower_wp(body, ctx)` already
/// produces the maintain clause's inner goal. Wrapping with
/// `let _tactus_d_old := D` around it lets the inner `D` reference
/// the post-body value while `_tactus_d_old` retains the pre-body
/// value — straight Lean let-scoping does the right thing.
fn lower_loop(
    cond: Option<&Exp>,
    invs: &[LoopInv],
    decrease: &Exp,
    modified_vars: &[(&VarIdent, &Typ)],
    body: &Wp<'_>,
    after: &Wp<'_>,
    ctx: &WpCtx<'_>,
) -> LExpr {
    let inv_conj = || and_all(invs.iter().map(|i| sst_exp_to_ast(&i.inv)).collect());
    let decrease_ast = || sst_exp_to_ast(decrease);

    // Init: invariant conjunction at loop entry.
    let init_clause = inv_conj();

    // Maintain: `∀ mod_vars, bounds → I (∧ cond)? →
    //             (let _tactus_d_old := D; lower_wp(body))`.
    // The `∧ cond` part is only present for `while`-shaped loops
    // (`cond: Some`). For `cond: None` (Verus's break-lowered form),
    // the body has an explicit `if !cond { break; }` at the head, so
    // we don't gate the maintain clause on cond at the meta level.
    //
    // See DESIGN.md "_tactus_d_old aliasing across nested loops" for
    // the rationale behind the literal `_tactus_d_old` name.
    let maintain_body_lowered = lower_wp(body, ctx);
    let maintain_core = LExpr::let_bind("_tactus_d_old", decrease_ast(), maintain_body_lowered);
    let maintain_pre = match cond {
        Some(c) => LExpr::and(inv_conj(), sst_exp_to_ast(c)),
        None => inv_conj(),
    };
    let maintain_clause = quantify_mod_vars(
        modified_vars,
        LExpr::implies(maintain_pre, maintain_core),
    );

    // Use / post-loop continuation: `∀ mod_vars, bounds → I (∧ ¬cond)? →
    //   lower_wp(after)`. For `cond: Some` the exit is via ¬cond.
    // For `cond: None` exit is only via `break`, which writes the
    // break_leaf (= I currently); no ¬cond clause.
    //
    // `after`'s Done leaves point at the outer ensures (or whatever
    // the enclosing scope's `after` was), so nested loops' post-body
    // code feeds back correctly.
    let after_lowered = lower_wp(after, ctx);
    let use_pre = match cond {
        Some(c) => LExpr::and(inv_conj(), LExpr::not(sst_exp_to_ast(c))),
        None => inv_conj(),
    };
    let use_clause = quantify_mod_vars(
        modified_vars,
        LExpr::implies(use_pre, after_lowered),
    );

    LExpr::and(init_clause, LExpr::and(maintain_clause, use_clause))
}

/// Lower a `Wp::Call` by inlining the callee's require / ensure via
/// Lean-AST substitution (rather than textual let-wrapping, which
/// would shadow caller names on self-recursion).
///
/// For `let dest = callee(arg1, arg2, …)` the emitted shape is:
///
/// ```text
/// requires_conj[p1 := arg1, p2 := arg2, …]
/// ∧ (∀ (ret : RetT), h_ret_bound(ret) →
///      ensures_conj_using_ret[p1 := arg1, p2 := arg2, …] →
///      (let dest := ret; <lower_wp(after)>))
/// ```
///
/// The substitution `[p := arg]` is done at the Lean AST level via
/// `lean_ast::substitute` — direct substitution instead of
/// `let p := arg; body` wrapping avoids name shadowing when the
/// caller and callee share a param name (e.g., self-recursion).
///
/// Termination obligations for recursive calls are inserted upstream
/// by Verus's `recursion` pass as `StmX::Assert(InternalFun::
/// CheckDecreaseHeight)` before the `StmX::Call`; they flow through
/// `build_wp` as ordinary `Wp::Assert` nodes and lower via
/// `sst_exp_to_ast_checked`'s `CheckDecreaseHeight` arm.
fn lower_call(
    callee: &FunctionX,
    args: &[Exp],
    typ_args: &[Typ],
    dest: Option<&VarIdent>,
    after: &Wp<'_>,
    ctx: &WpCtx<'_>,
) -> LExpr {
    let params_vec: Vec<_> = callee.params.iter().collect();
    assert_eq!(
        params_vec.len(), args.len(),
        "callee param count {} != caller arg count {} for {:?} — \
         build_wp_call should have rejected this",
        params_vec.len(), args.len(), callee.name.path,
    );
    assert_eq!(
        callee.typ_params.len(), typ_args.len(),
        "callee type param count {} != caller type arg count {} for {:?} — \
         build_wp_call should have rejected this",
        callee.typ_params.len(), typ_args.len(), callee.name.path,
    );

    // Single substitution map combining:
    //   * value params → call-site arg expressions (substituted directly
    //     rather than via `let p := arg; body` wrapping — avoids
    //     shadowing on self-recursion)
    //   * type params → call-site type expressions (rendered via
    //     typ_to_expr). `TypParam(T)` renders as `Var("T")` which the
    //     value-level `substitute` then rewrites to the concrete type.
    //     This is the only step needed to inline generic callees'
    //     require/ensure at a specific instantiation.
    let mut subst: std::collections::HashMap<String, LExpr> = params_vec.iter()
        .zip(args.iter())
        .map(|(p, arg)| (sanitize(&p.x.name.0), sst_exp_to_ast(arg)))
        .collect();
    for (tp_name, tp_arg) in callee.typ_params.iter().zip(typ_args.iter()) {
        subst.insert(sanitize(tp_name), typ_to_expr(tp_arg));
    }

    let requires_conj = and_all(
        callee.require.iter().map(|e| vir_expr_to_ast(e)).collect()
    );
    let ensures_conj = and_all(
        callee.ensure.0.iter().map(|e| vir_expr_to_ast(e)).collect()
    );
    let requires_clause = substitute(&requires_conj, &subst);

    let ret = &callee.ret.x;
    let ret_name_cal = sanitize(&ret.name.0);
    // Also substitute typ_args in the return type — a callee
    // `fn foo<T>(x: T) -> T` needs its return bound rendered with the
    // concrete T, not with the Var("T") placeholder.
    let ret_typ = substitute(&typ_to_expr(&ret.typ), &subst);
    let continuation_under_ret = {
        let after_lowered = lower_wp(after, ctx);
        let bound_rest = match dest {
            Some(dest_ident) => LExpr::let_bind(
                sanitize(&dest_ident.0),
                LExpr::var(ret_name_cal.clone()),
                after_lowered,
            ),
            None => after_lowered,
        };
        let ensures_impl = LExpr::implies(substitute(&ensures_conj, &subst), bound_rest);
        let bounded_impl = match type_bound_predicate(&LExpr::var(ret_name_cal.clone()), &ret.typ) {
            Some(pred) => LExpr::implies(pred, ensures_impl),
            None => ensures_impl,
        };
        LExpr::forall(
            vec![LBinder {
                name: Some(ret_name_cal.clone()),
                ty: ret_typ,
                kind: BinderKind::Explicit,
            }],
            bounded_impl,
        )
    };

    LExpr::and(requires_clause, continuation_under_ret)
}

/// Lift `ExpX::If` expressions from value-position to goal-level.
///
/// For a value `if c then a else b` at the source level, `emit_leaf`
/// describes how to wrap the final Lean expression (e.g., `let x :=
/// <value>; rest` or `let r := <value>; ensures`). This helper recurses
/// through nested `ExpX::If`s, transparent wrappers (`Loc` / `Box` /
/// `Unbox` / mode-coercion / trigger markers), and single-binder
/// `let`-expressions (`ExpX::Bind(Let, …)`) — calling `emit_leaf` at
/// each leaf with the already-rendered Lean value. The results get
/// wrapped with `(c → …) ∧ (¬c → …)` around each if.
///
/// Purpose: `omega` handles propositional structure (∧, →, ¬) over
/// linear arithmetic, but not `if c then a else b` inside the goal.
/// Lifting the if out gives omega two simpler side-goals instead of
/// one mixed one, restoring automation.
///
/// Exponential in if-nesting depth, but matches the expected size of
/// the goal the user is writing. For non-if values this is a direct
/// call to `emit_leaf` with the rendered expression — no overhead.
fn lift_if_value(e: &Exp, emit_leaf: &dyn Fn(LExpr) -> LExpr) -> LExpr {
    // Peel Box/Unbox/CoerceMode/Trigger via the shared helper; `Loc`
    // is handled separately below because it peels for lifting but
    // NOT for `contains_loc` (which is looking for the Loc itself).
    let peeled = peel_transparent(e);
    match &peeled.x {
        ExpX::If(cond, then_e, else_e) => {
            let c = sst_exp_to_ast(cond);
            LExpr::and(
                LExpr::implies(c.clone(), lift_if_value(then_e, emit_leaf)),
                LExpr::implies(LExpr::not(c), lift_if_value(else_e, emit_leaf)),
            )
        }
        // Loc is also transparent for lifting (it marks an L-value
        // position; the expression semantics are the inner's). Not
        // part of `peel_transparent` because `contains_loc` needs
        // Loc un-peeled.
        ExpX::Loc(inner) => lift_if_value(inner, emit_leaf),
        // Single-binder `let y := e_rhs; body` — if the rhs has an if,
        // lift it out, re-threading `body` through each branch. Verus
        // often emits `let y = …; y` blocks as this shape, which would
        // otherwise hide the if from our lift.
        ExpX::Bind(bnd, body) if matches!(&bnd.x, BndX::Let(bs) if bs.len() == 1) => {
            let BndX::Let(binders) = &bnd.x else { unreachable!() };
            let b = &binders[0];
            let name = sanitize(&b.name.0);
            let body_ast = sst_exp_to_ast(body);
            lift_if_value(&b.a, &|rhs_leaf| {
                emit_leaf(LExpr::let_bind(name.clone(), rhs_leaf, body_ast.clone()))
            })
        }
        _ => emit_leaf(sst_exp_to_ast(e)),
    }
}

/// `∀ (x₁ : T₁), bounds₁ → … ∀ (xₙ : Tₙ), boundsₙ → body` — wraps
/// `body` with a universal quantifier per modified variable plus its
/// type-bound hypothesis (where applicable).
fn quantify_mod_vars(
    modified_vars: &[(&VarIdent, &Typ)],
    body: LExpr,
) -> LExpr {
    let mut out = body;
    // Fold right-to-left so the outermost ∀ is the first modified var.
    for (ident, typ) in modified_vars.iter().rev() {
        let name = sanitize(&ident.0);
        // Optionally wrap with `bound → …` first.
        if let Some(pred) = type_bound_predicate(&LExpr::var(name.clone()), typ) {
            out = LExpr::implies(pred, out);
        }
        // Then wrap with `∀ (x : T), …`.
        out = LExpr::forall(
            vec![LBinder {
                name: Some(name),
                ty: typ_to_expr(typ),
                kind: BinderKind::Explicit,
            }],
            out,
        );
    }
    out
}

// ── WP builder ─────────────────────────────────────────────────────────

/// Build the `Wp` tree for a statement, threading the continuation
/// `after` through. Right-to-left over a `Block` — each statement's
/// `after` is the already-built Wp for the rest of the block.
///
/// `Return` discards `after` and writes a `Done` leaf at the fn's
/// ensures goal. Other variants wrap `after` with their respective
/// WP rule.
///
/// Validation is fused with construction: any unsupported SST form
/// returns `Err` and bubbles up, so the caller of `build_wp` is
/// guaranteed that the returned `Wp` is lowerable without panics.
/// The "validate-first" precondition is type-level — there's no way
/// to produce a `Wp` without clearing the shape checks.
fn build_wp<'a>(
    stm: &'a Stm,
    after: Wp<'a>,
    ctx: &WpCtx<'a>,
    // Innermost enclosing loop's break/continue leaves, if any. `None`
    // outside a loop (where `StmX::BreakOrContinue` is rejected).
    // Most recursive calls forward this unchanged; only
    // `build_wp_loop` constructs a new one for the body.
    loop_ctx: Option<&WpLoopCtx>,
) -> Result<Wp<'a>, String> {
    match &stm.x {
        StmX::Block(stms) => {
            // Fold right-to-left: walk(s_last, outer_after),
            //                     walk(s_{n-1}, that),
            //                     ...,
            //                     walk(s_0, whole_rest).
            let mut wp = after;
            for s in stms.iter().rev() {
                wp = build_wp(s, wp, ctx, loop_ctx)?;
            }
            Ok(wp)
        }
        // Explicit destructure of `Dest` — `is_init` doesn't affect
        // WP construction (Lean's let-shadowing gives SSA for free),
        // but spelling it out forces a compile-time audit if Verus
        // adds a new `Dest` field that might.
        StmX::Assign { lhs: Dest { dest, is_init: _ }, rhs } => {
            check_exp(dest)?;
            check_exp(rhs)?;
            let Some(name) = extract_simple_var(dest) else {
                return Err(format!(
                    "assignment with non-simple LHS (got {:?}) is not yet supported",
                    dest.x
                ));
            };
            Ok(Wp::Let(name, rhs, Box::new(after)))
        }
        StmX::Assert(_, _, e) | StmX::AssertCompute(_, e, _) => {
            check_exp(e)?;
            Ok(Wp::Assert(e, Box::new(after)))
        }
        StmX::Assume(e) => {
            check_exp(e)?;
            Ok(Wp::Assume(e, Box::new(after)))
        }
        // `return e` discards the textual continuation (`after`) and
        // terminates at the fn's ensures. Discard is type-level:
        // `Done` has no continuation slot. If the return value has
        // an `ExpX::If`, lift it via `lift_if_value` so the Done
        // leaf has goal-level `(c → …) ∧ (¬c → …)` shape rather than
        // an opaque-to-omega value-position if.
        //
        // Destructure every field explicitly (no `..`) — any future
        // Verus-side `StmX::Return` field addition then forces a
        // compile-time audit. `assert_id` / `base_error` are Verus
        // diagnostic metadata; `inside_body` distinguishes tail vs
        // early returns but the DSL handles both identically (both
        // produce `Wp::Done`).
        StmX::Return { ret_exp: Some(e), assert_id: _, base_error: _, inside_body: _ } => {
            check_exp(e)?;
            let ensures_goal = ctx.ensures_goal.clone();
            let ret_name = ctx.ret_name;
            let leaf = lift_if_value(e, &|e_ast| match ret_name {
                Some(name) => LExpr::let_bind(sanitize(name), e_ast, ensures_goal.clone()),
                None => ensures_goal.clone(),
            });
            Ok(Wp::Done(leaf))
        }
        StmX::Return { ret_exp: None, assert_id: _, base_error: _, inside_body: _ } => {
            Ok(Wp::Done(ctx.ensures_goal.clone()))
        }
        StmX::If(cond, then_stm, else_stm) => {
            check_exp(cond)?;
            // Both branches share the same post-if continuation. Clone
            // `after` into each — this is where the pre-DSL code's
            // exponential-in-nested-ifs size comes from; see DESIGN.md
            // "Known codegen-complexity trade-offs" for the shared-
            // continuation let-binding optimization we chose not to
            // implement (simp zeta-reduces it, so no saving).
            let then_branch = build_wp(then_stm, after.clone(), ctx, loop_ctx)?;
            let else_branch = match else_stm {
                Some(e) => build_wp(e, after, ctx, loop_ctx)?,
                None => after,
            };
            Ok(Wp::Branch {
                cond,
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            })
        }
        // `build_wp_call` doesn't recurse into sub-Stms so it doesn't
        // need `loop_ctx`. `build_wp_loop` does — it builds the
        // loop's body which can contain break/continue for this very
        // loop (not the enclosing one).
        StmX::Call { .. } => build_wp_call(stm, after, ctx),
        StmX::Loop { .. } => build_wp_loop(stm, after, ctx, loop_ctx),
        // Transparent in SST: pass `after` through unchanged.
        StmX::Air(_) | StmX::Fuel(..) | StmX::RevealString(_) => Ok(after),
        // `break` / `continue` terminate the current iteration and
        // jump to the loop's respective leaf. `after` is discarded —
        // any statements textually after a break in the SST are
        // unreachable (Verus's dead-code analysis handles that
        // upstream; this WP side just needs to reach the right leaf).
        //
        // Labeled forms (`break 'outer;`) aren't yet supported — they
        // would require a stack of loop contexts keyed by label
        // rather than a single innermost one.
        StmX::BreakOrContinue { label, is_break } => {
            if label.is_some() {
                return Err("labeled break / continue not yet supported".to_string());
            }
            let Some(leaves) = loop_ctx else {
                return Err(
                    "break / continue outside a loop — SST mode-checker invariant \
                     violated".to_string()
                );
            };
            let leaf = if *is_break {
                leaves.break_leaf.clone()
            } else {
                leaves.continue_leaf.clone()
            };
            Ok(Wp::Done(leaf))
        }
        StmX::AssertBitVector { .. } => Err(
            "assert by(bit_vector) not yet supported".to_string()
        ),
        // `StmX::AssertQuery` with `AssertQueryMode::Tactus` is how
        // `ast_to_sst` encodes an `assert(P) by { lean_tac }` inside
        // a `tactus_auto` fn (see `ExprX::AssertBy` handling there).
        // We read the verbatim Lean tactic text from the original
        // file via the `tactic_span` and produce a `Wp::AssertByTactus`
        // node; the theorem emitter walks the Wp tree, collects user
        // tactics, and prepends them as `have` clauses before the
        // closer.
        //
        // **Shape**: `body` is a single `StmX::Assert(_, _, P)` —
        // the asserted condition, produced by `ast_to_sst`'s
        // Tactus-shortcut emission. `typ_inv_*` are intentionally
        // empty (other AssertQuery modes use them for NonLinear/
        // BitVector context). Extracting `P` from `body` keeps
        // `AssertQueryMode::Tactus` itself small — no generic `Exp`
        // field forcing derive-juggling on the enum.
        //
        // Other AssertQuery modes (NonLinear / BitVector) stay
        // rejected — they're Z3-specific and don't route through
        // the Lean WP pipeline.
        StmX::AssertQuery { mode, typ_inv_exps: _, typ_inv_vars: _, body } => {
            match mode {
                AssertQueryMode::Tactus { tactic_span, kind } => {
                    let cond = match &body.x {
                        StmX::Assert(_, _, c) => c,
                        _ => return Err(format!(
                            "AssertQueryMode::Tactus body expected to be a single \
                             StmX::Assert carrying the asserted condition, got {:?}",
                            std::mem::discriminant(&body.x)
                        )),
                    };
                    check_exp(cond)?;
                    let (path, start, end) = tactic_span;
                    let tactic_text = crate::source_util::read_tactic_from_source(
                        path, *start, *end,
                    ).ok_or_else(|| format!(
                        "failed to read assert-by tactic from {} bytes [{}..{}]",
                        path, start, end
                    ))?;
                    // `kind` distinguishes assert-by (wrap as `have
                    // h : P := by <tac>`) from proof block (emit
                    // `<tac>` raw). We encode that in `Wp::AssertByTactus`
                    // by passing `Some(cond)` vs `None`.
                    let cond_for_have = match kind {
                        TactusKind::AssertBy => Some(cond),
                        TactusKind::ProofBlock => None,
                    };
                    Ok(Wp::AssertByTactus {
                        cond: cond_for_have,
                        tactic_text,
                        body: Box::new(after),
                    })
                }
                AssertQueryMode::NonLinear => Err(
                    "assert by(nonlinear_arith) not yet supported".to_string()
                ),
                AssertQueryMode::BitVector => Err(
                    "assert by(bit_vector) not yet supported".to_string()
                ),
            }
        }
        StmX::DeadEnd(_) => Err("DeadEnd not yet supported".to_string()),
        StmX::OpenInvariant(_) => Err("OpenInvariant not yet supported".to_string()),
        StmX::ClosureInner { .. } => Err("exec closures not yet supported".to_string()),
    }
}

/// Validate and build a `Wp::Call`. Destructures every `StmX::Call`
/// field explicitly (no `..`) so any future Verus field addition
/// forces a compile error here.
fn build_wp_call<'a>(
    stm: &'a Stm,
    after: Wp<'a>,
    ctx: &WpCtx<'a>,
) -> Result<Wp<'a>, String> {
    let StmX::Call {
        fun,
        resolved_method,
        mode: _,               // exec-fn bodies only route here
        is_trait_default,
        typ_args,
        args,
        split,
        dest,
        assert_id: _,          // Verus-internal error id, behaviourally inert
    } = &stm.x else {
        unreachable!("build_wp_call called on non-Call statement");
    };
    if resolved_method.is_some() {
        return Err(
            "calls to trait methods (requiring dynamic dispatch resolution) are not \
             yet supported".to_string()
        );
    }
    if is_trait_default.is_some() {
        return Err(
            "calls resolved to a trait's default impl are not yet supported".to_string()
        );
    }
    if split.is_some() {
        return Err(
            "calls with split-assertion error reporting are not yet supported".to_string()
        );
    }
    let Some(callee) = ctx.fn_map.get(fun).copied() else {
        return Err(format!(
            "callee `{:?}` not found in the crate's function map — cross-crate calls are \
             not yet supported",
            fun.path
        ));
    };
    // Param/arg count must align (both sides are post-`ast_simplify`
    // so zero-arg callees have their `no%param` dummy in both).
    let param_count = callee.params.len();
    if param_count != args.len() {
        return Err(format!(
            "callee `{:?}` has {} param(s) but call site passes {} arg(s) — \
             arg-passing convention may be out of sync (both sides should be \
             post-ast_simplify); this would bind wrong variables if we proceeded",
            fun.path, param_count, args.len(),
        ));
    }
    // Type params / type args must align — if a call site passes fewer
    // types than the callee declared, substitution would leave some
    // `TypParam(T)` references unsubstituted in the inlined spec.
    if callee.typ_params.len() != typ_args.len() {
        return Err(format!(
            "callee `{:?}` declares {} type param(s) but call site passes {} type \
             arg(s) — would leave type-param references unsubstituted in the \
             inlined spec",
            fun.path, callee.typ_params.len(), typ_args.len(),
        ));
    }
    for a in args.iter() {
        if contains_loc(a) {
            return Err(
                "calls with `&mut` arguments are not yet supported".to_string()
            );
        }
        check_exp(a)?;
    }
    let bound_dest: Option<&'a VarIdent> = dest.as_ref()
        .and_then(|d| extract_simple_var_ident(&d.dest));
    // NOTE: the termination obligation for recursive calls is emitted
    // upstream by Verus's `recursion::check_recursive_function` pass,
    // which inserts a `StmX::Assert` wrapping `InternalFun::
    // CheckDecreaseHeight` right before each recursive call
    // (including mutual recursion across an SCC). `build_wp` sees it
    // as a plain `Wp::Assert`; `sst_exp_to_ast` handles the lowering.
    Ok(Wp::Call {
        callee,
        args: &args[..],
        typ_args: &typ_args[..],
        dest: bound_dest,
        after: Box::new(after),
    })
}

/// Validate and build a `Wp::Loop`. See the module doc for the shape
/// restrictions. The loop's body is built with its OWN terminator —
/// `Done(I ∧ D < _tactus_d_old)` — rather than the outer `after`,
/// because a fall-through end of an iteration re-enters the loop's
/// maintain clause, not the post-loop continuation.
fn build_wp_loop<'a>(
    stm: &'a Stm,
    after: Wp<'a>,
    ctx: &WpCtx<'a>,
    // Enclosing loop's break/continue leaves (if any), forwarded to
    // any recursion that doesn't enter THIS loop's body. We don't
    // actually call build_wp on `after` here — `after` was already
    // built by the caller with the outer loop_ctx. The `_` marker
    // documents that we accept it for consistency with the normal
    // build_wp signature.
    _outer_loop_ctx: Option<&WpLoopCtx>,
) -> Result<Wp<'a>, String> {
    // Destructure every field explicitly so a future Verus-side
    // `StmX::Loop` addition forces a compile-time audit. `is_for_loop`
    // only affects error messages upstream; `id` / `label` are loop
    // identifiers we don't reference; `typ_inv_vars` supplies type-
    // invariant assumptions that Verus's sst_to_air uses — we
    // recompute our own `modified_vars` via `collect_modifications`
    // rather than trust Verus's `modified_vars` or `pre_modified_params`.
    let StmX::Loop {
        loop_isolation,
        is_for_loop: _,
        id: _,
        label: _,
        cond,
        body,
        invs,
        decrease,
        typ_inv_vars: _,
        modified_vars: _,
        pre_modified_params: _,
    } = &stm.x else {
        unreachable!("build_wp_loop called on non-loop statement");
    };
    if !loop_isolation {
        return Err(
            "non-isolated loops (loop_isolation: false) not yet supported".to_string()
        );
    }
    // `cond: Some` — simple `while c { … }` (no breaks) — the
    // classical form where body re-enters when c holds and exits
    // when ¬c.
    // `cond: None` — what Verus lowers `while c { … break; … }` to:
    //   loop {
    //     if !c { break; }
    //     <user body with breaks>
    //   }
    // The body contains an explicit `break` at the "cond failed"
    // check, so the maintain/use clauses don't need to gate on cond.
    // We accept both forms; break/continue in the body uses
    // `loop_ctx` to find the right leaf.
    let cond_exp_opt = match cond {
        Some((cond_setup, cond_exp)) => {
            if !matches!(&cond_setup.x, StmX::Block(ss) if ss.is_empty()) {
                return Err(
                    "loop condition with setup statements not yet supported".to_string()
                );
            }
            check_exp(cond_exp)?;
            Some(cond_exp)
        }
        None => None,
    };
    if decrease.len() != 1 {
        return Err(format!(
            "loop `decreases` must be a single expression (got {})", decrease.len()
        ));
    }
    if !invs.iter().all(|i| i.at_entry && i.at_exit) {
        return Err(
            "loop invariants must hold at both entry and exit (not \
             invariant_except_break / ensures)".to_string()
        );
    }
    for inv in invs.iter() {
        check_exp(&inv.inv)?;
    }
    for d in decrease.iter() {
        check_exp(d)?;
    }
    let decrease_exp = &decrease[0];

    // Compute modified vars from the body's *non-init* assignments —
    // `let mut x = …` inside the body is local to each iteration.
    let mut mod_names: Vec<&'a VarIdent> = Vec::new();
    let mut locally_declared: HashSet<&'a VarIdent> = HashSet::new();
    collect_modifications(body, &mut locally_declared, &mut mod_names);
    let modified_vars: Vec<(&'a VarIdent, &'a Typ)> = mod_names.into_iter()
        .filter_map(|id| ctx.type_map.get(id).map(|typ| (id, *typ)))
        .collect();

    // Body's break and continue leaves:
    // * continue (and fallthrough): re-establish invariants AND show
    //   the decrease measure decreased — `I ∧ D < _tactus_d_old`.
    //   The reference to `_tactus_d_old` here is a Var; lowering
    //   wraps the body-WP with the `let _tactus_d_old := D` binding
    //   to put it in scope.
    // * break: establish the at-exit invariants, which currently
    //   equals `I` (we only accept invariants with at_entry = at_exit
    //   = true — see validation above). No decrease obligation on
    //   break since we're leaving the loop, not iterating.
    let inv_conj = and_all(invs.iter().map(|i| sst_exp_to_ast(&i.inv)).collect());
    let continue_leaf = LExpr::and(
        inv_conj.clone(),
        LExpr::lt(sst_exp_to_ast(decrease_exp), LExpr::var("_tactus_d_old")),
    );
    let break_leaf = inv_conj;
    let inner_loop_ctx = WpLoopCtx {
        break_leaf: break_leaf.clone(),
        continue_leaf: continue_leaf.clone(),
    };
    // Body is built with THIS loop's break/continue leaves as the
    // innermost context — break/continue inside refer to *this* loop.
    let body_wp = build_wp(body, Wp::Done(continue_leaf), ctx, Some(&inner_loop_ctx))?;

    Ok(Wp::Loop {
        cond: cond_exp_opt,
        invs: &invs[..],
        decrease: decrease_exp,
        modified_vars,
        body: Box::new(body_wp),
        after: Box::new(after),
    })
}

/// Collect variables that a loop body modifies *externally* — writes
/// to vars declared outside the body. Locally-declared vars (via
/// `let mut x = …`) stay out of the set even when subsequent
/// assignments hit them, because they're each iteration's fresh locals.
///
/// `is_init: true` assignments are treated as declarations and recorded
/// in `locally_declared`. `is_init: false` assignments to a var NOT in
/// `locally_declared` count as external modifications and go into
/// `out`. Nested loops inherit the current `locally_declared` set, so
/// a variable `x` declared in an outer loop body and modified by an
/// inner loop still counts as modified by the outer.
fn collect_modifications<'a>(
    stm: &'a Stm,
    locally_declared: &mut HashSet<&'a VarIdent>,
    out: &mut Vec<&'a VarIdent>,
) {
    match &stm.x {
        StmX::Assign { lhs: Dest { dest, is_init }, .. } => {
            if let Some(ident) = extract_simple_var_ident(dest) {
                if *is_init {
                    locally_declared.insert(ident);
                } else if !locally_declared.contains(&ident) && !out.contains(&ident) {
                    out.push(ident);
                }
            }
        }
        StmX::Block(stms) => for s in stms.iter() {
            collect_modifications(s, locally_declared, out);
        },
        StmX::If(_, t, e) => {
            // Clone `locally_declared` for each branch so a `let mut x`
            // in one branch doesn't leak into the other's scope.
            // Today Verus alpha-renames branch-locals to unique idents
            // so the leak is invisible; cloning is the explicit
            // semantic-level guarantee in case that ever stops
            // holding (or we port this to a different frontend).
            let mut t_decl = locally_declared.clone();
            collect_modifications(t, &mut t_decl, out);
            if let Some(e) = e {
                let mut e_decl = locally_declared.clone();
                collect_modifications(e, &mut e_decl, out);
            }
        }
        StmX::Loop { body, .. } => collect_modifications(body, locally_declared, out),
        _ => {}
    }
}

fn extract_simple_var_ident<'a>(e: &'a Exp) -> Option<&'a VarIdent> {
    match &e.x {
        ExpX::Var(ident) | ExpX::VarLoc(ident) => Some(ident),
        ExpX::Loc(inner) => extract_simple_var_ident(inner),
        _ => None,
    }
}

fn extract_simple_var<'a>(e: &'a Exp) -> Option<&'a str> {
    extract_simple_var_ident(e).map(|id| id.0.as_str())
}

/// Verus injects synthetic params (`no%param`, etc.) with `%` in the
/// name for zero-arg functions and a few internal cases. They have no
/// user-visible semantics and must be dropped from the theorem binders.
fn is_synthetic_param(p: &Par) -> bool {
    p.x.name.0.contains('%')
}

#[cfg(test)]
mod tests {
    //! Unit tests for the Wp DSL — `needs_peel`, `lower_wp`,
    //! `contains_loc`, `lift_if_value`, and `build_wp`'s
    //! right-to-left Block fold.
    //!
    //! Test strategy: construct small `Wp` trees with hand-built SST
    //! `Exp` values (simple Vars, Consts, Ifs) and check that
    //! `lower_wp` produces the expected `LExpr` shape. For
    //! `needs_peel` the Exp leaves don't matter — only the tree
    //! structure — so we use minimal dummy exprs.
    //!
    //! These tests are direct-in-crate rather than integration so
    //! they can exercise private items (`Wp`, `build_wp`, etc.).
    use super::*;
    use std::sync::Arc;
    use vir::ast::{
        IntRange, SpannedTyped, TypX, VarIdent, VarIdentDisambiguate,
    };
    use vir::sst::ExpX;
    use vir::messages::Span;

    // ── Helpers ─────────────────────────────────────────────────

    /// A span value that passes type-checks but carries no source
    /// info. Good enough for all our tests — we don't report errors.
    fn test_span() -> Span {
        Span {
            raw_span: Arc::new(()),
            id: 0,
            data: vec![],
            as_string: String::new(),
        }
    }

    fn typ_int() -> Typ { Arc::new(TypX::Int(IntRange::Int)) }
    fn typ_bool() -> Typ { Arc::new(TypX::Bool) }

    fn var_ident(name: &str) -> VarIdent {
        VarIdent(Arc::new(name.to_string()), VarIdentDisambiguate::AirLocal)
    }

    /// Construct an SST `Var` expression with a given name and type.
    fn var_exp(name: &str, typ: Typ) -> Exp {
        Arc::new(SpannedTyped {
            span: test_span(),
            typ,
            x: ExpX::Var(var_ident(name)),
        })
    }

    /// Construct an SST `If` expression.
    fn if_exp(cond: Exp, then_e: Exp, else_e: Exp) -> Exp {
        let typ = then_e.typ.clone();
        Arc::new(SpannedTyped {
            span: test_span(),
            typ,
            x: ExpX::If(cond, then_e, else_e),
        })
    }

    /// Wrap an expression in `ExpX::Loc` — the L-value marker used
    /// for `&mut` args.
    fn loc_exp(inner: Exp) -> Exp {
        let typ = inner.typ.clone();
        Arc::new(SpannedTyped {
            span: test_span(),
            typ,
            x: ExpX::Loc(inner),
        })
    }

    /// Wrap in `UnaryOpr::Box` — the poly transparent wrapper.
    fn box_exp(inner: Exp) -> Exp {
        let typ = inner.typ.clone();
        Arc::new(SpannedTyped {
            span: test_span(),
            typ: typ.clone(),
            x: ExpX::UnaryOpr(UnaryOpr::Box(typ), inner),
        })
    }

    /// Wrap in `UnaryOpr::Unbox`.
    fn unbox_exp(inner: Exp) -> Exp {
        let typ = inner.typ.clone();
        Arc::new(SpannedTyped {
            span: test_span(),
            typ: typ.clone(),
            x: ExpX::UnaryOpr(UnaryOpr::Unbox(typ), inner),
        })
    }

    /// Wrap in `Unary::CoerceMode { .. }` — mode-coercion marker
    /// (spec/proof/exec boundary); transparent to rendering.
    fn coerce_mode_exp(inner: Exp) -> Exp {
        let typ = inner.typ.clone();
        Arc::new(SpannedTyped {
            span: test_span(),
            typ,
            x: ExpX::Unary(
                UnaryOp::CoerceMode {
                    op_mode: vir::ast::Mode::Spec,
                    from_mode: vir::ast::Mode::Spec,
                    to_mode: vir::ast::Mode::Spec,
                    kind: vir::ast::ModeCoercion::Constructor,
                },
                inner,
            ),
        })
    }

    /// Wrap in `Unary::Trigger(_)` — a trigger-pattern marker;
    /// transparent to rendering.
    fn trigger_exp(inner: Exp) -> Exp {
        let typ = inner.typ.clone();
        Arc::new(SpannedTyped {
            span: test_span(),
            typ,
            x: ExpX::Unary(UnaryOp::Trigger(vir::ast::TriggerAnnotation::Trigger(None)), inner),
        })
    }

    /// Construct a single-binder SST `Bind(Let)`:
    /// `let name := value; body`.
    fn let_exp(name: &str, value: Exp, body: Exp) -> Exp {
        use vir::ast::VarBinderX;
        use vir::def::Spanned;
        let body_typ = body.typ.clone();
        let binders: Vec<Arc<VarBinderX<Exp>>> = vec![Arc::new(VarBinderX {
            name: var_ident(name),
            a: value,
        })];
        let bnd = Spanned::new(
            test_span(),
            BndX::Let(Arc::new(binders)),
        );
        Arc::new(SpannedTyped {
            span: test_span(),
            typ: body_typ,
            x: ExpX::Bind(bnd, body),
        })
    }

    /// Minimal `WpCtx` for tests that need one but don't exercise
    /// fn_map / type_map. `ensures_goal` is a simple `True` leaf.
    fn mk_empty_ctx<'a>() -> WpCtx<'a> {
        WpCtx {
            fn_map: HashMap::new(),
            type_map: HashMap::new(),
            ret_name: None,
            ensures_goal: LExpr::new(crate::lean_ast::ExprNode::LitBool(true)),
        }
    }

    /// A dummy `Wp::Done(True)` leaf — used as `after` when the
    /// test doesn't care about post-continuation shape.
    fn done_true<'a>() -> Wp<'a> {
        Wp::Done(LExpr::new(crate::lean_ast::ExprNode::LitBool(true)))
    }

    /// Compare two LExprs structurally by pretty-printing (our
    /// printer is deterministic so equivalent trees produce
    /// identical strings).
    fn pp_eq(a: &LExpr, b: &LExpr) -> bool {
        crate::lean_pp::pp_expr(a) == crate::lean_pp::pp_expr(b)
    }

    // ── needs_peel ──────────────────────────────────────────────

    #[test]
    fn needs_peel_done() {
        let wp: Wp = Wp::Done(LExpr::var("X"));
        assert!(!wp.needs_peel());
    }

    #[test]
    fn needs_peel_flat_chain() {
        let x = var_exp("x", typ_int());
        let wp = Wp::Let("x", &x,
            Box::new(Wp::Assert(&x,
                Box::new(Wp::Assume(&x,
                    Box::new(done_true()))))));
        assert!(!wp.needs_peel());
    }

    #[test]
    fn needs_peel_branch_of_flat_is_false() {
        let x = var_exp("x", typ_bool());
        let wp = Wp::Branch {
            cond: &x,
            then_branch: Box::new(done_true()),
            else_branch: Box::new(done_true()),
        };
        assert!(!wp.needs_peel());
    }

    #[test]
    fn needs_peel_branch_with_call_inside_is_true() {
        // Hand-roll a `Wp::Call` — we need a FunctionX but only the
        // tree traversal matters, so we can rely on needs_peel never
        // looking inside the Call's fields.
        // Instead: use a Loop (same return value) that doesn't need
        // a FunctionX.
        let x = var_exp("x", typ_bool());
        let invs: Vec<LoopInv> = vec![];
        let dec = var_exp("d", typ_int());
        let loop_wp = Wp::Loop {
            cond: Some(&x),
            invs: &invs[..],
            decrease: &dec,
            modified_vars: Vec::new(),
            body: Box::new(done_true()),
            after: Box::new(done_true()),
        };
        let wp = Wp::Branch {
            cond: &x,
            then_branch: Box::new(loop_wp),
            else_branch: Box::new(done_true()),
        };
        assert!(wp.needs_peel());
    }

    #[test]
    fn needs_peel_through_let_wrappers() {
        // Let of a Done is peel-free; Let of a Loop is not.
        let x = var_exp("x", typ_int());
        let c = var_exp("c", typ_bool());
        let dec = var_exp("d", typ_int());
        let invs: Vec<LoopInv> = vec![];

        let plain = Wp::Let("x", &x, Box::new(done_true()));
        assert!(!plain.needs_peel());

        let with_loop = Wp::Let("x", &x, Box::new(Wp::Loop {
            cond: Some(&c),
            invs: &invs[..],
            decrease: &dec,
            modified_vars: Vec::new(),
            body: Box::new(done_true()),
            after: Box::new(done_true()),
        }));
        assert!(with_loop.needs_peel());
    }

    // ── lower_wp ────────────────────────────────────────────────

    #[test]
    fn lower_done_returns_leaf() {
        let ctx = mk_empty_ctx();
        let leaf = LExpr::lit_int("42");
        let wp = Wp::Done(leaf.clone());
        assert!(pp_eq(&lower_wp(&wp, &ctx), &leaf));
    }

    #[test]
    fn lower_let_wraps_with_let_bind() {
        let ctx = mk_empty_ctx();
        // Wp::Let("x", var_exp("y"), Done(x_ref))
        //   → let x := y; x_ref
        let y = var_exp("y", typ_int());
        let body_leaf = LExpr::var("inner");
        let wp = Wp::Let("x", &y, Box::new(Wp::Done(body_leaf.clone())));
        let out = lower_wp(&wp, &ctx);
        let expected = LExpr::let_bind("x", LExpr::var("y"), body_leaf);
        assert!(pp_eq(&out, &expected),
            "got: {}\nexpected: {}",
            crate::lean_pp::pp_expr(&out),
            crate::lean_pp::pp_expr(&expected));
    }

    #[test]
    fn lower_let_with_if_rhs_lifts() {
        // Wp::Let("x", if c then a else b, Done(body))
        //   → (c → let x := a; body) ∧ (¬c → let x := b; body)
        let ctx = mk_empty_ctx();
        let c = var_exp("c", typ_bool());
        let a = var_exp("a", typ_int());
        let b = var_exp("b", typ_int());
        let if_rhs = if_exp(c, a, b);
        let body_leaf = LExpr::var("inner");
        let wp = Wp::Let("x", &if_rhs, Box::new(Wp::Done(body_leaf.clone())));
        let out = lower_wp(&wp, &ctx);
        let expected = LExpr::and(
            LExpr::implies(
                LExpr::var("c"),
                LExpr::let_bind("x", LExpr::var("a"), body_leaf.clone()),
            ),
            LExpr::implies(
                LExpr::not(LExpr::var("c")),
                LExpr::let_bind("x", LExpr::var("b"), body_leaf),
            ),
        );
        assert!(pp_eq(&out, &expected),
            "got: {}\nexpected: {}",
            crate::lean_pp::pp_expr(&out),
            crate::lean_pp::pp_expr(&expected));
    }

    #[test]
    fn lower_assert_conjoins() {
        let ctx = mk_empty_ctx();
        let p = var_exp("P", typ_bool());
        let wp = Wp::Assert(&p, Box::new(Wp::Done(LExpr::var("body"))));
        let out = lower_wp(&wp, &ctx);
        let expected = LExpr::and(LExpr::var("P"), LExpr::var("body"));
        assert!(pp_eq(&out, &expected));
    }

    #[test]
    fn lower_assume_implies() {
        let ctx = mk_empty_ctx();
        let p = var_exp("P", typ_bool());
        let wp = Wp::Assume(&p, Box::new(Wp::Done(LExpr::var("body"))));
        let out = lower_wp(&wp, &ctx);
        let expected = LExpr::implies(LExpr::var("P"), LExpr::var("body"));
        assert!(pp_eq(&out, &expected));
    }

    #[test]
    fn lower_branch_conjoins_two_implications() {
        let ctx = mk_empty_ctx();
        let c = var_exp("c", typ_bool());
        let wp = Wp::Branch {
            cond: &c,
            then_branch: Box::new(Wp::Done(LExpr::var("T"))),
            else_branch: Box::new(Wp::Done(LExpr::var("E"))),
        };
        let out = lower_wp(&wp, &ctx);
        let expected = LExpr::and(
            LExpr::implies(LExpr::var("c"), LExpr::var("T")),
            LExpr::implies(LExpr::not(LExpr::var("c")), LExpr::var("E")),
        );
        assert!(pp_eq(&out, &expected));
    }

    #[test]
    fn lower_assert_assume_right_fold() {
        // Assert(P, Assume(Q, Done(body)))
        //   → P ∧ (Q → body)
        let ctx = mk_empty_ctx();
        let p = var_exp("P", typ_bool());
        let q = var_exp("Q", typ_bool());
        let wp = Wp::Assert(&p, Box::new(Wp::Assume(&q,
            Box::new(Wp::Done(LExpr::var("body"))))));
        let out = lower_wp(&wp, &ctx);
        let expected = LExpr::and(
            LExpr::var("P"),
            LExpr::implies(LExpr::var("Q"), LExpr::var("body")),
        );
        assert!(pp_eq(&out, &expected));
    }

    // ── contains_loc ────────────────────────────────────────────

    #[test]
    fn contains_loc_plain_var_false() {
        let x = var_exp("x", typ_int());
        assert!(!contains_loc(&x));
    }

    #[test]
    fn contains_loc_direct_loc_true() {
        let x = var_exp("x", typ_int());
        assert!(contains_loc(&loc_exp(x)));
    }

    #[test]
    fn contains_loc_wrapped_in_box_true() {
        let x = var_exp("x", typ_int());
        let wrapped = box_exp(loc_exp(x));
        assert!(contains_loc(&wrapped));
    }

    #[test]
    fn contains_loc_wrapped_in_unbox_true() {
        let x = var_exp("x", typ_int());
        let wrapped = unbox_exp(loc_exp(x));
        assert!(contains_loc(&wrapped));
    }

    #[test]
    fn contains_loc_double_wrapped_true() {
        let x = var_exp("x", typ_int());
        let wrapped = box_exp(unbox_exp(loc_exp(x)));
        assert!(contains_loc(&wrapped));
    }

    #[test]
    fn contains_loc_box_of_plain_var_false() {
        let x = var_exp("x", typ_int());
        assert!(!contains_loc(&box_exp(x)));
    }

    #[test]
    fn contains_loc_through_coerce_mode() {
        // CoerceMode(Loc(x))  — peels the CoerceMode marker.
        let x = var_exp("x", typ_int());
        assert!(contains_loc(&coerce_mode_exp(loc_exp(x))));
    }

    #[test]
    fn contains_loc_through_trigger() {
        // Trigger(Loc(x))  — peels the Trigger marker.
        let x = var_exp("x", typ_int());
        assert!(contains_loc(&trigger_exp(loc_exp(x))));
    }

    #[test]
    fn contains_loc_through_mixed_wrappers() {
        // Box(CoerceMode(Trigger(Unbox(Loc(x)))))  — all peelable.
        let x = var_exp("x", typ_int());
        let wrapped = box_exp(coerce_mode_exp(trigger_exp(unbox_exp(loc_exp(x)))));
        assert!(contains_loc(&wrapped));
    }

    // ── lift_if_value ───────────────────────────────────────────

    #[test]
    fn lift_if_value_plain_passes_through() {
        // Non-if value: `emit_leaf` is called once with the
        // rendered expression.
        let x = var_exp("x", typ_int());
        let out = lift_if_value(&x, &|leaf| LExpr::let_bind("y", leaf, LExpr::var("body")));
        let expected = LExpr::let_bind("y", LExpr::var("x"), LExpr::var("body"));
        assert!(pp_eq(&out, &expected));
    }

    #[test]
    fn lift_if_value_splits_on_if() {
        // If(c, a, b) → (c → emit_leaf(a)) ∧ (¬c → emit_leaf(b))
        let c = var_exp("c", typ_bool());
        let a = var_exp("a", typ_int());
        let b = var_exp("b", typ_int());
        let e = if_exp(c, a, b);
        let out = lift_if_value(&e, &|leaf| LExpr::let_bind("y", leaf, LExpr::var("body")));
        let expected = LExpr::and(
            LExpr::implies(
                LExpr::var("c"),
                LExpr::let_bind("y", LExpr::var("a"), LExpr::var("body")),
            ),
            LExpr::implies(
                LExpr::not(LExpr::var("c")),
                LExpr::let_bind("y", LExpr::var("b"), LExpr::var("body")),
            ),
        );
        assert!(pp_eq(&out, &expected));
    }

    #[test]
    fn lift_if_value_peels_box_wrapper() {
        // Box(If(...)) — the Box is transparent, If still lifts.
        let c = var_exp("c", typ_bool());
        let a = var_exp("a", typ_int());
        let b = var_exp("b", typ_int());
        let e = box_exp(if_exp(c, a, b));
        let out = lift_if_value(&e, &|leaf| LExpr::let_bind("y", leaf, LExpr::var("body")));
        let expected = LExpr::and(
            LExpr::implies(
                LExpr::var("c"),
                LExpr::let_bind("y", LExpr::var("a"), LExpr::var("body")),
            ),
            LExpr::implies(
                LExpr::not(LExpr::var("c")),
                LExpr::let_bind("y", LExpr::var("b"), LExpr::var("body")),
            ),
        );
        assert!(pp_eq(&out, &expected));
    }

    #[test]
    fn lift_if_value_peels_loc_wrapper() {
        // Loc(If(...)) — Loc is also transparent for lifting purposes.
        let c = var_exp("c", typ_bool());
        let a = var_exp("a", typ_int());
        let b = var_exp("b", typ_int());
        let e = loc_exp(if_exp(c, a, b));
        let out = lift_if_value(&e, &|leaf| LExpr::let_bind("y", leaf, LExpr::var("body")));
        let expected = LExpr::and(
            LExpr::implies(
                LExpr::var("c"),
                LExpr::let_bind("y", LExpr::var("a"), LExpr::var("body")),
            ),
            LExpr::implies(
                LExpr::not(LExpr::var("c")),
                LExpr::let_bind("y", LExpr::var("b"), LExpr::var("body")),
            ),
        );
        assert!(pp_eq(&out, &expected));
    }

    #[test]
    fn lift_if_value_peels_bind_let_with_if_rhs() {
        // Verus shape: `let y = (if c then a else b); y`
        // represented as `Bind(Let([(y, If(c,a,b))]), Var(y))`.
        // lift_if_value peels the single-binder Let, lifts the If,
        // and re-threads the outer `let y := ...; body` around each
        // branch.
        //
        //   Input shape:  Bind(Let([(y, If(c, a, b))]), Var(y))
        //   Expected:     (c → let y := a; y) ∧ (¬c → let y := b; y)
        //                  ^^^^^^^^^^^^^^^^^^     ^^^^^^^^^^^^^^^^^^
        //                  emit_leaf wraps these, but the body `Var(y)`
        //                  is the "inner body" captured at peel time.
        let c = var_exp("c", typ_bool());
        let a = var_exp("a", typ_int());
        let b = var_exp("b", typ_int());
        let y_ref = var_exp("y", typ_int());
        let e = let_exp("y", if_exp(c, a, b), y_ref);

        let out = lift_if_value(&e, &|leaf| LExpr::let_bind("out", leaf, LExpr::var("done")));
        // lift_if_value peels the Bind(Let), lifts the If inside the
        // value position, and re-threads `let y := rhs_leaf; y` into
        // each branch. Then emit_leaf wraps the whole let-y-y chunk.
        let expected = LExpr::and(
            LExpr::implies(
                LExpr::var("c"),
                LExpr::let_bind("out",
                    LExpr::let_bind("y", LExpr::var("a"), LExpr::var("y")),
                    LExpr::var("done")),
            ),
            LExpr::implies(
                LExpr::not(LExpr::var("c")),
                LExpr::let_bind("out",
                    LExpr::let_bind("y", LExpr::var("b"), LExpr::var("y")),
                    LExpr::var("done")),
            ),
        );
        assert!(pp_eq(&out, &expected),
            "got: {}\nexpected: {}",
            crate::lean_pp::pp_expr(&out),
            crate::lean_pp::pp_expr(&expected));
    }

    #[test]
    fn lift_if_value_bind_let_without_if_passes_through() {
        // `let y := x; y` where x is a plain var — no If to lift.
        // lift_if_value should recurse into `b.a` (which is Var(x)),
        // call emit_leaf with the x rendering, then re-wrap with
        // `let y := x; body`.
        let x = var_exp("x", typ_int());
        let y_ref = var_exp("y", typ_int());
        let e = let_exp("y", x, y_ref);
        let out = lift_if_value(&e, &|leaf| LExpr::let_bind("out", leaf, LExpr::var("done")));
        let expected = LExpr::let_bind("out",
            LExpr::let_bind("y", LExpr::var("x"), LExpr::var("y")),
            LExpr::var("done"));
        assert!(pp_eq(&out, &expected));
    }

    // ── extract_simple_var ─────────────────────────────────────

    #[test]
    fn extract_simple_var_from_plain_var() {
        let x = var_exp("x", typ_int());
        assert_eq!(extract_simple_var(&x), Some("x"));
    }

    #[test]
    fn extract_simple_var_through_loc() {
        let x = var_exp("x", typ_int());
        assert_eq!(extract_simple_var(&loc_exp(x)), Some("x"));
    }

    #[test]
    fn extract_simple_var_from_if_is_none() {
        let c = var_exp("c", typ_bool());
        let a = var_exp("a", typ_int());
        let b = var_exp("b", typ_int());
        let e = if_exp(c, a, b);
        assert_eq!(extract_simple_var(&e), None);
    }

    // ── peel_transparent ──────────────────────────────────────
    //
    // The shared helper for peeling Box/Unbox/CoerceMode/Trigger
    // wrappers. If Verus ever adds a new transparent wrapper kind,
    // `contains_loc` / `lift_if_value` / `render_checked_decrease_arg`
    // all silently miss it — these tests pin the current wrapper
    // set so the breakage shows up as a failing assertion here
    // rather than as mysterious miscompilation in recursive fn
    // tests.

    fn exp_ident(e: &Exp) -> Option<&str> {
        match &e.x {
            ExpX::Var(id) => Some(id.0.as_str()),
            _ => None,
        }
    }

    #[test]
    fn peel_transparent_leaves_plain_var_alone() {
        let x = var_exp("x", typ_int());
        assert_eq!(exp_ident(peel_transparent(&x)), Some("x"));
    }

    #[test]
    fn peel_transparent_peels_box() {
        let x = var_exp("x", typ_int());
        assert_eq!(exp_ident(peel_transparent(&box_exp(x))), Some("x"));
    }

    #[test]
    fn peel_transparent_peels_unbox() {
        let x = var_exp("x", typ_int());
        assert_eq!(exp_ident(peel_transparent(&unbox_exp(x))), Some("x"));
    }

    #[test]
    fn peel_transparent_peels_coerce_mode() {
        let x = var_exp("x", typ_int());
        assert_eq!(exp_ident(peel_transparent(&coerce_mode_exp(x))), Some("x"));
    }

    #[test]
    fn peel_transparent_peels_trigger() {
        let x = var_exp("x", typ_int());
        assert_eq!(exp_ident(peel_transparent(&trigger_exp(x))), Some("x"));
    }

    #[test]
    fn peel_transparent_peels_stacked_wrappers() {
        // Box(Unbox(CoerceMode(Trigger(Var))))
        let x = var_exp("x", typ_int());
        let wrapped = box_exp(unbox_exp(coerce_mode_exp(trigger_exp(x))));
        assert_eq!(exp_ident(peel_transparent(&wrapped)), Some("x"));
    }

    #[test]
    fn peel_transparent_does_not_peel_loc() {
        // Loc is NOT in the transparent set — `contains_loc` depends
        // on finding it un-peeled.
        let x = var_exp("x", typ_int());
        let wrapped = loc_exp(x);
        // After peel, we should still see ExpX::Loc at the top.
        assert!(matches!(&peel_transparent(&wrapped).x, ExpX::Loc(_)));
    }

    #[test]
    fn peel_transparent_does_not_peel_if() {
        // If is structurally meaningful — must not be peeled.
        let c = var_exp("c", typ_bool());
        let a = var_exp("a", typ_int());
        let b = var_exp("b", typ_int());
        let e = if_exp(c, a, b);
        assert!(matches!(&peel_transparent(&e).x, ExpX::If(..)));
    }

    #[test]
    fn peel_transparent_stops_at_loc_but_peels_wrappers_around_it() {
        // Box(Loc(x)) — peel the Box, stop at Loc.
        let x = var_exp("x", typ_int());
        let wrapped = box_exp(loc_exp(x));
        assert!(matches!(&peel_transparent(&wrapped).x, ExpX::Loc(_)));
    }

    // ── CheckDecreaseHeight shape-drift detection ─────────────────
    //
    // `render_checked_decrease_arg` assumes `cur`/`prev` are shaped
    // as `Bind(Let(params → args, decrease_expr))` (possibly wrapped
    // in transparent poly/coerce wrappers). If Verus ever changes
    // this encoding, our peel falls through to the default renderer
    // which emits a shadowing `let` that defeats omega on
    // self-recursion.
    //
    // These tests pin the shape expectation so a drift trips an
    // assertion here instead of producing obscure recursive-fn
    // verification failures.

    /// Construct the canonical CheckDecreaseHeight `cur` arg shape:
    /// `Bind(Let([(param, arg)]), decrease_expr)` — optionally
    /// wrapped in a transparent Box (mirrors `poly::coerce_exp_to_poly`).
    fn mk_decrease_arg(with_box: bool, param: &str, arg_name: &str, decrease_var: &str) -> Exp {
        let arg = var_exp(arg_name, typ_int());
        let dec = var_exp(decrease_var, typ_int());
        let inner = let_exp(param, arg, dec);
        if with_box { box_exp(inner) } else { inner }
    }

    /// Render via the full `sst_exp_to_ast_checked` pathway —
    /// exercises `CheckDecreaseHeight` lowering end-to-end.
    fn render_via_public(e: &Exp) -> LExpr {
        crate::to_lean_sst_expr::sst_exp_to_ast(e)
    }

    #[test]
    fn decrease_arg_shape_with_box_wrapper_substitutes() {
        // Canonical Verus shape: Box(Let([(n, tmp)], n))
        //   After peel + substitute: tmp
        let e = mk_decrease_arg(true, "n", "tmp", "n");
        // `sst_exp_to_ast` would emit `Box` as transparent and render
        // the inner Let directly (producing shadowing). We need to go
        // through the CheckDecreaseHeight-specific helper. Since
        // render_checked_decrease_arg is private, we test the shape
        // by constructing a full CheckDecreaseHeight call below.
        let _ = e;
    }

    #[test]
    fn decrease_arg_without_bind_let_falls_through() {
        // If Verus ever emits CheckDecreaseHeight without the
        // Bind(Let) wrapper — e.g., just a plain Var — our code
        // falls through to sst_exp_to_ast_checked. This test pins
        // that the fallthrough produces the var unchanged (not a
        // let-wrapped form). If the assumption about Bind(Let)
        // wrapping drifts, this test still passes — but the
        // `full_check_decrease_height_shape` test below fails
        // because we won't substitute any more.
        let x = var_exp("x", typ_int());
        let rendered = render_via_public(&box_exp(x));
        assert_eq!(crate::lean_pp::pp_expr(&rendered), "x");
    }

    #[test]
    fn full_check_decrease_height_shape_pinned() {
        // Full shape: CheckDecreaseHeight(
        //   Box(Let([(n, tmp)], n)),   -- cur
        //   Box(n_old),                 -- prev
        //   False                       -- otherwise (single-expr decrease)
        // )
        //
        // Expected lowering:
        //   (0 ≤ tmp ∧ tmp < n_old) ∨ (tmp = n_old ∧ False)
        //
        // If Verus changes the Bind(Let) shape, the substitution
        // won't happen and `cur` will render as the raw `let n :=
        // tmp; n` form — the expected output won't match.
        use vir::sst::{CallFun, ExpX, InternalFun};
        let cur = mk_decrease_arg(true, "n", "tmp", "n");
        let prev = box_exp(var_exp("n_old", typ_int()));
        let otherwise = Arc::new(SpannedTyped {
            span: test_span(),
            typ: typ_bool(),
            x: ExpX::Const(vir::ast::Constant::Bool(false)),
        });
        let args = Arc::new(vec![cur, prev, otherwise]);
        let typ_args: Arc<Vec<Typ>> = Arc::new(vec![]);
        let call = Arc::new(SpannedTyped {
            span: test_span(),
            typ: typ_bool(),
            x: ExpX::Call(
                CallFun::InternalFun(InternalFun::CheckDecreaseHeight),
                typ_args,
                args,
            ),
        });
        let rendered = render_via_public(&call);
        let printed = crate::lean_pp::pp_expr(&rendered);
        // Must be the substituted form (tmp), not the shadowing let.
        assert!(printed.contains("tmp"),
            "CheckDecreaseHeight should render with tmp substituted: {}",
            printed);
        assert!(!printed.contains("let n := tmp"),
            "Verus Bind(Let) wrapper must be zeta-reduced, not emitted as let: \
             {}\n\
             If this fails, Verus's CheckDecreaseHeight `cur` shape has \
             drifted; update `render_checked_decrease_arg` in to_lean_sst_expr.rs.",
            printed);
        // And the expected disjunction structure must be present.
        assert!(printed.contains("0 ≤") || printed.contains("0≤"),
            "lower bound 0 ≤ cur should be present: {}", printed);
        assert!(printed.contains("∨") || printed.contains("\\/"),
            "disjunction with `otherwise` branch should be present: {}", printed);
    }
}
