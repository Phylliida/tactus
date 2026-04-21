//! Weakest-precondition VC generation from SST → Lean AST.
//!
//! Takes an exec fn's `FuncCheckSst` (from `FunctionSst::exec_proof_check`)
//! and produces a `Theorem` AST node whose goal is the WP of the body and
//! whose tactic body is `tactus_auto`.
//!
//! # Current scope
//!
//! Handles bodies built from:
//!
//!   * `StmX::Block`     — nested/sequential composition
//!   * `StmX::Assign`    — simple-LHS `let x := e` bindings; non-simple
//!                         LHS (field writes, etc.) is rejected upfront
//!   * `StmX::Assert`    — obligations, conjoined into the goal
//!   * `StmX::Assume`    — hypotheses, threaded into the goal as implications
//!   * `StmX::If`        — branching; WP splits across `cond` / `¬cond`
//!   * `StmX::Return`    — terminator; any items after it in the
//!                         same sequence are unreachable and dropped.
//!                         Works at top level, inside a branch, or as
//!                         an early-return mid-block (`inside_body:
//!                         true`) — all three lower to the same
//!                         `BodyItem::Return`.
//!   * `StmX::Air`, `StmX::Fuel`, `StmX::RevealString` — transparent
//!   * `StmX::Call`      — direct named function calls. The callee's
//!                         `requires` becomes an obligation, its
//!                         `ensures` a hypothesis bound under `∀ ret`.
//!                         Callees are inlined (their spec is pulled
//!                         from `FunctionX`), so no Lean definition of
//!                         the callee is needed. Rejects: trait
//!                         methods, generics, `&mut` args, cross-crate
//!                         calls. See "Loop / Call obligations" below.
//!   * `StmX::Loop`      — `while` loops with `loop_isolation: true`,
//!                         simple `while` condition (no setup
//!                         statements), single-expression `decreases`,
//!                         invariants true at both entry and exit.
//!                         Loops can appear anywhere — top level,
//!                         inside if-branches, nested within another
//!                         loop's body, or in sequence — because each
//!                         loop contributes its obligations as
//!                         conjuncts into the enclosing goal (see
//!                         "Loop obligations" below). `break` /
//!                         `continue` aren't supported yet.
//!
//! Not yet supported: break/continue, lexicographic `decreases`,
//! pattern matching, closures, mutable references (`&mut`).
//! Fixed-width arithmetic overflow IS checked, but via `HasType`
//! assertions folded into the body WP — not via separate per-op
//! theorems.
//!
//! # Loop obligations (conjunctive WP)
//!
//! A loop inside an exec fn body contributes three pieces to the goal
//! of the enclosing theorem — conjoined inline rather than split into
//! separate theorems:
//!
//! ```
//! wp(pre; while cond inv I dec D { body }; post, ensures)
//!   = wp(pre,
//!       I                                       -- init: I holds at loop entry
//!       ∧ maintain_clause                       -- body preserves I and decreases D
//!       ∧ ∀ (mod_vars …), bounds → I ∧ ¬cond →  -- havoc; post-loop is reachable
//!           wp(post, ensures))
//! ```
//!
//! where `maintain_clause` is
//!
//! ```
//!   ∀ (mod_vars …), bounds → I ∧ cond →
//!     let d_old := D;
//!     wp(body, I ∧ D < d_old)
//! ```
//!
//! Non-modified surrounding state (fn params, other local lets) stays
//! in scope via the outer `let`/`∀` nesting that `build_goal` is
//! already building. Only `mod_vars` — variables the loop body writes
//! to — get the fresh universal quantification.
//!
//! Because the loop's contribution is itself a goal expression, the
//! recursion composes: a loop inside another loop's `body` lands
//! inside that inner `wp(body, …)`, and a loop inside an if-branch
//! lands inside the branch's continuation.
//!
//! # Mutation
//!
//! Simple mutation (`let mut x = …; x = …;`) needs no rename pass:
//! `StmX::Assign { is_init: false }` emits `let x := e` just like an
//! init, and Lean's let-shadowing gives us SSA semantics naturally.
//! This also works across if-branches — an inner branch's `let x := …`
//! only shadows within its implication, so the outer `x` remains in
//! scope for the other branch and the code after the if. Loops break
//! this trick because the loop body's mutations can't tunnel out
//! through shadowing; they'll need a real rename pass when we get
//! there.
//!
//! # Semantic model (weakest-precondition, in body order)
//!
//! We walk statements in source order and nest each one into the goal:
//!
//! * `let x = e` becomes `let x := e; <rest>`.
//! * `assume(P)` becomes `(P) → <rest>`.
//! * `assert(P)` becomes `(P) ∧ (<rest>)`. `P` must be provable without
//!   using assumes that appear *after* it — this is the property that
//!   separates us from a naive "conjoin everything" scheme.
//! * `if c { s₁ } else { s₂ }` becomes
//!   `(c → wp(s₁; <rest>)) ∧ (¬c → wp(s₂; <rest>))`. Both branches share
//!   the same continuation; we duplicate `<rest>` syntactically rather
//!   than let-binding a shared goal.
//! * `return e` is a terminator: it wraps the ensures as `let <ret> :=
//!   e; <ensures>` and any items after it in the same sequence are
//!   unreachable and dropped. Works for both tail returns and for
//!   early returns inside an `if` branch (the branch's continuation
//!   ends at the return; the outer `rest` never gets appended past it).
//!
//! The AST pretty-printer handles precedence, so constructors just build
//! `BinOp::And` / `BinOp::Implies` / `UnOp::Not` / `Let` without worrying
//! about parens.

use std::collections::{HashMap, HashSet};

use vir::sst::{
    BndX, Dest, Exp, ExpX, FuncCheckSst, FunctionSst, LoopInv, Par, Stm, StmX,
};
use vir::ast::{Fun, FunctionX, KrateX, Typ, UnaryOp, UnaryOpr, VarIdent};
use crate::lean_ast::{
    and_all, substitute, Binder as LBinder, BinderKind, Expr as LExpr, Tactic, Theorem,
};
use crate::to_lean_expr::vir_expr_to_ast;
use crate::to_lean_sst_expr::{sst_exp_to_ast, sst_exp_to_ast_checked, type_bound_predicate};
use crate::to_lean_type::{lean_name, sanitize, typ_to_expr};

/// Lookup table from callee `Fun` to its VIR-AST `FunctionX`. Used by
/// `BodyItem::Call` to inline a callee's `requires` / `ensures` at the
/// call site. Callee's spec lives on `FunctionX` (VIR-AST), not on
/// its `FunctionSst`, so the map points at the AST form.
pub type FnMap<'a> = HashMap<&'a Fun, &'a FunctionX>;

/// Shared context threaded through the WP builder. Collects the
/// per-verification-unit state that nearly every walker / builder
/// needs — the callee lookup, the local declaration types, the fn's
/// ensures goal (where `return` terminates), and the declared return
/// var name (if any). Future additions — source spans, current-fn
/// name, etc. — plug into this struct instead of growing every
/// function signature.
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
    /// Precondition: expressions in `check.post_condition.ens_exps`
    /// have been validated (e.g., via `check_exp`) — `sst_exp_to_ast`
    /// is infallible and would panic on unsupported forms. Validation
    /// happens in `exec_fn_theorems_to_ast` before calling `new`.
    pub fn new(krate: &'a KrateX, check: &'a FuncCheckSst) -> Self {
        let fn_map = krate.functions.iter().map(|f| (&f.x.name, &f.x)).collect();
        let type_map = check.local_decls.iter().map(|d| (&d.ident, &d.typ)).collect();
        let ret_name = check.post_condition.dest.as_ref().map(|v| v.0.as_str());
        let ensures_goal = and_all(
            check.post_condition.ens_exps.iter().map(sst_exp_to_ast).collect()
        );
        Self { fn_map, type_map, ret_name, ensures_goal }
    }
}

// ── Support check (helpers) ────────────────────────────────────────────
//
// The main validation is fused into `walk` below — a single pass that
// both checks shape constraints and builds the `BodyItem` sequence. The
// helpers here are the reusable bits.

// Callee param iteration is just `callee.params.iter()`. Our `FnMap`
// sees the POST-simplify `FunctionX` (see `verifier.rs`'s
// `vir_crate_simplified`), so for zero-arg fns the params list
// includes Verus's injected `no%param` dummy — matched positionally
// by a `Const(0)` dummy arg at the call site. Both sides align, so
// we can zip directly; the dummy param's substitution binds a name
// nothing references, inert.

/// Does this expression — or any transparently-wrapped inner — use
/// `ExpX::Loc`? `Loc` marks an L-value (`&mut` argument site). We peel
/// the same transparent wrappers as `lift_if_value` so a mutable borrow
/// buried under `Box` / `Unbox` / `CoerceMode` / `Trigger` is still
/// detected rather than silently accepted as by-value.
fn contains_loc(e: &Exp) -> bool {
    match &e.x {
        ExpX::Loc(_) => true,
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner)
        | ExpX::Unary(UnaryOp::CoerceMode { .. } | UnaryOp::Trigger(_), inner) => {
            contains_loc(inner)
        }
        _ => false,
    }
}

/// Validate an SST expression — `sst_exp_to_ast_checked` does both
/// validation AND rendering in a single pass, so we just call it and
/// discard the rendered result. Used by `walk` at the points where
/// it encounters expressions that `build_goal` will later re-render
/// via the infallible wrapper (at which point validation is known to
/// have passed).
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
/// (`walk`) so the "validate-first" precondition is enforced by
/// construction — there's no way to produce `BodyItem`s without having
/// already cleared the shape checks.
pub fn exec_fn_theorems_to_ast<'a>(
    krate: &'a KrateX,
    fn_sst: &'a FunctionSst,
    check: &'a FuncCheckSst,
) -> Result<Vec<Theorem>, String> {
    // Validate reqs / ens expressions before WpCtx::new renders them
    // via the infallible `sst_exp_to_ast`.
    for req in check.reqs.iter() {
        check_exp(req)?;
    }
    for ens in check.post_condition.ens_exps.iter() {
        check_exp(ens)?;
    }

    let ctx = WpCtx::new(krate, check);

    let name = format!("_tactus_body_{}", lean_name(&fn_sst.x.name.path));
    let mut binders = build_param_binders(fn_sst);
    binders.extend(build_req_binders(check));

    // Build the whole WP tree from the body, with the fn's ensures
    // as the natural continuation at the leaves. `Return` statements
    // inside the body replace their local `after` with the same
    // ensures goal (via `ctx.ensures_goal`).
    let body_wp = build_wp(&check.body, Wp::Done(ctx.ensures_goal.clone()), &ctx)?;
    let has_loop_or_call = body_wp.needs_peel();
    let goal = lower_wp(&body_wp, &ctx);
    let tactic = if has_loop_or_call { loop_tactic() } else { simple_tactic() };
    Ok(vec![Theorem { name, binders, goal, tactic }])
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
// `build_wp` (where walk produces it) and `lower_wp` (where it lowers
// to LExpr). No changes needed to a central dispatcher.

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
    Loop {
        cond: &'a Exp,
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
        args: Vec<&'a Exp>,
        dest: Option<(&'a VarIdent, &'a Typ)>,
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
        Wp::Branch { cond, then_branch, else_branch } => {
            let c = sst_exp_to_ast(cond);
            LExpr::and(
                LExpr::implies(c.clone(), lower_wp(then_branch, ctx)),
                LExpr::implies(LExpr::not(c), lower_wp(else_branch, ctx)),
            )
        }
        Wp::Loop { cond, invs, decrease, modified_vars, body, after } => {
            lower_loop(cond, invs, decrease, modified_vars, body, after, ctx)
        }
        Wp::Call { callee, args, dest, after } => {
            lower_call(callee, args, *dest, after, ctx)
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
    cond: &Exp,
    invs: &[LoopInv],
    decrease: &Exp,
    modified_vars: &[(&VarIdent, &Typ)],
    body: &Wp<'_>,
    after: &Wp<'_>,
    ctx: &WpCtx<'_>,
) -> LExpr {
    let inv_conj = || and_all(invs.iter().map(|i| sst_exp_to_ast(&i.inv)).collect());
    let cond_ast = || sst_exp_to_ast(cond);
    let decrease_ast = || sst_exp_to_ast(decrease);

    // Init: invariant conjunction at loop entry.
    let init_clause = inv_conj();

    // Maintain: `∀ mod_vars, bounds → I ∧ cond →
    //             (let _tactus_d_old := D; lower_wp(body))`.
    // See DESIGN.md "_tactus_d_old aliasing across nested loops" for
    // the rationale behind the literal name.
    let maintain_body_lowered = lower_wp(body, ctx);
    let maintain_core = LExpr::let_bind("_tactus_d_old", decrease_ast(), maintain_body_lowered);
    let maintain_clause = quantify_mod_vars(
        modified_vars,
        LExpr::implies(LExpr::and(inv_conj(), cond_ast()), maintain_core),
    );

    // Use / post-loop continuation: `∀ mod_vars, bounds → I ∧ ¬cond →
    //   lower_wp(after)`. `after`'s Done leaves point at the outer
    // ensures (or whatever the enclosing scope's `after` was), so
    // nested loops' post-body code feeds back correctly.
    let after_lowered = lower_wp(after, ctx);
    let use_clause = quantify_mod_vars(
        modified_vars,
        LExpr::implies(LExpr::and(inv_conj(), LExpr::not(cond_ast())), after_lowered),
    );

    LExpr::and(init_clause, LExpr::and(maintain_clause, use_clause))
}

/// Lower a `Wp::Call` by inlining the callee's require / ensure via
/// Lean-AST substitution (rather than textual let-wrapping, which
/// would shadow caller names on self-recursion). See the old
/// `build_call_conjunction` comment for the shape rationale; the
/// change here is just that the continuation is a `Wp` sub-tree
/// instead of a remaining-items slice.
fn lower_call(
    callee: &FunctionX,
    args: &[&Exp],
    dest: Option<(&VarIdent, &Typ)>,
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

    let subst: std::collections::HashMap<String, LExpr> = params_vec.iter()
        .zip(args.iter())
        .map(|(p, arg)| (sanitize(&p.x.name.0), sst_exp_to_ast(arg)))
        .collect();

    let requires_conj = and_all(
        callee.require.iter().map(|e| vir_expr_to_ast(e)).collect()
    );
    let ensures_conj = and_all(
        callee.ensure.0.iter().map(|e| vir_expr_to_ast(e)).collect()
    );
    let requires_clause = substitute(&requires_conj, &subst);

    let ret = &callee.ret.x;
    let ret_name_cal = sanitize(&ret.name.0);
    let ret_typ = typ_to_expr(&ret.typ);
    let continuation_under_ret = {
        let after_lowered = lower_wp(after, ctx);
        let bound_rest = match dest {
            Some((dest_ident, _)) => LExpr::let_bind(
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
    match &e.x {
        ExpX::If(cond, then_e, else_e) => {
            let c = sst_exp_to_ast(cond);
            LExpr::and(
                LExpr::implies(c.clone(), lift_if_value(then_e, emit_leaf)),
                LExpr::implies(LExpr::not(c), lift_if_value(else_e, emit_leaf)),
            )
        }
        // Peel transparent wrappers — they don't emit any Lean code
        // (`to_lean_sst_expr` elides them) so peeling here is safe.
        ExpX::Loc(inner) => lift_if_value(inner, emit_leaf),
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner) => {
            lift_if_value(inner, emit_leaf)
        }
        ExpX::Unary(UnaryOp::CoerceMode { .. } | UnaryOp::Trigger(_), inner) => {
            lift_if_value(inner, emit_leaf)
        }
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

/// Build the three-way conjunction contributed by a loop.
///
///   `I ∧ (∀ mod_vars, bounds → I ∧ cond → <maintain>)
///      ∧ (∀ mod_vars, bounds → I ∧ ¬cond → <wp(rest, outer_terminator)>)`
///
/// The outer `I` asserts the invariant at loop entry. Maintain and use
/// are both universally quantified over the loop's modified vars —
/// maintain because the loop body must preserve `I` and decrease `D`
/// for an arbitrary iteration start; use because after the loop exits,
/// the only thing we know about modified vars is `I ∧ ¬cond`.
///
/// The maintain clause uses its own local terminator `I ∧ D < d_old`
/// (one per loop). The use clause threads the outer `terminator`
/// through, so a nested loop's post-loop code feeds back into the
/// outer loop's post-body goal / fn ensures.
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

// ── WP builder (walk) ──────────────────────────────────────────────────

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
) -> Result<Wp<'a>, String> {
    match &stm.x {
        StmX::Block(stms) => {
            // Fold right-to-left: walk(s_last, outer_after),
            //                     walk(s_{n-1}, that),
            //                     ...,
            //                     walk(s_0, whole_rest).
            let mut wp = after;
            for s in stms.iter().rev() {
                wp = build_wp(s, wp, ctx)?;
            }
            Ok(wp)
        }
        StmX::Assign { lhs: Dest { dest, .. }, rhs } => {
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
        StmX::Return { ret_exp: Some(e), .. } => {
            check_exp(e)?;
            let ensures_goal = ctx.ensures_goal.clone();
            let ret_name = ctx.ret_name;
            let leaf = lift_if_value(e, &|e_ast| match ret_name {
                Some(name) => LExpr::let_bind(sanitize(name), e_ast, ensures_goal.clone()),
                None => ensures_goal.clone(),
            });
            Ok(Wp::Done(leaf))
        }
        StmX::Return { ret_exp: None, .. } => Ok(Wp::Done(ctx.ensures_goal.clone())),
        StmX::If(cond, then_stm, else_stm) => {
            check_exp(cond)?;
            // Both branches share the same post-if continuation. Clone
            // `after` into each — this is where the pre-DSL code's
            // exponential-in-nested-ifs size comes from; see DESIGN.md
            // "Known codegen-complexity trade-offs" for the shared-
            // continuation let-binding optimization we chose not to
            // implement (simp zeta-reduces it, so no saving).
            let then_branch = build_wp(then_stm, after.clone(), ctx)?;
            let else_branch = match else_stm {
                Some(e) => build_wp(e, after, ctx)?,
                None => after,
            };
            Ok(Wp::Branch {
                cond,
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            })
        }
        StmX::Call { .. } => build_wp_call(stm, after, ctx),
        StmX::Loop { .. } => build_wp_loop(stm, after, ctx),
        // Transparent in SST: pass `after` through unchanged.
        StmX::Air(_) | StmX::Fuel(..) | StmX::RevealString(_) => Ok(after),
        StmX::BreakOrContinue { .. } => Err(
            "break/continue not yet supported".to_string()
        ),
        StmX::AssertBitVector { .. } => Err(
            "assert by(bit_vector) not yet supported".to_string()
        ),
        StmX::AssertQuery { .. } => Err(
            "assert by(...) queries not yet supported".to_string()
        ),
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
    if !typ_args.is_empty() {
        return Err(
            "calls to generic functions (non-empty type args) are not yet supported".to_string()
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
    for a in args.iter() {
        if contains_loc(a) {
            return Err(
                "calls with `&mut` arguments are not yet supported".to_string()
            );
        }
        check_exp(a)?;
    }
    let arg_refs: Vec<&'a Exp> = args.iter().collect();
    let bound_dest: Option<(&'a VarIdent, &'a Typ)> = dest.as_ref().and_then(|d| {
        let ident = extract_simple_var_ident(&d.dest)?;
        let typ = ctx.type_map.get(ident).copied()?;
        Some((ident, typ))
    });
    // NOTE: the termination obligation for recursive calls is emitted
    // upstream by Verus's `recursion::check_recursive_function` pass,
    // which inserts a `StmX::Assert` wrapping `InternalFun::
    // CheckDecreaseHeight` right before each recursive call
    // (including mutual recursion across an SCC). `build_wp` sees it
    // as a plain `Wp::Assert`; `sst_exp_to_ast` handles the lowering.
    Ok(Wp::Call {
        callee,
        args: arg_refs,
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
) -> Result<Wp<'a>, String> {
    let StmX::Loop {
        loop_isolation, cond, body, invs, decrease, modified_vars: _, ..
    } = &stm.x else {
        unreachable!("build_wp_loop called on non-loop statement");
    };
    if !loop_isolation {
        return Err(
            "non-isolated loops (loop_isolation: false) not yet supported".to_string()
        );
    }
    let Some((cond_setup, cond_exp)) = cond else {
        return Err("loops without a simple `while` condition not yet supported".to_string());
    };
    if !matches!(&cond_setup.x, StmX::Block(ss) if ss.is_empty()) {
        return Err(
            "loop condition with setup statements not yet supported".to_string()
        );
    }
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
    check_exp(cond_exp)?;
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

    // Body's local terminator: `I ∧ D < _tactus_d_old`. The reference
    // to `_tactus_d_old` here is a Var; lowering wraps the body-WP
    // with the `let _tactus_d_old := D` binding to put it in scope.
    let inv_conj = and_all(invs.iter().map(|i| sst_exp_to_ast(&i.inv)).collect());
    let maintain_local_goal = LExpr::and(
        inv_conj,
        LExpr::lt(sst_exp_to_ast(decrease_exp), LExpr::var("_tactus_d_old")),
    );
    let body_wp = build_wp(body, Wp::Done(maintain_local_goal), ctx)?;

    Ok(Wp::Loop {
        cond: cond_exp,
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
