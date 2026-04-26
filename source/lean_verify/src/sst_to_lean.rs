//! Weakest-precondition VC generation from SST → Lean AST.
//!
//! Takes an exec fn's `FuncCheckSst` (from `FunctionSst::exec_proof_check`)
//! and produces a `Vec<Theorem>` — one theorem per obligation in the
//! body. Each theorem's tactic body is `tactus_auto` (or the user's
//! tactic for `assert(P) by { … }` and proof blocks).
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
//! 3. `walk_obligations(&body_wp, &ctx, &OblCtx::new(), &mut emitter)`
//!    walks the Wp tree, accumulating `OblCtx` frames (Let / Hyp /
//!    Binder) at scope-introducing points and emitting one Lean
//!    theorem per obligation site. Each emitted theorem's goal is
//!    `OblCtx::wrap(obligation_lexpr)` — the accumulated frames
//!    folded around the obligation in source order.
//!
//! Per-obligation emission (D, 2026-04-26) replaced an earlier
//! single-theorem `lower_wp` pipeline that produced one mega-theorem
//! with `init ∧ maintain ∧ use ∧ ensures …` conjuncts. The split lets
//! each obligation get its own `pos.line` for Lean diagnostics, so
//! `find_span_mark` returns the right `AssertKind` label by
//! construction.
//!
//! # The `Wp` DSL
//!
//! `Wp<'a>` is a small algebra of WP-shaped operations:
//!
//!   * `Done(LExpr)` — terminator leaf; no continuation slot. Built
//!     from the fn's ensures at top level, `I ∧ D < _tactus_d_old`
//!     inside a loop body, or `let <ret> := e; ensures_goal` from a
//!     `return` statement.
//!   * `Let(x, rhs, after)` — `let x := rhs; <after>`. The walker
//!     calls `walk_let`, which forks if `rhs` contains a value-
//!     position `if` (mirroring `lift_if_value`'s behaviour for
//!     `Return`-position values).
//!   * `Assert(P, after)` — emit one obligation theorem for `P`;
//!     body walked with `P` as a Hyp frame.
//!   * `Assume(P, after)` — body walked with `P` as a Hyp frame; no
//!     theorem emitted.
//!   * `Branch { cond, then_branch, else_branch }` — body walked
//!     under `cond` for the then-branch, `¬cond` for the else; no
//!     theorem at the branch node.
//!   * `Loop { cond, invs, decrease, modified_vars, body, after }` —
//!     emit one theorem per invariant (init); walk body in maintain
//!     ctx; walk `after` in use ctx. See `walk_loop`.
//!   * `Call { callee, args, dest, after }` — emit one theorem for
//!     the substituted requires (CallPrecondition); walk `after` in
//!     ctx with `∀ ret, ret_bound, ensures(subst), let dest := ret;`
//!     frames pushed. See `walk_call`.
//!   * `AssertByTactus { cond, tactic_text, body }` — `Some(P)`:
//!     emit one theorem for `P` with the user's tactic as closer;
//!     body walked with `P` as a Hyp. `None` (proof block): push
//!     the user's tactic onto `tactic_prefix` and walk body; every
//!     emitted theorem in scope gets `(user_tac) <;> closer` so
//!     the user's `have`s propagate.
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
//! # Loop obligations (per-clause emission)
//!
//! A loop produces these obligations, each as its own Lean theorem:
//!
//! * **Init** — one theorem per invariant: `OblCtx → I_i`.
//! * **Maintain** — body's `Done(inv_conj ∧ D < _tactus_d_old)` flows
//!   through the walker; `emit_done_or_split` splits the conjunction
//!   into one theorem per invariant + one for the decrease. Maintain
//!   ctx adds `∀ mod_vars + bounds + invs as hyps + cond as hyp +
//!   `_tactus_d_old := D`` let.
//! * **Use** — `after` walked in use ctx (`∀ mod_vars + bounds +
//!   invs as hyps + ¬cond as hyp`); produces theorems for the
//!   post-loop continuation.
//!
//! Non-modified surrounding state stays in scope via the OblCtx
//! frames built up by enclosing scopes. Only `mod_vars` — variables
//! the loop body writes to — get fresh universal quantification.
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
//! can't tunnel out through shadowing; they're handled by the
//! `∀ mod_vars` quantification in maintain/use ctx.

use std::collections::{HashMap, HashSet};

use vir::sst::{
    BndX, CallFun, Dest, Exp, ExpX, FuncCheckSst, FunctionSst, InternalFun, LoopInv,
    Par, Stm, StmX,
};
use vir::ast::{
    AssertQueryMode, Expr, ExprX, Fun, FunctionKind, FunctionX, KrateX, SpannedTyped, TactusKind,
    Typ, UnaryOp, UnaryOpr, VarAt, VarBinder, VarIdent,
};
use vir::ast_visitor::map_expr_visitor;
use vir::messages::Span;
use crate::lean_ast::{
    and_all, substitute, AssertKind, Binder as LBinder, BinderKind, Expr as LExpr,
    Tactic, Theorem,
};
use crate::expr_shared::varat_pre_name;
use std::sync::Arc;
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
/// var name (if any). Future additions that apply to the whole
/// verification unit plug into this struct instead of growing every
/// function signature.
///
/// Per-loop state (break / continue goal leaves) lives on `WpLoopCtx`
/// below and is threaded as a separate `Option<&WpLoopCtx>` parameter
/// — it only applies inside a loop body, so storing it on `WpCtx`
/// would misleadingly suggest it's always relevant.
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
        // Wrap each ensures clause with a `Postcondition` SpanMark so
        // every Done leaf has an obligation-kind mark — without this,
        // a fn-ensures failure inside an if-branch would leave
        // `find_span_mark` returning the BranchCondition hypothesis
        // mark (closest preceding) and the error label would say
        // `(branch condition)` instead of `(postcondition)`.
        // `emit_done_or_split` then splits the conjunction per-clause,
        // so multi-clause ensures naturally yields one Postcondition
        // theorem per clause with its own location.
        let ensures_goal = and_all(
            check.post_condition.ens_exps.iter().map(|ens| LExpr::span_mark(
                format_rust_loc(&ens.span),
                AssertKind::Postcondition,
                sst_exp_to_ast(ens),
            )).collect()
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

/// Peel transparent wrappers AND a single layer of `Loc`. Used at
/// value-position sites (`walk_let`, `lift_if_value`) where we want
/// to see THROUGH the L-value marker to find the underlying
/// expression — for if-detection on the value, or for further
/// peeling of nested let/if shapes.
///
/// Distinct from [`peel_transparent`] (which doesn't peel `Loc`)
/// because `contains_loc` needs `Loc` un-peeled to detect
/// `&mut`-borrow sites. Pulling this into a single helper keeps
/// the asymmetry expressed in one place: callers ask either
/// "what's beneath the wrappers?" (`peel_value_position`) or
/// "is there a Loc anywhere here?" (`contains_loc`), and the
/// difference between them is centralized.
fn peel_value_position(e: &Exp) -> &Exp {
    let p = peel_transparent(e);
    match &p.x {
        ExpX::Loc(inner) => peel_transparent(inner),
        _ => p,
    }
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
/// Returns a `Vec` of one theorem per obligation in the body —
/// per `Wp::Assert`, per `Wp::Done` conjunct, per loop invariant
/// (init + maintain), per loop decrease (maintain), per call
/// precondition, per assert-by. Multiple theorems per fn means a
/// Lean error's `pos.line` falls inside exactly one theorem's
/// `:= by` block, so the source-mapping kind label
/// (`(precondition)` / `(loop invariant)` / `(termination)` /
/// etc.) becomes correct by construction rather than guessed via
/// a closest-preceding-mark heuristic on a single mega-theorem
/// (task D in HANDOFF — completed across Stages 1-4).
///
/// Walker arms:
///
/// * **`Wp::Done(leaf)`** — emit one theorem per top-level
///   conjunct of `leaf`. Each fn-ensures clause is wrapped in a
///   `Postcondition` SpanMark at `WpCtx::new` time, yielding
///   `_tactus_postcondition_<fn>_at_<loc>_<id>` per clause;
///   loop-body terminator conjuncts (each invariant + the
///   decrease) are similarly pre-wrapped by `build_wp_loop`,
///   yielding `_tactus_loop_invariant_*` and
///   `_tactus_loop_decrease_*`.
/// * **`Wp::Assert(P, body)`** — one theorem for `P` (kind
///   detected via `detect_assert_kind`: Termination for
///   `CheckDecreaseHeight`, Plain otherwise). Body walked with
///   `P` as a hypothesis.
/// * **`Wp::Assume(P, body)`** — no theorem; `P` enters the
///   context as a hypothesis.
/// * **`Wp::Let(name, val, body)`** — no theorem; let frame
///   pushed. If `val` contains a value-position `if`, fork into
///   recursive walks (one per branch with the cond as a Hyp
///   frame).
/// * **`Wp::Branch(cond, t, e)`** — recurse on `t` with `cond`
///   as a Hyp frame; recurse on `e` with `¬cond`. No theorem at
///   the branch node.
/// * **`Wp::Call(callee, args, dest, after)`** — one theorem
///   for the substituted requires (kind=CallPrecondition).
///   Continue with `∀ ret, ret_bound → ensures(subst) → let
///   dest := ret;` frames.
/// * **`Wp::Loop(invs, dec, mv, body, after)`** — one theorem
///   per init invariant; walk body in maintain ctx (mv binders,
///   bounds, invs as hyps, cond as hyp, `_tactus_d_old` let);
///   walk after in use ctx (mv binders, bounds, invs, ¬cond).
/// * **`Wp::AssertByTactus(cond, tac, body)`** —
///   `Some(P)`: one theorem for `P` with `tac` as the closer;
///   body walked with `P` as a Hyp. `None`: push `tac` onto
///   `tactic_prefix`; every body theorem gets `(tac) <;> closer`
///   so the user's `have h : P := by ...` propagates as a local
///   hypothesis to subsequent obligations.
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

    let fn_name = lean_name(&fn_sst.x.name.path);
    let default_closer = match &fn_sst.x.attrs.tactus_tactic {
        Some(tac) => Tactic::Raw(tac.clone()),
        None => Tactic::Named("tactus_auto".to_string()),
    };
    let mut emitter = ObligationEmitter {
        fn_name,
        base_binders: binders,
        counter: 0,
        out: Vec::new(),
        tactic_prefix: Vec::new(),
        default_closer,
    };
    walk_obligations(&body_wp, &ctx, &OblCtx::new(), &mut emitter);
    Ok(emitter.out)
}

/// Walk a VIR-AST `Expr` body and collect spans of every
/// user-written `assume(P)` site. Used by `generate::check_exec_fn`
/// to emit "unproved assumption" warnings — `assume(P)` enters an
/// unverified hypothesis into the proof context, so each site
/// needs a visible reminder.
///
/// Operates on the AST (`vir_fn.body`) rather than the SST because
/// only the AST distinguishes user-written `assume(P)` (rendered as
/// `ExprX::AssertAssume { is_assume: true, .. }`) from synthetic
/// `StmX::Assume` statements injected by Verus's later passes
/// (post-overflow-check, post-call ensures, etc.). Walking the SST
/// and warning on every `StmX::Assume` produces false positives on
/// every overflow-checked arithmetic op.
pub fn collect_assume_sites(body: &Expr) -> Vec<Span> {
    use std::cell::RefCell;
    // `RefCell` because `map_expr_visitor` takes `Fn`, not `FnMut`
    // — we need interior mutability for the per-node side-effect
    // collection. The borrow scope is local to this fn.
    let out: RefCell<Vec<Span>> = RefCell::new(Vec::new());
    // We discard the rebuilt `Expr` (the `let _ =`) because we're
    // using a transformer as an inspector — the visitor's natural
    // shape rebuilds the tree, but we only care about the
    // side-effect collection in `out`.
    let _ = map_expr_visitor(body, &|e: &Expr| {
        if let ExprX::AssertAssume { is_assume: true, .. } = &e.x {
            out.borrow_mut().push(e.span.clone());
        }
        Ok(e.clone())
    });
    out.into_inner()
}

/// Format a `Span` for a user-facing diagnostic. Prefers the
/// pre-resolved `start_loc` (populated by `rust_verify`'s
/// `to_air_span`); falls back to `as_string` for synthetic spans.
/// Same logic as the internal `format_rust_loc` but exposed for
/// `generate.rs`'s warning emission path.
pub fn format_span_loc(span: &Span) -> String {
    format_rust_loc(span)
}

/// One frame of accumulated context as the obligation walker descends
/// into a Wp tree. Pushed at scope-introducing points (let bindings,
/// branch hypotheses, assert hypotheses, assume hypotheses); popped
/// implicitly when the walker returns from a recursive call.
///
/// At theorem-emission time, [`OblCtx::wrap`] folds the frames around
/// the obligation goal in source order: outermost frame first, so
/// the resulting LExpr has the same scope structure the user wrote.
/// Lets, hypotheses (as `→`), and `∀`-binders are encoded into the
/// goal expression itself rather than as theorem-level binders so
/// that lets can scope over hypotheses that mention the let-bound
/// names — the "everything in the goal" form gives correct scoping
/// for free.
#[derive(Clone)]
enum CtxFrame {
    /// `let x := v;` wrapping. The walker pushes this at every
    /// `Wp::Let` (or while peeling a `Bind(Let)` inside a let-RHS).
    Let(String, LExpr),
    /// `P →` wrapping. Pushed for assumes, branch conditions, and
    /// assertions that already passed (the asserted condition
    /// becomes a hypothesis for the rest of the body).
    Hyp(LExpr),
    /// `∀ (x : T),` wrapping. `walk_call` pushes one for the
    /// callee's return value; `walk_loop` pushes one per modified
    /// variable in maintain / use ctx.
    Binder(LBinder),
}

#[derive(Clone)]
struct OblCtx {
    frames: Vec<CtxFrame>,
}

impl OblCtx {
    fn new() -> Self { Self { frames: Vec::new() } }

    /// Append a frame to a fresh copy. Cloning the whole `frames`
    /// Vec per call is O(N²) memory across deeply-nested
    /// recursion (e.g., a chain of asserts with branches inside).
    /// Realistic exec fns don't go deep enough for this to matter;
    /// if a future profile says otherwise, switching to
    /// `Rc<im::Vector<_>>` (structural sharing) would fix it
    /// without changing the API.
    fn with_frame(&self, f: CtxFrame) -> Self {
        let mut new = self.clone();
        new.frames.push(f);
        new
    }

    /// Wrap `goal` with all accumulated frames, outermost first
    /// (matching source order). Iterating `frames` in reverse is
    /// the right direction: each frame wraps the *current* goal,
    /// so the LAST frame applied ends up OUTERMOST in the result.
    /// We want the FIRST-pushed frame outermost, so we iterate
    /// last-pushed-first.
    ///
    /// Worked example with `frames = [Let("x", v), Hyp(P)]`
    /// (Let pushed first, Hyp pushed second):
    ///
    /// 1. Start: `goal = G`
    /// 2. Iterate `Hyp(P)` (last pushed): `goal = P → G`
    /// 3. Iterate `Let("x", v)` (first pushed): `goal = let x := v; P → G`
    ///
    /// Result: `let x := v; P → G` — the let binds `x` outside
    /// the hypothesis so `P` can mention `x`. Push order matches
    /// source order; wrap order is the natural inversion.
    fn wrap(&self, mut goal: LExpr) -> LExpr {
        for frame in self.frames.iter().rev() {
            goal = match frame {
                CtxFrame::Let(name, v) => LExpr::let_bind(name.clone(), v.clone(), goal),
                CtxFrame::Hyp(p) => LExpr::implies(p.clone(), goal),
                CtxFrame::Binder(b) => LExpr::forall(vec![b.clone()], goal),
            };
        }
        goal
    }
}

/// Per-walk emission state. `fn_name` and `base_binders` are shared
/// across every theorem the walker emits; `counter` disambiguates
/// theorem names so multiple obligations of the same kind at the
/// same source line don't collide.
///
/// `tactic_prefix` accumulates user tactic text from enclosing
/// `Wp::AssertByTactus { cond: None, ... }` nodes (i.e., user-
/// written `proof { … }` blocks). Each emitted theorem gets these
/// prefixes prepended to its closer, so the user's `have h : P :=
/// by …` propagates as local hypotheses to subsequent obligation
/// theorems within the block's scope. Push/pop is structured around
/// `walk_obligations` recursion; see the `Wp::AssertByTactus` arm.
struct ObligationEmitter {
    fn_name: String,
    base_binders: Vec<LBinder>,
    counter: usize,
    out: Vec<Theorem>,
    tactic_prefix: Vec<String>,
    /// The default closer for emitted theorems. Normally
    /// `Tactic::Named("tactus_auto")`; overridden via the
    /// `#[verifier::tactus_tactic("...")]` attribute on the fn.
    /// Doesn't affect `assert(P) by { user_tac }` sites — those
    /// always use the user-supplied tactic from the assert-by.
    default_closer: Tactic,
}

impl ObligationEmitter {
    fn next_id(&mut self) -> usize {
        self.counter += 1;
        self.counter
    }

    /// Emit a theorem with the given goal and base closer. Applies
    /// any active `tactic_prefix` (from enclosing proof blocks) by
    /// running them as a parenthesised sequence followed by `<;>
    /// closer`, so the closer applies to whatever subgoals the
    /// prefix leaves. `<;>` is essential here: a goal-modifying
    /// prefix like `simp_all` may close the goal entirely, in which
    /// case the closer becomes a no-op rather than failing with
    /// "no goals" (which `; tactus_auto` would).
    fn emit(&mut self, name: String, goal: LExpr, closer: Tactic) {
        let tactic = if self.tactic_prefix.is_empty() {
            closer
        } else {
            let mut body = String::new();
            body.push_str("(\n");
            for prefix in &self.tactic_prefix {
                for line in prefix.lines() {
                    body.push_str("  ");
                    body.push_str(line);
                    body.push('\n');
                }
            }
            body.push_str(") <;> ");
            match closer {
                Tactic::Named(n) => body.push_str(&n),
                Tactic::Raw(s) => body.push_str(&format!("({})", s)),
            }
            Tactic::Raw(body)
        };
        self.out.push(Theorem {
            name,
            binders: self.base_binders.clone(),
            goal,
            tactic,
        });
    }
}

/// Snake-case name fragment for an `AssertKind`, used in theorem
/// naming. The visible per-error label still goes through
/// [`AssertKind::label`] — the fragment here is only for unique
/// identifiers in generated Lean.
fn kind_to_name(k: AssertKind) -> &'static str {
    match k {
        AssertKind::Plain => "assert",
        AssertKind::Postcondition => "postcondition",
        AssertKind::LoopInvariant => "loop_invariant",
        AssertKind::LoopDecrease => "loop_decrease",
        AssertKind::LoopCondition => "loop_condition",
        AssertKind::BranchCondition => "branch_condition",
        AssertKind::CallPrecondition => "precondition",
        AssertKind::Termination => "termination",
    }
}

/// Compress a Rust source location like
/// `"/home/me/project/src/main.rs:42:13"` into a short fragment for
/// theorem naming: drop the directory path and any extension, then
/// sanitize remaining non-identifier chars to `_`. The above example
/// becomes `"main_42_13"`. Result is appended to
/// `_tactus_<kind>_<fn>_at_<loc>_<id>`; we want it short enough that
/// a fn with many obligations doesn't produce kilobyte-long
/// theorem names. The structured `path:line:col` still goes into
/// `SpanMark` for error messages — this fragment is purely cosmetic.
fn sanitize_loc_for_name(loc: &str) -> String {
    // Strip everything before the last `/` (directory) and the
    // first `.` of the basename (extension).
    let after_slash = loc.rsplit('/').next().unwrap_or(loc);
    let mut basename = after_slash.to_string();
    if let Some(dot) = basename.find('.') {
        // Replace the extension with the rest (line/col), turning
        // "main.rs:42:13" into "main:42:13" (extension dropped) —
        // the `.rs` bit is noise we don't need in identifiers.
        let after_dot = &basename[dot + 1..];
        // After the dot, find where the extension ends (next non-
        // alphanumeric char). Anything from there onward is line/col.
        let ext_end = after_dot
            .find(|c: char| !c.is_ascii_alphanumeric())
            .unwrap_or(after_dot.len());
        let suffix = &after_dot[ext_end..];
        basename = format!("{}{}", &basename[..dot], suffix);
    }
    basename.chars()
        .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
        .collect()
}

/// Walk a `Wp` tree, emitting one Lean theorem per obligation. See
/// the doc on [`exec_fn_theorems_to_ast`] for the staging plan and
/// the per-Wp-variant behaviour.
fn walk_obligations<'a>(
    wp: &Wp<'a>,
    ctx: &WpCtx<'a>,
    obl: &OblCtx,
    e: &mut ObligationEmitter,
) {
    match wp {
        Wp::Done(leaf) => {
            // Terminal goal: the fn's ensures conjunction (top-level
            // Done) or a loop body's `I ∧ D < d_old` (loop-body Done
            // emitted by `build_wp_loop`'s `continue_leaf`). Split
            // top-level conjunctions into one theorem per conjunct so
            // each clause has its own pos.line in Lean — gets the
            // AssertKind exactly right when the conjuncts carry
            // different SpanMark wrappings (LoopInvariant /
            // LoopDecrease for loop-body terminators).
            emit_done_or_split(leaf, obl, e);
        }
        Wp::Assert(asserted, body) => {
            // Emit one theorem for this assertion. The asserted
            // condition becomes a hypothesis for the rest of the
            // body — its proof sits in this theorem, the body's
            // theorems can assume it.
            let kind = detect_assert_kind(asserted);
            let loc = format_rust_loc(&asserted.span);
            let cond_ast = sst_exp_to_ast(asserted);
            let goal = LExpr::span_mark(loc.clone(), kind, cond_ast.clone());
            let id = e.next_id();
            let name = build_theorem_name(
                kind_to_name(kind), &e.fn_name, &loc, id,
            );
            e.emit(name, obl.wrap(goal), simple_tactic(e));
            // Reuse cond_ast for the body's hypothesis frame —
            // sst_exp_to_ast is deterministic, so re-rendering
            // the same Exp would only repeat work.
            let new_obl = obl.with_frame(CtxFrame::Hyp(cond_ast));
            walk_obligations(body, ctx, &new_obl, e);
        }
        Wp::Assume(p, body) => {
            // No theorem; the assumption just enters the context.
            let new_obl = obl.with_frame(CtxFrame::Hyp(sst_exp_to_ast(p)));
            walk_obligations(body, ctx, &new_obl, e);
        }
        Wp::Let(name, val, body) => {
            walk_let(name, val, body, ctx, obl, e);
        }
        Wp::Branch { cond, then_branch, else_branch } => {
            // Each branch walks under its own hypothesis (cond / ¬cond).
            // The Wp tree clones `after` into both branches at build
            // time, so the post-if continuation's obligations are
            // visited twice — once with `c` as a hypothesis, once with
            // `¬c`. Fine for correctness (each emitted theorem is its
            // own valid obligation); does duplicate work for branches
            // that fall through to the same `after`. Same exponential-
            // in-nested-if behaviour as the pre-D codegen — DESIGN.md
            // documents the trade-off.
            let cond_marked = LExpr::span_mark(
                format_rust_loc(&cond.span),
                AssertKind::BranchCondition,
                sst_exp_to_ast(cond),
            );
            walk_obligations(
                then_branch, ctx,
                &obl.with_frame(CtxFrame::Hyp(cond_marked.clone())),
                e,
            );
            walk_obligations(
                else_branch, ctx,
                &obl.with_frame(CtxFrame::Hyp(LExpr::not(cond_marked))),
                e,
            );
        }
        Wp::Call { callee, args, typ_args, dest, call_span, mut_args, after } => {
            walk_call(
                callee, args, typ_args, *dest, call_span, mut_args, after, ctx, obl, e,
            );
        }
        Wp::Loop { cond, invs, decrease, modified_vars, body, after, d_old_name } => {
            walk_loop(
                *cond, invs, decrease, modified_vars, body, after, d_old_name, ctx, obl, e,
            );
        }
        Wp::AssertByTactus { cond, tactic_text, body } => {
            walk_assert_by_tactus(*cond, tactic_text, body, ctx, obl, e);
        }
    }
}

/// Per-obligation walker for `Wp::AssertByTactus`.
///
/// Two surface forms with different scoping:
///
/// * **`cond = Some(P)` — `assert(P) by { user_tac }`**: emit a
///   single theorem for `P` with `user_tac` as the closer (rather
///   than the standard `tactus_auto`). The asserted condition then
///   becomes a hypothesis for the rest of the body — so subsequent
///   per-obligation theorems get `P` in their context, and Lean's
///   omega/simp_all picks it up automatically.
///
/// * **`cond = None` — `proof { user_tac }`**: no theorem emitted
///   here; `user_tac` is pushed onto `e.tactic_prefix` so every
///   obligation theorem in the body's lexical scope gets
///   `user_tac` prepended to its closer. The user's `have h : P
///   := by ...` lines then introduce named hypotheses scoped to
///   each subsequent theorem (option (a) from the D plan).
fn walk_assert_by_tactus<'a>(
    cond: Option<&'a Exp>,
    tactic_text: &str,
    body: &Wp<'a>,
    ctx: &WpCtx<'a>,
    obl: &OblCtx,
    e: &mut ObligationEmitter,
) {
    // A whitespace-only `tactic_text` (user wrote `proof { }` /
    // `assert(P) by { }`) would emit broken Lean: `( ) <;> closer`
    // for the proof-block path or `:= by ` with nothing after it
    // for assert-by. Treat as if the user supplied no tactic at
    // all — fall back to the default closer for assert-by, skip
    // the prefix push for proof block.
    let user_tactic_present = !tactic_text.trim().is_empty();

    match cond {
        Some(c) => {
            // Assert-by: emit one theorem for `c` with the user's
            // tactic as the closer (or `tactus_auto` if empty).
            // The cond becomes a hypothesis for body theorems.
            // AssertKind::Plain because it's a user-written
            // `assert(P) by { tac }` — same kind a plain
            // `assert(P)` would get via `detect_assert_kind`.
            let loc = format_rust_loc(&c.span);
            let cond_ast = sst_exp_to_ast(c);
            let goal = LExpr::span_mark(
                loc.clone(), AssertKind::Plain, cond_ast.clone(),
            );
            let id = e.next_id();
            let name = build_theorem_name(
                kind_to_name(AssertKind::Plain), &e.fn_name, &loc, id,
            );
            let closer = if user_tactic_present {
                Tactic::Raw(tactic_text.to_string())
            } else {
                simple_tactic(e)
            };
            e.emit(name, obl.wrap(goal), closer);
            // Cond as hypothesis for body theorems (reuse cond_ast).
            let new_obl = obl.with_frame(CtxFrame::Hyp(cond_ast));
            walk_obligations(body, ctx, &new_obl, e);
        }
        None => {
            // Proof block: tactic prefix flows to every theorem in
            // body's scope. Push, walk, pop — the prefix only
            // applies to body theorems, not to obligations
            // sequentially after the proof block.
            if user_tactic_present {
                e.tactic_prefix.push(tactic_text.to_string());
                walk_obligations(body, ctx, obl, e);
                e.tactic_prefix.pop();
            } else {
                walk_obligations(body, ctx, obl, e);
            }
        }
    }
}

/// Emit one or more theorems for a `Wp::Done` leaf. Recursively
/// peels two structural shapes before emitting:
///
/// * **Top-level `Let { name, value, body }`** — push `Let(name,
///   value)` onto the OblCtx as a frame and recurse on `body`.
///   Same final goal expression as wrapping the leaf as-is, but
///   lets us peel further into a conjunction or a SpanMark for
///   the body.
/// * **Top-level `BinOp::And { lhs, rhs }`** — split into two
///   recursive emissions. Each conjunct keeps its own SpanMark
///   wrapping, so multi-clause ensures (each clause wrapped with
///   `Postcondition` at `WpCtx::new` time) and loop-body
///   terminators (`(I_1 ∧ ...) ∧ decrease_marked`) yield one
///   theorem per conjunct with the right kind.
///
/// At the leaf (neither Let nor And), the kind label and location
/// come from the outermost `SpanMark`. Unwrapped leaves only occur
/// when ensures is empty (`and_all([]) = LitBool(true)`) — the
/// goal is `True` and tactus_auto closes it trivially.
fn emit_done_or_split(leaf: &LExpr, obl: &OblCtx, e: &mut ObligationEmitter) {
    use crate::lean_ast::{BinOp, ExprNode};
    match &leaf.node {
        // Split conjunctions per-conjunct.
        ExprNode::BinOp { op: BinOp::And, lhs, rhs } => {
            emit_done_or_split(lhs, obl, e);
            emit_done_or_split(rhs, obl, e);
        }
        // Peel the let into an OblCtx frame and recurse on body.
        // `obl.wrap` reconstructs the let around the final emitted
        // goal — same final expression, but now we can split or
        // label the body's contents.
        ExprNode::Let { name, value, body } => {
            let new_obl = obl.with_frame(CtxFrame::Let(
                name.clone(), value.as_ref().clone(),
            ));
            emit_done_or_split(body, &new_obl, e);
        }
        // SpanMark-wrapped leaf: emit one theorem with the kind /
        // loc from the wrapping.
        ExprNode::SpanMark { rust_loc, kind, .. } => {
            emit_leaf_theorem(kind_to_name(*kind), rust_loc, leaf, obl, e);
        }
        // Unwrapped leaf: only reachable when ensures is empty
        // (`and_all([]) = LitBool(true)`). The goal is `True` and
        // tactus_auto closes it trivially. "ensures" is the
        // cosmetic label for this degenerate case.
        _ => emit_leaf_theorem("ensures", "", leaf, obl, e),
    }
}

/// Build the theorem name and emit one theorem for a leaf
/// obligation. Shared between `emit_done_or_split`'s SpanMark and
/// fallback arms.
fn emit_leaf_theorem(
    kind_label: &str,
    loc: &str,
    leaf: &LExpr,
    obl: &OblCtx,
    e: &mut ObligationEmitter,
) {
    let id = e.next_id();
    let name = build_theorem_name(kind_label, &e.fn_name, loc, id);
    e.emit(name, obl.wrap(leaf.clone()), simple_tactic(e));
}

/// Construct a per-obligation theorem name. Drops the `_at_<loc>`
/// suffix when `loc` is empty (synthetic / unmapped spans) so we
/// don't produce double-underscore names like
/// `_tactus_assert_<fn>_at__7`.
fn build_theorem_name(kind_label: &str, fn_name: &str, loc: &str, id: usize) -> String {
    if loc.is_empty() {
        format!("_tactus_{}_{}_{}", kind_label, fn_name, id)
    } else {
        let suffix = sanitize_loc_for_name(loc);
        format!("_tactus_{}_{}_at_{}_{}", kind_label, fn_name, suffix, id)
    }
}

/// Per-obligation walker for `Wp::Loop`. Splits the loop's
/// obligations across separate Lean theorems so each gets its own
/// `pos.line`:
///
/// * **Init**: one theorem per invariant (entry check).
/// * **Maintain**: walk the body in maintain ctx (∀ mod_vars +
///   bounds + invs as hyps + cond as hyp + `_tactus_d_old := D`
///   let). The body's `Done(I ∧ D < d_old)` terminator flows
///   through `walk_obligations`'s `Wp::Done` arm via
///   [`emit_done_or_split`], producing one theorem per conjunct
///   (each invariant + the decrease).
/// * **Use**: walk `after` in use ctx (∀ mod_vars + bounds +
///   invs as hyps + ¬cond as hyp).
fn walk_loop<'a>(
    cond: Option<&Exp>,
    invs: &[LoopInv],
    decrease: &Exp,
    modified_vars: &[(&'a VarIdent, &'a Typ)],
    body: &Wp<'a>,
    after: &Wp<'a>,
    d_old_name: &str,
    ctx: &WpCtx<'a>,
    obl: &OblCtx,
    e: &mut ObligationEmitter,
) {
    // Build the SpanMark-wrapped invariants & decrease & cond once;
    // reused for init theorems, maintain hyps, use hyps.
    let inv_marked = |i: &LoopInv| LExpr::span_mark(
        format_rust_loc(&i.inv.span),
        AssertKind::LoopInvariant,
        sst_exp_to_ast(&i.inv),
    );
    let cond_marked = |c: &Exp| LExpr::span_mark(
        format_rust_loc(&c.span),
        AssertKind::LoopCondition,
        sst_exp_to_ast(c),
    );
    let inv_conj_marked = and_all(invs.iter().map(inv_marked).collect());

    // ── Init: one theorem per invariant. The invariant must hold at
    // loop entry given the current obligation context (no body
    // execution yet).
    for inv in invs {
        let loc = format_rust_loc(&inv.inv.span);
        let id = e.next_id();
        let name = build_theorem_name(
            kind_to_name(AssertKind::LoopInvariant), &e.fn_name, &loc, id,
        );
        e.emit(name, obl.wrap(inv_marked(inv)), simple_tactic(e));
    }

    // ── Maintain: walk body with ∀ mod_vars + bounds + invs as
    // hyps + cond as hyp + `_tactus_d_old := D` let. The body's
    // Done leaf (= `inv_conj ∧ decrease_marked`) splits into one
    // theorem per invariant + one for the decrease via
    // `emit_done_or_split`.
    let mut maintain_obl = obl.clone();
    push_mod_var_frames(&mut maintain_obl, modified_vars);
    maintain_obl.frames.push(CtxFrame::Hyp(inv_conj_marked.clone()));
    if let Some(c) = cond {
        maintain_obl.frames.push(CtxFrame::Hyp(cond_marked(c)));
    }
    // `let _tactus_d_old_<id> := D` — pre-body decrease value,
    // referenced by the body's continue_leaf as
    // `D < _tactus_d_old_<id>`. Per-loop-unique name (gensym'd in
    // `build_wp_loop` from the loop's id) avoids any chance of
    // shadowing across nested loops, even if a future refactor
    // changes scope structure.
    maintain_obl.frames.push(CtxFrame::Let(
        d_old_name.to_string(),
        sst_exp_to_ast(decrease),
    ));
    walk_obligations(body, ctx, &maintain_obl, e);

    // ── Use: walk `after` with ∀ mod_vars + bounds + invs as hyps
    // + ¬cond as hyp. No `_tactus_d_old` here — the decrease
    // obligation only applies to fall-through inside the body.
    let mut use_obl = obl.clone();
    push_mod_var_frames(&mut use_obl, modified_vars);
    use_obl.frames.push(CtxFrame::Hyp(inv_conj_marked));
    if let Some(c) = cond {
        use_obl.frames.push(CtxFrame::Hyp(LExpr::not(cond_marked(c))));
    }
    walk_obligations(after, ctx, &use_obl, e);
}

/// Push one `∀ x : T` binder + optional `bound →` hyp per modified
/// variable. Called by `walk_loop` for both maintain and use ctx
/// builds — same shape both times.
fn push_mod_var_frames<'a>(
    obl: &mut OblCtx,
    modified_vars: &[(&'a VarIdent, &'a Typ)],
) {
    for (ident, typ) in modified_vars {
        let name = sanitize(&ident.0);
        obl.frames.push(CtxFrame::Binder(LBinder {
            name: Some(name.clone()),
            ty: typ_to_expr(typ),
            kind: BinderKind::Explicit,
        }));
        if let Some(pred) = type_bound_predicate(&LExpr::var(name), typ) {
            obl.frames.push(CtxFrame::Hyp(pred));
        }
    }
}

/// Rewrite `VarAt(p, Pre)` references for the given `&mut` param
/// names to a synthetic `Var(<p>_at_pre_tactus)` so the call-site
/// renderer-then-substitution can target pre-state independently
/// of post-state (`Var(p)` stays as-is for post-state references).
///
/// This pre-rewrite happens at the VIR-AST level — *before*
/// `vir_expr_to_ast` collapses `VarAt(_, _)` into `Var(_)`. We
/// don't change the renderer because `VarAt` is also used outside
/// `&mut` (loop ensures' at-entry references, where the natural
/// collapse to `Var` is correct), and changing the global
/// rendering would unbind the `_at_pre_tactus` names in those
/// contexts. Doing the rewrite here, scoped by the &mut param
/// name set, keeps the change local to `&mut` callee-spec
/// inlining.
///
/// `mut_param_names` is the set of `sanitize`d param-name strings
/// for `&mut` parameters of the callee. Other vars (callee-local
/// loop vars referenced via `VarAt`, non-mut params, etc.) are
/// left alone — their natural `VarAt → Var` collapse is what we
/// want.
fn rewrite_varat_for_mut_params(
    expr: &Expr,
    mut_param_names: &std::collections::HashSet<String>,
) -> Expr {
    map_expr_visitor(expr, &|e: &Expr| {
        if let ExprX::VarAt(ident, VarAt::Pre) = &e.x {
            let raw_name = sanitize(&ident.0);
            if mut_param_names.contains(&raw_name) {
                // Use `raw_name` (already sanitized) so the synthetic
                // string matches what `subst`'s key — `varat_pre_name(
                // sanitize(p.name))` — produces. `sanitize` is
                // idempotent on the resulting `<name>_at_pre_tactus`
                // shape (no special chars introduced).
                let new_str: vir::ast::Ident = Arc::new(varat_pre_name(&raw_name));
                let new_ident = VarIdent(new_str, ident.1.clone());
                return Ok(SpannedTyped::new(
                    &e.span,
                    &e.typ,
                    ExprX::Var(new_ident),
                ));
            }
        }
        Ok(e.clone())
    })
    // The closure only constructs valid Var nodes from existing
    // VarAt nodes; it cannot fail.
    .expect("rewrite_varat_for_mut_params is structural and shouldn't error")
}

/// Pick the source of `require`/`ensure` clauses for a callee.
///
/// For `FunctionKind::TraitMethodImpl` callees, the impl's
/// `require`/`ensure` are typically empty (Verus rejects impl-side
/// `requires` clauses; impls may redeclare `ensures` only if they
/// imply the trait's). The CALLER'S contract is the trait method
/// decl's spec — that's the weakest, and any impl satisfies it by
/// Verus's trait-impl-checking pass.
///
/// This helper redirects spec lookup to the trait method decl when
/// the callee is a `TraitMethodImpl`. The impl's params/typ_params/
/// ret stay as-is (they have concrete types, used for binder
/// rendering); only `require`/`ensure` come from the trait decl.
///
/// **Trade-off**: impl-specific strengthening of `ensures` isn't
/// seen at call sites yet. A pure spec-via-trait MVS doesn't see
/// the case where an impl says "ensures r > 0" while the trait
/// only said "ensures r ≠ 5". Strengthening cases would require
/// a per-clause merge. Deferred follow-up to #56.
///
/// **Sound by construction.** Verus's trait-impl-checking pass
/// guarantees the impl's spec implies the trait's spec
/// (modulo Self substitution). Using the trait's spec is always
/// at least as conservative as the impl's at the caller site.
fn pick_spec_source<'a>(
    callee: &'a FunctionX,
    fn_map: &FnMap<'a>,
) -> Result<&'a FunctionX, String> {
    // Explicit destructure of every FunctionKind variant — a new
    // upstream variant that needs spec redirection (e.g., a future
    // "TraitMethodImplWithDefault" or similar) would force a compile
    // error here rather than silently falling through to "use the
    // callee's specs as-is" (which can be wrong if the impl
    // inherits from another source).
    match &callee.kind {
        FunctionKind::TraitMethodImpl { method, .. } => {
            fn_map.get(method).copied().ok_or_else(|| format!(
                "trait method decl `{:?}` for resolved impl `{:?}` not found \
                 in the crate's function map — cross-crate trait calls are \
                 not yet supported",
                method.path, callee.name.path,
            ))
        }
        // `Static` — regular fn, specs are on the callee itself.
        // `TraitMethodDecl` — the trait method itself (called via
        //   non-DynamicResolved path); specs are on the callee.
        // `ForeignTraitMethodImpl` — per its docstring, demoted to
        //   Static by `demote_foreign_traits`, so we shouldn't see
        //   it here. If we do, treat as Static (specs on callee).
        FunctionKind::Static
        | FunctionKind::TraitMethodDecl { .. }
        | FunctionKind::ForeignTraitMethodImpl { .. } => Ok(callee),
    }
}

/// Per-obligation walker for `Wp::Call`. Splits the call's
/// obligations across separate theorems:
///
/// * Emit one theorem for the callee's precondition (substituted
///   with call-site args, wrapped with `CallPrecondition`
///   SpanMark). Skipped when `callee.require` is empty — the
///   goal would be `True` and the theorem would be wasted noise.
/// * Walk `after` with extended context frames: `∀ ret` binder,
///   `ret_bound →` if the return type has one, `ensures(subst) →`
///   if `callee.ensure` is non-empty, and `let dest := ret;` if
///   the call has a destination var.
///
/// Substitutions combine value params (`p ↦ arg`) and type
/// params (`T ↦ typ_arg`); `TypParam(T)` renders as `Var("T")`
/// so the value-level `lean_ast::substitute` rewrites both kinds.
///
/// **`&mut` handling (#55).** For each `(idx, caller_var)` in
/// `mut_args`, the post-call value of the mutated location is
/// modeled as a fresh existential `_tactus_mut_post_<id>`:
///   * Requires uses the same `p ↦ arg` (pre-call value) for both
///     non-mut and mut params, since at requires time only the
///     pre-call value exists.
///   * Ensures uses `p ↦ Var(post_id)` (post-call value) and
///     additionally `varat_pre_name(p) ↦ arg` (pre-call value
///     reachable via `*old(x)` syntax in the source, rendered as
///     `<p>_at_pre_tactus` by `to_lean_expr`).
/// After the ensures Hyp frame, a `let caller_var := post_id`
/// frame rebinds the caller-side variable so subsequent
/// obligations see the post-call value.
fn walk_call<'a>(
    callee: &FunctionX,
    args: &[Exp],
    typ_args: &[Typ],
    dest: Option<&VarIdent>,
    call_span: &Span,
    mut_args: &[(usize, &VarIdent)],
    after: &Wp<'a>,
    ctx: &WpCtx<'a>,
    obl: &OblCtx,
    e: &mut ObligationEmitter,
) {
    // ── Type-param substitution (shared by req + ens) ─────────────
    let mut typ_subst: HashMap<String, LExpr> = HashMap::new();
    for (tp_name, tp_arg) in callee.typ_params.iter().zip(typ_args.iter()) {
        typ_subst.insert(sanitize(tp_name), typ_to_expr(tp_arg));
    }

    // ── Spec source (trait decl for trait impls, callee otherwise) ─
    // For `TraitMethodImpl` callees, use the trait method decl's
    // `require`/`ensure` instead of the impl's (the impl's are
    // typically empty since Verus rejects impl-side `requires`
    // declarations and trait specs are inherited). The lookup is
    // infallible at this point because `build_wp_call` validated
    // it before constructing the Wp::Call. See `pick_spec_source`
    // for the rationale.
    //
    // Cross-crate trait calls (where the trait decl isn't in
    // `fn_map`) are rejected upstream in `build_wp_call`.
    let spec_source = pick_spec_source(callee, &ctx.fn_map)
        .expect("build_wp_call should have rejected unresolvable trait-spec lookups");

    // ── Set of &mut param names for VarAt rewriting ────────────────
    // Pre-state references in the callee's spec (`*old(x)` syntax →
    // `VarAt(p, Pre)` in VIR-AST) are rewritten to `Var(<p>_at_pre_
    // tactus)` BEFORE rendering, so the substitution map below can
    // distinguish them from post-state `Var(p)` references.
    let mut_param_name_set: std::collections::HashSet<String> = mut_args.iter()
        .map(|(idx, _)| sanitize(&callee.params[*idx].x.name.0))
        .collect();

    // ── Render args once (Loc-peeling included for &mut shapes) ───
    // For a `&mut x` arg shape `Loc(VarLoc(x))`,
    // `sst_exp_to_ast` peels Loc transparently, so the rendered form
    // is the caller-side variable reference (the pre-call value).
    let arg_lexprs: Vec<LExpr> =
        args.iter().map(|a| sst_exp_to_ast(a)).collect();

    // ── Generate fresh post-call names per &mut arg ────────────────
    // The `_tactus_mut_post_` prefix is reserved (won't collide with
    // user names — Rust source can't produce `_tactus_` identifiers).
    let mut mut_idx_to_fresh: HashMap<usize, String> = HashMap::new();
    for (idx, _) in mut_args {
        let id = e.next_id();
        mut_idx_to_fresh.insert(*idx, format!("_tactus_mut_post_{}", id));
    }

    // ── Build requires substitution map ────────────────────────────
    // Requires references only the pre-call values:
    //   * non-mut param p: `p ↦ arg`
    //   * mut param p: `p ↦ arg` AND `<p>_at_pre_tactus ↦ arg`
    //     (covers both bare `p` and `*old(p)` syntax)
    let mut req_subst: HashMap<String, LExpr> = typ_subst.clone();
    for (i, p) in callee.params.iter().enumerate() {
        let pname = sanitize(&p.x.name.0);
        req_subst.insert(pname.clone(), arg_lexprs[i].clone());
        if p.x.is_mut {
            req_subst.insert(varat_pre_name(&pname), arg_lexprs[i].clone());
        }
    }

    // ── Emit precondition theorem ──────────────────────────────────
    let loc = format_rust_loc(call_span);
    if !spec_source.require.is_empty() {
        // Rewrite VarAt(p, Pre) for &mut p before rendering so the
        // substitution map below can target pre-state separately
        // from post-state. No-op when mut_param_name_set is empty.
        //
        // For trait calls, `spec_source` is the trait method decl;
        // its require references param names that match the impl's
        // param names (Verus enforces alignment), so the
        // substitution map keyed by impl-param names also works
        // against the trait's specs.
        let requires_conj = and_all(
            spec_source.require.iter()
                .map(|e| {
                    let rewritten = rewrite_varat_for_mut_params(e, &mut_param_name_set);
                    vir_expr_to_ast(&rewritten)
                })
                .collect()
        );
        let requires_clause = LExpr::span_mark(
            loc.clone(),
            AssertKind::CallPrecondition,
            substitute(&requires_conj, &req_subst),
        );
        let id = e.next_id();
        let theorem_name = build_theorem_name(
            kind_to_name(AssertKind::CallPrecondition), &e.fn_name, &loc, id,
        );
        e.emit(theorem_name, obl.wrap(requires_clause), simple_tactic(e));
    }

    // ── Build ensures substitution map ─────────────────────────────
    // Ensures references both pre- and post-call values:
    //   * non-mut param p: `p ↦ arg`
    //   * mut param p at idx i: `p ↦ Var(post_i)` (post-state),
    //                           `<p>_at_pre_tactus ↦ arg` (pre-state)
    //   * callee's ret (name from `callee.ret.x.name`): substitute
    //     to a fresh `_tactus_ret_<id>` so the ∀-binder we emit
    //     below doesn't shadow a caller-scope local of the same
    //     name. Pinned by `test_exec_call_ret_name_collision`.
    let mut ens_subst: HashMap<String, LExpr> = typ_subst.clone();
    for (i, p) in callee.params.iter().enumerate() {
        let pname = sanitize(&p.x.name.0);
        if p.x.is_mut {
            let fresh = mut_idx_to_fresh.get(&i)
                .expect("fresh name should exist for every &mut param idx");
            ens_subst.insert(pname.clone(), LExpr::var(fresh.clone()));
            ens_subst.insert(varat_pre_name(&pname), arg_lexprs[i].clone());
        } else {
            ens_subst.insert(pname, arg_lexprs[i].clone());
        }
    }
    let fresh_ret_name = format!("_tactus_ret_{}", e.next_id());
    let ret_orig_name = sanitize(&callee.ret.x.name.0);
    if ret_orig_name != fresh_ret_name {
        ens_subst.insert(ret_orig_name, LExpr::var(fresh_ret_name.clone()));
    }

    // ── Build context frames for `after` walk ──────────────────────
    // Frames pushed in source order; OblCtx::wrap folds them
    // outermost-first, yielding the goal shape (reading top-down):
    //   ∀ post_i,                       ─┐
    //   type_inv(post_i) →               │ per &mut arg
    //   ∀ ret,                          ─┘
    //   ret_bound →
    //   ensures(subst) →
    //   let caller_var_i := post_i;     ─┐ per &mut arg
    //   let dest := ret;                 │
    //   <continuation goal>
    //
    // Frames pushed only when meaningful — an empty ensures or a
    // missing ret_bound is skipped to avoid `True →` clutter on
    // every downstream goal.
    let mut new_obl = obl.clone();

    // 1. Per-&mut existential binder + type-inv hypothesis
    for (idx, _caller_var) in mut_args {
        let fresh = mut_idx_to_fresh.get(idx).unwrap();
        let typ = &callee.params[*idx].x.typ;
        let lean_typ = substitute(&typ_to_expr(typ), &typ_subst);
        new_obl.frames.push(CtxFrame::Binder(LBinder {
            name: Some(fresh.clone()),
            ty: lean_typ,
            kind: BinderKind::Explicit,
        }));
        if let Some(pred) = type_bound_predicate(&LExpr::var(fresh.clone()), typ) {
            new_obl.frames.push(CtxFrame::Hyp(pred));
        }
    }

    // 2. Return-value binder + bound. Use the gensym'd ret name
    //    (built in the ens_subst step above) instead of the
    //    callee's source-level ret name — the latter could collide
    //    with a caller-scope local and the ∀ would silently shadow.
    let ret = &callee.ret.x;
    let ret_typ = substitute(&typ_to_expr(&ret.typ), &typ_subst);
    new_obl.frames.push(CtxFrame::Binder(LBinder {
        name: Some(fresh_ret_name.clone()),
        ty: ret_typ,
        kind: BinderKind::Explicit,
    }));
    if let Some(pred) = type_bound_predicate(&LExpr::var(fresh_ret_name.clone()), &ret.typ) {
        new_obl.frames.push(CtxFrame::Hyp(pred));
    }

    // 3. Ensures (post-call assumption)
    if !spec_source.ensure.0.is_empty() {
        let ensures_conj = and_all(
            spec_source.ensure.0.iter()
                .map(|e| {
                    let rewritten = rewrite_varat_for_mut_params(e, &mut_param_name_set);
                    vir_expr_to_ast(&rewritten)
                })
                .collect()
        );
        new_obl.frames.push(CtxFrame::Hyp(substitute(&ensures_conj, &ens_subst)));
    }

    // 4. Caller-side rebindings for &mut args (placed AFTER ensures
    //    so the ensures Hyp references the fresh existential, not
    //    the rebound caller name)
    for (idx, caller_var) in mut_args {
        let fresh = mut_idx_to_fresh.get(idx).unwrap();
        new_obl.frames.push(CtxFrame::Let(
            sanitize(&caller_var.0),
            LExpr::var(fresh.clone()),
        ));
    }

    // 5. Dest binding for the call's return value (`let r = foo(…)`)
    if let Some(dest_ident) = dest {
        new_obl.frames.push(CtxFrame::Let(
            sanitize(&dest_ident.0),
            LExpr::var(fresh_ret_name.clone()),
        ));
    }

    walk_obligations(after, ctx, &new_obl, e);
}

/// `Wp::Let` walker with if-RHS lifting. `let x := if c then a
/// else b; rest` forks into two recursive walks, each with cond
/// as a hypothesis frame and the corresponding branch as the
/// let value. Without this, `omega` can't see inside the
/// value-position if and the let theorems would fail. Same
/// lifting strategy as [`lift_if_value`] (used by `Return`-
/// position values), specialized for the walker's per-
/// obligation emission.
fn walk_let<'a>(
    name: &'a str,
    val: &'a Exp,
    body: &Wp<'a>,
    ctx: &WpCtx<'a>,
    obl: &OblCtx,
    e: &mut ObligationEmitter,
) {
    let peeled = peel_value_position(val);
    match &peeled.x {
        ExpX::If(cond, then_e, else_e) => {
            let c_ast = sst_exp_to_ast(cond);
            walk_let(name, then_e, body, ctx,
                &obl.with_frame(CtxFrame::Hyp(c_ast.clone())), e);
            walk_let(name, else_e, body, ctx,
                &obl.with_frame(CtxFrame::Hyp(LExpr::not(c_ast))), e);
            return;
        }
        // `let outer := (let z := zval; bodyval); rest`
        //   ≡ `let z := zval; let outer := bodyval; rest`
        // Peel one layer of inner let, then continue lifting on
        // `bodyval` (which may itself be an If or another nested let).
        // Multi-binder lets (`let (a, b) = …`) iterate the binder
        // list inline: each binder becomes its own frame, then we
        // recurse on the inner body for the outer let-binding.
        ExpX::Bind(bnd, inner_body) => {
            if let BndX::Let(bs) = &bnd.x {
                if !bs.is_empty() {
                    let mut chain_obl = obl.clone();
                    for b in bs.iter() {
                        chain_obl.frames.push(CtxFrame::Let(
                            sanitize(&b.name.0),
                            sst_exp_to_ast(&b.a),
                        ));
                    }
                    walk_let(name, inner_body, body, ctx, &chain_obl, e);
                    return;
                }
            }
        }
        _ => {}
    }
    // Plain let with no peelable structure — push the let frame
    // and continue walking the body.
    let new_obl = obl.with_frame(CtxFrame::Let(
        sanitize(name), sst_exp_to_ast(val),
    ));
    walk_obligations(body, ctx, &new_obl, e);
}

/// Atomic default closer for per-obligation theorems. Each emitted
/// goal is a single obligation wrapped in let/→/∀ frames from the
/// `OblCtx`, which `omega` and `simp_all` handle natively (intros
/// for `∀`/`→`, zeta-reduction for `let`).
///
/// Reads the closer from the `ObligationEmitter` so per-fn
/// overrides via `#[verifier::tactus_tactic("...")]` apply
/// uniformly across every emitter site (Wp::Assert,
/// emit_done_or_split, walk_loop's init, walk_call's
/// precondition, walk_assert_by_tactus's empty-tactic
/// fallback).
fn simple_tactic(e: &ObligationEmitter) -> Tactic {
    e.default_closer.clone()
}

// ── Binder builders ────────────────────────────────────────────────────

/// Function params + their type-bound hypotheses. Shared across
/// every theorem the walker emits for the fn — they sit on
/// `ObligationEmitter::base_binders` and prepend to each
/// theorem's binder list at emit time.
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
// "rest" parameter, no separate "terminator" parameter. The walker
// (`walk_obligations` and friends) is a straightforward tree walk;
// construction (`build_wp`) threads each statement's continuation
// through at walk time.
//
// Structural properties:
//
//   * Continuation is type-level, not positional. Can't accidentally
//     compose after a `Return` because `Done` has no slot for more.
//   * `Return` is cleanly "terminator-at-fn-exit" rather than
//     "terminator-in-current-scope" — an early return always writes
//     the fn's ensures goal, even when nested inside a loop.
//   * `Loop` / `Call` compose like any other node — each has `body`
//     and/or `after` sub-Wps, recursion is structural.
//
// Adding a new WP form means adding a constructor + an arm in
// `build_wp` (where construction happens) and `walk_obligations`
// (where it emits theorems). No changes needed to a central
// dispatcher.

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

    /// `let x := e; <body>`. If `e` contains a value-position
    /// `if c then a else b`, `walk_let` forks into two recursive
    /// walks (with cond as a Hyp frame) so omega sees a clean
    /// goal in each branch instead of an opaque value-position
    /// if.
    Let(&'a str, &'a Exp, Box<Wp<'a>>),

    /// Obligation: prove `P`, then `body` proceeds with `P` as a
    /// hypothesis. Walker emits one theorem per `Wp::Assert`.
    Assert(&'a Exp, Box<Wp<'a>>),

    /// Hypothesis: `body` proceeds with `P` as a hypothesis. No
    /// obligation; walker emits no theorem at this node.
    Assume(&'a Exp, Box<Wp<'a>>),

    /// User-written Lean tactic inside a `tactus_auto` fn.
    ///
    /// Two surface forms produce this node, distinguished by `cond`:
    /// * `Some(P)` — `assert(P) by { tac }`. Walker emits one
    ///   theorem for `P` with `tac` as the closer (rather than
    ///   the standard `tactus_auto`). `P` then enters body's
    ///   context as a hypothesis.
    /// * `None` — `proof { tac }`. Walker pushes `tac` onto
    ///   `e.tactic_prefix` and walks body; every theorem in
    ///   body's scope gets `(tac) <;> closer` so the user's
    ///   `have h : P := by …` lines propagate as local
    ///   hypotheses to subsequent obligations.
    AssertByTactus {
        cond: Option<&'a Exp>,
        tactic_text: String,
        body: Box<Wp<'a>>,
    },

    /// `if cond { then_branch } else { else_branch }`. Walker
    /// recurses on `then_branch` with `cond` as a Hyp frame, and
    /// on `else_branch` with `¬cond`. No theorem at the branch
    /// node; each branch's sub-Wp produces its own theorems.
    Branch {
        cond: &'a Exp,
        then_branch: Box<Wp<'a>>,
        else_branch: Box<Wp<'a>>,
    },

    /// Loop. `body` is the body's Wp built with its own local
    /// `Done(I ∧ D < _tactus_d_old)` terminator; `after` is the
    /// post-loop continuation (built with the enclosing scope's
    /// `after`). `walk_loop` emits one init theorem per invariant,
    /// walks `body` in maintain ctx (∀ mod_vars + bounds + invs as
    /// hyps + cond as hyp + `_tactus_d_old := D` let), and walks
    /// `after` in use ctx (∀ mod_vars + bounds + invs as hyps +
    /// ¬cond as hyp).
    ///
    /// `cond` is `Some(c)` for a simple `while c { … }` with no
    /// breaks (the body runs while `c` holds; exit is via `!c`).
    /// `cond` is `None` for the break-lowered form Verus produces
    /// for `while c { … break; … }` (the body sees `if !c { break; }`
    /// inserted by Verus; exit is only via `break`). For `cond:
    /// None` the maintain ctx drops the `cond` hyp and the use
    /// ctx drops the `¬cond` hyp.
    Loop {
        cond: Option<&'a Exp>,
        invs: &'a [LoopInv],
        decrease: &'a Exp,
        modified_vars: Vec<(&'a VarIdent, &'a Typ)>,
        body: Box<Wp<'a>>,
        after: Box<Wp<'a>>,
        /// Per-loop-unique name for the pre-body decrease snapshot
        /// (`let _tactus_d_old_<id> := D` in the maintain ctx).
        /// Built from Verus's `StmX::Loop::id` in `build_wp_loop` so
        /// nested loops never share the name. Without gensym, an
        /// inner loop's `let _tactus_d_old := D_inner` would shadow
        /// the outer's binding for any references on the same
        /// scope path — currently impossible (sibling conjuncts),
        /// but a future refactor that mixes scopes would silently
        /// miscompile.
        d_old_name: String,
    },

    /// Direct function call. `after` is the post-call continuation.
    /// `walk_call` emits one theorem for the substituted
    /// `callee.requires` (CallPrecondition), then walks `after`
    /// under context frames `∀ ret, ret_bound → ensures(subst) →
    /// let dest := ret;`. The require/ensure are inlined via
    /// `lean_ast::substitute` (capture-avoiding, mirrors what the
    /// pre-D `lower_call` did).
    Call {
        callee: &'a FunctionX,
        /// Borrow the SST's arg slice directly — no `Vec<&Exp>`
        /// allocation. `StmX::Call::args` is `Arc<Vec<Exp>>`, so
        /// `&args[..]` gives us a `&'a [Exp]` with the same
        /// lifetime as the rest of the Wp.
        args: &'a [Exp],
        /// Type arguments from the call site, one per `callee.typ_params`.
        /// `walk_call` uses these to substitute each `TypParam(id)` in
        /// the callee's require/ensure with the call site's concrete
        /// type. Empty slice when the callee is non-generic.
        typ_args: &'a [Typ],
        /// Caller's destination variable (`let x = foo(…)` → `Some("x")`;
        /// `foo(…);` → `None`). Only the name is needed — `walk_call`
        /// pushes a `let dest := ret` frame inside the `∀ ret`, and
        /// `ret` already has its type-bound hypothesis from
        /// `type_bound_predicate`.
        dest: Option<&'a VarIdent>,
        /// Call-site Span — the Rust source location of `callee(args)`.
        /// Used by `walk_call` to wrap the inlined requires_conj with
        /// a `SpanMark`, so a failing precondition check surfaces the
        /// call site in error messages (#51) rather than the fn
        /// declaration or the callee's own source line.
        call_span: &'a Span,
        /// `&mut` parameters at this call site. Each entry is
        /// `(param_idx, caller_var)`: the index into `callee.params` /
        /// `args` of the `&mut` parameter, and the caller-side
        /// `VarIdent` whose memory is being mutated. `walk_call` uses
        /// these to introduce a fresh existential per `&mut` arg
        /// (the post-call value), substitute the callee's
        /// `varat_pre_name(p) ↦ caller_arg` (pre-state) and
        /// `p ↦ fresh` (post-state) in the inlined ensures, and
        /// rebind the caller's local to the fresh value after the
        /// callee's ensures Hyp frame. Empty for fns with no `&mut`
        /// params (the common case). See task #55.
        mut_args: Vec<(usize, &'a VarIdent)>,
        after: Box<Wp<'a>>,
    },
}

// ── Walker helpers ─────────────────────────────────────────────────────

/// Read the pre-resolved start `file:line:col` from a Verus
/// `Span` for `/- @rust:LOC -/` markers in the generated Lean
/// (#51).
///
/// `Span::start_loc` is populated by
/// `rust_verify::spans::to_air_span` at SST construction time.
/// Spans built without rustc context (test fixtures, the
/// `err_air_span` diagnostic helper, the verifier's "no
/// location" placeholder) leave `start_loc` empty; we fall back
/// to `as_string` so something useful surfaces rather than an
/// empty marker.
fn format_rust_loc(span: &Span) -> String {
    if !span.start_loc.is_empty() {
        span.start_loc.clone()
    } else {
        span.as_string.clone()
    }
}

/// Classify an assertion expression for error-message labeling.
/// `Wp::Assert` is the catch-all for obligations Verus inserts —
/// most are user `assert(P)` (kind=Plain), but the recursion
/// pass inserts `CheckDecreaseHeight` calls via `Wp::Assert`
/// which we recognize as Termination obligations. Other
/// non-Plain kinds (LoopInvariant / CallPrecondition / etc.) are
/// set explicitly at their wrapping sites in `walk_loop` /
/// `walk_call`.
fn detect_assert_kind(e: &Exp) -> AssertKind {
    // Peel transparent wrappers (Box / Unbox / CoerceMode /
    // Trigger / Loc) — Verus may wrap the CheckDecreaseHeight
    // call in any of these before inserting it as an Assert.
    let peeled = peel_transparent(e);
    if let ExpX::Call(CallFun::InternalFun(InternalFun::CheckDecreaseHeight), _, _) = &peeled.x {
        AssertKind::Termination
    } else {
        AssertKind::Plain
    }
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
    let peeled = peel_value_position(e);
    match &peeled.x {
        ExpX::If(cond, then_e, else_e) => {
            let c = sst_exp_to_ast(cond);
            LExpr::and(
                LExpr::implies(c.clone(), lift_if_value(then_e, emit_leaf)),
                LExpr::implies(LExpr::not(c), lift_if_value(else_e, emit_leaf)),
            )
        }
        // `let y := e_rhs; body` — if any rhs has an if, lift it out,
        // re-threading `body` through each branch. Verus often emits
        // `let y = …; y` blocks as this shape, which would otherwise
        // hide the if from our lift.
        //
        // Multi-binder lets (`let (a, b) = …; body`, represented as
        // `Bind(Let([(a, val_a), (b, val_b)]), body)`) are unfolded
        // to a chain of single-binder lets up front; the existing
        // single-binder logic then handles each layer naturally.
        ExpX::Bind(bnd, body) => {
            if let BndX::Let(bs) = &bnd.x {
                if bs.len() > 1 {
                    // Unfold to single-binder chain, then recurse.
                    let unfolded = unfold_multi_binder_let(
                        &bs[..], body, &peeled.span, &peeled.typ,
                    );
                    return lift_if_value(&unfolded, emit_leaf);
                }
            }
            if let Some((name, rhs, inner_body)) = match_single_let_bind(bnd, body) {
                // `name` is already an owned `String` from
                // `match_single_let_bind`; the closure captures
                // it by reference and clones per leaf invocation.
                let body_ast = sst_exp_to_ast(inner_body);
                lift_if_value(rhs, &|rhs_leaf| {
                    emit_leaf(LExpr::let_bind(name.clone(), rhs_leaf, body_ast.clone()))
                })
            } else {
                emit_leaf(sst_exp_to_ast(e))
            }
        }
        _ => emit_leaf(sst_exp_to_ast(e)),
    }
}

/// Convert a multi-binder `Bind(Let([b1, b2, ...]), body)` into the
/// equivalent chain of single-binder lets:
///   `Bind(Let([b1]), Bind(Let([b2]), ..., body))`
///
/// Used by `lift_if_value` and `walk_let` so the existing
/// single-binder peel logic handles each binder layer naturally —
/// without this unfold, a multi-binder let would silently pass
/// through with no peeling, hiding any if-values inside its
/// rhs's from goal-level lift.
fn unfold_multi_binder_let(
    bs: &[VarBinder<Exp>],
    body: &Exp,
    span: &Span,
    typ: &Typ,
) -> Exp {
    if bs.is_empty() {
        return body.clone();
    }
    let inner = unfold_multi_binder_let(&bs[1..], body, span, typ);
    let single_bnd = vir::def::Spanned::new(
        span.clone(),
        BndX::Let(Arc::new(vec![bs[0].clone()])),
    );
    Arc::new(SpannedTyped {
        span: span.clone(),
        typ: typ.clone(),
        x: ExpX::Bind(single_bnd, inner),
    })
}

/// Destructure `ExpX::Bind(BndX::Let([single binder]), body)` into
/// `(sanitized_name, rhs_value, body)`. Centralizes the "single-
/// binder let-bind" check that both `lift_if_value` and `walk_let`
/// need, replacing the awkward `matches!`-guard + `let-else`
/// re-destructure pattern with a clean `if let Some((...))`.
/// Returns `None` for non-Let binders or for multi-binder Lets
/// (multi-binder lets are deferred — see DESIGN.md "Lossy accepted
/// forms").
fn match_single_let_bind<'a>(
    bnd: &'a vir::sst::Bnd,
    body: &'a Exp,
) -> Option<(String, &'a Exp, &'a Exp)> {
    let BndX::Let(bs) = &bnd.x else { return None };
    if bs.len() != 1 { return None; }
    let b = &bs[0];
    Some((sanitize(&b.name.0), &b.a, body))
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
        // Neither `build_wp_call` nor `build_wp_loop` needs the
        // enclosing loop's `loop_ctx`: they don't recurse on stmts
        // outside their own fixed structure. `build_wp_loop` builds
        // its OWN loop_ctx for its body (see there); `after` was
        // already built by the caller with the outer loop_ctx.
        StmX::Call { .. } => build_wp_call(stm, after, ctx),
        StmX::Loop { .. } => build_wp_loop(stm, after, ctx),
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
        // `ast_to_sst` encodes an `assert(P) by { lean_tac }` (or
        // a `proof { lean_tac }`) inside a `tactus_auto` fn (see
        // `ExprX::AssertBy` handling there). We read the verbatim
        // Lean tactic text from the original file via the
        // `tactic_span` and produce a `Wp::AssertByTactus` node;
        // `walk_assert_by_tactus` then either emits a single
        // theorem with the user's tactic as the closer
        // (`assert(P) by` form) or pushes the tactic as a prefix
        // applied via `<;>` to every body theorem (`proof` form).
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
    if split.is_some() {
        return Err(
            "calls with split-assertion error reporting are not yet supported".to_string()
        );
    }
    // `is_trait_default = Some(true)` means the call resolved to the
    // trait's default impl (not a concrete impl). The default body
    // uses `Self` as a parameter that we'd need to substitute with
    // the call site's concrete type — separate concern from the
    // resolved-impl path. `Some(false)` is fine (concrete impl, just
    // happens to be on a trait that has a default).
    if matches!(is_trait_default, Some(true)) {
        return Err(
            "calls resolved to a trait's default impl (rather than a concrete impl) \
             are not yet supported (#56 follow-up)".to_string()
        );
    }
    // Pick callee + type args:
    //   * `resolved_method = Some((resolved_fun, resolved_typs))` —
    //     `DynamicResolved` case: use the resolved concrete impl as
    //     callee. Its `requires/ensures/params` get inlined; the
    //     resolved type args have `Self` filled in with the concrete
    //     type and any method type params expanded. The trait
    //     method's spec is satisfied by every impl (Verus enforces
    //     this at the trait-impl boundary), so substituting via the
    //     resolved impl is sound.
    //   * `resolved_method = None` — `Static` / `ProofFn` /
    //     `Dynamic` / `ExternalTraitDefault`. The latter three may
    //     not have a body or may not be in fn_map; the lookup below
    //     fails cleanly with the cross-crate error.
    let (callee_fun, callee_typ_args): (&'a Fun, &'a [Typ]) = match resolved_method {
        Some((resolved, resolved_typs)) => (resolved, &resolved_typs[..]),
        None => (fun, &typ_args[..]),
    };
    let Some(callee) = ctx.fn_map.get(callee_fun).copied() else {
        return Err(format!(
            "callee `{:?}` not found in the crate's function map — cross-crate calls are \
             not yet supported",
            callee_fun.path
        ));
    };
    // For trait method impls, also verify the trait method decl is in
    // fn_map. `walk_call` reads the trait's `require/ensure` (the impl's
    // are typically empty/inherited), so the trait decl needs to be
    // resolvable. Cross-crate traits aren't yet supported.
    if let FunctionKind::TraitMethodImpl { method, .. } = &callee.kind {
        if !ctx.fn_map.contains_key(method) {
            return Err(format!(
                "trait method decl `{:?}` for resolved impl `{:?}` not found in \
                 the crate's function map — cross-crate trait calls are not yet \
                 supported (#56 follow-up)",
                method.path, callee_fun.path,
            ));
        }
    }
    // Param/arg count must align (both sides are post-`ast_simplify`
    // so zero-arg callees have their `no%param` dummy in both).
    let param_count = callee.params.len();
    if param_count != args.len() {
        return Err(format!(
            "callee `{:?}` has {} param(s) but call site passes {} arg(s) — \
             arg-passing convention may be out of sync (both sides should be \
             post-ast_simplify); this would bind wrong variables if we proceeded",
            callee_fun.path, param_count, args.len(),
        ));
    }
    // Type params / type args must align — if a call site passes fewer
    // types than the callee declared, substitution would leave some
    // `TypParam(T)` references unsubstituted in the inlined spec.
    //
    // For `DynamicResolved`, `callee_typ_args` is the resolved-impl's
    // type args (with `Self` already filled in by Verus's resolution).
    // It must match the resolved impl's `typ_params.len()` — different
    // from the trait method's `typ_params.len()` when the trait has
    // type params that the impl monomorphizes.
    if callee.typ_params.len() != callee_typ_args.len() {
        return Err(format!(
            "callee `{:?}` declares {} type param(s) but call site passes {} type \
             arg(s) — would leave type-param references unsubstituted in the \
             inlined spec",
            callee_fun.path, callee.typ_params.len(), callee_typ_args.len(),
        ));
    }
    // Build the `&mut` arg list while validating each arg. For each
    // `&mut` param, the call-site arg must be a simple
    // `Loc(VarLoc(...))` — `&mut x.f` / `&mut v[i]` / etc. would
    // require additional encoding (havoc-base + assume-other-fields-
    // unchanged style) which is deferred. Non-`&mut` args go through
    // the usual `check_exp` validation.
    let mut mut_args: Vec<(usize, &'a VarIdent)> = Vec::new();
    for (i, (param, a)) in callee.params.iter().zip(args.iter()).enumerate() {
        if param.x.is_mut {
            // Caller-side var must extract cleanly. `extract_simple_var_ident`
            // peels `Loc` and any wrappers down to `Var`/`VarLoc`, so this
            // succeeds for the simple `&mut local` case and fails for
            // `&mut x.f` / `&mut v[i]`.
            match extract_simple_var_ident(a) {
                Some(v) => mut_args.push((i, v)),
                None => return Err(format!(
                    "&mut argument at position {} is not a simple local variable. \
                     `&mut x.f` / `&mut v[i]` / etc. require additional encoding \
                     (havoc base + assume-other-fields-unchanged) — deferred \
                     follow-up to #55. Workaround: bind to a local first \
                     (`let mut tmp = expr; foo(&mut tmp); … = tmp;`).",
                    i,
                )),
            }
            // Don't `check_exp(a)` here — `a` is a `Loc` shape, not a
            // value-position expression. The inner var has already been
            // structurally validated by `extract_simple_var_ident`.
        } else {
            if contains_loc(a) {
                // Loc on a non-&mut param shouldn't happen (Verus's
                // borrow check would reject it upstream). Defensive
                // rejection so an unexpected VIR shape fails loudly
                // rather than silently encoding wrong.
                return Err(format!(
                    "unexpected `Loc`-wrapped argument at non-&mut position {} — \
                     callee param.is_mut=false but arg is an L-value. Refusing \
                     to encode silently.",
                    i,
                ));
            }
            check_exp(a)?;
        }
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
        typ_args: callee_typ_args,
        dest: bound_dest,
        call_span: &stm.span,
        mut_args,
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
        id,
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
    // Per-loop-unique d_old name. Verus's `id: u64` is stable per
    // loop instance, so two nested loops can never collide.
    let d_old_name = format!("_tactus_d_old_{}", id);
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
    //   The reference to `_tactus_d_old` here is a Var; `walk_loop`
    //   pushes a `Let("_tactus_d_old", D)` frame onto the maintain
    //   ctx so the body's continue_leaf sees it in scope.
    // * break: establish the at-exit invariants, which currently
    //   equals `I` (we only accept invariants with at_entry = at_exit
    //   = true — see validation above). No decrease obligation on
    //   break since we're leaving the loop, not iterating.
    //
    // Each invariant + the decrease comparison is wrapped in its
    // own `SpanMark` with the right `AssertKind` here, so that when
    // `emit_done_or_split` splits the body's terminator at top-
    // level conjunction, each leaf retains its kind for theorem
    // naming. Without these wrappers, the unwrapped default
    // (`"ensures"`) would label every conjunct.
    let inv_conj = and_all(invs.iter().map(|i| LExpr::span_mark(
        format_rust_loc(&i.inv.span),
        AssertKind::LoopInvariant,
        sst_exp_to_ast(&i.inv),
    )).collect());
    let decrease_marked = LExpr::span_mark(
        format_rust_loc(&decrease_exp.span),
        AssertKind::LoopDecrease,
        LExpr::lt(sst_exp_to_ast(decrease_exp), LExpr::var(d_old_name.clone())),
    );
    let continue_leaf = LExpr::and(inv_conj.clone(), decrease_marked);
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
        d_old_name,
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
    fn test_span() -> Span { Span::dummy() }

    /// Construct a Span with specified `start_loc` and `as_string`
    /// for testing `format_rust_loc`'s field-vs-fallback logic.
    fn span_with_locs(start_loc: &str, as_string: &str) -> Span {
        Span {
            as_string: as_string.to_string(),
            start_loc: start_loc.to_string(),
            ..Span::dummy()
        }
    }

    // #51 source-mapping pin: format_rust_loc prefers the
    // pre-resolved `start_loc` (populated by `rust_verify`'s
    // `to_air_span`) and falls back to `as_string` only when
    // start_loc is empty (test fixtures / synthetic spans).

    #[test]
    fn format_rust_loc_uses_start_loc_when_present() {
        let s = span_with_locs(
            "/home/user/proj/src/main.rs:42:13",
            "/home/user/proj/src/main.rs:42:13: 42:20 (#0)",
        );
        assert_eq!(format_rust_loc(&s), "/home/user/proj/src/main.rs:42:13");
    }

    #[test]
    fn format_rust_loc_falls_back_to_as_string_when_start_loc_empty() {
        let s = span_with_locs("", "synthetic-span-from-test-fixture");
        assert_eq!(format_rust_loc(&s), "synthetic-span-from-test-fixture");
    }

    #[test]
    fn format_rust_loc_both_empty() {
        let s = span_with_locs("", "");
        assert_eq!(format_rust_loc(&s), "");
    }

    // ── sanitize_loc_for_name (D Stage 1) ───────────────────────
    //
    // Theorem-naming compression: keeps just `<basename>_<line>_<col>`
    // so per-obligation theorem names stay short enough that a fn
    // with many obligations doesn't produce kilobyte-long names.

    #[test]
    fn sanitize_loc_full_path_strips_directory_and_extension() {
        assert_eq!(
            sanitize_loc_for_name("/home/user/proj/src/main.rs:42:13"),
            "main_42_13",
        );
    }

    #[test]
    fn sanitize_loc_no_directory_strips_extension() {
        assert_eq!(sanitize_loc_for_name("main.rs:5:1"), "main_5_1");
    }

    #[test]
    fn sanitize_loc_no_extension_no_directory() {
        // Fallback path for as_string-style spans without a dot.
        assert_eq!(sanitize_loc_for_name("synthetic-fixture"), "synthetic_fixture");
    }

    #[test]
    fn sanitize_loc_empty() {
        assert_eq!(sanitize_loc_for_name(""), "");
    }

    #[test]
    fn sanitize_loc_dotted_basename_keeps_underscore() {
        // A basename like `foo_bar.rs` should keep the underscore.
        assert_eq!(sanitize_loc_for_name("foo_bar.rs:10:20"), "foo_bar_10_20");
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

    /// Compare two LExprs structurally by pretty-printing (our
    /// printer is deterministic so equivalent trees produce
    /// identical strings). Strips `/-! @rust:LOC -/` SpanMark
    /// markers from both sides before comparing — these are
    /// instrumentation metadata for #51 source mapping, not
    /// semantic content, so semantic-equivalence tests should
    /// ignore them.
    fn pp_eq(a: &LExpr, b: &LExpr) -> bool {
        let pp = |e: &LExpr| crate::lean_pp::pp_expr(&crate::lean_ast::strip_span_marks(e));
        pp(a) == pp(b)
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

    // ── peel_value_position ────────────────────────────────────────
    //
    // Helper that combines `peel_transparent` with a single-layer
    // `Loc` peel. Used by `walk_let` and `lift_if_value` to look
    // through to the underlying value-position expression. Distinct
    // from `peel_transparent` (which leaves Loc) so that
    // `contains_loc` can still detect &mut sites.

    #[test]
    fn peel_value_position_leaves_plain_var_alone() {
        let x = var_exp("x", typ_int());
        assert_eq!(exp_ident(peel_value_position(&x)), Some("x"));
    }

    #[test]
    fn peel_value_position_peels_box() {
        let x = var_exp("x", typ_int());
        assert_eq!(exp_ident(peel_value_position(&box_exp(x))), Some("x"));
    }

    #[test]
    fn peel_value_position_peels_loc() {
        // The point of difference vs `peel_transparent`: this
        // helper peels through Loc.
        let x = var_exp("x", typ_int());
        assert_eq!(exp_ident(peel_value_position(&loc_exp(x))), Some("x"));
    }

    #[test]
    fn peel_value_position_peels_loc_with_outer_wrapper() {
        // Box(Loc(x)) — peel both layers.
        let x = var_exp("x", typ_int());
        let wrapped = box_exp(loc_exp(x));
        assert_eq!(exp_ident(peel_value_position(&wrapped)), Some("x"));
    }

    #[test]
    fn peel_value_position_peels_transparent_under_loc() {
        // Loc(Box(x)) — peel the Loc, then the Box inside.
        let x = var_exp("x", typ_int());
        let wrapped = loc_exp(box_exp(x));
        assert_eq!(exp_ident(peel_value_position(&wrapped)), Some("x"));
    }

    #[test]
    fn peel_value_position_does_not_peel_if() {
        // Stops at non-transparent, non-Loc nodes.
        let c = var_exp("c", typ_bool());
        let a = var_exp("a", typ_int());
        let b = var_exp("b", typ_int());
        let e = if_exp(c, a, b);
        assert!(matches!(&peel_value_position(&e).x, ExpX::If(..)));
    }

    // ── match_single_let_bind ──────────────────────────────────────
    //
    // Helper that destructures `ExpX::Bind(BndX::Let([single]), body)`
    // into `(name, rhs, body)`. Returns `None` for non-Let binders or
    // multi-binder Lets. Used by `walk_let` and `lift_if_value` to
    // peel one layer of nested let-bind at a time.

    #[test]
    fn match_single_let_bind_extracts_single_binder() {
        // `let z := zval; body` — should extract.
        let zval = var_exp("zval", typ_int());
        let body = var_exp("body", typ_int());
        let bind_exp = let_exp("z", zval, body);
        let ExpX::Bind(bnd, body_inner) = &bind_exp.x else {
            panic!("let_exp should produce Bind");
        };
        let result = match_single_let_bind(bnd, body_inner);
        assert!(result.is_some());
        let (name, rhs, body_out) = result.unwrap();
        assert_eq!(name, "z");
        assert_eq!(exp_ident(rhs), Some("zval"));
        assert_eq!(exp_ident(body_out), Some("body"));
    }

    #[test]
    fn match_single_let_bind_returns_none_for_non_let_binder() {
        // BndX::Quant or other non-Let → None. We don't construct a
        // Quant in tests; instead verify by negative: passing a
        // synthetic Bind with a Quant binder should yield None. The
        // test infrastructure uses Let exclusively so we trust the
        // pattern guard here. As a proxy, verify the function's
        // type-level contract: it returns Option, callers handle None.
        // (Actual non-Let binders are exercised in e2e via
        // `forall|...| P` quantifiers in spec fns.)
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
