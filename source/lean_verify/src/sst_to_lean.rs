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
    AssertQueryMode, Fun, FunctionX, KrateX, TactusKind, Typ, UnaryOp, UnaryOpr, VarIdent,
};
use vir::messages::Span;
use crate::lean_ast::{
    and_all, substitute, AssertKind, Binder as LBinder, BinderKind, Expr as LExpr,
    Tactic, Theorem,
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
///   conjunct of `leaf`. Top-level fn-ensures conjuncts produce
///   `_tactus_ensures_<fn>_<id>`; loop-body terminator conjuncts
///   produce `_tactus_loop_invariant_<fn>_at_<loc>_<id>` and
///   `_tactus_loop_decrease_<fn>_at_<loc>_<id>` because each
///   conjunct carries a SpanMark with its kind from
///   `build_wp_loop`.
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
    let mut emitter = ObligationEmitter {
        fn_name,
        base_binders: binders,
        counter: 0,
        out: Vec::new(),
        tactic_prefix: Vec::new(),
    };
    walk_obligations(&body_wp, &ctx, &OblCtx::new(), &mut emitter);
    Ok(emitter.out)
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
    /// `∀ (x : T),` wrapping. Stage 2's call walker pushes one
    /// for the callee's return value; Stage 3's loop walker will
    /// push one per modified variable.
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
    /// (matching source order). A `Let("x", v)` outside a
    /// `Hyp(P_uses_x)` frame produces `let x := v; P_uses_x → goal`,
    /// so the hypothesis can reference `x`.
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
            let id = e.next_id();
            let kind = detect_assert_kind(asserted);
            let label = kind_to_name(kind);
            let loc = format_rust_loc(&asserted.span);
            let suffix = sanitize_loc_for_name(&loc);
            let name = format!("_tactus_{}_{}_at_{}_{}", label, e.fn_name, suffix, id);
            let cond_ast = sst_exp_to_ast(asserted);
            let goal = LExpr::span_mark(loc, kind, cond_ast.clone());
            e.emit(name, obl.wrap(goal), simple_tactic());
            let new_obl = obl.with_frame(CtxFrame::Hyp(sst_exp_to_ast(asserted)));
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
        Wp::Call { callee, args, typ_args, dest, call_span, after } => {
            walk_call(callee, args, typ_args, *dest, call_span, after, ctx, obl, e);
        }
        Wp::Loop { cond, invs, decrease, modified_vars, body, after } => {
            walk_loop(*cond, invs, decrease, modified_vars, body, after, ctx, obl, e);
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
    match cond {
        Some(c) => {
            // Assert-by: emit one theorem for `c` with the user's
            // tactic as the closer. The cond becomes a hypothesis
            // for body theorems. AssertKind::Plain because it's a
            // user-written `assert(P) by { tac }` — same kind that
            // a plain `assert(P)` would get from `detect_assert_kind`.
            let id = e.next_id();
            let loc = format_rust_loc(&c.span);
            let suffix = sanitize_loc_for_name(&loc);
            let name = format!(
                "_tactus_assert_{}_at_{}_{}", e.fn_name, suffix, id,
            );
            let goal = LExpr::span_mark(
                loc, AssertKind::Plain, sst_exp_to_ast(c),
            );
            e.emit(name, obl.wrap(goal), Tactic::Raw(tactic_text.to_string()));
            // Cond as hypothesis for body theorems.
            let new_obl = obl.with_frame(CtxFrame::Hyp(sst_exp_to_ast(c)));
            walk_obligations(body, ctx, &new_obl, e);
        }
        None => {
            // Proof block: tactic prefix flows to every theorem in
            // body's scope. Push, walk, pop — the prefix only
            // applies to body theorems, not to obligations
            // sequentially after the proof block.
            e.tactic_prefix.push(tactic_text.to_string());
            walk_obligations(body, ctx, obl, e);
            e.tactic_prefix.pop();
        }
    }
}

/// Emit one or more theorems for a `Wp::Done` leaf. If the leaf is
/// a top-level conjunction, recursively split into one theorem per
/// conjunct. Each conjunct preserves its own `SpanMark` wrapping
/// (if any), so loop-body terminators (`(I_1 ∧ I_2 ∧ ...) ∧
/// D < d_old`) yield separate `LoopInvariant_*` / `LoopDecrease_*`
/// theorems with the right kind in each name. Top-level fn-ensures
/// terminators (no SpanMark wrapping) yield `_tactus_ensures_N`
/// per clause.
fn emit_done_or_split(leaf: &LExpr, obl: &OblCtx, e: &mut ObligationEmitter) {
    use crate::lean_ast::{BinOp, ExprNode};
    if let ExprNode::BinOp { op: BinOp::And, lhs, rhs } = &leaf.node {
        emit_done_or_split(lhs, obl, e);
        emit_done_or_split(rhs, obl, e);
        return;
    }
    let id = e.next_id();
    let (kind_label, loc) = match &leaf.node {
        ExprNode::SpanMark { rust_loc, kind, .. } => {
            (kind_to_name(*kind), rust_loc.clone())
        }
        // Unwrapped → top-level fn ensures clause. Use "ensures"
        // rather than `kind_to_name(Plain)` ("assert") since the
        // theorem isn't an explicit `assert(P)`.
        _ => ("ensures", String::new()),
    };
    let name = if loc.is_empty() {
        format!("_tactus_{}_{}_{}", kind_label, e.fn_name, id)
    } else {
        let suffix = sanitize_loc_for_name(&loc);
        format!("_tactus_{}_{}_at_{}_{}", kind_label, e.fn_name, suffix, id)
    };
    e.emit(name, obl.wrap(leaf.clone()), simple_tactic());
}

/// Per-obligation walker for `Wp::Loop`. Emits init theorems (one
/// per invariant), walks the body in a maintain context, and walks
/// `after` in a use context. Per-obligation equivalent of
/// [`lower_loop`]'s `init ∧ maintain ∧ use` conjunctive form —
/// splitting it so each invariant's init/maintain check, the
/// decrease-decreased check, and the post-loop continuation get
/// their own pos.line in Lean.
///
/// The body's `Done(I ∧ D < d_old)` terminator (built by
/// `build_wp_loop`) flows naturally through `walk_obligations`'s
/// `Wp::Done` arm via [`emit_done_or_split`], producing one
/// theorem per conjunct (each invariant + the decrease).
fn walk_loop<'a>(
    cond: Option<&Exp>,
    invs: &[LoopInv],
    decrease: &Exp,
    modified_vars: &[(&'a VarIdent, &'a Typ)],
    body: &Wp<'a>,
    after: &Wp<'a>,
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
        let id = e.next_id();
        let loc = format_rust_loc(&inv.inv.span);
        let suffix = sanitize_loc_for_name(&loc);
        let name = format!(
            "_tactus_loop_invariant_{}_at_{}_{}", e.fn_name, suffix, id,
        );
        e.emit(name, obl.wrap(inv_marked(inv)), simple_tactic());
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
    // `let _tactus_d_old := D` — pre-body decrease value, referenced
    // by the body's continue_leaf as `D < _tactus_d_old`. Must come
    // AFTER the cond hyp (which doesn't reference `_tactus_d_old`)
    // but BEFORE walking the body (which does).
    maintain_obl.frames.push(CtxFrame::Let(
        "_tactus_d_old".to_string(),
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

/// Per-obligation walker for `Wp::Call`. Emits one theorem for the
/// callee's precondition (substituted with call-site args), then
/// continues walking `after` with the extended context: a `∀ ret`
/// binder, the ret's type-bound hypothesis (if any), the callee's
/// substituted `ensures` as a hypothesis, and a `let dest := ret`
/// if the call has a destination var. Per-obligation equivalent of
/// [`lower_call`]'s
/// `requires ∧ ∀ ret, bound → ensures → let dest := ret; <after>`
/// shape — splitting it into a precondition theorem (Lean checks
/// `requires`) plus a richer context for the continuation (which
/// produces its own theorems via the recursive walk).
fn walk_call<'a>(
    callee: &FunctionX,
    args: &[Exp],
    typ_args: &[Typ],
    dest: Option<&VarIdent>,
    call_span: &Span,
    after: &Wp<'a>,
    ctx: &WpCtx<'a>,
    obl: &OblCtx,
    e: &mut ObligationEmitter,
) {
    // Substitution map combining value params → call-site args and
    // type params → call-site type expressions. Mirrors `lower_call`
    // exactly so the per-obligation form produces the same logical
    // content as the prior single-theorem form. `TypParam(T)` renders
    // as `Var("T")` so the value-level substitute rewrites both kinds.
    let params_vec: Vec<_> = callee.params.iter().collect();
    let mut subst: std::collections::HashMap<String, LExpr> = params_vec.iter()
        .zip(args.iter())
        .map(|(p, arg)| (sanitize(&p.x.name.0), sst_exp_to_ast(arg)))
        .collect();
    for (tp_name, tp_arg) in callee.typ_params.iter().zip(typ_args.iter()) {
        subst.insert(sanitize(tp_name), typ_to_expr(tp_arg));
    }

    // Precondition theorem: substitute requires with subst, wrap in a
    // SpanMark with the call-site span (NOT the callee's source) so
    // a failing precondition surfaces the call in the caller's source
    // — same rationale as `lower_call`'s requires_clause wrapping.
    let requires_conj = and_all(
        callee.require.iter().map(|e| vir_expr_to_ast(e)).collect()
    );
    let loc = format_rust_loc(call_span);
    let requires_clause = LExpr::span_mark(
        loc.clone(),
        AssertKind::CallPrecondition,
        substitute(&requires_conj, &subst),
    );
    let id = e.next_id();
    let suffix = sanitize_loc_for_name(&loc);
    let theorem_name = format!(
        "_tactus_precondition_{}_at_{}_{}", e.fn_name, suffix, id,
    );
    e.emit(theorem_name, obl.wrap(requires_clause), simple_tactic());

    // Continuation: walk `after` under a fresh context that pushes
    // the post-call binders/hypotheses/lets in the same order
    // `lower_call` would have nested them. Reading the resulting
    // wrap from outermost to innermost: `∀ ret, ret_bound → ensures
    // → let dest := ret; <continuation>`.
    let ret = &callee.ret.x;
    let ret_name_cal = sanitize(&ret.name.0);
    let ret_typ = substitute(&typ_to_expr(&ret.typ), &subst);
    let ensures_conj = and_all(
        callee.ensure.0.iter().map(|e| vir_expr_to_ast(e)).collect()
    );
    let substituted_ensures = substitute(&ensures_conj, &subst);

    let mut new_obl = obl.clone();
    new_obl.frames.push(CtxFrame::Binder(LBinder {
        name: Some(ret_name_cal.clone()),
        ty: ret_typ,
        kind: BinderKind::Explicit,
    }));
    if let Some(pred) = type_bound_predicate(&LExpr::var(ret_name_cal.clone()), &ret.typ) {
        new_obl.frames.push(CtxFrame::Hyp(pred));
    }
    new_obl.frames.push(CtxFrame::Hyp(substituted_ensures));
    if let Some(dest_ident) = dest {
        new_obl.frames.push(CtxFrame::Let(
            sanitize(&dest_ident.0),
            LExpr::var(ret_name_cal),
        ));
    }

    walk_obligations(after, ctx, &new_obl, e);
}

/// `Wp::Let` walker with if-RHS lifting (mirrors `lift_if_value`'s
/// behaviour in `lower_wp`). `let x := if c then a else b; rest`
/// forks into two recursive walks, each with cond as a hypothesis
/// frame and the corresponding branch as the let value. Without
/// this, `omega` can't see inside the value-position if and the
/// let theorems would fail.
fn walk_let<'a>(
    name: &'a str,
    val: &'a Exp,
    body: &Wp<'a>,
    ctx: &WpCtx<'a>,
    obl: &OblCtx,
    e: &mut ObligationEmitter,
) {
    // Peel transparent wrappers AND a single layer of `Loc` — same as
    // `lift_if_value`. `Loc` peels for if-detection but isn't part of
    // `peel_transparent` because `contains_loc` needs Loc un-peeled.
    let peeled = peel_transparent(val);
    let peeled = match &peeled.x {
        ExpX::Loc(inner) => peel_transparent(inner),
        _ => peeled,
    };
    match &peeled.x {
        ExpX::If(cond, then_e, else_e) => {
            let c_ast = sst_exp_to_ast(cond);
            walk_let(name, then_e, body, ctx,
                &obl.with_frame(CtxFrame::Hyp(c_ast.clone())), e);
            walk_let(name, else_e, body, ctx,
                &obl.with_frame(CtxFrame::Hyp(LExpr::not(c_ast))), e);
        }
        // `let outer := (let z := zval; bodyval); rest`
        //   ≡ `let z := zval; let outer := bodyval; rest`
        // Peel one layer of inner let, then continue lifting on
        // `bodyval` (which may itself be an If or another nested let).
        ExpX::Bind(bnd, inner_body) if matches!(&bnd.x, BndX::Let(bs) if bs.len() == 1) => {
            let BndX::Let(bs) = &bnd.x else { unreachable!() };
            let inner_b = &bs[0];
            let inner_name = sanitize(&inner_b.name.0);
            let new_obl = obl.with_frame(CtxFrame::Let(
                inner_name, sst_exp_to_ast(&inner_b.a),
            ));
            walk_let(name, inner_body, body, ctx, &new_obl, e);
        }
        _ => {
            let new_obl = obl.with_frame(CtxFrame::Let(
                sanitize(name), sst_exp_to_ast(val),
            ));
            walk_obligations(body, ctx, &new_obl, e);
        }
    }
}

/// Atomic `tactus_auto` for per-obligation theorems. Each emitted
/// goal is a single obligation wrapped in let/→/∀ frames from the
/// `OblCtx`, which `omega` and `simp_all` handle natively (intros
/// for `∀`/`→`, zeta-reduction for `let`).
fn simple_tactic() -> Tactic {
    Tactic::Named("tactus_auto".to_string())
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
            // `&mut` args need havoc-after-call semantics: post-call,
            // the mutated parameter is any value satisfying its type
            // invariant AND the callee's `ensures` (which may
            // reference the new value). Encoding: `∀ (x' : T),
            // type_inv(x') → ensures[x ↦ x'] → <continuation>`
            // replacing the current pre/post pair. Tracked as task
            // #55 — see DESIGN.md "&mut in exec-fn calls" for the
            // plan (single-arg first, then multi-arg / aliasing).
            return Err(
                "calls with `&mut` arguments require havoc-after-call \
                 semantics — tracked as task #55. Workaround: refactor \
                 to a non-mutating signature (`fn foo(x: T) -> T` + \
                 caller re-binds) until the feature lands.".to_string()
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
        call_span: &stm.span,
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
    // Wrap each invariant + the decrease comparison with a SpanMark
    // carrying the right `AssertKind`. When the per-obligation walker
    // (D Stage 3) splits a body's terminator at top-level conjunction,
    // each leaf retains its kind for theorem naming. Without these
    // wrappers, every conjunct would be labeled `ensures` (the
    // unwrapped default in `emit_done_or_split`).
    let inv_conj = and_all(invs.iter().map(|i| LExpr::span_mark(
        format_rust_loc(&i.inv.span),
        AssertKind::LoopInvariant,
        sst_exp_to_ast(&i.inv),
    )).collect());
    let decrease_marked = LExpr::span_mark(
        format_rust_loc(&decrease_exp.span),
        AssertKind::LoopDecrease,
        LExpr::lt(sst_exp_to_ast(decrease_exp), LExpr::var("_tactus_d_old")),
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
