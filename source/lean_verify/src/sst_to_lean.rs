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
    BndX, CallFun, Dest, Exp, ExpX, FuncCheckSst, FunctionSst, LoopInv, Par, Stm, StmX,
};
use vir::ast::{BinaryOp, Fun, FunctionX, KrateX, Typ, UnaryOp, UnaryOpr, VarIdent};
use crate::lean_ast::{
    and_all, Binder as LBinder, BinderKind, Expr as LExpr, Tactic, Theorem,
};
use crate::to_lean_expr::vir_expr_to_ast;
use crate::to_lean_sst_expr::{sst_exp_to_ast, type_bound_predicate};
use crate::to_lean_type::{lean_name, sanitize, typ_to_expr};

/// Lookup table from callee `Fun` to its VIR-AST `FunctionX`. Used by
/// `BodyItem::Call` to inline a callee's `requires` / `ensures` at the
/// call site. Callee's spec lives on `FunctionX` (VIR-AST), not on
/// its `FunctionSst`, so the map points at the AST form.
pub type FnMap<'a> = HashMap<&'a Fun, &'a FunctionX>;

/// Shared context threaded through the WP builder. Collects the
/// per-verification-unit state that nearly every walker / builder
/// needs — the callee lookup (for inlining call specs) and the local
/// declaration types (for loop modified-var quantification). Future
/// additions — source spans, current-fn name, ret binder — plug into
/// this struct instead of growing every function signature.
pub struct WpCtx<'a> {
    pub fn_map: FnMap<'a>,
    pub type_map: HashMap<&'a VarIdent, &'a Typ>,
}

impl<'a> WpCtx<'a> {
    /// Build the context for verifying `check` against `krate`.
    /// `fn_map` is from the whole-krate function list; `type_map` is
    /// from the check's own local declarations.
    pub fn new(krate: &'a KrateX, check: &'a FuncCheckSst) -> Self {
        let fn_map = krate.functions.iter().map(|f| (&f.x.name, &f.x)).collect();
        let type_map = check.local_decls.iter().map(|d| (&d.ident, &d.typ)).collect();
        Self { fn_map, type_map }
    }
}

// ── Support check (helpers) ────────────────────────────────────────────
//
// The main validation is fused into `walk` below — a single pass that
// both checks shape constraints and builds the `BodyItem` sequence. The
// helpers here are the reusable bits.

/// Detect a call that's been through Verus's zero-arg-fn desugaring.
///
/// `ast_simplify` injects a dummy `Const(0)` arg at the call site for
/// fns that have no user-visible params / type params (see
/// `ast_simplify.rs:528`). Parallel desugaring injects a matching
/// `no%param` param into the callee's `params` — BUT that second half
/// only fires on `simplify_krate`, which runs *after* `self.vir_crate`
/// is stored (`verifier.rs:3163`). `WpCtx::new` sees the pre-simplify
/// `FunctionX`, so its `params` for a zero-arg callee is empty.
///
/// The asymmetry means: at a zero-arg call site, `args.len() == 1`
/// (the injected `Const(0)`) but `callee.params.len() == 0`. We detect
/// this shape explicitly and skip the synthetic arg so zip alignment
/// stays correct.
fn is_zero_arg_desugared(callee: &FunctionX) -> bool {
    use vir::ast::ItemKind;
    callee.params.is_empty()
        && callee.typ_params.is_empty()
        && !matches!(callee.item_kind, ItemKind::Const | ItemKind::Static)
        && !callee.attrs.broadcast_forall
}

/// Iterate over the callee's real (user-visible) parameters. Since
/// our `FnMap` uses the pre-simplify `FunctionX`, synthetic params
/// haven't been injected yet — so this is just `callee.params.iter()`.
/// The wrapper exists for symmetry with `skip_zero_arg_dummy` on the
/// args side and for future expansion if we ever route through a
/// post-simplify form.
fn real_params(callee: &FunctionX) -> impl Iterator<Item = &vir::ast::Param> {
    callee.params.iter()
}

/// How many leading args to skip to align with `real_params(callee)`.
/// See `is_zero_arg_desugared` for the one case that's nonzero today.
fn arg_skip(callee: &FunctionX) -> usize {
    if is_zero_arg_desugared(callee) { 1 } else { 0 }
}

/// Does this type bottom out at `TypX::Int(_)` once transparent
/// wrappers (`Boxed`, `Decorate`) are peeled? Mirrors
/// `vir::recursion::height_is_int` — for those types the `height`
/// encoding is identity and `CheckDecreaseHeight` lowers to a plain
/// `0 ≤ cur ∧ cur < prev` check (see `to_lean_sst_expr.rs`).
fn is_int_height(typ: &Typ) -> bool {
    match &**typ {
        vir::ast::TypX::Int(_) => true,
        vir::ast::TypX::Boxed(inner) | vir::ast::TypX::Decorate(_, _, inner) => {
            is_int_height(inner)
        }
        _ => false,
    }
}

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

fn check_exp(e: &Exp) -> Result<(), String> {
    match &e.x {
        ExpX::Const(_) | ExpX::Var(_) | ExpX::VarLoc(_) | ExpX::VarAt(..)
        | ExpX::StaticVar(_) | ExpX::ExecFnByName(_) | ExpX::NullaryOpr(_) => Ok(()),
        ExpX::Unary(op, inner) => match op {
            UnaryOp::Not
            | UnaryOp::Clip { .. }
            | UnaryOp::CoerceMode { .. }
            | UnaryOp::Trigger(_) => check_exp(inner),
            other => Err(format!("unsupported unary op: {:?}", other)),
        },
        ExpX::UnaryOpr(_, inner) => check_exp(inner),
        ExpX::Binary(op, l, r) => match op {
            BinaryOp::HeightCompare { .. }
            | BinaryOp::Index(_, _)
            | BinaryOp::StrGetChar
            | BinaryOp::IeeeFloat(_) => Err(format!("unsupported binary op: {:?}", op)),
            _ => { check_exp(l)?; check_exp(r) }
        },
        ExpX::BinaryOpr(_, l, r) => { check_exp(l)?; check_exp(r) }
        ExpX::If(c, t, e) => { check_exp(c)?; check_exp(t)?; check_exp(e) }
        ExpX::Call(target, _, args) => {
            use vir::sst::InternalFun;
            match target {
                // `CheckDecreaseHeight` is Verus's auto-injected
                // termination obligation for recursive calls. We
                // support int-typed decreases (the common case) and
                // lower in `sst_exp_to_ast`. Non-int decreases would
                // need a Lean `height` function encoding — deferred.
                CallFun::InternalFun(InternalFun::CheckDecreaseHeight) => {
                    if args.len() != 3 {
                        return Err(format!(
                            "CheckDecreaseHeight expects 3 args (cur, prev, otherwise), got {}",
                            args.len()
                        ));
                    }
                    if !is_int_height(&args[0].typ) {
                        return Err(format!(
                            "recursive call termination check with non-int decrease \
                             (type {:?}) not yet supported — only int decreases work today",
                            args[0].typ
                        ));
                    }
                    args.iter().try_for_each(check_exp)
                }
                CallFun::InternalFun(_) => Err(
                    "internal function calls not yet supported".to_string()
                ),
                CallFun::Fun(_, _) | CallFun::Recursive(_) => {
                    args.iter().try_for_each(check_exp)
                }
            }
        }
        ExpX::Bind(bnd, body) => {
            match &bnd.x {
                BndX::Let(binders) => binders.iter().try_for_each(|b| check_exp(&b.a))?,
                BndX::Quant(..) | BndX::Lambda(..) => {}
                BndX::Choose(_, _, cond) => check_exp(cond)?,
            }
            check_exp(body)
        }
        ExpX::WithTriggers(_, inner) | ExpX::Loc(inner) => check_exp(inner),
        ExpX::Ctor(..) => Err("datatype constructors not yet supported in exec fns".to_string()),
        ExpX::CallLambda(..) => Err("closure calls not yet supported in exec fns".to_string()),
        ExpX::ArrayLiteral(_) => Err("array literals not yet supported in exec fns".to_string()),
        ExpX::Old(..) => Err("`old(...)` not yet supported in exec fns".to_string()),
        ExpX::Interp(_) => Err(
            "Interp nodes should never escape the interpreter (internal bug)".to_string()
        ),
        ExpX::FuelConst(_) => Err("FuelConst not yet supported".to_string()),
    }
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
    let ctx = WpCtx::new(krate, check);

    // Expressions in requires/ensures aren't walked (they aren't
    // statements), so validate them separately here.
    for req in check.reqs.iter() {
        check_exp(req)?;
    }
    for ens in check.post_condition.ens_exps.iter() {
        check_exp(ens)?;
    }

    let name = format!("_tactus_body_{}", lean_name(&fn_sst.x.name.path));
    let mut binders = build_param_binders(fn_sst);
    binders.extend(build_req_binders(check));

    let items = walk(&check.body, &ctx)?;
    let has_loop_or_call = items.iter().any(BodyItem::needs_peel);
    let goal = build_goal(
        &items,
        check.post_condition.dest.as_ref().map(|v| v.0.as_str()),
        &check.post_condition.ens_exps,
        &ctx,
    );
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

// ── Goal builder ───────────────────────────────────────────────────────

/// Construct the theorem goal by folding body items in source order. See
/// the module doc for the WP rules — each item wraps the goal built from
/// the remainder of the body. `Return` terminates: items after it are
/// dropped because they're unreachable.
///
/// Thin wrapper around `build_goal_with_terminator`; the terminator for
/// the top-level call is the ensures conjunction.
fn build_goal(
    items: &[BodyItem<'_>],
    ret_name: Option<&str>,
    ensures: &[Exp],
    ctx: &WpCtx<'_>,
) -> LExpr {
    let terminator = and_all(ensures.iter().map(sst_exp_to_ast).collect());
    build_goal_with_terminator(items, ret_name, &terminator, ctx)
}

/// The real WP builder, parameterized on what the continuation ends in.
///
/// At the top of the body, `terminator` is the ensures conjunction and
/// the function acts like textbook WP. Inside a loop's maintain clause,
/// `terminator` is `I ∧ D < d_old` — so the loop's body walker can
/// reuse all of the same item-handling logic with a different terminal
/// goal. One function, one set of rules.
///
/// The base case (empty items) returns a clone of the terminator.
/// `Return(e)` with a named dest emits `let <ret> := e; <terminator>`;
/// without a dest (unit return in a unit fn), the return value is
/// dropped — it's always `()`.
fn build_goal_with_terminator(
    items: &[BodyItem<'_>],
    ret_name: Option<&str>,
    terminator: &LExpr,
    ctx: &WpCtx<'_>,
) -> LExpr {
    let Some((head, rest)) = items.split_first() else { return terminator.clone() };
    match head {
        // An `ExpX::If` on the RHS of a let (or as the returned value,
        // below) is a value whose structure omega can't reason about —
        // omega handles `∧`/`→`/`¬` over linear arith but not
        // `if c then a else b` inside the goal. Lift it out: split
        // `let x := if c then a else b; rest` into
        // `(c → let x := a; rest) ∧ (¬c → let x := b; rest)`.
        // Recursion handles nested if-exprs.
        BodyItem::Let(name, rhs) => lift_if_value(rhs, &|rhs_ast| {
            LExpr::let_bind(
                sanitize(name), rhs_ast,
                build_goal_with_terminator(rest, ret_name, terminator, ctx),
            )
        }),
        BodyItem::Assume(e) => LExpr::implies(
            sst_exp_to_ast(e),
            build_goal_with_terminator(rest, ret_name, terminator, ctx),
        ),
        BodyItem::Assert(e) => LExpr::and(
            sst_exp_to_ast(e),
            build_goal_with_terminator(rest, ret_name, terminator, ctx),
        ),
        BodyItem::Return(e) => lift_if_value(e, &|e_ast| match ret_name {
            Some(name) => LExpr::let_bind(sanitize(name), e_ast, terminator.clone()),
            None => terminator.clone(),
        }),
        // WP: `(c → wp(then ++ rest)) ∧ (¬c → wp(else ++ rest))`. `rest`
        // duplicates syntactically — see DESIGN.md "Known codegen-
        // complexity trade-offs". If a branch ends in `Return`, its
        // continuation terminates there and `rest` is appended but
        // ignored.
        BodyItem::IfThenElse { cond, then_items, else_items } => {
            let then_all: Vec<BodyItem<'_>> =
                then_items.iter().chain(rest.iter()).cloned().collect();
            let else_all: Vec<BodyItem<'_>> =
                else_items.iter().chain(rest.iter()).cloned().collect();
            let cond_ast = sst_exp_to_ast(cond);
            LExpr::and(
                LExpr::implies(
                    cond_ast.clone(),
                    build_goal_with_terminator(&then_all, ret_name, terminator, ctx),
                ),
                LExpr::implies(
                    LExpr::not(cond_ast),
                    build_goal_with_terminator(&else_all, ret_name, terminator, ctx),
                ),
            )
        }
        // WP: `I ∧ maintain ∧ havoc_continuation`. See the
        // "Loop obligations (conjunctive WP)" section of the module
        // doc for the shape.
        BodyItem::Loop { cond, invs, decrease, modified_vars, body_items } => {
            build_loop_conjunction(
                cond, invs, decrease, modified_vars, body_items,
                rest, ret_name, terminator, ctx,
            )
        }
        // WP: `requires ∧ (∀ ret, bound(ret) → ensures(ret) →
        // wp(rest))`. Inlines the callee's spec instead of emitting
        // a Lean definition for it. See `build_call_conjunction`.
        BodyItem::Call { callee, args, dest } => {
            build_call_conjunction(callee, args, *dest, rest, ret_name, terminator, ctx)
        }
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
fn build_loop_conjunction(
    cond: &Exp,
    invs: &[LoopInv],
    decrease: &Exp,
    modified_vars: &[(&VarIdent, &Typ)],
    body_items: &[BodyItem<'_>],
    rest: &[BodyItem<'_>],
    ret_name: Option<&str>,
    terminator: &LExpr,
    ctx: &WpCtx<'_>,
) -> LExpr {
    let inv_conj = || and_all(invs.iter().map(|i| sst_exp_to_ast(&i.inv)).collect());
    let cond_ast = || sst_exp_to_ast(cond);
    let decrease_ast = || sst_exp_to_ast(decrease);

    // Init: at the loop entry (in the current enclosing context), the
    // invariant conjunction must hold.
    let init_clause = inv_conj();

    // Maintain: `∀ mod_vars, bounds → I ∧ cond →
    //              (let _tactus_d_old := D; wp(body, I ∧ D < _tactus_d_old))`.
    // The let-binding captures the decrease measure before the body
    // runs; the inner `D` after body mutations shadow the relevant
    // variable refers to the new value.
    //
    // We reuse the literal name `_tactus_d_old` for every loop. For
    // nested loops this means the inner `let _tactus_d_old := D_inner`
    // shadows the outer's binding — which works out because the
    // shadow is confined to the inner's maintain clause (its own
    // conjunct), and the outer's reference to `_tactus_d_old` lives
    // in the outer's maintain (a different conjunct). See DESIGN.md
    // "_tactus_d_old aliasing across nested loops" — a gensym'd
    // name per loop would make the scoping more obvious but isn't
    // needed for correctness.
    let post_body = LExpr::and(
        inv_conj(),
        LExpr::lt(decrease_ast(), LExpr::var("_tactus_d_old")),
    );
    let maintain_body_wp = build_goal_with_terminator(body_items, ret_name, &post_body, ctx);
    let maintain_core = LExpr::let_bind("_tactus_d_old", decrease_ast(), maintain_body_wp);
    let maintain_clause = quantify_mod_vars(
        modified_vars,
        LExpr::implies(LExpr::and(inv_conj(), cond_ast()), maintain_core),
    );

    // Use / continuation: `∀ mod_vars, bounds → I ∧ ¬cond →
    //   wp(rest, outer_terminator)`.
    let rest_goal = build_goal_with_terminator(rest, ret_name, terminator, ctx);
    let use_clause = quantify_mod_vars(
        modified_vars,
        LExpr::implies(LExpr::and(inv_conj(), LExpr::not(cond_ast())), rest_goal),
    );

    LExpr::and(init_clause, LExpr::and(maintain_clause, use_clause))
}

/// Emit the WP conjunction contributed by a single function call.
///
/// For `let dest = callee(arg1, arg2, …)`:
///
/// ```
/// (let p1 := arg1; let p2 := arg2; …; requires_conj)
/// ∧ (∀ (ret : RetT), h_ret_bound(ret) →
///      (let p1 := arg1; let p2 := arg2; …; ensures_conj_using_ret) →
///      (let dest := ret; wp(rest, outer_terminator)))
/// ```
///
/// Parameter substitution is done via Lean `let`-bindings rather than
/// rewriting the callee's spec at the SST level — same trick as
/// `_tactus_d_old`, cheap and obviously correct.
///
/// `ret` is the callee's declared return-var name (pulled from
/// `FunctionX::ret`). If the callee returns unit or the call discards
/// its result, the `∀` is skipped and `dest` isn't bound.
///
/// Termination obligations (for recursive calls, including mutual)
/// are injected upstream by Verus's `recursion` pass as
/// `StmX::Assert(InternalFun::CheckDecreaseHeight)` — they appear
/// before the `StmX::Call` in the SST and flow through `walk` as
/// normal assert items. The Lean lowering lives in
/// `to_lean_sst_expr::sst_exp_to_ast`.
fn build_call_conjunction(
    callee: &FunctionX,
    args: &[&Exp],
    dest: Option<(&VarIdent, &Typ)>,
    rest: &[BodyItem<'_>],
    ret_name: Option<&str>,
    terminator: &LExpr,
    ctx: &WpCtx<'_>,
) -> LExpr {
    // Strip any `ast_simplify`-injected dummy arg so zip aligns with
    // `callee.params`. `walk_call` already verified the counts after
    // the strip, so zipping cannot silently truncate. Unconditional
    // assert is defense-in-depth: if a future refactor produces
    // `BodyItem::Call` through a different path, this fires
    // immediately rather than binding wrong variables silently.
    let real_params_vec: Vec<_> = real_params(callee).collect();
    let skip = arg_skip(callee);
    let real_arg_refs: &[&Exp] = &args[skip..];
    assert_eq!(
        real_params_vec.len(), real_arg_refs.len(),
        "callee real-param count {} != caller real-arg count {} for {:?} — \
         walk_call should have rejected this",
        real_params_vec.len(), real_arg_refs.len(), callee.name.path,
    );

    // Render each real arg's Lean expression once; reuse across the
    // requires wrap and the ensures wrap.
    let arg_asts: Vec<LExpr> = real_arg_refs.iter().map(|a| sst_exp_to_ast(a)).collect();

    // Wrap a goal `inner` with `let p1 := arg1; let p2 := arg2; …;
    // inner` so the callee's param names resolve to the caller's
    // argument expressions without needing a tree-rewrite pass.
    let wrap_with_arg_lets = |inner: LExpr| -> LExpr {
        real_params_vec.iter().zip(arg_asts.iter()).rev().fold(inner, |acc, (p, arg_ast)| {
            LExpr::let_bind(sanitize(&p.x.name.0), arg_ast.clone(), acc)
        })
    };

    let requires_conj = and_all(
        callee.require.iter().map(|e| vir_expr_to_ast(e)).collect()
    );
    let ensures_conj = and_all(
        callee.ensure.0.iter().map(|e| vir_expr_to_ast(e)).collect()
    );

    let requires_clause = wrap_with_arg_lets(requires_conj);

    // Continuation under a havoc'd return value. If the callee's
    // return type is a tuple or unit with no declared ret name,
    // skip the ∀ and treat the ensures as a flat hypothesis.
    let ret = &callee.ret.x;
    let ret_name_cal = sanitize(&ret.name.0);
    let ret_typ = typ_to_expr(&ret.typ);
    let continuation_under_ret = {
        let rest_goal = build_goal_with_terminator(rest, ret_name, terminator, ctx);
        // If the caller has a destination, bind `let dest := <ret>;
        // rest_goal` inside the ∀. Otherwise rest sees the call as
        // having no bound value.
        let bound_rest = match dest {
            Some((dest_ident, _)) => LExpr::let_bind(
                sanitize(&dest_ident.0),
                LExpr::var(ret_name_cal.clone()),
                rest_goal,
            ),
            None => rest_goal,
        };
        // ensures(ret) → bound_rest
        let ensures_impl = LExpr::implies(wrap_with_arg_lets(ensures_conj), bound_rest);
        // Optionally wrap with `h_bound(ret) → …`.
        let bounded_impl = match type_bound_predicate(&LExpr::var(ret_name_cal.clone()), &ret.typ) {
            Some(pred) => LExpr::implies(pred, ensures_impl),
            None => ensures_impl,
        };
        // ∀ ret : RetTyp, ...
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

// ── Body walk ──────────────────────────────────────────────────────────

#[derive(Clone)]
enum BodyItem<'a> {
    Let(&'a str, &'a Exp),
    Assert(&'a Exp),
    Assume(&'a Exp),
    /// Terminator: wraps the ensures as `let <ret> := e; <ensures>` and
    /// discards any subsequent items in the same sequence. Populated
    /// from `StmX::Return { ret_exp: Some(_), inside_body: false }`.
    Return(&'a Exp),
    /// `if <cond> { <then_items> } else { <else_items> }` — both branches
    /// are already flattened into `BodyItem` sequences. Either branch
    /// may end with a `Return` (handled by `build_goal`).
    IfThenElse {
        cond: &'a Exp,
        then_items: Vec<BodyItem<'a>>,
        else_items: Vec<BodyItem<'a>>,
    },
    /// `while <cond> invariant <invs> decreases <decrease> { <body_items> }`.
    /// Loop bodies are flattened through `Block` composition; nested
    /// loops appear as inner `Loop` variants and compose naturally
    /// through `build_goal`. Modified vars are computed from the
    /// body's assignments and resolved to types at walk time so
    /// `build_goal` doesn't need the type map.
    ///
    /// `invs` is borrowed directly from the SST's `LoopInvs` (an
    /// `Arc<Vec<LoopInv>>`) — no intermediate `Vec`. `build_goal`
    /// pulls the `.inv` field off each `LoopInv` when it needs the
    /// invariant expression.
    Loop {
        cond: &'a Exp,
        invs: &'a [LoopInv],
        decrease: &'a Exp,
        modified_vars: Vec<(&'a VarIdent, &'a Typ)>,
        body_items: Vec<BodyItem<'a>>,
    },
    /// `foo(arg1, arg2, …)` optionally binding the result to a local.
    /// `callee` is the full VIR-AST `FunctionX` so `build_goal` has
    /// the requires / ensures / param list / return var all in one
    /// place. Args are borrowed from the SST.
    ///
    /// **Termination obligations for recursive calls** are handled
    /// upstream by Verus itself (`vir::recursion`): right before each
    /// recursive call, Verus inserts a `StmX::Assert(…)` containing
    /// an `ExpX::Call(InternalFun::CheckDecreaseHeight, …)` that
    /// encodes "callee's decrease strictly decreases from caller's."
    /// So we get termination for free — including mutual recursion
    /// across a whole SCC — as long as our SST translator knows how
    /// to lower `CheckDecreaseHeight`. See `sst_exp_to_ast`.
    Call {
        callee: &'a FunctionX,
        args: Vec<&'a Exp>,
        /// `Some((name, typ))` for `let x = foo(…)`; `None` for
        /// discarded or unit return.
        dest: Option<(&'a VarIdent, &'a Typ)>,
    },
}

impl<'a> BodyItem<'a> {
    /// Does this item — or any sub-item nested inside it — produce a
    /// goal shape that needs structural peeling? Loops, calls (which
    /// introduce `∀ result, …`), and `IfThenElse` wrapping either
    /// qualify; flat Let/Assert/Assume/Return chains don't. Used at
    /// theorem-emit time to pick between plain `tactus_auto` and the
    /// `tactus_peel`-prefixed loop tactic.
    fn needs_peel(&self) -> bool {
        match self {
            BodyItem::Loop { .. } | BodyItem::Call { .. } => true,
            BodyItem::IfThenElse { then_items, else_items, .. } => {
                then_items.iter().any(Self::needs_peel)
                    || else_items.iter().any(Self::needs_peel)
            }
            _ => false,
        }
    }
}

/// Flatten an SST statement tree into a sequence of `BodyItem`s, while
/// simultaneously validating every shape we see. A `Block` concatenates
/// its children's flattenings; `If` / `Loop` become their own composite
/// items whose sub-bodies are recursively flattened; transparent forms
/// (`Air`, `Fuel`, `RevealString`) contribute nothing; and any variant
/// we don't know how to emit — plus any disallowed shape nested inside
/// one we do — becomes an `Err("… not yet supported")` that bubbles up
/// through the call chain.
///
/// Fusing validation with transformation means the "supported_body ran
/// first" precondition is enforced by construction: there's no way to
/// reach the body of `exec_fn_theorems_to_ast` with unchecked `BodyItem`s
/// because `walk` is the only producer. Previously this was a runtime
/// invariant guarded by `.expect`; now it's a type-level one guarded by
/// `Result`.
///
/// `ctx.type_map` is used by loop walking to attach the type of each
/// modified variable; `ctx.fn_map` is used by call walking to look up
/// the callee's `FunctionX`. Termination obligations for recursive
/// calls are emitted upstream by Verus as `StmX::Assert(InternalFun::
/// CheckDecreaseHeight)` — they flow through here as ordinary
/// asserts; `sst_exp_to_ast` handles the Lean-level lowering.
fn walk<'a>(
    stm: &'a Stm,
    ctx: &WpCtx<'a>,
) -> Result<Vec<BodyItem<'a>>, String> {
    match &stm.x {
        StmX::Block(stms) => {
            let mut out: Vec<BodyItem<'a>> = Vec::new();
            for s in stms.iter() {
                out.extend(walk(s, ctx)?);
            }
            Ok(out)
        }
        StmX::Assign { lhs: Dest { dest, .. }, rhs } => {
            check_exp(dest)?;
            check_exp(rhs)?;
            // `BodyItem::Let` needs a simple-var LHS; anything fancier
            // (field writes, index writes, tuple destructure) would
            // need a different WP shape. Reject upfront so the user
            // sees a clear "not yet supported" instead of a silent
            // drop.
            let Some(name) = extract_simple_var(dest) else {
                return Err(format!(
                    "assignment with non-simple LHS (got {:?}) is not yet supported",
                    dest.x
                ));
            };
            Ok(vec![BodyItem::Let(name, rhs)])
        }
        StmX::Assert(_, _, e) | StmX::AssertCompute(_, e, _) => {
            check_exp(e)?;
            Ok(vec![BodyItem::Assert(e)])
        }
        StmX::Assume(e) => {
            check_exp(e)?;
            Ok(vec![BodyItem::Assume(e)])
        }
        // `inside_body` distinguishes a tail return from an "early"
        // return (one with code after it in the same block). Both
        // exit the fn; `build_goal_with_terminator` handles them
        // uniformly — each `Return` terminates its item list and
        // subsequent items get dropped on that branch.
        StmX::Return { ret_exp: Some(e), .. } => {
            check_exp(e)?;
            Ok(vec![BodyItem::Return(e)])
        }
        StmX::Return { ret_exp: None, .. } => Ok(Vec::new()),
        StmX::If(cond, then_stm, else_stm) => {
            check_exp(cond)?;
            let then_items = walk(then_stm, ctx)?;
            let else_items = match else_stm {
                Some(e) => walk(e, ctx)?,
                None => Vec::new(),
            };
            Ok(vec![BodyItem::IfThenElse { cond, then_items, else_items }])
        }
        StmX::Call { .. } => walk_call(stm, ctx),
        StmX::Loop { .. } => walk_loop(stm, ctx),
        // Transparent in SST: contribute nothing to the WP goal.
        StmX::Air(_) | StmX::Fuel(..) | StmX::RevealString(_) => Ok(Vec::new()),
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

/// Validate and build a `BodyItem::Call`. Destructures every field
/// explicitly (no `..`) so any future Verus field addition forces a
/// compile error here.
fn walk_call<'a>(
    stm: &'a Stm,
    ctx: &WpCtx<'a>,
) -> Result<Vec<BodyItem<'a>>, String> {
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
        unreachable!("walk_call called on non-Call statement");
    };
    // Reject every known "dispatch isn't just a direct call" shape.
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
    // Param/arg count MUST match after stripping any `ast_simplify`-
    // injected dummy arg. If Verus ever changes its arg-passing
    // convention so this invariant breaks, we want a clean rejection
    // here — not a silent zip-to-shorter in `build_call_conjunction`,
    // which would bind the wrong variables and produce a spec that
    // isn't the callee's.
    let skip = arg_skip(callee);
    if args.len() < skip {
        return Err(format!(
            "callee `{:?}` looks zero-arg-desugared but call site passes only {} arg(s)",
            fun.path, args.len(),
        ));
    }
    let real_param_count = real_params(callee).count();
    let real_arg_count = args.len() - skip;
    if real_param_count != real_arg_count {
        return Err(format!(
            "callee `{:?}` has {} real param(s) but call site passes {} real arg(s) \
             (raw args: {}; dummy skip: {}) — arg-passing convention may be \
             out of sync; this would bind wrong variables if we proceeded",
            fun.path, real_param_count, real_arg_count, args.len(), skip,
        ));
    }
    for a in args.iter() {
        // `ExpX::Loc` marks `&mut` args (even under transparent
        // wrappers). We only support by-value today; `&mut` would
        // need havoc-after-call semantics.
        if contains_loc(a) {
            return Err(
                "calls with `&mut` arguments are not yet supported".to_string()
            );
        }
        check_exp(a)?;
    }
    let arg_refs: Vec<&'a Exp> = args.iter().collect();
    // Extract the caller's destination var name + type. `None` if the
    // call discards its result (`foo(…);` without `let x =`).
    let bound_dest: Option<(&'a VarIdent, &'a Typ)> = dest.as_ref().and_then(|d| {
        let ident = extract_simple_var_ident(&d.dest)?;
        let typ = ctx.type_map.get(ident).copied()?;
        Some((ident, typ))
    });
    // NOTE: termination obligation is emitted upstream by Verus's
    // own `recursion::check_recursive_function` pass, which inserts a
    // `StmX::Assert` wrapping `InternalFun::CheckDecreaseHeight`
    // right before each recursive call (including mutual recursion
    // across an SCC). Our walk sees that Assert as a normal
    // `BodyItem::Assert`; the conjunct appears in the WP goal and
    // `tactus_auto` / the user must discharge it. See
    // `to_lean_sst_expr::call_fun_to_ast`'s `CheckDecreaseHeight`
    // arm for the Lean lowering.
    Ok(vec![BodyItem::Call {
        callee,
        args: arg_refs,
        dest: bound_dest,
    }])
}

/// Validate and build a `BodyItem::Loop`. See the module doc for the
/// shape restrictions this enforces.
fn walk_loop<'a>(
    stm: &'a Stm,
    ctx: &WpCtx<'a>,
) -> Result<Vec<BodyItem<'a>>, String> {
    let StmX::Loop {
        loop_isolation, cond, body, invs, decrease, modified_vars: _, ..
    } = &stm.x else {
        unreachable!("walk_loop called on non-loop statement");
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
    // `let mut x = …` inside the body is local to each iteration and
    // shouldn't leak into the outer quantification. Nested loops use
    // the same logic recursively, so an inner loop's local decls stay
    // local even when the outer loop computes its own modified set.
    let mut mod_names: Vec<&'a VarIdent> = Vec::new();
    let mut locally_declared: HashSet<&'a VarIdent> = HashSet::new();
    collect_modifications(body, &mut locally_declared, &mut mod_names);
    let modified_vars: Vec<(&'a VarIdent, &'a Typ)> = mod_names.into_iter()
        .filter_map(|id| ctx.type_map.get(id).map(|typ| (id, *typ)))
        .collect();

    let body_items = walk(body, ctx)?;

    Ok(vec![BodyItem::Loop {
        cond: cond_exp,
        invs: &invs[..],
        decrease: decrease_exp,
        modified_vars,
        body_items,
    }])
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
