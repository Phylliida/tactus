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
//!   * `StmX::Return`    — terminator (works at top level and inside a
//!                         branch; `inside_body: true` is rejected)
//!   * `StmX::Air`, `StmX::Fuel`, `StmX::RevealString` — transparent
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

use vir::sst::{
    BndX, CallFun, Dest, Exp, ExpX, FuncCheckSst, FunctionSst, LoopInv, Par, Stm, StmX,
};
use vir::ast::{BinaryOp, Typ, UnaryOp, VarIdent};
use crate::lean_ast::{
    and_all, Binder as LBinder, BinderKind, Expr as LExpr, Tactic, Theorem,
};
use crate::to_lean_sst_expr::{sst_exp_to_ast, type_bound_predicate};
use crate::to_lean_type::{lean_name, sanitize, typ_to_expr};

// ── Support check ──────────────────────────────────────────────────────
//
// Before building any AST, we walk the whole `FuncCheckSst` and confirm
// every statement and every expression is something we know how to emit.

/// Confirm the function's body, requires, and ensures only use SST forms
/// that `sst_to_lean` currently knows how to emit.
pub fn supported_body(check: &FuncCheckSst) -> Result<(), String> {
    check_stm(&check.body)?;
    for req in check.reqs.iter() {
        check_exp(req)?;
    }
    for ens in check.post_condition.ens_exps.iter() {
        check_exp(ens)?;
    }
    Ok(())
}

fn check_stm(stm: &Stm) -> Result<(), String> {
    match &stm.x {
        StmX::Block(stms) => stms.iter().try_for_each(check_stm),
        StmX::Assign { lhs: Dest { dest, .. }, rhs } => {
            check_exp(dest)?;
            check_exp(rhs)?;
            // `walk` can only turn simple-var LHS assignments into
            // `let` bindings; anything fancier (field writes, index
            // writes, tuple destructure) would be silently dropped,
            // which is a soundness hazard. Reject upfront so the
            // user sees a clear "not yet supported" instead of a
            // spurious pass.
            if extract_simple_var(dest).is_none() {
                return Err(format!(
                    "assignment with non-simple LHS (got {:?}) is not yet supported",
                    dest.x
                ));
            }
            Ok(())
        }
        StmX::Return { ret_exp: Some(e), inside_body: false, .. } => check_exp(e),
        StmX::Return { ret_exp: None, inside_body: false, .. } => Ok(()),
        StmX::Return { inside_body: true, .. } => Err(
            "early returns from within a block are not yet supported".to_string()
        ),
        StmX::Assert(_, _, e) | StmX::Assume(e) => check_exp(e),
        StmX::AssertCompute(_, e, _) => check_exp(e),
        StmX::Air(_) | StmX::Fuel(..) | StmX::RevealString(_) => Ok(()),
        StmX::If(cond, then_stm, else_stm) => {
            check_exp(cond)?;
            check_stm(then_stm)?;
            else_stm.as_ref().map_or(Ok(()), |e| check_stm(e))
        }
        StmX::Loop {
            loop_isolation, cond, body, invs, decrease, modified_vars, ..
        } => {
            if !loop_isolation {
                return Err(
                    "non-isolated loops (loop_isolation: false) not yet supported".to_string()
                );
            }
            let Some((cond_setup, cond_exp)) = cond else {
                return Err("loops without a simple `while` condition not yet supported".to_string());
            };
            // The condition setup block must be empty — complex condition
            // expressions that desugar into statements aren't supported.
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
            // Verus may or may not populate `modified_vars` at this
            // stage of the pipeline (it's computed on the way into
            // sst_to_air, which we're not going through). We don't
            // rely on it — we recompute the set ourselves from the
            // body's `StmX::Assign` LHSs. Flag as "ignored" to make
            // the binding explicit.
            let _ = modified_vars;
            check_exp(cond_exp)?;
            check_stm(body)?;
            for inv in invs.iter() {
                check_exp(&inv.inv)?;
            }
            for d in decrease.iter() {
                check_exp(d)?;
            }
            Ok(())
        }
        StmX::Call { .. } => Err("function calls in exec fn body not yet supported".to_string()),
        StmX::BreakOrContinue { .. } => Err("break/continue not yet supported".to_string()),
        StmX::AssertBitVector { .. } => Err("assert by(bit_vector) not yet supported".to_string()),
        StmX::AssertQuery { .. } => Err("assert by(...) queries not yet supported".to_string()),
        StmX::DeadEnd(_) => Err("DeadEnd not yet supported".to_string()),
        StmX::OpenInvariant(_) => Err("OpenInvariant not yet supported".to_string()),
        StmX::ClosureInner { .. } => Err("exec closures not yet supported".to_string()),
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
            if matches!(target, CallFun::InternalFun(_)) {
                return Err("internal function calls not yet supported".to_string());
            }
            args.iter().try_for_each(check_exp)
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
/// Precondition: `supported_body(check)` returned `Ok(())`. Returns a
/// `Vec` because future slices may want to split obligations into
/// separate theorems (e.g., for per-loop diagnostics); today it's
/// always length 1 — loops contribute conjuncts to the main goal
/// rather than their own top-level theorems.
pub fn exec_fn_theorems_to_ast(fn_sst: &FunctionSst, check: &FuncCheckSst) -> Vec<Theorem> {
    let name = format!("_tactus_body_{}", lean_name(&fn_sst.x.name.path));
    let mut binders = build_param_binders(fn_sst);
    binders.extend(build_req_binders(check));

    // `check.local_decls` → type lookup for modified-var bounds when a
    // loop emits its havoc quantification.
    let type_map: std::collections::HashMap<&VarIdent, &Typ> = check.local_decls.iter()
        .map(|d| (&d.ident, &d.typ))
        .collect();

    let items = walk(&check.body, &type_map);
    let has_loop = items.iter().any(BodyItem::contains_loop);
    let goal = build_goal(
        &items,
        check.post_condition.dest.as_ref().map(|v| v.0.as_str()),
        &check.post_condition.ens_exps,
    );
    let tactic = if has_loop { loop_tactic() } else { simple_tactic() };
    vec![Theorem { name, binders, goal, tactic }]
}

/// Atomic `tactus_auto` for straight-line exec fn theorems — their
/// goals are a single chain of `let` / `→` / `∧` that omega handles
/// directly.
fn simple_tactic() -> Tactic {
    Tactic::Named("tactus_auto".to_string())
}

/// Loop theorems have a conjunctive shape `init ∧ maintain ∧ use`
/// per loop; nested / sequential loops produce nested conjunctions
/// of the same shape. Structural peeling belongs at emit time because
/// we know the shape, but we don't know a priori how deeply nested it
/// is: sequential loops chain, loops inside if-branches compose with
/// the branch's `c → …`, and nested loops stack within maintain.
///
/// `repeat'` recursively peels any top-level `∧` (via `apply
/// And.intro`) and any leading `∀` / `→` (via `intro`) across all
/// open goals until no more structural splitting is possible. The
/// resulting leaves are arithmetic; `tactus_auto` closes each.
fn loop_tactic() -> Tactic {
    // `tactus_peel` (defined in TactusPrelude.lean) recursively splits
    // `∧`s and introduces `∀` / `→` binders across all subgoals,
    // terminating naturally at arithmetic leaves. Then
    // `all_goals tactus_auto` closes each leaf. No hardcoded depth —
    // the recursion follows the goal's structure, so deeply-nested
    // loops work the same as shallow ones.
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
) -> LExpr {
    let terminator = and_all(ensures.iter().map(sst_exp_to_ast).collect());
    build_goal_with_terminator(items, ret_name, &terminator)
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
) -> LExpr {
    let Some((head, rest)) = items.split_first() else { return terminator.clone() };
    match head {
        BodyItem::Let(name, rhs) => LExpr::let_bind(
            sanitize(name), sst_exp_to_ast(rhs),
            build_goal_with_terminator(rest, ret_name, terminator),
        ),
        BodyItem::Assume(e) => LExpr::implies(
            sst_exp_to_ast(e),
            build_goal_with_terminator(rest, ret_name, terminator),
        ),
        BodyItem::Assert(e) => LExpr::and(
            sst_exp_to_ast(e),
            build_goal_with_terminator(rest, ret_name, terminator),
        ),
        BodyItem::Return(e) => match ret_name {
            Some(name) => LExpr::let_bind(sanitize(name), sst_exp_to_ast(e), terminator.clone()),
            None => terminator.clone(),
        },
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
                    build_goal_with_terminator(&then_all, ret_name, terminator),
                ),
                LExpr::implies(
                    LExpr::not(cond_ast),
                    build_goal_with_terminator(&else_all, ret_name, terminator),
                ),
            )
        }
        // WP: `I ∧ maintain ∧ havoc_continuation`. See the
        // "Loop obligations (conjunctive WP)" section of the module
        // doc for the shape.
        BodyItem::Loop { cond, invs, decrease, modified_vars, body_items } => {
            build_loop_conjunction(
                cond, invs, decrease, modified_vars, body_items,
                rest, ret_name, terminator,
            )
        }
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
) -> LExpr {
    let inv_conj = || and_all(invs.iter().map(|i| sst_exp_to_ast(&i.inv)).collect());
    let cond_ast = || sst_exp_to_ast(cond);
    let decrease_ast = || sst_exp_to_ast(decrease);

    // Init: at the loop entry (in the current enclosing context), the
    // invariant conjunction must hold.
    let init_clause = inv_conj();

    // Maintain: `∀ mod_vars, bounds → I ∧ cond →
    //              (let d_old := D; wp(body, I ∧ D < d_old))`.
    // The `let d_old := D` captures the decrease measure before the
    // body runs; the inner `D` after any mutations inside body has
    // shadowed the relevant variable will refer to the new value.
    let post_body = LExpr::and(
        inv_conj(),
        LExpr::lt(decrease_ast(), LExpr::var("_tactus_d_old")),
    );
    let maintain_body_wp = build_goal_with_terminator(body_items, ret_name, &post_body);
    let maintain_core = LExpr::let_bind("_tactus_d_old", decrease_ast(), maintain_body_wp);
    let maintain_clause = quantify_mod_vars(
        modified_vars,
        LExpr::implies(LExpr::and(inv_conj(), cond_ast()), maintain_core),
    );

    // Use / continuation: `∀ mod_vars, bounds → I ∧ ¬cond →
    //   wp(rest, outer_terminator)`.
    let rest_goal = build_goal_with_terminator(rest, ret_name, terminator);
    let use_clause = quantify_mod_vars(
        modified_vars,
        LExpr::implies(LExpr::and(inv_conj(), LExpr::not(cond_ast())), rest_goal),
    );

    LExpr::and(init_clause, LExpr::and(maintain_clause, use_clause))
}

/// `∀ (x₁ : T₁), bounds₁ → … ∀ (xₙ : Tₙ), boundsₙ → body` — wraps
/// `body` with a universal quantifier per modified variable plus its
/// type-bound hypothesis (where applicable).
fn quantify_mod_vars(
    modified_vars: &[(&VarIdent, &Typ)],
    body: LExpr,
) -> LExpr {
    use crate::lean_ast::ExprNode;
    let mut out = body;
    // Fold right-to-left so the outermost ∀ is the first modified var.
    for (ident, typ) in modified_vars.iter().rev() {
        let name = sanitize(&ident.0);
        // Optionally wrap with `bound → …` first.
        if let Some(pred) = type_bound_predicate(&LExpr::var(name.clone()), typ) {
            out = LExpr::implies(pred, out);
        }
        // Then wrap with `∀ (x : T), …`.
        let binder = LBinder {
            name: Some(name),
            ty: typ_to_expr(typ),
            kind: BinderKind::Explicit,
        };
        out = LExpr::new(ExprNode::Forall { binders: vec![binder], body: Box::new(out) });
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
}

impl<'a> BodyItem<'a> {
    /// Does this item — or any sub-item nested inside it — contain a
    /// loop? Used at theorem-emit time to pick between the plain
    /// `tactus_auto` tactic and the structural-peeling loop tactic.
    fn contains_loop(&self) -> bool {
        match self {
            BodyItem::Loop { .. } => true,
            BodyItem::IfThenElse { then_items, else_items, .. } => {
                then_items.iter().any(Self::contains_loop)
                    || else_items.iter().any(Self::contains_loop)
            }
            _ => false,
        }
    }
}

/// Flatten an SST statement tree into a sequence of `BodyItem`s. A
/// `Block` concatenates its children's flattenings; `If` / `Loop`
/// become their own composite items whose sub-bodies are recursively
/// flattened; transparent forms (`Air`, `Fuel`, `RevealString`)
/// contribute nothing; and variants rejected by `check_stm` are
/// unreachable. `type_map` is threaded through so loops can attach the
/// type of each modified variable.
fn walk<'a>(
    stm: &'a Stm,
    type_map: &std::collections::HashMap<&'a VarIdent, &'a Typ>,
) -> Vec<BodyItem<'a>> {
    match &stm.x {
        StmX::Block(stms) => stms.iter().flat_map(|s| walk(s, type_map)).collect(),
        StmX::Assign { lhs: Dest { dest, .. }, rhs } => {
            extract_simple_var(dest).map_or_else(Vec::new, |name| vec![BodyItem::Let(name, rhs)])
        }
        StmX::Assert(_, _, e) | StmX::AssertCompute(_, e, _) => vec![BodyItem::Assert(e)],
        StmX::Assume(e) => vec![BodyItem::Assume(e)],
        // `ret_exp: Some` — normal tail return (top-level or ending a
        // branch). `ret_exp: None` is a unit return; contributes nothing.
        StmX::Return { ret_exp: Some(e), .. } => vec![BodyItem::Return(e)],
        StmX::Return { ret_exp: None, .. } => Vec::new(),
        StmX::If(cond, then_stm, else_stm) => vec![BodyItem::IfThenElse {
            cond,
            then_items: walk(then_stm, type_map),
            else_items: else_stm.as_ref().map_or_else(Vec::new, |e| walk(e, type_map)),
        }],
        StmX::Loop { cond, body, invs, decrease, .. } => {
            let (_, cond_exp) = cond.as_ref().expect("check_stm guarantees Some cond");
            let decrease_exp = decrease.first().expect("check_stm guarantees one decrease");
            // Compute modified vars from the loop body's *non-init*
            // assignments — `let mut x = …` inside the body is local
            // to each iteration and shouldn't leak into the outer
            // quantification. (Nested loops use the same logic
            // recursively, so an inner loop's local decls stay local
            // even when the outer loop computes its own modified set.)
            // Verus's own `modified_vars` field isn't populated on the
            // SST we receive here; computing it ourselves works
            // regardless of pipeline stage.
            let mut mod_names: Vec<&'a VarIdent> = Vec::new();
            let mut locally_declared: std::collections::HashSet<&'a VarIdent> =
                std::collections::HashSet::new();
            collect_modifications(body, &mut locally_declared, &mut mod_names);
            let modified_vars: Vec<(&'a VarIdent, &'a Typ)> = mod_names.into_iter()
                .filter_map(|id| type_map.get(id).map(|typ| (id, *typ)))
                .collect();
            vec![BodyItem::Loop {
                cond: cond_exp,
                invs: &invs[..],
                decrease: decrease_exp,
                modified_vars,
                body_items: walk(body, type_map),
            }]
        }
        // Transparent in SST: contribute nothing to the WP goal.
        StmX::Air(_) | StmX::Fuel(..) | StmX::RevealString(_) => Vec::new(),
        // All rejected by `check_stm`. Reaching them here means the
        // support-check and the walker fell out of sync.
        StmX::Call { .. }
        | StmX::BreakOrContinue { .. }
        | StmX::AssertBitVector { .. }
        | StmX::AssertQuery { .. }
        | StmX::DeadEnd(_)
        | StmX::OpenInvariant(_)
        | StmX::ClosureInner { .. } => unreachable!(
            "sst_to_lean::walk: {:?} should have been rejected by supported_body",
            stm.x
        ),
    }
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
    locally_declared: &mut std::collections::HashSet<&'a VarIdent>,
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
            collect_modifications(t, locally_declared, out);
            if let Some(e) = e { collect_modifications(e, locally_declared, out); }
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
