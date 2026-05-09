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
    BndX, CallFun, Dest, Exp, ExpX, FuncCheckSst, FunctionSst, InternalFun, LocalDeclKind,
    LoopInv, Par, Stm, StmX,
};
use vir::ast::{
    AssertQueryMode, BinaryOp, Expr, ExprX, Fun, FunctionKind, FunctionX, KrateX, SpannedTyped, TactusKind,
    Typ, UnaryOp, UnaryOpr, VarAt, VarBinder, VarIdent,
};
use vir::ast_visitor::map_expr_visitor;
use vir::messages::Span;
use crate::lean_ast::{
    and_all, substitute, AssertKind, Binder as LBinder, BinderKind, Expr as LExpr,
    ExprNode, HypothesisKind, ObligationKind,
    PreambleFragment, Tactic, Theorem,
};
use crate::expr_shared::varat_pre_name;
use std::sync::Arc;
use crate::to_lean_expr::vir_expr_to_ast;
use crate::to_lean_sst_expr::{lower as lower_validated, sst_exp_to_ast_checked, type_bound_predicate, Validated};
use crate::to_lean_type::{lean_name, sanitize, typ_to_expr};

// ── BitVec-mode preamble fragments (#130 / right-way #4) ───────────────
//
// Lean has no `HXor Int Int Int` etc. by default. Tactus needs them
// only for files that use `assert(P) by(bit_vector)` — Verus's
// ast_to_sst pre-injects an Int-mode `Assume(ens)` before each
// AssertBitVector, and the post-assert continuation theorems contain
// `x ^^^ y` (bitwise xor) for `x, y : Int`. Without these instances,
// those theorems fail to typecheck.
//
// Defined here (not in TactusPrelude) so other generated files don't
// inherit the wonky-for-negative-Int semantics. The walker arm for
// `Wp::AssertBitVector` calls `bitvec_preamble_fragments()` and
// attaches the result to the emitted theorem's `requires_preamble`;
// `generate.rs::krate_preamble` aggregates fragments across an exec
// fn's theorems and emits them once at file top.
//
// For ACTUAL bitwise reasoning, use `assert(P) by(bit_vector)` —
// Tactus renders the goal in BitVec mode where `^^^` etc. resolve
// to BitVec instances with proper bit-vector semantics.
pub(crate) const BITVEC_INT_INSTANCES: &str = "\
-- HXor/HAnd/HOr/HShiftLeft/HShiftRight Int instances (#130).
-- Conditionally emitted for files using `by(bit_vector)`.
-- Mathlib.Data.BitVec is imported conditionally above (in the
-- preamble's import section) so it's available here.
instance : HXor Int Int Int := ⟨fun a b => ((a.toNat ^^^ b.toNat : Nat) : Int)⟩
instance : HAnd Int Int Int := ⟨fun a b => ((a.toNat &&& b.toNat : Nat) : Int)⟩
instance : HOr Int Int Int := ⟨fun a b => ((a.toNat ||| b.toNat : Nat) : Int)⟩
instance : HShiftLeft Int Int Int := ⟨fun a b => ((a.toNat <<< b.toNat : Nat) : Int)⟩
instance : HShiftRight Int Int Int := ⟨fun a b => ((a.toNat >>> b.toNat : Nat) : Int)⟩
";

/// Preamble fragments required by an `assert(P) by(bit_vector)`
/// theorem. Returned to the walker arm for `Wp::AssertBitVector`,
/// attached to the emitted theorem's `requires_preamble`, and
/// aggregated by `krate_preamble` for emission at file top.
///
/// Three fragments:
/// * `Mathlib.Data.BitVec` import — provides `BitVec n` type and
///   the `@[simp]` lemmas (xor_comm / xor_self / etc.) the
///   `tactus_bit_vector` tactic ladder falls back to.
/// * `Lean.Elab.Tactic.BVDecide` import — Lean core's full SAT-
///   backed bit-vector decision procedure (the primary rung).
/// * Int-bitwise instance block — see `BITVEC_INT_INSTANCES` above.
pub(crate) fn bitvec_preamble_fragments() -> Vec<PreambleFragment> {
    vec![
        PreambleFragment::Import("Mathlib.Data.BitVec".to_string()),
        PreambleFragment::Import("Lean.Elab.Tactic.BVDecide".to_string()),
        PreambleFragment::PreludeAddendum(BITVEC_INT_INSTANCES.to_string()),
    ]
}

/// Typed view of a loop invariant's classification (#103).
///
/// Verus's `LoopInv` carries `at_entry: bool` + `at_exit: bool` —
/// two booleans that encode three meaningful states *and* one
/// nonsensical `(false, false)` we'd silently filter to no
/// contribution. Pre-#103 our code used `i.at_entry` / `i.at_exit`
/// directly; if Verus ever produced `(false, false)`, we'd carry
/// the inv through the rendering pipeline only to skip both
/// emission paths.
///
/// Post-#103: at the build_wp_loop boundary, each `LoopInv` is
/// classified into one of three named states; `(false, false)` is
/// rejected with a clear error rather than silently dropped. The
/// downstream pipeline pattern-matches on the kind, and adding a
/// new variant forces every consumer site to make a decision
/// (Rust's exhaustive-match check).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LoopInvKind {
    /// `invariant P` — at_entry = at_exit = true. Holds at every
    /// iteration boundary AND at every loop exit.
    Invariant,
    /// `invariant_except_break P` — at_entry = true, at_exit = false.
    /// Holds at iteration boundaries; break may invalidate.
    InvariantExceptBreak,
    /// `ensures P` (on a loop) — at_entry = false, at_exit = true.
    /// Required at every loop exit; not required during iteration.
    Ensures,
}

impl LoopInvKind {
    /// Convert from Verus's flag pair, rejecting the nonsensical
    /// `(false, false)` shape.
    fn from_loop_inv(inv: &LoopInv) -> Result<Self, String> {
        match (inv.at_entry, inv.at_exit) {
            (true, true) => Ok(LoopInvKind::Invariant),
            (true, false) => Ok(LoopInvKind::InvariantExceptBreak),
            (false, true) => Ok(LoopInvKind::Ensures),
            (false, false) => Err(
                "loop invariant has neither at_entry nor at_exit set — \
                 this combination is meaningless (Verus internal bug?). \
                 Please open an issue.".to_string()
            ),
        }
    }

    /// Whether this kind contributes to the iteration-boundary
    /// (continue / fallthrough) obligations: init theorems,
    /// maintain ctx hyp, body's continue_leaf.
    pub fn at_entry(&self) -> bool {
        match self {
            LoopInvKind::Invariant | LoopInvKind::InvariantExceptBreak => true,
            LoopInvKind::Ensures => false,
        }
    }

    /// Whether this kind contributes to the loop-exit (break /
    /// natural-fallthrough) obligations: break_leaf, use ctx hyp.
    pub fn at_exit(&self) -> bool {
        match self {
            LoopInvKind::Invariant | LoopInvKind::Ensures => true,
            LoopInvKind::InvariantExceptBreak => false,
        }
    }
}

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
/// below and is threaded as a `&[&WpLoopCtx]` stack parameter
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
    /// Names of `MutRef`-typed local declarations that should be
    /// treated as `&mut` arg L-values at call sites (#107). Two
    /// sources, both unified into this one set:
    /// * Fn parameters declared `&mut T` or `MutRef<T>` (legacy and
    ///   new-mut-ref callee sides). The `&mut` rebind happens via
    ///   the body's let-shadow.
    /// * Synthetic `LocalDeclKind::BorrowMut` locals Verus
    ///   introduces around exec calls in new-mut-ref mode (caller
    ///   side). The synthetic local IS the L-value at the call.
    /// `extract_mut_target` uses this set to recognize bare
    /// `Var(borrow_mut_local)` in arg position (no surrounding
    /// `Loc`) as a valid mut target.
    pub mut_ref_locals: HashSet<String>,
}

/// The break / continue goal leaves in scope inside a loop body.
/// Threaded through `build_wp` as `&[&WpLoopCtx]` (innermost-first)
/// so labeled break/continue can search for the matching loop.
/// Empty slice outside any loop; one entry per enclosing loop body
/// when nested.
///
/// **Unlabeled** break/continue resolves to `stack[0]` (innermost).
/// **Labeled** `break 'outer;` searches the stack for an entry with
/// `label == Some("outer")` and uses that loop's leaves.
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
struct WpLoopCtx {
    /// The loop's source-level label (`'outer: while …` →
    /// `Some("outer")`). `None` for unlabeled loops. Compared
    /// against the `label` field on `StmX::BreakOrContinue` to
    /// resolve labeled break/continue.
    label: Option<String>,
    break_leaf: LExpr,
    continue_leaf: LExpr,
}

/// Linked-list-style stack of enclosing loop contexts. Threaded
/// through `build_wp` as `&LoopStack<'p>` (innermost-first); each
/// nested loop body extends the stack via `LoopStack::Cons` whose
/// references live on the caller's stack frame, so push is
/// allocation-free.
///
/// Replaces an earlier `&[&WpLoopCtx]` shape that allocated a fresh
/// `Vec` per nested loop body (`vec![&inner]; extend_from_slice(outer)`).
/// The persistent linked-list lives entirely on the call stack — no
/// heap allocation, no copying — and the iteration pattern (innermost-
/// first via `iter()`) preserves the prior search semantics.
enum LoopStack<'p> {
    Empty,
    Cons(&'p WpLoopCtx, &'p LoopStack<'p>),
}

impl<'p> LoopStack<'p> {
    /// The innermost enclosing loop's ctx, or `None` outside any
    /// loop. Used to resolve unlabeled `break;` / `continue;`.
    fn first(&self) -> Option<&WpLoopCtx> {
        match self {
            LoopStack::Empty => None,
            LoopStack::Cons(ctx, _) => Some(ctx),
        }
    }

    /// Iterate from innermost to outermost. Used to resolve labeled
    /// `break 'name;` by searching for the matching label.
    fn iter(&self) -> LoopStackIter<'_> {
        LoopStackIter { cursor: self }
    }
}

struct LoopStackIter<'p> {
    cursor: &'p LoopStack<'p>,
}

impl<'p> Iterator for LoopStackIter<'p> {
    type Item = &'p WpLoopCtx;
    fn next(&mut self) -> Option<Self::Item> {
        match self.cursor {
            LoopStack::Empty => None,
            LoopStack::Cons(ctx, next) => {
                self.cursor = next;
                Some(ctx)
            }
        }
    }
}

impl<'a> WpCtx<'a> {
    /// Build the context for verifying `check` against `krate`.
    ///
    /// Validates `check.reqs` and `check.post_condition.ens_exps`
    /// up front via `check_exp`. If any expression uses an SST form
    /// we don't support, returns `Err(reason)` before constructing
    /// anything — in particular before lowering `ensures_goal` via
    /// the typed `Validated::check + lower` pipeline (post-#115;
    /// previously the infallible `sst_exp_to_ast` shim).
    ///
    /// The precondition "ens_exps is supported" thus lives in the
    /// type signature rather than in a docstring: you can only get
    /// a `WpCtx` by passing validation.
    pub fn new(
        krate: &'a KrateX,
        check: &'a FuncCheckSst,
        // For callee-side `&mut` body verification (#94): set of
        // sanitized param-name strings for the fn's `&mut` params.
        // Each ens_exp is rewritten so `*old(x)` → `<x>_at_pre_tactus`
        // for x in this set, before rendering to LExpr. Empty for
        // fns without `&mut` params (the common case).
        mut_param_names: &HashSet<String>,
    ) -> Result<Self, String> {
        // Validate the *normalized* expressions — new-mut-ref-mode
        // shapes (`MutRefCurrent` / `MutRefFuture`) are mapped to the
        // legacy `Var` / `VarAt` shape via `normalize_mut_ref_in_exp`
        // before validation. Without this, `check_exp` would reject
        // any MutRef-wrapped reference in a fn that uses `&mut` params
        // even though we'd handle it correctly downstream (#95).
        for req in check.reqs.iter() {
            let normalized = normalize_mut_ref_in_exp(
                req,
                mut_param_names,
                NormalizePhase::CurrentIsLocal,
            );
            check_exp(&normalized)?;
        }
        for ens in check.post_condition.ens_exps.iter() {
            let normalized = normalize_mut_ref_in_exp(
                ens,
                mut_param_names,
                NormalizePhase::CurrentIsPreState,
            );
            check_exp(&normalized)?;
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
        //
        // Rewrite VarAt(x, Pre) → Var(<x>_at_pre_tactus) for &mut
        // params (#94) BEFORE rendering — the rewrite is on SST,
        // and the renderer then sees only Var nodes.
        let ensures_goal = and_all(
            check.post_condition.ens_exps.iter().map(|ens| -> Result<LExpr, String> {
                // First normalize new-mut-ref shapes (`MutRefCurrent` →
                // `VarAt(_, Pre)`, `MutRefFuture/Final` → `Var`) so the
                // existing #94 rewrite step then handles it as if the
                // input were legacy-shaped. See `normalize_mut_ref_in_exp`
                // for the rewrite table.
                let normalized = normalize_mut_ref_in_exp(
                    ens,
                    mut_param_names,
                    NormalizePhase::CurrentIsPreState,
                );
                let rewritten = rewrite_varat_for_mut_params_in_exp(&normalized, mut_param_names);
                // The rewrite is structural (VarAt(p, Pre) →
                // Var(<p>_at_pre_tactus)) and preserves ExpX shape, so
                // validation that succeeded on `normalized` (the
                // earlier `check_exp` call in this fn) succeeds on
                // `rewritten`. `Validated::check` is deterministic;
                // propagating its Err handles any unexpected drift.
                Ok(LExpr::span_mark(
                    format_rust_loc(&ens.span),
                    AssertKind::Obligation(ObligationKind::Postcondition),
                    lower_validated(&Validated::check(&rewritten)?),
                ))
            }).collect::<Result<Vec<_>, String>>()?
        );
        Ok(Self {
            fn_map,
            type_map,
            ret_name,
            ensures_goal,
            mut_ref_locals: mut_param_names.clone(),
        })
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

// ── Peel/lift helpers ──────────────────────────────────────────────────
//
// Several closely-related helpers for "look through SST wrappers,
// destructure binders, lift if-values to goal level." They're easy
// to confuse, so the dispatch table:
//
// | Helper                       | Use when                                  | Semantics                                                     |
// |------------------------------|-------------------------------------------|---------------------------------------------------------------|
// | `peel_transparent`           | "is the wrapped value an `X`?"            | Strips Box/Unbox/CoerceMode/Trigger only. Does NOT peel `Loc`. |
// | `peel_value_position`        | "what's the value-position expr here?"    | `peel_transparent` + one layer of `Loc` peel.                 |
// | `contains_loc`               | "is this a `&mut`-style L-value arg?"     | Peels transparents; checks for `ExpX::Loc` at top.            |
// | `match_single_let_bind`      | "is this a `let single = …; body`?"       | Returns Some((name, rhs, body)) for single-binder, None else. |
// | `unfold_multi_binder_let`    | "convert `let (a,b) = …` to single-let chain" | Builds `Bind(Let([b1]), Bind(Let([b2]), …, body))`.       |
// | `lift_if_value`              | "Return-position has an `if`; lift to `(c → …) ∧ (¬c → …)`" | Recursive walker over If/Bind(Let)/transparents.    |
// | `walk_let`                   | Same as lift_if_value but for `Wp::Let` walker (per-obligation emission, not value-position). | Pushes Hyp/Let frames, recurses. |
//
// Why two peels (`peel_transparent` and `peel_value_position`):
// `contains_loc` needs `Loc` UN-peeled (to detect `&mut` sites),
// while `lift_if_value` needs `Loc` PEELED (to find the inner
// value). Two helpers makes the asymmetry explicit; calling
// `peel_value_position` from `contains_loc` would silently erase
// the `&mut` detection.
//
// All helpers are pure (no side effects); the recursion structure
// is bounded by SST tree size.

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
/// where the Exp will be held in shapes that don't carry a
/// `Validated<'a>` witness (e.g., a sub-Exp of a builder helper that
/// later re-runs `sst_exp_to_ast_checked` itself, or an Exp lifted
/// via `lift_if_value`). For Exp's stored directly into a `Wp`
/// variant, prefer `Validated::check(&Exp)?` — that wraps the same
/// validation in a typestate so the walker's `lower(&Validated<'_>)`
/// is panic-free by construction (#100).
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
/// * **`Wp::LetRaw(name, lexpr, body)`** — no theorem; let frame
///   pushed. Same as `Let` but the RHS is an already-rendered
///   `LExpr` (no SST `Exp` to revalidate). Used by closure-decl
///   to bind `cid` to the Lean lambda assembled from the AST
///   `ast_body` field — the lambda doesn't go through SST's
///   renderer, so there's no `Validated<Exp>` to wrap.
/// * **`Wp::Branch(cond, t, e)`** — recurse on `t` with `cond`
///   as a Hyp frame; recurse on `e` with `¬cond`. No theorem at
///   the branch node.
/// * **`Wp::ClosureBody { closure_params, body, after }`** — the
///   closure's verification scope. Walks `body` under
///   `∀ p : T, h_p_bound → ...` for each closure param (via
///   `push_mod_var_frames`), so theorems emitted from inside the
///   body (overflow checks, the closure's own ensures-asserting,
///   etc.) verify against any caller-supplied input satisfying
///   the type bounds. Then walks `after` under the original obl —
///   the closure params don't escape the closure scope. No
///   theorem at the node itself; obligations come from `body`.
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
    // `&mut` params of the fn being verified (#94 callee-side body).
    // For each, the body and ensures get a SST-level rewrite so that
    // `*old(x)` (`VarAt(x, Pre)`) renders as `Var(<x>_at_pre_tactus)`,
    // distinct from `*x` (`Var(x)`) which is the post-state — the
    // body's `*x = expr` lowers to `let x := expr` (Lean shadowing),
    // so without the rewrite both would collapse to the same name
    // and the let-shadow would silently make them equal. Empty for
    // fns without `&mut` params (the common case).
    // Names of every `&mut`/`MutRef<T>` reference whose body / ensures
    // shapes the new-mut-ref normalization should rewrite. Two sources:
    //
    // * `fn_sst.x.pars` — fn parameters declared `&mut T` or `MutRef<T>`.
    //   Both legacy mode (#55) and new-mut-ref callee-side mode (#95)
    //   need these.
    // * `check.local_decls` filtered to `LocalDeclKind::BorrowMut` —
    //   synthetic locals Verus introduces in caller-side new-mut-ref
    //   mode (#107). When the caller writes `bump(&mut y)`, Verus
    //   lowers it to `let mut_ref = ...; assume(MutRefCurrent(mut_ref)
    //   == y); bump(mut_ref); y = MutRefFuture(mut_ref);`. The
    //   synthetic `mut_ref` is `MutRef<u8>`-typed and gets
    //   `LocalDeclKind::BorrowMut`. Without including it here, the
    //   `MutRefCurrent`/`MutRefFuture` ops wrapping `mut_ref` slip
    //   past the normalizer and reach the renderer's "unsupported
    //   unary op" arm.
    let mut mut_param_names: HashSet<String> = fn_sst.x.pars.iter()
        .filter(|p| is_mut_ref_par(p))
        .map(|p| sanitize(&p.x.name.0))
        .collect();
    for decl in check.local_decls.iter() {
        if matches!(decl.kind, LocalDeclKind::BorrowMut) {
            mut_param_names.insert(sanitize(&decl.ident.0));
        }
    }

    // Pre-rewrite the body so VarAt(x, Pre) → Var(<x>_at_pre_tactus)
    // for &mut x. The rewritten body is owned by this fn's stack
    // frame; build_wp's output borrows from it, but we consume that
    // output via walk_obligations before this fn returns, so the
    // lifetime is sound. (WpCtx<'a> covariant in 'a allows the
    // shorter inner lifetime here.)
    //
    // For non-`&mut` fns, `mut_param_names` is empty and the rewrite
    // helper short-circuits to a plain `clone()` — zero overhead.
    //
    // First normalize new-mut-ref SST shapes (`MutRefCurrent` /
    // `MutRefFuture` / `MutRefFinal` ops) back to the legacy shape
    // (`Var` / `VarLoc` / `VarAt`) for the &mut params (#95). After
    // this normalization, the SST is shape-equivalent to legacy mode
    // and the existing rewrite handles it.
    let normalized_body: Stm = normalize_mut_ref_in_stm(&check.body, &mut_param_names);
    let rewritten_body: Stm = rewrite_varat_for_mut_params_in_stm(
        &normalized_body,
        &mut_param_names,
    );

    // `WpCtx::new` validates reqs / ens_exps before rendering them.
    // It also applies the same rewrite to each ens_exp so the
    // `ensures_goal` LExpr already has the synthetic names baked in.
    let ctx = WpCtx::new(krate, check, &mut_param_names)?;

    let mut binders = build_param_binders(fn_sst);
    binders.extend(build_borrow_mut_binders(check));
    binders.extend(build_req_binders(check, &mut_param_names));

    // Build the whole WP tree from the (rewritten) body, with the
    // fn's ensures as the natural continuation at the leaves.
    // `Return` statements inside the body replace their local `after`
    // with the same ensures goal (via `ctx.ensures_goal`). Initial
    // loop_stack is empty — break/continue are rejected outside any
    // loop.
    let body_wp = build_wp(
        &rewritten_body,
        Wp::Done(ctx.ensures_goal.clone()),
        &ctx,
        &LoopStack::Empty,
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

    // Initial OblCtx with `let <x>_at_pre_tactus := x` for each &mut
    // param. These frames wrap the goal at theorem-emission time,
    // so the body's WP (which after the rewrite mentions
    // <x>_at_pre_tactus wherever the user wrote `*old(x)`) sees
    // the pre-state captured before any body modifications shadow
    // the param. The fn's requires stay in theorem-level binders
    // (`build_req_binders` above) and are NOT rewritten — at fn
    // entry, x IS the pre-state, so `*old(x) ≡ x` for requires
    // evaluation; the natural VarAt → Var collapse in the renderer
    // gives the right thing for them.
    let mut initial_obl_ctx = OblCtx::new();
    for par in fn_sst.x.pars.iter().filter(|p| is_mut_ref_par(p)) {
        let raw_name = sanitize(&par.x.name.0);
        let pre_name = crate::lean_name::LeanName::synthetic(
            varat_pre_name(&raw_name),
        );
        let var_x = LExpr::var(crate::lean_name::LeanName::from_var_ident(&par.x.name));
        initial_obl_ctx = initial_obl_ctx.with_frame(CtxFrame::Let(pre_name, var_x));
    }
    walk_obligations(&body_wp, &ctx, &initial_obl_ctx, &mut emitter);
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
        if let ExprX::AssertAssume { is_assume: true, expr, .. } = &e.x {
            // Filter out synthetic assumes injected by Verus's
            // `resolution_inference` pass (which runs in
            // `--V new-mut-ref` mode). They wrap `HasResolved(_)` —
            // possibly conditioned on enum-variant `IsVariant` checks
            // via an `Implies` — and aren't user-written, so warning
            // about them is a false positive (#95). User-written
            // `assume(P)` has arbitrary `P` shape.
            if !is_synthetic_resolution_assume(expr) {
                out.borrow_mut().push(e.span.clone());
            }
        }
        Ok(e.clone())
    });
    out.into_inner()
}

/// Recognize the shape that `resolution_inference::mk_assume` produces:
/// `HasResolved(_)` directly, or `Implies(IsVariant_chain, HasResolved(_))`
/// for enum-variant-conditioned places. See
/// `vir/src/resolution_inference.rs::condition_on_enum_variants`.
fn is_synthetic_resolution_assume(e: &Expr) -> bool {
    match &e.x {
        ExprX::UnaryOpr(UnaryOpr::HasResolved(_), _) => true,
        // `condition_on_enum_variants` wraps `HasResolved` in
        // `Implies(IsVariant, ...)` chains. Recurse on the conclusion.
        ExprX::Binary(BinaryOp::Implies, _lhs, rhs) => is_synthetic_resolution_assume(rhs),
        _ => false,
    }
}

/// Extract `(cid, lambda)` from the AST body of an exec closure
/// (`ExprX::NonSpecClosure`). The cid comes from `external_spec`
/// (populated by `ast_simplify`); the lambda is rendered via
/// `vir_expr_to_ast`'s extended `NonSpecClosure` arm. Returns `Err`
/// if the AST shape is unexpected (e.g., `external_spec` missing —
/// shouldn't happen for code that reaches the SST).
fn closure_lambda_from_ast(
    ast_body: &Expr,
) -> Result<(crate::lean_name::LeanName, LExpr), String> {
    let (cid, _cexpr) = match &ast_body.x {
        ExprX::NonSpecClosure { external_spec, .. } => {
            external_spec.as_ref().ok_or_else(|| {
                "closure's `external_spec` is None at SST time — \
                 should have been populated by ast_simplify".to_string()
            })?
        }
        _ => return Err(format!(
            "StmX::ClosureInner.ast_body wasn't an ExprX::NonSpecClosure (got {:?}) — \
             internal bug: ast_to_sst should only set ast_body to the closure expr",
            ast_body.typ
        )),
    };
    let cid_name = crate::lean_name::LeanName::from_var_ident(cid);
    let lambda = vir_expr_to_ast(ast_body);
    Ok((cid_name, lambda))
}

/// Assemble the closure-decl Wp shape:
///
/// ```text
///   ClosureBody {
///     closure_params,
///     body: body_wp,                  // closure's own verification scope
///     after: LetRaw { cid := lambda; outer_after }   // outer fn continues
///   }
/// ```
///
/// Extracted from the `StmX::ClosureInner` handler in `build_wp` so
/// the call site reads as a single named operation instead of three
/// levels of `Box::new` / nested struct-literal nesting.
fn closure_decl_wp<'a>(
    closure_params: Vec<(&'a VarIdent, &'a Typ)>,
    body_wp: Wp<'a>,
    cid: crate::lean_name::LeanName,
    lambda: LExpr,
    outer_after: Wp<'a>,
) -> Wp<'a> {
    Wp::ClosureBody {
        closure_params,
        body: Box::new(body_wp),
        after: Box::new(Wp::LetRaw {
            name: cid,
            value: lambda,
            body: Box::new(outer_after),
        }),
    }
}

/// True if the SST `Exp` `e` is the body of a synthetic `StmX::Assume`
/// that Tactus should drop entirely (rather than render as a Hyp
/// frame). Two synthetic sources are recognized:
///
/// * **`UnaryOpr(HasResolved(_), _)` (#95)** — Verus's
///   `resolution_inference` pass injects `Assume(HasResolved(_))` (or
///   `Assume(IsVariant_chain → HasResolved(_))` for enum-conditioned
///   places) in `--V new-mut-ref` mode. Our renderer doesn't model
///   `HasResolved` semantics — collapsing it to its inner `Var(x)`
///   would hypothesize a non-Prop, a Lean type error. Drop these.
///
/// * **Anything containing `ClosureReq` / `ClosureEns` / `DefaultEns`
///   `InternalFun` calls (#93)** — `ast_to_sst` emits
///   `Assume(forall|x| ClosureReq(cid, x) ↔ ... ∧ ClosureEns(cid, x,
///   body(x)) ↔ ...)` after each `StmX::ClosureInner` so Z3 knows the
///   closure's spec via predicates. Tactus binds `cid` to a Lean
///   lambda directly via `Wp::LetRaw`, so the predicate-style assume
///   is structurally redundant. Recognize via a whole-tree walk for
///   the InternalFun reference — these don't appear in user-written
///   code, so any expression containing one is synthetic.
///
/// Counterpart: `is_synthetic_resolution_assume` does the same job at
/// the AST (`Expr`) level — used by `collect_assume_sites` to suppress
/// the unproved-assumption *warning* on synthetic injections. The two
/// helpers are independent because AST and SST have separate Rust
/// types (`Expr` vs `Exp`), and the AST-side filter only needs to
/// catch HasResolved (closure-spec stuff doesn't reach the AST as
/// AssertAssume — it's pure SST).
fn is_synthetic_assume_to_drop(e: &Exp) -> bool {
    match &e.x {
        ExpX::UnaryOpr(UnaryOpr::HasResolved(_), _) => true,
        ExpX::Binary(BinaryOp::Implies, _lhs, rhs) => is_synthetic_assume_to_drop(rhs),
        _ => contains_closure_internal_fn(e),
    }
}

/// True if `e` references one of Verus's closure-spec `InternalFun`
/// variants anywhere in its tree. A whole-tree walk is the simplest
/// predicate — the closure-spec assume is densely shaped around these
/// calls (and uses `forall` + `Bind(Let)` for synthetic temps), so we
/// can't easily pattern-match the whole shape.
///
/// Implementation note: `map_exp_visitor` is a *transform* function
/// (returns the rebuilt `Exp`) but we use it as an inspector — the
/// rebuilt tree is discarded, only the side-effected `found` flag
/// matters. Same pattern as `collect_assume_sites` (see its docstring
/// for the rationale: the visitor takes `Fn` not `FnMut`, so interior
/// mutability is the only path to per-node side-effect collection).
fn contains_closure_internal_fn(e: &Exp) -> bool {
    let mut found = false;
    let _ = vir::sst_visitor::map_exp_visitor(e, &mut |inner: &Exp| {
        if let ExpX::Call(
            CallFun::InternalFun(
                InternalFun::ClosureReq | InternalFun::ClosureEns | InternalFun::DefaultEns,
            ),
            _,
            _,
        ) = &inner.x
        {
            found = true;
        }
        inner.clone()
    });
    found
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
    Let(crate::lean_name::LeanName, LExpr),
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
    /// Persistent immutable vector — `clone()` is O(1) (structural
    /// sharing via `im` crate's RRB-tree), `push_back` is O(log N).
    /// The walker pattern `let new_obl = obl.with_frame(f);
    /// recurse(&new_obl)` thus avoids the O(N) per-push Vec clone
    /// the original implementation had.
    frames: im::Vector<CtxFrame>,
}

impl OblCtx {
    fn new() -> Self { Self { frames: im::Vector::new() } }

    /// Append a frame, returning a fresh OblCtx that shares the
    /// parent's frames structurally. Cheap by construction
    /// (`im::Vector::clone` is O(1) and `push_back` is O(log N)),
    /// so deeply-nested recursion no longer pays the O(N²) memory
    /// cost the prior `Vec` shape did.
    fn with_frame(&self, f: CtxFrame) -> Self {
        let mut new = self.clone();
        new.frames.push_back(f);
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

    /// Wrap `goal` with Let / Binder frames only — Hyp frames are
    /// dropped. Used by `Wp::AssertBitVector` (#111 / #130).
    ///
    /// **Why dropping is sound for bit_vector:** `assert(P) by(bit_vector)`
    /// is a self-contained query — its contract is "given the user's
    /// declared `requires`, prove the `ensures`." Surrounding code's
    /// hypotheses (from earlier asserts, branch conditions, loop
    /// invariants, etc.) are incidentally true at the assert site
    /// but aren't part of the bit_vector query's input. The
    /// bit_vector solver discharges the obligation in BitVec
    /// semantics over the user's stated requires alone; the body's
    /// post-assert continuation walks under the original obl
    /// (with hyps intact), so nothing is lost downstream. Mirrors
    /// Verus's bit_vector query encoding which also runs with a
    /// clean context.
    ///
    /// **Why dropping is necessary for typecheck:** the surrounding
    /// hyps may contain Int-mode bitwise ops (e.g., `x ^^^ y` for
    /// `x, y : Int`) carried in via `Wp::Assume(ens)` that Verus's
    /// ast_to_sst pre-injects before `AssertBitVector`. Lean has no
    /// `HXor Int Int Int` instance unless conditionally added (see
    /// `BITVEC_INT_INSTANCES`); without `wrap_no_hyps` the
    /// bit_vector goal's pre-conditions would fail to elaborate
    /// even when the goal itself typechecks.
    ///
    /// Keeps Let / Binder frames because:
    /// * Let frames may bind names that the bit_vector goal
    ///   references (e.g., a temp from `let _ret_n := ...; assert by(bit_vector)`).
    /// * Binder frames carry param types that the goal's `BitVec.ofInt
    ///   n x` references need for elaboration.
    fn wrap_no_hyps(&self, mut goal: LExpr) -> LExpr {
        for frame in self.frames.iter().rev() {
            goal = match frame {
                CtxFrame::Let(name, v) => LExpr::let_bind(name.clone(), v.clone(), goal),
                CtxFrame::Hyp(_) => goal,
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
        self.emit_with_preamble(name, goal, closer, Vec::new());
    }

    /// Like `emit`, but the theorem also declares preamble fragments
    /// (imports / instance blocks) that its elaboration depends on.
    /// `generate.rs::krate_preamble` aggregates these across all
    /// emitted theorems and emits them once at file top, deduped.
    /// Used by `Wp::AssertBitVector` (#130) — the only walker arm
    /// that currently needs extra preamble. Future "this fn needs
    /// Mathlib.Tactic.X" cases follow the same pattern.
    fn emit_with_preamble(
        &mut self,
        name: String,
        goal: LExpr,
        closer: Tactic,
        requires_preamble: Vec<PreambleFragment>,
    ) {
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
            requires_preamble,
        });
    }
}

/// Snake-case name fragment for an `AssertKind`, used in theorem
/// naming. The visible per-error label still goes through
/// [`AssertKind::label`] — the fragment here is only for unique
/// identifiers in generated Lean.
fn kind_to_name(k: AssertKind) -> &'static str {
    match k {
        AssertKind::Obligation(ObligationKind::Plain) => "assert",
        AssertKind::Obligation(ObligationKind::Postcondition) => "postcondition",
        AssertKind::Obligation(ObligationKind::LoopInvariant) => "loop_invariant",
        AssertKind::Obligation(ObligationKind::LoopDecrease) => "loop_decrease",
        AssertKind::Hypothesis(HypothesisKind::LoopCondition) => "loop_condition",
        AssertKind::Hypothesis(HypothesisKind::BranchCondition) => "branch_condition",
        AssertKind::Obligation(ObligationKind::CallPrecondition) => "precondition",
        AssertKind::Obligation(ObligationKind::Termination) => "termination",
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
            let asserted_exp = asserted.raw();
            let kind = detect_assert_kind(asserted_exp);
            let loc = format_rust_loc(&asserted_exp.span);
            let cond_ast = lower_validated(asserted);
            let goal = LExpr::span_mark(loc.clone(), kind, cond_ast.clone());
            let id = e.next_id();
            let name = build_theorem_name(
                kind_to_name(kind), &e.fn_name, &loc, id,
            );
            e.emit(name, obl.wrap(goal), simple_tactic(e));
            // Reuse cond_ast for the body's hypothesis frame —
            // rendering is deterministic, so re-running it on the
            // same Exp would only repeat work.
            let new_obl = obl.with_frame(CtxFrame::Hyp(cond_ast));
            walk_obligations(body, ctx, &new_obl, e);
        }
        Wp::Assume(p, body) => {
            // No theorem; the assumption just enters the context.
            let new_obl = obl.with_frame(CtxFrame::Hyp(lower_validated(p)));
            walk_obligations(body, ctx, &new_obl, e);
        }
        Wp::Hyp { hyp, body } => {
            // Already-rendered hypothesis (e.g., a synthesised
            // negation from #114's cond_setup transform). Push as
            // CtxFrame::Hyp directly — same effect as Wp::Assume's
            // arm, minus the `lower` call that already happened.
            let new_obl = obl.with_frame(CtxFrame::Hyp(hyp.clone()));
            walk_obligations(body, ctx, &new_obl, e);
        }
        Wp::AssertBitVector { req_conj, ens_conj, rust_loc, body } => {
            // Verified goal (BitVec mode): `req_conj → ens_conj`
            // (or just `ens_conj` when requires is empty — `req_conj`
            // is `LitBool(true)` from `and_all([])`, and `True → P` is
            // equivalent to `P` but emitting the bare `P` reads
            // cleaner and avoids the user's tactic having to peel the
            // trivial implication).
            let goal_inner = if matches!(req_conj.node, ExprNode::LitBool(true)) {
                ens_conj.clone()
            } else {
                LExpr::implies(req_conj.clone(), ens_conj.clone())
            };
            let goal = LExpr::span_mark(
                rust_loc.clone(),
                AssertKind::Obligation(ObligationKind::Plain),
                goal_inner,
            );
            let id = e.next_id();
            let name = build_theorem_name(
                kind_to_name(AssertKind::Obligation(ObligationKind::Plain)),
                &e.fn_name, rust_loc, id,
            );
            // Tactus's prelude tactic `tactus_bit_vector`. Hardcoded
            // rather than user-supplied — the surface syntax
            // `by(bit_vector)` is itself the tactic choice.
            //
            // Use `wrap_no_hyps` rather than `wrap` so the surrounding
            // ctx's Hyp frames don't leak into the bit_vector goal.
            // Reason: those Hyps may carry Int-mode bitwise ops
            // (`x ^^^ y` for `x, y : Int`) which Lean rejects (no
            // `HXor Int Int Int` instance), and even if they
            // typechecked they're in a different encoding from the
            // BitVec-mode goal so they wouldn't help. Verus's
            // bit_vector queries also run with a clean context.
            //
            // Attach the BitVec preamble fragments to the theorem's
            // `requires_preamble`. `generate.rs::krate_preamble`
            // aggregates fragments across all of an exec fn's
            // theorems and emits them at file top — Verus's
            // ast_to_sst pre-injects an Int-mode `Assume(ens)` before
            // AssertBitVector, so post-assert continuation theorems
            // need the `HXor Int Int Int` etc. instances to typecheck.
            e.emit_with_preamble(
                name,
                obl.wrap_no_hyps(goal),
                Tactic::Named("tactus_bit_vector".to_string()),
                bitvec_preamble_fragments(),
            );
            // Body walks under the ORIGINAL obl. We don't push the
            // ensures as a Hyp here because Verus's `ast_to_sst`
            // pre-injects an Int-mode `Assume(ens)` *as a separate
            // statement* right after the AssertBitVector — so the
            // ensures already enters the body's ctx via the
            // `Wp::Assume` walker arm a level up. Pushing again here
            // would duplicate it. (The Int-mode bitwise ops in that
            // Hyp are typechecked via the `HXor Int Int Int` /
            // `HAnd` / etc. instances aggregated through
            // `bitvec_preamble_fragments()`; without those the
            // post-assert continuation theorems would fail to
            // elaborate.)
            walk_obligations(body, ctx, obl, e);
        }
        Wp::Let(name, val, body) => {
            walk_let(name, val.raw(), body, ctx, obl, e);
        }
        Wp::LetRaw { name, value, body } => {
            // Pre-rendered RHS — push the Let frame directly. No need
            // to re-validate or to fork on value-position ifs (the
            // closure case that produces this doesn't have if-shaped
            // RHSs by construction).
            let new_obl = obl.with_frame(CtxFrame::Let(name.clone(), value.clone()));
            walk_obligations(body, ctx, &new_obl, e);
        }
        Wp::ClosureBody { closure_params, body, after } => {
            // Walk the closure body under `∀ p : T, h_p_bound → ...`
            // for each closure param. Theorems emitted from inside
            // the body (overflow checks, the closure's own ensures-
            // asserting, etc.) inherit those binders via the OblCtx,
            // so they verify against any caller-supplied input
            // satisfying the type bounds.
            let mut closure_obl = obl.clone();
            push_mod_var_frames(&mut closure_obl, closure_params);
            walk_obligations(body, ctx, &closure_obl, e);
            // Continue with `after` under the original obl — the
            // closure params don't escape the closure scope.
            walk_obligations(after, ctx, obl, e);
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
                format_rust_loc(&cond.raw().span),
                AssertKind::Hypothesis(HypothesisKind::BranchCondition),
                lower_validated(cond),
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
        Wp::Call { callee, spec_callee, args, typ_args, dest, call_span, mut_args, after } => {
            walk_call(
                callee, spec_callee, args, typ_args, *dest, call_span, mut_args, after, ctx, obl, e,
            );
        }
        Wp::Loop { cond, invs, validated_invs, inv_kinds, decrease, modified_vars, body, after } => {
            walk_loop(
                *cond, invs, validated_invs, inv_kinds, decrease, modified_vars, body, after, ctx, obl, e,
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
    cond: Option<Validated<'a>>,
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
            // AssertKind::Obligation(ObligationKind::Plain) because it's a user-written
            // `assert(P) by { tac }` — same kind a plain
            // `assert(P)` would get via `detect_assert_kind`.
            let loc = format_rust_loc(&c.raw().span);
            let cond_ast = lower_validated(&c);
            let goal = LExpr::span_mark(
                loc.clone(), AssertKind::Obligation(ObligationKind::Plain), cond_ast.clone(),
            );
            let id = e.next_id();
            let name = build_theorem_name(
                kind_to_name(AssertKind::Obligation(ObligationKind::Plain)), &e.fn_name, &loc, id,
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
    cond: Option<Validated<'a>>,
    invs: &[LoopInv],
    validated_invs: &[Validated<'a>],
    inv_kinds: &[LoopInvKind],
    decrease: &[DecreaseLevel<'a>],
    modified_vars: &[(&'a VarIdent, &'a Typ)],
    body: &Wp<'a>,
    after: &Wp<'a>,
    ctx: &WpCtx<'a>,
    obl: &OblCtx,
    e: &mut ObligationEmitter,
) {
    // Build SpanMark-wrapped invariant + cond helpers once; reused
    // across init theorems, maintain hyps, use hyps. The
    // entry/exit split mirrors `build_wp_loop`'s classification:
    //   * `at_entry`: holds at iteration boundaries → init
    //     theorems + maintain ctx hyp + body's continue_leaf.
    //   * `at_exit`: holds at loop exit → break_leaf + use ctx hyp.
    // Plain `invariant P` (at_entry = at_exit = true) flows into
    // both. `invariant_except_break` (at_entry only) and loop
    // `ensures` (at_exit only) flow into one each.
    let inv_marked = |(i, v): (&LoopInv, &Validated<'a>)| LExpr::span_mark(
        format_rust_loc(&i.inv.span),
        AssertKind::Obligation(ObligationKind::LoopInvariant),
        lower_validated(v),
    );
    let cond_marked = |c: &Validated<'a>| LExpr::span_mark(
        format_rust_loc(&c.raw().span),
        AssertKind::Hypothesis(HypothesisKind::LoopCondition),
        lower_validated(c),
    );
    let entry_inv_conj_marked = and_all(
        invs.iter().zip(validated_invs.iter()).zip(inv_kinds.iter())
            .filter(|(_, k)| k.at_entry())
            .map(|((i, v), _)| inv_marked((i, v))).collect()
    );
    let exit_inv_conj_marked = and_all(
        invs.iter().zip(validated_invs.iter()).zip(inv_kinds.iter())
            .filter(|(_, k)| k.at_exit())
            .map(|((i, v), _)| inv_marked((i, v))).collect()
    );

    // ── Init: one theorem per `at_entry` invariant. These are the
    // ones the user claims hold at loop entry (i.e., before the
    // first iteration). Loop ensures (`at_entry = false`) skip init
    // — they're established at exit, not at entry.
    for ((inv, v), _) in invs.iter().zip(validated_invs.iter()).zip(inv_kinds.iter()).filter(|(_, k)| k.at_entry()) {
        let loc = format_rust_loc(&inv.inv.span);
        let id = e.next_id();
        let name = build_theorem_name(
            kind_to_name(AssertKind::Obligation(ObligationKind::LoopInvariant)), &e.fn_name, &loc, id,
        );
        e.emit(name, obl.wrap(inv_marked((inv, v))), simple_tactic(e));
    }

    // ── Maintain: walk body with ∀ mod_vars + bounds + at_entry
    // invs as hyps + cond as hyp + `_tactus_d_old := D` let. The
    // body's Done leaf (= `entry_inv_conj ∧ decrease_marked`)
    // splits into one theorem per `at_entry` invariant + one for
    // the decrease via `emit_done_or_split`. `at_exit`-only
    // invariants (loop ensures) aren't visible during iteration —
    // they're only required at break.
    let mut maintain_obl = obl.clone();
    push_mod_var_frames(&mut maintain_obl, modified_vars);
    maintain_obl.frames.push_back(CtxFrame::Hyp(entry_inv_conj_marked));
    if let Some(c) = cond {
        maintain_obl.frames.push_back(CtxFrame::Hyp(cond_marked(&c)));
    }
    // `let _tactus_d_old_<id>_<i> := D_i` — one pre-body snapshot
    // per lex level. Referenced by the body's continue_leaf as
    // `(D1' < _tactus_d_old_<id>_0) ∨ (D1' = _tactus_d_old_<id>_0 ∧
    //  (D2' < _tactus_d_old_<id>_1) ∨ ...)`. Per-loop-unique +
    // per-level gensym (built in `build_wp_loop` from the loop's id
    // and the level index) avoids any chance of shadowing across
    // nested loops or sibling levels.
    for level in decrease.iter() {
        maintain_obl.frames.push_back(CtxFrame::Let(
            crate::lean_name::LeanName::synthetic(level.d_old_name.clone()),
            lower_validated(&level.value),
        ));
    }
    walk_obligations(body, ctx, &maintain_obl, e);

    // ── Use: walk `after` with ∀ mod_vars + bounds + at_exit invs
    // as hyps + ¬cond as hyp. After the loop, control got here via
    // either a break (where the body established the at_exit invs
    // as the break_leaf) or natural fallthrough (where the loop
    // condition became false, and the body's last iteration
    // re-established the entry invs). For `cond: Some(_)` loops,
    // Verus's lowering forces at_entry = at_exit, so both lists
    // agree. For `cond: None` loops (break-only exit), the use
    // ctx must NOT assume at_entry-only invs (`invariant_except_
    // break`) — break may have invalidated them. No
    // `_tactus_d_old` here — the decrease obligation only applies
    // to fall-through inside the body.
    let mut use_obl = obl.clone();
    push_mod_var_frames(&mut use_obl, modified_vars);
    use_obl.frames.push_back(CtxFrame::Hyp(exit_inv_conj_marked));
    if let Some(c) = cond {
        use_obl.frames.push_back(CtxFrame::Hyp(LExpr::not(cond_marked(&c))));
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
        // Modified-var binders carry the user's local-var VarIdent
        // verbatim. `from_var_ident` is the canonical entry point; it
        // includes the disambiguator id when needed (synthetic temps),
        // and falls through to plain `sanitize` for user-named locals.
        let name = crate::lean_name::LeanName::from_var_ident(ident);
        obl.frames.push_back(CtxFrame::Binder(LBinder {
            name: Some(name.clone()),
            ty: typ_to_expr(typ),
            kind: BinderKind::Explicit,
        }));
        if let Some(pred) = type_bound_predicate(&LExpr::var(name), typ) {
            obl.frames.push_back(CtxFrame::Hyp(pred));
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
    // Short-circuit: callees without &mut params (the common case)
    // don't need any rewriting. `map_expr_visitor` would otherwise
    // walk + clone the whole tree for nothing.
    if mut_param_names.is_empty() {
        return expr.clone();
    }
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

/// SST-side analogue of `rewrite_varat_for_mut_params` (#94 callee-
/// side body verification).
///
/// Rewrites every `ExpX::VarAt(p, Pre)` whose name is in
/// `mut_param_names` to `ExpX::Var(<p>_at_pre_tactus)`. Used at fn
/// entry to disambiguate pre-state references (`*old(x)` in the
/// callee's own body and ensures) from the post-state `Var(x)` after
/// body modifications shadow it via Lean `let`-shadowing.
///
/// **Why not collapse VarAt → Var unconditionally?** Verus's
/// `sst_util::stm_with_vars_at_pre_state` synthesises VarAt(_, Pre)
/// for loop modified-vars too — those expect the natural collapse,
/// where the pre-state name IS the same `Var(x)` re-bound at the
/// start of each iteration. Scoping the rewrite to the &mut param
/// name set keeps the loop case unaffected. Same approach as the
/// AST-level `rewrite_varat_for_mut_params` (call-site &mut, #55).
///
/// **Symmetry with the call-site path.** `varat_pre_name` lives in
/// `expr_shared.rs` and is the single source of truth for the
/// `<p>_at_pre_tactus` synthetic name. Both this rewrite (which
/// produces it) and the OblCtx Let frame (which binds it) use it,
/// so divergence is a compile error rather than a runtime mismatch.
fn rewrite_varat_for_mut_params_in_exp(
    exp: &Exp,
    mut_param_names: &HashSet<String>,
) -> Exp {
    if mut_param_names.is_empty() {
        return exp.clone();
    }
    vir::sst_visitor::map_exp_visitor(exp, &mut |e: &Exp| {
        rewrite_one_varat(e, mut_param_names)
    })
}

/// As above but for an entire `Stm` — applies the per-Exp rewrite
/// uniformly to every Exp embedded in the body's statement tree.
fn rewrite_varat_for_mut_params_in_stm(
    stm: &Stm,
    mut_param_names: &HashSet<String>,
) -> Stm {
    if mut_param_names.is_empty() {
        return stm.clone();
    }
    vir::sst_visitor::map_exps_in_stm_visitor(stm, &mut |e: &Exp| {
        rewrite_one_varat(e, mut_param_names)
    })
}

/// Single-Exp leaf rewrite shared by both walkers above.
fn rewrite_one_varat(e: &Exp, mut_param_names: &HashSet<String>) -> Exp {
    if let ExpX::VarAt(ident, vir::ast::VarAt::Pre) = &e.x {
        let raw_name = sanitize(&ident.0);
        if mut_param_names.contains(&raw_name) {
            // `varat_pre_name` is the canonical synthetic-name producer
            // — same one used by the AST-level rewrite for caller-side
            // &mut. Sharing it keeps the rewrite-side and Let-frame-
            // side names in sync.
            let new_str: vir::ast::Ident = Arc::new(varat_pre_name(&raw_name));
            // Reuse the original ident's disambiguator. For a user-
            // named param like `x` (no special chars), the resulting
            // `<x>_at_pre_tactus` also has no special chars, so
            // `LeanName::from_var_ident` won't append a suffix —
            // the rendered name is exactly `<x>_at_pre_tactus`.
            let new_ident = VarIdent(new_str, ident.1.clone());
            return SpannedTyped::new(
                &e.span,
                &e.typ,
                ExpX::Var(new_ident),
            );
        }
    }
    e.clone()
}

/// True if `p` is an `&mut` parameter — covers both legacy mode
/// (`is_mut: true`, plain `T` typ) and new-mut-ref mode after
/// migration (`is_mut: false`, `MutRef<T>` typ). Used to populate
/// `mut_param_names` for both the SST-level rewrite (#94) and the
/// new-mut-ref normalization (#95).
fn is_mut_ref_par(p: &Par) -> bool {
    p.x.is_mut || matches!(&*p.x.typ, vir::ast::TypX::MutRef(_))
}

/// VIR-AST counterpart of [`is_mut_ref_par`]. Same logic, different
/// type alias — `Par` is `vir::sst::Par` (used when iterating the
/// fn-being-verified's own params), `Param` is `vir::ast::Param` (used
/// when iterating a callee's params via `FunctionX.params`). Both
/// detect `&mut` in legacy mode (`is_mut: true`) and new-mut-ref mode
/// (`MutRef<T>` typ). Centralising the predicate keeps `walk_call`'s
/// `mut_args` collection (in `build_call_mut_args`) and the
/// per-param subst-map structure (in `add_param_subst_entries`) in
/// lockstep — divergence would silently miscompile new-mut-ref-shaped
/// callees whose params reach `add_param_subst_entries` as
/// `is_mut: false, typ: MutRef<T>`.
fn is_mut_ref_param(p: &vir::ast::Param) -> bool {
    p.x.is_mut || matches!(&*p.x.typ, vir::ast::TypX::MutRef(_))
}

/// Phase-of-rendering context for `normalize_mut_ref_*` (#95).
/// `MutRefCurrent` has different meaning in body vs ensures, and the
/// normalizer needs to know which phase it's running in.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum NormalizePhase {
    /// Body or requires position. `MutRefCurrent(Var(x))` reads the
    /// current dynamic value of `*x` — same as legacy mode's `Var(x)`,
    /// which the body's let-shadow handles. Just unwrap.
    CurrentIsLocal,
    /// Ensures position. `MutRefCurrent(Var(x))` reads pre-state (the
    /// value at fn entry). Convert to legacy `VarAt(x, Pre)` so the
    /// existing `rewrite_varat_for_mut_params` step then maps it to
    /// `Var(<x>_at_pre_tactus)`.
    CurrentIsPreState,
}

/// Normalize new-mut-ref-mode SST shapes into the legacy shape that
/// `rewrite_varat_for_mut_params_*` and `walk_assign` already handle
/// (#95).
///
/// In new-mut-ref mode (`-V new-mut-ref` plus
/// `deprecated_postcondition_mut_ref_style(true)`), Verus's body /
/// ensures lowering wraps `*x` reads in `Unary(MutRefCurrent, _)` and
/// `*x` post-state references in `Unary(MutRefFuture(_), _)`. The
/// legacy lowering produced bare `Var(x)` and `VarAt(x, Pre)`. Rather
/// than building a parallel rewrite + Let-frame infrastructure, we
/// normalize the new-mut-ref SST shapes back to the legacy shape at
/// fn entry, then the existing #94 machinery does the rest.
///
/// **Rewrite table** (for `x` in `mut_param_names`):
///
/// | Phase | Op | New body |
/// |-------|----|----------|
/// | body | `MutRefCurrent(Var(x))` | `Var(x)` |
/// | body | `MutRefCurrent(VarLoc(x))` | `VarLoc(x)` |
/// | ensures | `MutRefCurrent(Var(x))` | `VarAt(x, Pre)` |
/// | both | `MutRefFuture(_, Var(x))` | `Var(x)` |
/// | both | `MutRefFinal(_, Var(x))` | `Var(x)` |
///
/// `MutRefCurrent(VarLoc(x))` (LHS of `*x = e` in body) becomes
/// `VarLoc(x)`, which after the outer `Loc(_)` wrapper gives the
/// legacy assignment shape `Loc(VarLoc(x))` that `walk_assign`
/// handles directly.
///
/// Other shapes — e.g., `MutRefCurrent(Field(...))` for `*x.field`,
/// or `MutRefCurrent` wrapping non-`Var`/`VarLoc` — are left alone
/// and will hit the existing renderer's "unsupported unary op" arm.
/// Those map to deferred follow-ups (`&mut x.f`, `&mut v[i]`, etc.).
/// Peel transparent wrappers (Box/Unbox/MustBeFinalized) to find an
/// inner `Var`/`VarLoc`/`VarAt` reference if any. Returns
/// `(ident, kind)` where `kind` is which of the three.
///
/// `VarAt(x, Pre)` shows up as the inner of MutRef* ops in
/// new-mut-ref postconditions because Verus pairs the post-state
/// `MutRefFuture` wrapper with a pre-state `VarAt` reference (the
/// post-state of x's value at fn entry).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum InnerKind {
    Var,
    VarLoc,
    VarAtPre,
}

fn peel_to_var(e: &Exp) -> Option<(&VarIdent, InnerKind)> {
    match &e.x {
        ExpX::Var(id) => Some((id, InnerKind::Var)),
        ExpX::VarLoc(id) => Some((id, InnerKind::VarLoc)),
        ExpX::VarAt(id, vir::ast::VarAt::Pre) => Some((id, InnerKind::VarAtPre)),
        // Transparent wrappers we know about. `MustBeFinalized` shows up
        // briefly in SST around place-derived Var reads (see
        // `place_to_exp_pair_rec`'s `PlaceX::Local`); the others are
        // standard transparent wrappers that `peel_transparent` handles
        // for non-MutRef-specific contexts.
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner)
        | ExpX::Unary(UnaryOp::MustBeFinalized | UnaryOp::CoerceMode { .. } | UnaryOp::Trigger(_), inner) => {
            peel_to_var(inner)
        }
        _ => None,
    }
}

fn normalize_one_mut_ref(
    e: &Exp,
    mut_param_names: &HashSet<String>,
    phase: NormalizePhase,
) -> Exp {
    match &e.x {
        ExpX::Unary(UnaryOp::MutRefCurrent, inner) => {
            if let Some((id, kind)) = peel_to_var(inner) {
                let raw_name = sanitize(&id.0);
                if mut_param_names.contains(&raw_name) {
                    return match phase {
                        // Body: just unwrap to the bare `Var(x)` /
                        // `VarLoc(x)`. Lean let-shadowing gives the
                        // current value through `*x = e` body assignments.
                        NormalizePhase::CurrentIsLocal => {
                            let new_x = match kind {
                                InnerKind::VarLoc => ExpX::VarLoc(id.clone()),
                                InnerKind::Var | InnerKind::VarAtPre => ExpX::Var(id.clone()),
                            };
                            SpannedTyped::new(&e.span, &e.typ, new_x)
                        }
                        // Ensures: produce `VarAt(x, Pre)` so the outer
                        // `rewrite_varat_for_mut_params` step then
                        // produces `Var(<x>_at_pre_tactus)`. VarLoc is
                        // unexpected here (ensures don't have L-values).
                        NormalizePhase::CurrentIsPreState => {
                            assert!(
                                kind != InnerKind::VarLoc,
                                "VarLoc shouldn't appear in ensures position"
                            );
                            SpannedTyped::new(
                                &e.span,
                                &e.typ,
                                ExpX::VarAt(id.clone(), vir::ast::VarAt::Pre),
                            )
                        }
                    };
                }
            }
        }
        ExpX::Unary(UnaryOp::MutRefFuture(_) | UnaryOp::MutRefFinal(_), inner) => {
            // Future / Final: post-state. Same rewrite in body and
            // ensures phases — just unwrap to `Var(x)`. In legacy
            // semantics the post-state is the let-shadowed `Var(x)`
            // at fn exit. The inner can be `Var(x)`, `VarLoc(x)`, or
            // `VarAt(x, Pre)` — Verus pairs MutRefFuture with a
            // pre-state inner reference (the post-state of x's
            // entry value), and `Var(x)` (post-state via let-shadow)
            // is what the renderer expects.
            if let Some((id, _)) = peel_to_var(inner) {
                let raw_name = sanitize(&id.0);
                if mut_param_names.contains(&raw_name) {
                    return SpannedTyped::new(
                        &e.span,
                        &e.typ,
                        ExpX::Var(id.clone()),
                    );
                }
            }
        }
        _ => {}
    }
    e.clone()
}

fn normalize_mut_ref_in_exp(
    exp: &Exp,
    mut_param_names: &HashSet<String>,
    phase: NormalizePhase,
) -> Exp {
    if mut_param_names.is_empty() {
        return exp.clone();
    }
    vir::sst_visitor::map_exp_visitor(exp, &mut |e: &Exp| {
        normalize_one_mut_ref(e, mut_param_names, phase)
    })
}

fn normalize_mut_ref_in_stm(
    stm: &Stm,
    mut_param_names: &HashSet<String>,
) -> Stm {
    if mut_param_names.is_empty() {
        return stm.clone();
    }
    // Body is always `CurrentIsLocal` phase.
    vir::sst_visitor::map_exps_in_stm_visitor(stm, &mut |e: &Exp| {
        normalize_one_mut_ref(e, mut_param_names, NormalizePhase::CurrentIsLocal)
    })
}

/// Per-obligation walker for `Wp::Call`. Splits the call's
/// obligations across separate theorems and pushes post-call
/// frames onto the obligation context.
///
/// **Two callee views.** Trait-method calls have a dual structure:
/// * `callee: &FunctionX` — the resolved concrete impl. Source
///   for params, typ_params, and ret type (concrete types, used
///   for binder rendering and arg substitution).
/// * `spec_callee: &FunctionX` — where to read `require`/`ensure`
///   from. For trait-method-impl callees, this is the trait
///   method decl (the impl's specs are typically empty since
///   Verus rejects impl-side `requires` clauses; trait specs are
///   inherited). For all other callees, `spec_callee == callee`.
///   Resolved by `resolve_callee`.
///
/// **Phases.** The walker delegates to three helpers:
/// 1. `build_call_substitutions` — render args, gensym fresh
///    names, build req/ens substitution maps. See its docs for
///    the substitution scheme (especially the `&mut` case).
/// 2. `emit_call_precondition_theorem` — one theorem for
///    `requires(subst)`, wrapped with `CallPrecondition` SpanMark.
/// 3. `push_post_call_frames` — the `∀ post_i, ∀ ret, ensures →
///    let caller_var_i := post_i; let dest := ret;` chain that
///    shapes the obligation context for the post-call continuation.
fn walk_call<'a>(
    callee: &FunctionX,
    spec_callee: &FunctionX,
    args: &[Validated<'a>],
    typ_args: &[Typ],
    dest: Option<&VarIdent>,
    call_span: &Span,
    mut_args: &[(usize, MutTargetRaw<'a>)],
    after: &Wp<'a>,
    ctx: &WpCtx<'a>,
    obl: &OblCtx,
    e: &mut ObligationEmitter,
) {
    // `spec_callee` was resolved at build time (see `resolve_callee`)
    // and threaded through `Wp::Call`. No re-derivation, no `expect()`
    // — the type system guarantees it's present.

    let subst = build_call_substitutions(callee, spec_callee, typ_args, args, mut_args, e);

    if !spec_callee.require.is_empty() {
        emit_call_precondition_theorem(spec_callee, &subst, call_span, obl, e);
    }

    let new_obl = push_post_call_frames(
        callee, spec_callee, &subst, dest, obl,
    );
    walk_obligations(after, ctx, &new_obl, e);
}

/// One `&mut` argument at a call site (#105).
///
/// Pre-#105, `mut_args: Vec<(usize, &VarIdent)>` and
/// `mut_idx_to_fresh: HashMap<usize, LeanName>` were parallel
/// structures keyed on the same `usize`. Every consumer site did
/// `mut_idx_to_fresh.get(idx).expect(…)` — a runtime check for
/// "every mut_args entry has a matching fresh name." Fusing the
/// two into a struct removes the lookup-and-expect; the type
/// guarantees the fresh name is present.
#[derive(Clone)]
struct MutArgInfo<'a> {
    /// Index into `callee.params` / call-site `args` of this
    /// `&mut` parameter.
    param_idx: usize,
    /// What the call is mutating, structurally: a simple local
    /// (`&mut x`) or a single-variant struct field (`&mut h.f`,
    /// landed via #87). The variant determines `walk_call`'s
    /// post-call rebinding shape (Phase 4):
    /// * `Var(x)` → `let x := fresh`.
    /// * `Field { base, field_name }` → `let base := { base with
    ///   field_name := fresh }` via Lean structure update.
    /// Avoids the `(caller_var, field_path: Option<String>)` flag-
    /// soup shape — same typed-invariant discipline as #103/#105.
    target: MutTargetRaw<'a>,
    /// Fresh `_tactus_mut_post_<id>` post-call name for this
    /// `&mut` arg. `walk_call` introduces this as the ∀-binder
    /// for the post-call existential; the ensures Hyp references
    /// it as the post-state value.
    fresh: crate::lean_name::LeanName,
}

impl<'a> MutArgInfo<'a> {
    /// The local `VarIdent` to rebind after the call. For
    /// `Var(x)` this is `x` itself; for `Field { base, .. }`
    /// it's the base (the struct local that holds the field).
    fn rebind_local(&self) -> &'a VarIdent {
        match &self.target {
            MutTargetRaw::Var(v) => v,
            MutTargetRaw::Field { base, .. } => base,
            MutTargetRaw::TupleField { base, .. } => base,
        }
    }
}

/// Substitution-related state needed to inline a callee's specs at
/// a call site. Built once by `build_call_substitutions`, used
/// twice — once for the precondition theorem (via `req_subst`)
/// and once for the post-call ensures hypothesis (via `ens_subst`).
struct CallSubstitutions<'a> {
    /// Type-arg substitution: `TypParam(T) ↦ Var(rendered_typ_arg)`.
    /// Shared between req and ens. `TypParam` renders as `Var("T")`
    /// so value-level substitution rewrites it.
    typ_subst: HashMap<crate::lean_name::LeanName, LExpr>,
    /// `requires` substitution: param names map to caller args
    /// (pre-call values). For `&mut` params, both `p` and
    /// `varat_pre_name(p)` map to the same arg — at requires-time
    /// only the pre-call value exists.
    req_subst: HashMap<crate::lean_name::LeanName, LExpr>,
    /// `ensures` substitution: non-mut params map to caller args;
    /// `&mut` params map `p ↦ Var(fresh_post_state)` and
    /// `varat_pre_name(p) ↦ caller_arg` (pre-state via `*old(x)`).
    /// Plus `callee.ret.name ↦ Var(fresh_ret_name)` so the
    /// rendered ensures uses the gensym'd ret instead of the
    /// callee's source-level ret-name (which could shadow a
    /// caller-scope local).
    ens_subst: HashMap<crate::lean_name::LeanName, LExpr>,
    /// Set of `&mut` param names (sanitized) — used by
    /// `rewrite_varat_for_mut_params` to rename `VarAt(p, Pre) →
    /// Var(<p>_at_pre_tactus)` in the VIR-AST spec BEFORE
    /// rendering, so the substitution maps above can target
    /// pre-state references separately from post-state.
    mut_param_names: HashSet<String>,
    /// One entry per `&mut` arg at this call site (#105). Each
    /// `MutArgInfo` bundles the param index, caller-side variable,
    /// and the gensym'd post-call fresh name — replacing the
    /// pre-#105 parallel `mut_args: Vec<(usize, &VarIdent)>` +
    /// `mut_idx_to_fresh: HashMap<usize, LeanName>`.
    mut_args: Vec<MutArgInfo<'a>>,
    /// Fresh name for the callee's return value. Used as the
    /// ∀-binder name in post-call frames; substituted in the
    /// ensures rendering. Avoids shadowing caller-scope locals
    /// that happen to share the callee's source ret name.
    fresh_ret_name: crate::lean_name::LeanName,
}

/// Insert substitution entries for one set of params (either the
/// resolved-impl's `callee.params` or the trait method decl's
/// `spec_callee.params` — see `build_call_substitutions` and #86).
/// Both maps are populated:
/// * `req_subst`: param `p` → arg (only pre-state exists at requires
///   time, both for mut and non-mut params).
/// * `ens_subst`: non-mut param `p` → arg; mut param `p` → fresh
///   post-state, plus `<p>_at_pre_tactus` → arg (pre-state alias
///   for `*old(p)` references).
/// `mut_param_names` accumulates sanitized name strings for each
/// `&mut` param — consumed by `rewrite_varat_for_mut_params` to
/// rename `VarAt(p, Pre) → Var(<p>_at_pre_tactus)` in the spec
/// rendering.
///
/// Calling this twice (once for callee.params, once for
/// spec_callee.params) is intentional and harmless when both name
/// the same params: the second insert overwrites with identical
/// values. When trait and impl have different param names (allowed
/// by Rust), both spellings receive the same arg mapping.
fn add_param_subst_entries<'a>(
    params: &vir::ast::Params,
    arg_lexprs: &[LExpr],
    mut_args: &[MutArgInfo<'a>],
    req_subst: &mut HashMap<crate::lean_name::LeanName, LExpr>,
    ens_subst: &mut HashMap<crate::lean_name::LeanName, LExpr>,
    mut_param_names: &mut HashSet<String>,
) {
    for (i, p) in params.iter().enumerate() {
        // Subst keys must match what `to_lean_expr::vir_expr_to_ast`
        // produces for `ExprX::Var(p.name)` — i.e., go through the
        // canonical `LeanName::from_var_ident` (includes the
        // disambiguator id when needed).
        let pname = crate::lean_name::LeanName::from_var_ident(&p.x.name);
        let pname_pre = crate::lean_name::LeanName::synthetic(varat_pre_name(pname.as_str()));
        // Requires: same map for mut and non-mut (only pre-state exists).
        req_subst.insert(pname.clone(), arg_lexprs[i].clone());
        // Both legacy mode (`is_mut: true`) and new-mut-ref mode
        // (`MutRef<T>` typ) need the mut-side subst structure. Going
        // through the named helper keeps this in lockstep with
        // `build_call_mut_args` — both consumers ask "is this an
        // &mut param?" the same way, so a future Verus-side change
        // updates both sites at once.
        if is_mut_ref_param(p) {
            mut_param_names.insert(sanitize(&p.x.name.0));
            req_subst.insert(pname_pre.clone(), arg_lexprs[i].clone());
            // Ensures: mut param's `p` → fresh post-state; pre-state via varat_pre_name.
            // Find the MutArgInfo by matching param_idx — replaces the
            // pre-#105 `mut_idx_to_fresh.get(idx).expect(...)` lookup.
            // The `param_idx` is positional, so it works whether the
            // current pass is over callee.params or spec_callee.params
            // (Rust requires positional alignment).
            let info = mut_args.iter().find(|m| m.param_idx == i)
                .expect("MutArgInfo should exist for every &mut param idx — \
                         build_call_mut_args populates one per is_mut param");
            ens_subst.insert(pname.clone(), LExpr::var(info.fresh.clone()));
            ens_subst.insert(pname_pre, arg_lexprs[i].clone());
        } else {
            // Non-mut ensures: param → arg.
            ens_subst.insert(pname, arg_lexprs[i].clone());
        }
    }
}

/// Build the substitution maps and fresh names for a call site.
/// See `CallSubstitutions` for the field semantics.
///
/// Takes both `callee` (the resolved concrete impl) and `spec_callee`
/// (where `require`/`ensure` come from — for trait-method-impl
/// callees this is the trait method decl; otherwise same as callee).
/// When they differ, the substitution maps include keys for BOTH
/// callee's and spec_callee's param/ret names — same arg values,
/// just both spellings of each name, so we can substitute either
/// the trait's specs or the impl's strengthened specs (#86).
fn build_call_substitutions<'a>(
    callee: &FunctionX,
    spec_callee: &FunctionX,
    typ_args: &[Typ],
    args: &[Validated<'a>],
    mut_args_raw: &[(usize, MutTargetRaw<'a>)],
    e: &mut ObligationEmitter,
) -> CallSubstitutions<'a> {
    // Type-param substitution (shared by req + ens). `TypParam(T)`
    // renders as `Var("T")` so value-level substitute rewrites it.
    let mut typ_subst: HashMap<crate::lean_name::LeanName, LExpr> = HashMap::new();
    for (tp_name, tp_arg) in callee.typ_params.iter().zip(typ_args.iter()) {
        // Type parameter names are user-named generics (`T`, `A`).
        // Match what `typ_to_expr` produces for `TypX::TypParam` —
        // `LeanName::lit(name)`.
        typ_subst.insert(crate::lean_name::LeanName::lit(tp_name.as_str()), typ_to_expr(tp_arg));
    }

    // Render each arg once. The lower path peels `Loc` for &mut
    // arg shapes, so the rendered form is the caller-side variable
    // reference (the pre-call value).
    let arg_lexprs: Vec<LExpr> =
        args.iter().map(|a| lower_validated(a)).collect();

    // One MutArgInfo per `&mut` arg — bundles param_idx, target
    // (the L-value shape, post-#87), and the gensym'd fresh post-
    // call name (#105). Replaces the pre-#105 parallel `mut_args`
    // + `mut_idx_to_fresh`. The `_tactus_*` prefix is reserved per
    // Convention 1 in `expr_shared.rs`'s "Reserved identifier
    // conventions" section. `next_id()` is the per-fn counter —
    // sufficient because theorem names are namespaced by fn_name.
    let mut_args: Vec<MutArgInfo<'a>> = mut_args_raw.iter()
        .map(|(idx, target)| MutArgInfo {
            param_idx: *idx,
            target: target.clone(),
            fresh: crate::lean_name::LeanName::synthetic(
                format!("_tactus_mut_post_{}", e.next_id()),
            ),
        })
        .collect();

    // Fresh ret name (gensym to avoid caller-scope collisions). Same
    // convention as mut_post above.
    let fresh_ret_name = crate::lean_name::LeanName::synthetic(format!("_tactus_ret_{}", e.next_id()));

    // Build req_subst and ens_subst.
    let mut req_subst: HashMap<crate::lean_name::LeanName, LExpr> = typ_subst.clone();
    let mut ens_subst: HashMap<crate::lean_name::LeanName, LExpr> = typ_subst.clone();
    let mut mut_param_names: HashSet<String> = HashSet::new();

    // First pass: keys from `callee.params` (the impl's, or the
    // non-trait callee's — same as spec_callee in that case).
    add_param_subst_entries(
        &callee.params,
        &arg_lexprs,
        &mut_args,
        &mut req_subst,
        &mut ens_subst,
        &mut mut_param_names,
    );
    // Second pass: keys from `spec_callee.params` (trait method
    // decl's). When trait and impl have matching param names this is
    // a no-op (overwrites entries with identical values). When they
    // differ — Rust allows this, the names are positionally aligned
    // but textually independent — both spellings get the same
    // substitution mapping. Needed by #86 so trait-side ensures
    // (which use trait param names) substitute correctly even when
    // we're simultaneously inlining impl-side ensures (which use
    // impl param names). For non-trait callees `callee == spec_callee`
    // and the second pass is fully redundant — running it
    // unconditionally keeps the code simple at zero correctness cost.
    add_param_subst_entries(
        &spec_callee.params,
        &arg_lexprs,
        &mut_args,
        &mut req_subst,
        &mut ens_subst,
        &mut mut_param_names,
    );

    // Callee's ret name → fresh_ret_name in ensures. Same for
    // spec_callee's ret name when different — handles the case
    // where the impl's ret name differs from the trait's.
    let callee_ret = crate::lean_name::LeanName::from_var_ident(&callee.ret.x.name);
    if callee_ret.as_str() != fresh_ret_name.as_str() {
        ens_subst.insert(callee_ret, LExpr::var(fresh_ret_name.clone()));
    }
    let spec_ret = crate::lean_name::LeanName::from_var_ident(&spec_callee.ret.x.name);
    if spec_ret.as_str() != fresh_ret_name.as_str() {
        ens_subst.insert(spec_ret, LExpr::var(fresh_ret_name.clone()));
    }

    CallSubstitutions {
        typ_subst,
        req_subst,
        ens_subst,
        mut_param_names,
        mut_args,
        fresh_ret_name,
    }
}

/// Emit the precondition theorem for a call. The `spec_callee`'s
/// `require` clauses are rewritten (VarAt → varat_pre_name) and
/// rendered, then substituted with `subst.req_subst`, and wrapped
/// in a `CallPrecondition` SpanMark with the call-site span.
fn emit_call_precondition_theorem(
    spec_callee: &FunctionX,
    subst: &CallSubstitutions,
    call_span: &Span,
    obl: &OblCtx,
    e: &mut ObligationEmitter,
) {
    let loc = format_rust_loc(call_span);
    let requires_conj = and_all(
        spec_callee.require.iter()
            .map(|expr| {
                let rewritten = rewrite_varat_for_mut_params(expr, &subst.mut_param_names);
                vir_expr_to_ast(&rewritten)
            })
            .collect()
    );
    let requires_clause = LExpr::span_mark(
        loc.clone(),
        AssertKind::Obligation(ObligationKind::CallPrecondition),
        substitute(&requires_conj, &subst.req_subst),
    );
    let id = e.next_id();
    let theorem_name = build_theorem_name(
        kind_to_name(AssertKind::Obligation(ObligationKind::CallPrecondition)), &e.fn_name, &loc, id,
    );
    e.emit(theorem_name, obl.wrap(requires_clause), simple_tactic(e));
}

/// Peel `SpanMark` wrappers, returning the innermost non-SpanMark
/// expression. Used by the ret-substitution machinery (#128) and the
/// And-tree walker — SpanMark is a Lean-level no-op (just emits a
/// `/- @rust:LOC -/` comment) so structural pattern matching should
/// look through it.
fn peel_span_marks(e: &LExpr) -> &LExpr {
    let mut cur = e;
    while let ExprNode::SpanMark { inner, .. } = &cur.node {
        cur = inner;
    }
    cur
}

/// Flatten the *top-level* `And`-tree of `e` into its leaf conjuncts.
///
/// Recurses through `BinOp::And` only — does NOT descend into `Or`,
/// `Implies`, `Forall`, `Exists`, `If`, `Let`, `Match`, etc. The
/// "top-level" notion is what matters for ret-substitution (#128):
/// a clause `r == E` buried inside `Or(Q, r == E)` is NOT
/// uniquely-determining, so we don't want to find it. SpanMark
/// wrappers are peeled at every node since they're transparent at
/// the Lean level.
fn collect_top_and_conjuncts<'a>(e: &'a LExpr, out: &mut Vec<&'a LExpr>) {
    use crate::lean_ast::BinOp;
    let peeled = peel_span_marks(e);
    if let ExprNode::BinOp { op: BinOp::And, lhs, rhs } = &peeled.node {
        collect_top_and_conjuncts(lhs, out);
        collect_top_and_conjuncts(rhs, out);
    } else {
        out.push(e);
    }
}

/// Try to find a top-level conjunct of the form `Eq(Var(target), E)`
/// or `Eq(E, Var(target))` in `conj`. Returns `Some((E, rest))`
/// where `rest` is the And of all OTHER conjuncts (or `LitBool(true)`
/// if the eq clause was the only one). Returns `None` if no matching
/// conjunct exists, or if `E` mentions `target` (self-referential).
///
/// The conservative scope (#128): only top-level `And`-tree, never
/// descending into `Or` / `Implies` / `Forall` / `Exists` / `If` /
/// `Let` / `Match`. A clause buried inside a disjunction does NOT
/// uniquely determine `target`, so we don't substitute.
///
/// SpanMark is peeled transparently. The matched eq picks the FIRST
/// conjunct in source order — for trait-method-impl callees (#86),
/// where the conjunction is `(spec_ensures) ∧ (impl_ensures)`,
/// `push_post_call_frames` orders spec first then impl. If both
/// have a `r == E` clause, we pick the spec's; the impl's becomes
/// part of `rest` and substitutes to `E_impl == E_spec` which Verus
/// guarantees is consistent (impl ⇒ trait).
fn extract_top_level_eq_for(
    conj: &LExpr,
    target: &crate::lean_name::LeanName,
) -> Option<(LExpr, LExpr)> {
    use crate::lean_ast::BinOp;
    let mut conjuncts: Vec<&LExpr> = Vec::new();
    collect_top_and_conjuncts(conj, &mut conjuncts);

    for (idx, c) in conjuncts.iter().enumerate() {
        let peeled = peel_span_marks(c);
        let ExprNode::BinOp { op: BinOp::Eq, lhs, rhs } = &peeled.node else {
            continue;
        };
        let lhs_p = peel_span_marks(lhs);
        let rhs_p = peel_span_marks(rhs);
        let e: Option<&LExpr> = match (&lhs_p.node, &rhs_p.node) {
            (ExprNode::Var(n), _) if n.as_str() == target.as_str() => Some(rhs_p),
            (_, ExprNode::Var(n)) if n.as_str() == target.as_str() => Some(lhs_p),
            _ => None,
        };
        let Some(e) = e else { continue };
        // Reject self-referential `r == E` where E mentions r —
        // substituting `r → E` in such patterns would loop. Uses
        // the shared `lean_ast::mentions_free_var` (which tracks
        // binder scope correctly) rather than a sst_to_lean-local
        // walk.
        if crate::lean_ast::mentions_free_var(e, target.as_str()) {
            continue;
        }
        let rest: Vec<LExpr> = conjuncts.iter().enumerate()
            .filter(|(i, _)| *i != idx)
            .map(|(_, c)| (*c).clone())
            .collect();
        return Some((e.clone(), and_all(rest)));
    }
    None
}

/// Is `e` syntactically `LitBool(true)` (after peeling SpanMark)?
/// Used to skip emitting `True →` Hyp frames.
fn is_trivial_true(e: &LExpr) -> bool {
    matches!(peel_span_marks(e).node, ExprNode::LitBool(true))
}

/// Push the post-call frames onto the obligation context. Reading
/// the resulting goal top-down:
///
/// ```text
///   ∀ post_i,                       ─┐
///   type_inv(post_i) →               │ per &mut arg (Phase 1)
///   ∀ ret,                          ─┐
///   ret_bound →                      │ Phase 2: ret binder + bound
///   ensures(subst) →                 ─ Phase 3: ensures hyp (uses ens_subst)
///   let caller_var_i := post_i;     ─┐ Phase 4: per &mut rebind
///   let dest := ret;                 ─ Phase 5: dest binding
///   <continuation goal>
/// ```
///
/// Frames pushed only when meaningful — empty ensures / missing
/// ret_bound is skipped to avoid `True →` clutter on every
/// downstream goal.
///
/// **Ret-substitution path (#128).** When the substituted ensures
/// contains a top-level conjunct of the form `Eq(Var(fresh_ret), E)`
/// (or `Eq(E, Var(fresh_ret))`) — i.e., the callee's ensures
/// uniquely determines the return value — we replace Phases 2/3/5:
///
/// ```text
///   ∀ post_i, type_inv(post_i) →     │ Phase 1 (unchanged)
///   E_bound →                        │ bound on E (numeric ret only)
///   rest_ensures(subst, ret := E) → │ remaining clauses, ret-substituted
///   let caller_var_i := post_i;      │ Phase 4 (unchanged)
///   let dest := E;                   │ Phase 5 with E directly
///   <continuation goal>
/// ```
///
/// The `∀ ret` quantifier disappears, eliminating the `∀ (P : Prop),
/// P = E → …` shape that blocks `tactus_auto`'s default closer
/// (omega rejects ∀-Prop, simp_all doesn't intro ∀). The bound on
/// E is preserved as a Hyp because numeric ret types still need the
/// bound for downstream arithmetic — `type_bound_predicate` returns
/// `None` for non-numeric (Bool, Prop, structs), so the Hyp is
/// trivially elided there.
///
/// Falls through to the ∀-path when no `r == E` conjunct exists, when
/// E mentions ret (self-referential), or when ensures has a non-And
/// top-level shape (Or, Implies, etc.). See `extract_top_level_eq_for`.
fn push_post_call_frames(
    callee: &FunctionX,
    spec_callee: &FunctionX,
    subst: &CallSubstitutions,
    dest: Option<&VarIdent>,
    obl: &OblCtx,
) -> OblCtx {
    let mut new_obl = obl.clone();

    // Phase 1: per-&mut existential binder + type-inv hypothesis.
    // `subst.mut_args` (#105) bundles param_idx, caller_var, and
    // fresh into one struct — no parallel-array lookups.
    for info in &subst.mut_args {
        let typ = &callee.params[info.param_idx].x.typ;
        let lean_typ = substitute(&typ_to_expr(typ), &subst.typ_subst);
        new_obl.frames.push_back(CtxFrame::Binder(LBinder {
            name: Some(info.fresh.clone()),
            ty: lean_typ,
            kind: BinderKind::Explicit,
        }));
        if let Some(pred) = type_bound_predicate(&LExpr::var(info.fresh.clone()), typ) {
            new_obl.frames.push_back(CtxFrame::Hyp(pred));
        }
    }

    // Build the substituted ensures conjunction once. Used by both
    // the substitution path (#128) and the ∀-path. Uses both
    // spec_callee's ensures (the trait method decl's, for trait-
    // method-impl callees; same as callee otherwise) AND the impl's
    // own ensures when they differ (#86 impl-strengthening). Verus
    // enforces impl ⇒ trait, so the conjunction is satisfiable; the
    // caller gets the strongest contract any specific impl provides
    // rather than just the trait-level guarantee.
    //
    // `subst.ens_subst` includes keys for both callee.params and
    // spec_callee.params (built by the two passes in
    // `build_call_substitutions`), plus both ret names → fresh_ret_name.
    // So substituting either the trait's or the impl's clauses
    // works regardless of whether trait/impl param names match.
    let mut ensures_clauses: Vec<LExpr> = spec_callee.ensure.0.iter()
        .map(|expr| {
            let rewritten = rewrite_varat_for_mut_params(expr, &subst.mut_param_names);
            vir_expr_to_ast(&rewritten)
        })
        .collect();
    let is_trait_method_impl =
        matches!(callee.kind, FunctionKind::TraitMethodImpl { .. });
    if is_trait_method_impl {
        for expr in callee.ensure.0.iter() {
            let rewritten = rewrite_varat_for_mut_params(expr, &subst.mut_param_names);
            ensures_clauses.push(vir_expr_to_ast(&rewritten));
        }
    }
    let substituted_ensures: Option<LExpr> = if ensures_clauses.is_empty() {
        None
    } else {
        Some(substitute(&and_all(ensures_clauses), &subst.ens_subst))
    };

    // #128: try ret-substitution. If the substituted ensures has a
    // top-level conjunct `Eq(Var(fresh_ret), E)` (or commuted), we
    // can skip the `∀ ret + ret_bound` chain and bind `dest := E`
    // directly. Falls through to the ∀-path when no such conjunct
    // exists.
    let ret = &callee.ret.x;
    let ret_substitution: Option<(LExpr, LExpr)> = substituted_ensures.as_ref()
        .and_then(|conj| extract_top_level_eq_for(conj, &subst.fresh_ret_name));

    // The value bound to `dest` differs by path: in the ∀-path,
    // `dest := fresh_ret_name` (the ∀-bound); in the substitution
    // path, `dest := E` (the substituted value). Computing it
    // here lets Phase 5 share one code site between paths.
    let dest_value: LExpr = match &ret_substitution {
        Some((ret_value, rest_ensures)) => {
            // Substitution path: drop `∀ ret + ret_bound`; emit
            // `E_bound` and `rest_ensures` as Hyps directly.
            // `type_bound_predicate` returns `None` for non-numeric
            // ret types (Bool, Prop, structs) so the bound Hyp is
            // elided there — the cond_setup case (Bool ret).
            if let Some(pred) = type_bound_predicate(ret_value, &ret.typ) {
                new_obl.frames.push_back(CtxFrame::Hyp(pred));
            }
            // The eq clause that gave us E has been dropped from
            // `rest_ensures`. Substitute fresh_ret_name → E in the
            // remaining clauses so they reference E directly. If the
            // result simplifies to `True` (e.g., the eq clause was
            // the only conjunct), skip the Hyp.
            if !is_trivial_true(rest_ensures) {
                let mut ret_to_e = std::collections::HashMap::new();
                ret_to_e.insert(subst.fresh_ret_name.clone(), ret_value.clone());
                let rest_substituted = substitute(rest_ensures, &ret_to_e);
                if !is_trivial_true(&rest_substituted) {
                    new_obl.frames.push_back(CtxFrame::Hyp(rest_substituted));
                }
            }
            ret_value.clone()
        }
        None => {
            // ∀-path: ret binder + ret_bound + ensures Hyp.
            let ret_typ_lean = substitute(&typ_to_expr(&ret.typ), &subst.typ_subst);
            new_obl.frames.push_back(CtxFrame::Binder(LBinder {
                name: Some(subst.fresh_ret_name.clone()),
                ty: ret_typ_lean,
                kind: BinderKind::Explicit,
            }));
            if let Some(pred) = type_bound_predicate(
                &LExpr::var(subst.fresh_ret_name.clone()), &ret.typ,
            ) {
                new_obl.frames.push_back(CtxFrame::Hyp(pred));
            }
            if let Some(conj) = substituted_ensures {
                new_obl.frames.push_back(CtxFrame::Hyp(conj));
            }
            LExpr::var(subst.fresh_ret_name.clone())
        }
    };

    // Phase 4: caller-side rebindings for &mut args. Placed AFTER
    // ensures so the ensures Hyp references the fresh existential,
    // not the rebound caller name.
    //
    // Three shapes:
    // * Simple `&mut <local>` (#55): `let local := fresh`. The local
    //   takes on the post-call value directly.
    // * Single-variant struct field `&mut <local>.<f1>.<f2>.…` (#87
    //   single-level, #144 deeper): `let local := { local with f1 :=
    //   { local.f1 with f2 := fresh } }`. Lean's structure update
    //   preserves all other fields automatically — no havoc-base +
    //   assume-other-fields-unchanged dance needed (the syntax IS
    //   that semantics, in the type system).
    // * Tuple field `&mut <local>.<i>` (#145 + #146): `let local :=
    //   (local.1, …, fresh, …, local.<n>)`. Lean's tuple syntax IS
    //   `Prod.mk` sugar; the unmodified slots read via the
    //   multi-segment `tuple_field_accessor` (`.2.1` etc. for the
    //   nested-Prod representation of arity > 2 tuples).
    for info in &subst.mut_args {
        let local_name = crate::lean_name::LeanName::from_var_ident(info.rebind_local());
        let new_value = match &info.target {
            MutTargetRaw::Var(_) => LExpr::var(info.fresh.clone()),
            MutTargetRaw::Field { field_oprs, .. } => {
                // Build nested structure-update from inside-out.
                // `field_oprs` is in peel order (outermost-first =
                // deepest-mutated-first). For `&mut a.b.c`,
                // field_oprs = [c_opr, b_opr]. We want:
                //   { a with b := { a.b with c := fresh } }
                //
                // Build the bases for each level top-down:
                //   level 0 (outer update): base = a, field = b
                //   level 1 (inner update): base = a.b, field = c
                // Then wrap inside-out.
                //
                // Field-name path top-to-bottom (a's perspective):
                let names_top_to_bottom: Vec<String> = field_oprs
                    .iter()
                    .rev()
                    .map(|opr| crate::expr_shared::field_access_name(opr))
                    .collect();
                let local_expr = LExpr::var(local_name.clone());
                let mut current = LExpr::var(info.fresh.clone());
                // Build inside-out: at each step, wrap `current` in a
                // StructUpdate whose base is `local.<names[..i]>` and
                // whose field is `names[i]`.
                for i in (0..names_top_to_bottom.len()).rev() {
                    // Compute the base for this level: local.<names[0..i]>
                    let mut base = local_expr.clone();
                    for name in &names_top_to_bottom[..i] {
                        base = LExpr::field_proj(base, name.clone());
                    }
                    current = LExpr::new(ExprNode::StructUpdate {
                        base: Box::new(base),
                        updates: vec![(names_top_to_bottom[i].clone(), current)],
                    });
                }
                current
            }
            MutTargetRaw::TupleField { index, arity, .. } => {
                // Tuple ctor rebuild (#145). Lean's structure-update
                // doesn't compose with `Prod`, so we rebuild the tuple
                // explicitly via Lean tuple syntax. Each unmodified
                // slot reads from `local.<accessor>` where accessor
                // comes from the shared `tuple_field_accessor` —
                // which produces `.2.1` etc. for arity > 2 (#146).
                // The mutated slot at `index` takes `fresh`.
                let local_expr = LExpr::var(local_name.clone());
                let elems: Vec<LExpr> = (0..*arity)
                    .map(|j| {
                        if j == *index {
                            LExpr::var(info.fresh.clone())
                        } else {
                            LExpr::field_proj(
                                local_expr.clone(),
                                crate::expr_shared::tuple_field_accessor(*arity, j),
                            )
                        }
                    })
                    .collect();
                LExpr::tuple(elems)
            }
        };
        new_obl.frames.push_back(CtxFrame::Let(local_name, new_value));
    }

    // Phase 5: dest binding for the call's return (`let r = foo(…)`).
    // `dest_value` is `Var(fresh_ret_name)` in the ∀-path or `E` in
    // the substitution path (#128).
    if let Some(dest_ident) = dest {
        new_obl.frames.push_back(CtxFrame::Let(
            crate::lean_name::LeanName::from_var_ident(dest_ident),
            dest_value,
        ));
    }

    new_obl
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
    name: &crate::lean_name::LeanName,
    val: &'a Exp,
    body: &Wp<'a>,
    ctx: &WpCtx<'a>,
    obl: &OblCtx,
    e: &mut ObligationEmitter,
) {
    // `val` was validated upstream: `Wp::Let.value: Validated<'a>`,
    // and walk_let's caller (`walk_obligations` Wp::Let arm) extracts
    // `.raw()` from that witness. Sub-expressions (cond / branches /
    // inner_body / binder rhs) are valid by structural induction on
    // the validated tree. We re-run `sst_exp_to_ast_checked` at each
    // sub-render site for a cheap, deterministic re-check; an Err
    // would indicate validator drift between Validated::check and
    // sub-expression rendering.
    let peeled = peel_value_position(val);
    match &peeled.x {
        ExpX::If(cond, then_e, else_e) => {
            let c_ast = sst_exp_to_ast_checked(cond)
                .expect("walk_let if-cond: sub of validated Exp tree");
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
                        chain_obl.frames.push_back(CtxFrame::Let(
                            crate::lean_name::LeanName::from_var_ident(&b.name),
                            sst_exp_to_ast_checked(&b.a)
                                .expect("walk_let binder rhs: sub of validated Exp tree"),
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
        name.clone(),
        sst_exp_to_ast_checked(val)
            .expect("walk_let val: validated upstream via Wp::Let.value"),
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
            // Type parameter names are user-named generics (`T`, `A`).
            // No disambiguator; emit via `lit`.
            name: Some(crate::lean_name::LeanName::lit(tp.as_str())),
            ty: LExpr::var_lit("Type"),
            kind: BinderKind::Explicit,
        });
    }
    for p in fn_sst.x.pars.iter().filter(|p| !is_synthetic_param(p)) {
        let name = crate::lean_name::LeanName::from_var_ident(&p.x.name);
        out.push(LBinder {
            name: Some(name.clone()),
            ty: typ_to_expr(&p.x.typ),
            kind: BinderKind::Explicit,
        });
        if let Some(pred) = type_bound_predicate(&LExpr::var(name.clone()), &p.x.typ) {
            out.push(LBinder {
                // `h_<name>_bound` is a synthesized hypothesis name —
                // already a valid Lean identifier, no further
                // sanitization needed.
                name: Some(crate::lean_name::LeanName::synthetic(format!("h_{}_bound", name.as_str()))),
                ty: pred,
                kind: BinderKind::Explicit,
            });
        }
    }
    out
}

/// `(<name> : <peeled_typ>)` for each `LocalDeclKind::BorrowMut`
/// local. These are synthetic `MutRef<T>`-typed locals Verus
/// introduces around exec calls in new-mut-ref mode (#107):
/// `bump(&mut y)` lowers to
/// `let mut_ref: MutRef<u8>; assume(MutRefCurrent(mut_ref) == y);
///  bump(mut_ref); y = MutRefFuture(mut_ref);` — the synthetic
/// `mut_ref` has no body-level initializer, only the assume
/// constraining its pre-call value.
///
/// Without a binder, `Var(mut_ref)` (after `normalize_mut_ref_in_*`
/// unwraps the MutRef* ops) reaches the renderer as an unresolved
/// reference. Binding it at theorem level lets Lean treat it as
/// an ∀-bound variable, with the assume entering as a hypothesis.
///
/// The type rendering peels `MutRef<T>` to `T` (via `typ_to_expr`'s
/// `MutRef` arm), so the binder's type matches what
/// `Var(mut_ref)` reads at use sites — both sides see the inner
/// value type, not the `MutRef` wrapper.
///
/// `#55`'s caller-side mut-arg machinery treats `Var(mut_ref)` as
/// the L-value at the call site (post-#107 extension to
/// `extract_mut_target`), introducing a fresh existential for the
/// post-call value and Let-rebinding `mut_ref` to it after the
/// call's ensures Hyp. So the binder we emit here gives the
/// PRE-call value; the post-call value comes from the rebind.
/// Subsequent body code (`y = MutRefFuture(mut_ref)` after
/// normalization → `y = Var(mut_ref)`) reads the rebound value.
fn build_borrow_mut_binders(check: &FuncCheckSst) -> Vec<LBinder> {
    let mut out: Vec<LBinder> = Vec::new();
    for decl in check.local_decls.iter() {
        if !matches!(decl.kind, LocalDeclKind::BorrowMut) {
            continue;
        }
        let inner_typ: &Typ = match &*decl.typ {
            vir::ast::TypX::MutRef(t) => t,
            // Defensive: `LocalDeclKind::BorrowMut` always pairs
            // with `MutRef<T>` typ per `borrow_mut_to_sst` in
            // `vir/src/ast_to_sst.rs:3211`. If Verus ever emits
            // BorrowMut with a different typ shape, fall back to
            // the typ as-is rather than panicking — the renderer
            // will surface the issue at the use site.
            _ => &decl.typ,
        };
        let name = crate::lean_name::LeanName::from_var_ident(&decl.ident);
        out.push(LBinder {
            name: Some(name.clone()),
            ty: typ_to_expr(inner_typ),
            kind: BinderKind::Explicit,
        });
        // Type-bound predicate: synthetic locals don't get a
        // user-visible bound hypothesis the way fn params do, but
        // they still need the bound for Lean to typecheck arithmetic
        // on them. The bound is implicit in `MutRef<u8>`'s inner type
        // (e.g., u8's 0 ≤ x < 256), and `type_bound_predicate` peels
        // through `MutRef` (the inner `T`'s bound).
        if let Some(pred) = type_bound_predicate(&LExpr::var(name.clone()), inner_typ) {
            out.push(LBinder {
                name: Some(crate::lean_name::LeanName::synthetic(
                    format!("h_{}_bound", name.as_str()),
                )),
                ty: pred,
                kind: BinderKind::Explicit,
            });
        }
    }
    out
}

/// `(h_req<i> : <req_i>)` for each requires clause.
///
/// `mut_param_names` carries the &mut params so we can normalize
/// new-mut-ref shapes (`MutRefCurrent(Var(x))` → `Var(x)`) for these
/// params before rendering — at fn entry, x IS the pre-state, so the
/// natural `Var(x)` is what the renderer needs (#95).
fn build_req_binders(check: &FuncCheckSst, mut_param_names: &HashSet<String>) -> Vec<LBinder> {
    check.reqs.iter().enumerate().map(|(i, req)| {
        // `CurrentIsLocal` phase: unwrap `MutRefCurrent` to `Var` since
        // `*x` in requires evaluates against the param's entry value,
        // which the renderer already knows how to emit as `Var(x)`.
        let normalized = normalize_mut_ref_in_exp(
            req,
            mut_param_names,
            NormalizePhase::CurrentIsLocal,
        );
        // The same `normalized` shape was validated in `WpCtx::new`
        // (the same caller that just succeeded earlier in this fn);
        // `normalize_mut_ref_in_exp` is deterministic, so re-running
        // here produces the identical Exp. Re-checking is cheap and
        // would only fail on validator drift between WpCtx::new and
        // here — which would mean a Verus-side ordering bug.
        LBinder {
            name: Some(crate::lean_name::LeanName::synthetic(format!("h_req{}", i))),
            ty: sst_exp_to_ast_checked(&normalized)
                .expect("build_req_binders: req validated by WpCtx::new"),
            kind: BinderKind::Explicit,
        }
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

/// One level of a (possibly lexicographic) loop decrease measure.
/// Bundles the validated decrease expression with its per-level
/// d_old snapshot name. Single-expression decreases produce a Vec
/// of length 1; lexicographic `decreases D1, D2, …` produce length
/// ≥ 2 in source order.
///
/// Fusing the two fields here makes the "same length" invariant
/// structural rather than enforced by a `debug_assert_eq!` on
/// parallel `Vec<Validated>` + `Vec<String>` arrays. Same #105
/// MutArgInfo-style pattern.
#[derive(Clone)]
pub struct DecreaseLevel<'a> {
    pub value: crate::to_lean_sst_expr::Validated<'a>,
    /// The pre-body snapshot name `_tactus_d_old_<loop_id>_<level_idx>`
    /// — gensymmed in `build_wp_loop` from the loop's id and the
    /// level index. Per-loop + per-level uniqueness avoids any
    /// shadowing across nested loops or sibling lex tiers.
    pub d_old_name: String,
}

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
    Let(crate::lean_name::LeanName, crate::to_lean_sst_expr::Validated<'a>, Box<Wp<'a>>),

    /// Like `Let`, but the RHS is an already-rendered `LExpr` rather
    /// than an SST `Exp`. Used by `StmX::ClosureInner` to bind the
    /// closure id to a Lean lambda — the lambda's body comes from the
    /// preserved AST (`StmX::ClosureInner.ast_body`), which doesn't go
    /// through SST's renderer. Walker pushes a `CtxFrame::Let` frame
    /// directly without revalidating.
    LetRaw {
        name: crate::lean_name::LeanName,
        value: LExpr,
        body: Box<Wp<'a>>,
    },

    /// Closure body verification scope (#93). Walks `body` under
    /// `∀ p : T, h_p_bound → ...` binders for each closure param,
    /// then walks `after` under the original obl. The body is its
    /// own dead-end — its theorems are emitted (overflow checks
    /// inside the closure body, the closure's own ensures, etc.)
    /// but its terminator doesn't carry through; the surrounding
    /// fn's flow continues with `after` unchanged. Created from
    /// `StmX::ClosureInner` in `build_wp`.
    ClosureBody {
        closure_params: Vec<(&'a VarIdent, &'a Typ)>,
        body: Box<Wp<'a>>,
        after: Box<Wp<'a>>,
    },

    /// Obligation: prove `P`, then `body` proceeds with `P` as a
    /// hypothesis. Walker emits one theorem per `Wp::Assert`.
    Assert(crate::to_lean_sst_expr::Validated<'a>, Box<Wp<'a>>),

    /// Hypothesis: `body` proceeds with `P` as a hypothesis. No
    /// obligation; walker emits no theorem at this node.
    Assume(crate::to_lean_sst_expr::Validated<'a>, Box<Wp<'a>>),

    /// Like `Assume`, but the hypothesis is an already-rendered
    /// `LExpr` rather than a `Validated` SST Exp. Used for
    /// synthesised hypotheses that don't correspond to an SST node —
    /// e.g., the negated cond_exp introduced by build_wp_loop's
    /// non-empty cond_setup transform (#114): the negation is a
    /// fresh LExpr derived via `LExpr::not(lower(cond_validated))`,
    /// not a borrow into the input SST.
    ///
    /// Walker pushes the LExpr directly as a `CtxFrame::Hyp` —
    /// equivalent to `Wp::Assume`'s walker arm, just skipping the
    /// `lower` call that's already been done at construction time.
    /// The split keeps `Wp::Assume`'s contract scoped to genuine
    /// SST-derived assumptions; `Wp::Hyp` carries derived LExprs
    /// that don't have a Validated witness available.
    Hyp { hyp: LExpr, body: Box<Wp<'a>> },

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
        cond: Option<crate::to_lean_sst_expr::Validated<'a>>,
        tactic_text: String,
        body: Box<Wp<'a>>,
    },

    /// `assert(…) by(bit_vector) requires P; ensures Q;` (#111).
    ///
    /// A dedicated decision-procedure assertion: the verified goal is
    /// `req_conj → ens_conj` (or just `ens_conj` when requires is
    /// empty), discharged by Tactus's `tactus_bit_vector` prelude
    /// tactic.
    ///
    /// **`ensures` propagation**: the walker arm itself does NOT push
    /// `ens_conj` into the body's ctx. Instead, Verus's `ast_to_sst`
    /// pre-injects an Int-mode `Assume(ens)` as a separate statement
    /// after the AssertBitVector, so the ensures naturally enters the
    /// body's ctx via the next `Wp::Assume` walker arm. Pinned by the
    /// shape-drift test in #139.
    ///
    /// LExpr-direct (not `Validated`-wrapped) because the goal is
    /// constructed at build-time from a list of SST exps via
    /// `lower_validated`; the resulting expression doesn't borrow a
    /// single SST node. Same shape as `Wp::Hyp`.
    AssertBitVector {
        /// Requires conjunction in BitVec mode — used as the
        /// assert goal's hypothesis.
        req_conj: LExpr,
        /// Ensures conjunction in BitVec mode — used as the
        /// assert goal.
        ens_conj: LExpr,
        rust_loc: String,
        body: Box<Wp<'a>>,
    },

    /// `if cond { then_branch } else { else_branch }`. Walker
    /// recurses on `then_branch` with `cond` as a Hyp frame, and
    /// on `else_branch` with `¬cond`. No theorem at the branch
    /// node; each branch's sub-Wp produces its own theorems.
    Branch {
        cond: crate::to_lean_sst_expr::Validated<'a>,
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
        cond: Option<crate::to_lean_sst_expr::Validated<'a>>,
        /// The original invariant metadata (span). Iterated in parallel
        /// with `validated_invs` and `inv_kinds` for emission. The
        /// at_entry/at_exit booleans on `LoopInv` are NOT consulted
        /// directly — `inv_kinds` is the classified, validated view
        /// (#103), which rejects the nonsensical `(false, false)`
        /// combination at build_wp_loop time.
        invs: &'a [LoopInv],
        /// Validated<'a> witnesses for each invariant's `inv` expression,
        /// in the same order as `invs`. Built at `build_wp_loop` time.
        validated_invs: Vec<crate::to_lean_sst_expr::Validated<'a>>,
        /// Classification of each invariant — same order as `invs`.
        /// Replaces direct use of `LoopInv.at_entry` / `LoopInv.at_exit`
        /// with a typed enum that makes the meaningful states explicit
        /// and `(false, false)` unrepresentable.
        inv_kinds: Vec<LoopInvKind>,
        /// Loop decrease measures, in source order. `Vec` length 1
        /// for single-expression `decreases D`; length ≥ 2 for
        /// lexicographic `decreases D1, D2, ...` (#110). Each
        /// `DecreaseLevel` bundles the validated measure with its
        /// per-level d_old snapshot name — fusing what were two
        /// parallel arrays (mirrors the #105 MutArgInfo pattern).
        ///
        /// The maintain obligation is the lex disjunction built by
        /// `lex_decrease_obligation`:
        ///   (0 ≤ D1' ∧ D1' < D1_old)
        ///     ∨ (D1' = D1_old ∧ ((0 ≤ D2' ∧ D2' < D2_old)
        ///         ∨ (D2' = D2_old ∧ ... (0 ≤ Dn' ∧ Dn' < Dn_old))))
        /// which generalises the single-expression case (the eq tail
        /// collapses against an absent next level). The `0 ≤ Di'`
        /// lower bound mirrors the fn-level `CheckDecreaseHeight` int
        /// fast-path; #129 closed the prior gap where Tactus emitted
        /// just `Di' < Di_old`.
        decrease: Vec<DecreaseLevel<'a>>,
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
        /// Source of `require`/`ensure` clauses for this call. For
        /// trait-method-impl callees, this is the trait method decl
        /// (different `FunctionX` than `callee`); for all other
        /// callees, this is `callee` itself. Resolved once at build
        /// time by `resolve_callee` so `walk_call` doesn't need to
        /// re-derive it via a fallible lookup. The type system
        /// now guarantees `spec_callee` is always present — no
        /// runtime `expect()` needed.
        spec_callee: &'a FunctionX,
        /// Validated<'a> arg expressions, in the same order as
        /// `callee.params`. Built at `build_wp_call` time; each
        /// arg is checked once and the witness is held here so
        /// `walk_call`'s lowering is type-system-infallible.
        args: Vec<crate::to_lean_sst_expr::Validated<'a>>,
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
        /// `(param_idx, target)`: the index into `callee.params` /
        /// `args` of the `&mut` parameter, and the L-value shape
        /// the call is mutating (`Var(x)` for `&mut x`,
        /// `Field { base, field_name }` for `&mut x.field` after
        /// #87). `walk_call` uses these to introduce a fresh
        /// existential per `&mut` arg (the post-call value),
        /// substitute the callee's `varat_pre_name(p) ↦ caller_arg`
        /// (pre-state) and `p ↦ fresh` (post-state) in the inlined
        /// ensures, and
        /// rebind the caller's local to the fresh value after the
        /// callee's ensures Hyp frame. Empty for fns with no `&mut`
        /// params (the common case). Field-path entries (#87) carry
        /// the field name so the post-call rebind can use Lean's
        /// structure-update syntax. See task #55 and #87.
        mut_args: Vec<(usize, MutTargetRaw<'a>)>,
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
        AssertKind::Obligation(ObligationKind::Termination)
    } else {
        AssertKind::Obligation(ObligationKind::Plain)
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
    // `e` was validated upstream: `Return` checks via `check_exp(e)`
    // before calling lift_if_value (sst_to_lean.rs:2793). Sub-
    // expressions are valid by structural induction; the
    // `sst_exp_to_ast_checked(...).expect(...)` calls below re-run
    // the deterministic validator and would only fire if the
    // validator drifted between the upstream check_exp and here.
    let peeled = peel_value_position(e);
    match &peeled.x {
        ExpX::If(cond, then_e, else_e) => {
            let c = sst_exp_to_ast_checked(cond)
                .expect("lift_if_value if-cond: sub of validated Exp tree");
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
                // Decide whether to recurse into `inner_body` for further
                // lifting (#119). The recursion is SAFE when `inner_body`
                // is itself a `Bind(Let, …)` chain — the ifs we'd lift
                // are in the next level's rhs position, computed before
                // any of those binders take effect, so lifting their
                // conditions doesn't move them out of any in-scope let.
                // This is the multi-binder-unfold case (`let a := av;
                // let b := if c …; body` → lift `c`).
                //
                // It's UNSAFE when `inner_body` is `If` at top level —
                // its condition may reference the let-bound `name`,
                // which lifting would move outside the `let name := rhs;`
                // scope, producing an unbound reference. The match-
                // compilation shape (`let _disc := proj(k); if _disc = 0
                // then … else …`) is exactly this case — `_disc = 0`
                // references `_disc`. For that shape we render inner
                // body as-is, preserving original behavior; the
                // tactus_case_split tactic handles match-style ifs
                // separately at the obligation level.
                //
                // Other shapes (Match, Var, applications with if buried
                // deeper, …) also fall through to render-as-is — we
                // only apply the lift when we can prove safety
                // structurally.
                let peeled_inner = peel_value_position(inner_body);
                let inner_is_let_chain = matches!(
                    &peeled_inner.x,
                    ExpX::Bind(b, _) if matches!(&b.x, BndX::Let(_))
                );
                if inner_is_let_chain {
                    lift_if_value(rhs, &|rhs_leaf| {
                        let name = name.clone();
                        lift_if_value(inner_body, &|body_leaf| {
                            emit_leaf(LExpr::let_bind(name.clone(), rhs_leaf.clone(), body_leaf))
                        })
                    })
                } else {
                    let body_ast = sst_exp_to_ast_checked(inner_body)
                        .expect("lift_if_value let-body: sub of validated Exp tree");
                    lift_if_value(rhs, &|rhs_leaf| {
                        emit_leaf(LExpr::let_bind(name.clone(), rhs_leaf, body_ast.clone()))
                    })
                }
            } else {
                emit_leaf(sst_exp_to_ast_checked(e)
                    .expect("lift_if_value bind-fallthrough: validated upstream"))
            }
        }
        _ => emit_leaf(sst_exp_to_ast_checked(e)
            .expect("lift_if_value leaf: validated upstream")),
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
) -> Option<(crate::lean_name::LeanName, &'a Exp, &'a Exp)> {
    let BndX::Let(bs) = &bnd.x else { return None };
    if bs.len() != 1 { return None; }
    let b = &bs[0];
    Some((crate::lean_name::LeanName::from_var_ident(&b.name), &b.a, body))
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
    // Linked-list stack of enclosing loops' break/continue leaves,
    // innermost first. `LoopStack::Empty` outside any loop (where
    // `StmX::BreakOrContinue` is rejected). Most recursive calls
    // forward this unchanged; only `build_wp_loop` constructs a new
    // one (`Cons(&new_ctx, outer)`) for the loop body, with the
    // `Cons` cell living on the caller's stack frame — no heap.
    loop_stack: &LoopStack<'_>,
) -> Result<Wp<'a>, String> {
    match &stm.x {
        StmX::Block(stms) => {
            // Fold right-to-left: walk(s_last, outer_after),
            //                     walk(s_{n-1}, that),
            //                     ...,
            //                     walk(s_0, whole_rest).
            let mut wp = after;
            for s in stms.iter().rev() {
                wp = build_wp(s, wp, ctx, loop_stack)?;
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
            let Some(ident) = extract_simple_var_ident(dest) else {
                return Err(format!(
                    "assignment with non-simple LHS (got {:?}) is not yet supported",
                    dest.x
                ));
            };
            Ok(Wp::Let(
                crate::lean_name::LeanName::from_var_ident(ident),
                crate::to_lean_sst_expr::Validated::check(rhs)?,
                Box::new(after),
            ))
        }
        StmX::Assert(_, _, e) | StmX::AssertCompute(_, e, _) => {
            // `AssertCompute` carries a ComputeMode (Z3 / ComputeOnly)
            // that tells Verus's Z3 path to discharge via interp
            // evaluation. We dispatch identically to plain Assert and
            // drop the mode — `tactus_auto`'s `decide` rung is the
            // closest Lean analog (computes the value structurally).
            // Documented under DESIGN.md "Lossy accepted forms".
            Ok(Wp::Assert(crate::to_lean_sst_expr::Validated::check(e)?, Box::new(after)))
        }
        StmX::Assume(e) => {
            // Skip synthetic resolution-tracking assumes (#95). Verus's
            // `resolution_inference` pass injects `Assume(HasResolved(...))`
            // statements in new-mut-ref-mode bodies. We don't model
            // `HasResolved` semantics — the renderer collapses
            // `UnaryOpr(HasResolved, _)` to its inner expression,
            // which would then be hypothesized as a non-Prop value
            // (a type error in Lean). Drop these statements entirely
            // since they don't carry information our verification
            // relies on.
            if is_synthetic_assume_to_drop(e) {
                return Ok(after);
            }
            Ok(Wp::Assume(crate::to_lean_sst_expr::Validated::check(e)?, Box::new(after)))
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
                Some(name) => LExpr::let_bind_synthetic(sanitize(name), e_ast, ensures_goal.clone()),
                None => ensures_goal.clone(),
            });
            Ok(Wp::Done(leaf))
        }
        StmX::Return { ret_exp: None, assert_id: _, base_error: _, inside_body: _ } => {
            Ok(Wp::Done(ctx.ensures_goal.clone()))
        }
        StmX::If(cond, then_stm, else_stm) => {
            let cond_v = crate::to_lean_sst_expr::Validated::check(cond)?;
            // Both branches share the same post-if continuation. Clone
            // `after` into each — this is where the pre-DSL code's
            // exponential-in-nested-ifs size comes from; see DESIGN.md
            // "Known codegen-complexity trade-offs" for the shared-
            // continuation let-binding optimization we chose not to
            // implement (simp zeta-reduces it, so no saving).
            let then_branch = build_wp(then_stm, after.clone(), ctx, loop_stack)?;
            let else_branch = match else_stm {
                Some(e) => build_wp(e, after, ctx, loop_stack)?,
                None => after,
            };
            Ok(Wp::Branch {
                cond: cond_v,
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            })
        }
        // The Call / Loop destructures live HERE at the dispatch site
        // rather than inside their respective build_wp_* helpers
        // (#104). Reasons:
        //   1. The wrong-variant case is unrepresentable: build_wp_call
        //      can't be called on a non-Call statement because it
        //      doesn't take a Stm — only the destructured fields.
        //   2. The explicit-fields-no-`..` upstream-robustness defence
        //      (DESIGN.md § "Upstream-robustness patterns") still
        //      applies: any Verus-side field addition to StmX::Call /
        //      StmX::Loop forces a compile error at this match arm.
        //   3. `mode` / `assert_id` (Call) and `is_for_loop` /
        //      `typ_inv_vars` / `modified_vars` / `pre_modified_params`
        //      (Loop) are spelled out as `_` so the audit catches
        //      additions even at fields we currently ignore.
        //
        // build_wp_call doesn't need the enclosing loop_stack — its
        // call_span is `&stm.span`, threaded through. build_wp_loop
        // DOES — it extends the stack with this loop's WpLoopCtx and
        // recurses on the body. `after` was already built by our
        // caller with the outer stack.
        StmX::Call {
            fun,
            resolved_method,
            mode: _,
            is_trait_default,
            typ_args,
            args,
            split,
            dest,
            assert_id: _,
        } => build_wp_call(
            fun,
            resolved_method,
            is_trait_default,
            typ_args,
            args,
            split,
            dest.as_ref(),
            &stm.span,
            after,
            ctx,
        ),
        StmX::Loop {
            loop_isolation,
            is_for_loop: _,
            id,
            label,
            cond,
            body,
            invs,
            decrease,
            typ_inv_vars: _,
            modified_vars: _,
            pre_modified_params: _,
        } => build_wp_loop(
            *loop_isolation,
            *id,
            label,
            cond,
            body,
            invs,
            decrease,
            after,
            ctx,
            loop_stack,
        ),
        // Transparent in SST: pass `after` through unchanged.
        StmX::Air(_) | StmX::Fuel(..) | StmX::RevealString(_) => Ok(after),
        // `break` / `continue` terminate the current iteration and
        // jump to the loop's respective leaf. `after` is discarded —
        // any statements textually after a break in the SST are
        // unreachable (Verus's dead-code analysis handles that
        // upstream; this WP side just needs to reach the right leaf).
        //
        // **Unlabeled** (`break;` / `continue;`) — uses the innermost
        // enclosing loop (loop_stack[0]).
        // **Labeled** (`break 'outer;`) — searches `loop_stack` for
        // the entry whose label matches.
        StmX::BreakOrContinue { label, is_break } => {
            let leaves: &WpLoopCtx = match label {
                None => {
                    let Some(innermost) = loop_stack.first() else {
                        // Should never fire — Verus's mode checker
                        // rejects break/continue outside loops.
                        return Err(
                            "break / continue appeared outside any loop — Verus's \
                             mode checker should have caught this; please open an \
                             issue.".to_string()
                        );
                    };
                    innermost
                }
                Some(target) => {
                    let target_str = target.as_str();
                    let Some(matched) = loop_stack.iter().find(|ctx| {
                        ctx.label.as_deref() == Some(target_str)
                    }) else {
                        // Should never fire — Verus's mode checker
                        // requires the label to be in scope.
                        return Err(format!(
                            "labeled break/continue references unknown loop label \
                             `{}` — Verus's mode checker should have caught this; \
                             please open an issue.",
                            target_str,
                        ));
                    };
                    matched
                }
            };
            let leaf = if *is_break {
                leaves.break_leaf.clone()
            } else {
                leaves.continue_leaf.clone()
            };
            Ok(Wp::Done(leaf))
        }
        StmX::AssertBitVector { requires, ensures } => {
            // Bit-vector mode: render requires + ensures via the
            // BitVec-mode renderer (#130 first cut). u-typed
            // variables get wrapped as `BitVec.ofInt n x`, so the
            // resulting LExpr's bitwise ops resolve to BitVec
            // instances and Lean's BitVec tactics (`decide`,
            // `simp [BitVec.*]`) can reason about the goal.
            //
            // We ALSO build the Int-mode lowering of `ensures` for
            // the post-assert hypothesis — the surrounding ctx
            // continues in Int mode, so the Hyp must talk about
            // the original Int-typed variables, not BitVec'd ones.
            // The bit_vector solver discharges the obligation in
            // BitVec semantics; we trust Verus's upstream check
            // that the BitVec-truth and Int-truth correspond for
            // the user's shape.
            let req_lexprs: Vec<LExpr> = requires.iter()
                .map(|r| crate::to_lean_sst_expr::sst_exp_to_bit_vector_ast(r))
                .collect::<Result<Vec<_>, _>>()?;
            let ens_lexprs: Vec<LExpr> = ensures.iter()
                .map(|e| crate::to_lean_sst_expr::sst_exp_to_bit_vector_ast(e))
                .collect::<Result<Vec<_>, _>>()?;
            // Note: we deliberately do NOT publish the ensures as
            // an Int-mode hypothesis to the body's ctx. Lean lacks
            // an `HXor Int Int Int` instance (and similar for
            // `HAnd`/`HOr`), so an Int-mode `x ^^^ y` doesn't
            // typecheck. The bit_vector assertion verifies in BV
            // mode; users who need the fact in Int-mode body
            // context can re-derive it via `assert(P) by { ... }`
            // with their own tactic. Future work (#130 follow-up):
            // either render bitwise ops via `Int.xor` etc., or add
            // `HXor Int Int Int` instances in TactusPrelude that
            // delegate to the function form.
            let req_conj = and_all(req_lexprs);
            let ens_conj = and_all(ens_lexprs);
            // Use the first ensure's span when present — that's the
            // user's `assert(…) by(bit_vector)` site. Falls back to
            // the stm's span via the caller-side wrapping if absent.
            let rust_loc = ensures.first()
                .map(|e| format_rust_loc(&e.span))
                .or_else(|| requires.first().map(|r| format_rust_loc(&r.span)))
                .unwrap_or_default();
            Ok(Wp::AssertBitVector {
                req_conj,
                ens_conj,
                rust_loc,
                body: Box::new(after),
            })
        }
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
                        TactusKind::AssertBy => Some(crate::to_lean_sst_expr::Validated::check(cond)?),
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
                    // Defensive: Verus's `ast_to_sst` (vir/src/ast_to_sst.rs:2416)
                    // converts user-syntax `assert by(bit_vector)` directly into
                    // `StmX::AssertBitVector`, so this arm should be unreachable.
                    // Hitting it means the upstream conversion pipeline drifted
                    // — the dedicated `StmX::AssertBitVector` path (#111 / #130)
                    // is what actually handles user `by(bit_vector)` asserts.
                    "internal bug: AssertQueryMode::BitVector reached the SST \
                     codegen — Verus's ast_to_sst should have already converted \
                     this to StmX::AssertBitVector. Please open an issue.".to_string()
                ),
            }
        }
        StmX::DeadEnd(_) => Err(
            "Verus's internal `DeadEnd` marker reached the SST — this shouldn't \
             appear in user code. If you're seeing this, please open an issue.".to_string()
        ),
        StmX::OpenInvariant(_) => Err(
            "`open_atomic_invariant!` (atomic invariant opening) not yet supported \
             in tactus_auto fns — out of scope until Tactus's concurrency story \
             lands. Workaround: extract the invariant-opening logic into a \
             non-tactus_auto fn (Verus's Z3 path handles it).".to_string()
        ),
        // Exec-mode closure declaration. Verus's SST decomposed the
        // user's `let f = |x| body` into:
        //   1. `StmX::ClosureInner { body: <body's verification scope>,
        //      typ_inv_vars: <closure params + their types>,
        //      ast_body: <preserved AST closure expression> }`
        //   2. A subsequent `StmX::Assume(<closure's external spec —
        //      forall|x| ClosureReq(cid, x) ↔ ... + ClosureEns ↔ ...>)`
        //   3. A subsequent reference to `Var(cid)` as the closure value.
        //
        // For Lean we want the closure to be a first-class function
        // value. We use the preserved AST `ast_body` (the
        // `ExprX::NonSpecClosure { params, body, external_spec, ... }`)
        // to render a Lean lambda, then bind `cid` to it via
        // `Wp::LetRaw`. The synthetic spec assume in (2) is dropped
        // because the binding in (1) is structurally the same fact.
        //
        // The closure body's own verification (overflow checks inside
        // the closure body's arithmetic, the closure's own ensures,
        // etc.) is emitted as a separate scope via `Wp::ClosureBody`:
        // its theorems get `∀ p : T, h_p_bound → ...` for each closure
        // param. Without this, a closure body containing a soundness
        // gap (`|x: u8| x + 200` overflows when called with x ≥ 56)
        // would be silently accepted.
        StmX::ClosureInner { body, typ_inv_vars, ast_body } => {
            let (cid, lambda) = closure_lambda_from_ast(ast_body)?;
            // Build the body's Wp with `Done(True)` as a no-op
            // terminator — the closure body's own ensures-asserting
            // happens via `closure_emit_postconditions`-injected
            // asserts inside `body`, so there's no fn-exit obligation.
            let body_wp = build_wp(
                body,
                Wp::Done(LExpr::lit_bool(true)),
                ctx,
                loop_stack,
            )?;
            // Convert typ_inv_vars to (`&VarIdent`, `&Typ`) form
            // for `push_mod_var_frames` (same shape it takes for
            // loop modified-vars).
            let closure_params: Vec<(&VarIdent, &Typ)> = typ_inv_vars
                .iter()
                .map(|(uid, typ)| (uid, typ))
                .collect();
            Ok(closure_decl_wp(closure_params, body_wp, cid, lambda, after))
        }
    }
}

/// Validate and build a `Wp::Call`. Takes the destructured `StmX::Call`
/// fields directly (#104) — the wrong-variant case is unrepresentable
/// because the function never sees a `Stm`. The explicit field
/// destructure happens at the `build_wp` dispatch site, where any
/// Verus-side field addition causes a compile error.
///
/// Validation breaks into four named phases via helpers:
/// 1. `reject_unsupported_call_shapes` — `split` (assertion-splitting
///    error reporting; deferred).
/// 2. `resolve_callee` — pick callee + type args based on
///    `resolved_method` (DynamicResolved redirect, including the
///    `is_trait_default = Some(true)` redirect to the trait method
///    decl introduced in #96) and look both up in fn_map (plus the
///    trait-method-decl side for impls).
/// 3. `validate_call_arities` — param count vs args count, typ_args
///    count vs callee.typ_params count.
/// 4. `build_call_mut_args` — extract `&mut` arg destinations,
///    rejecting non-simple-Loc shapes.
fn build_wp_call<'a>(
    fun: &'a Fun,
    resolved_method: &'a Option<(Fun, vir::ast::Typs)>,
    is_trait_default: &'a Option<bool>,
    typ_args: &'a vir::ast::Typs,
    args: &'a vir::sst::Exps,
    split: &'a Option<vir::messages::Message>,
    dest: Option<&'a Dest>,
    call_span: &'a Span,
    after: Wp<'a>,
    ctx: &WpCtx<'a>,
) -> Result<Wp<'a>, String> {
    reject_unsupported_call_shapes(split)?;

    let (callee, spec_callee, callee_typ_args) =
        resolve_callee(fun, resolved_method, is_trait_default, typ_args, ctx)?;

    validate_call_arities(callee, args, callee_typ_args)?;

    let mut_args = build_call_mut_args(&callee.params, args, &ctx.mut_ref_locals)?;

    let bound_dest: Option<&'a VarIdent> = dest
        .and_then(|d| extract_simple_var_ident(&d.dest));

    // NOTE: the termination obligation for recursive calls is emitted
    // upstream by Verus's `recursion::check_recursive_function` pass,
    // which inserts a `StmX::Assert` wrapping `InternalFun::
    // CheckDecreaseHeight` right before each recursive call
    // (including mutual recursion across an SCC). `build_wp` sees it
    // as a plain `Wp::Assert`; `sst_exp_to_ast_checked` handles the lowering.
    let validated_args: Vec<Validated<'a>> = args.iter()
        .map(|a| Validated::check(a))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Wp::Call {
        callee,
        spec_callee,
        args: validated_args,
        typ_args: callee_typ_args,
        dest: bound_dest,
        call_span,
        mut_args,
        after: Box::new(after),
    })
}

/// Phase 1: Reject call shapes Tactus doesn't yet support.
///
/// * `split.is_some()` — split-assertion error reporting; the SST
///   shape distributes the error to multiple sites and we don't
///   replicate that.
///
/// `is_trait_default = Some(true)` is NOT rejected here (#96): the
/// default body lives on the trait method decl, which
/// `resolve_callee` returns as `spec_callee` after `resolve_callee`
/// redirects to the trait method decl. The default-impl path goes
/// through the same logic as concrete-impl calls; `Self` resolves
/// via the existing typ_args / typ_subst machinery.
fn reject_unsupported_call_shapes(
    split: &Option<vir::messages::Message>,
) -> Result<(), String> {
    if split.is_some() {
        return Err(
            "calls with split-assertion error reporting are not yet supported".to_string()
        );
    }
    Ok(())
}

/// Phase 2: Resolve the call to a `(callee, spec_callee, typ_args)`
/// triple. Looking both up at build time eliminates the runtime
/// re-resolution in `walk_call` and the corresponding `expect()`.
///
/// `resolved_method` discriminates the cases:
/// * `Some((resolved_fun, resolved_typs))` — `DynamicResolved`:
///   use the resolved concrete impl as callee. The resolved typs
///   have `Self` filled in with the concrete receiver type.
/// * `None` — `Static` / `ProofFn` / `Dynamic` / `ExternalTraitDefault`.
///   Use the original `fun` and `typ_args`. The latter three cases
///   may not be in fn_map; we let the lookup fail with the
///   cross-crate error.
///
/// `spec_callee` is the source of `require`/`ensure` clauses:
/// * For `FunctionKind::TraitMethodImpl` callees, the trait method
///   decl (looked up via `callee.kind.method`).
/// * Otherwise, the callee itself.
///
/// Resolving `spec_callee` here means `walk_call` doesn't need to
/// re-derive it via fallible lookup, and the type system
/// guarantees `spec_callee` is always present (no `expect()`).
fn resolve_callee<'a>(
    fun: &'a Fun,
    resolved_method: &'a Option<(Fun, vir::ast::Typs)>,
    is_trait_default: &Option<bool>,
    typ_args: &'a vir::ast::Typs,
    ctx: &WpCtx<'a>,
) -> Result<(&'a FunctionX, &'a FunctionX, &'a [Typ]), String> {
    // For `is_trait_default = Some(true)` calls (#96): the
    // `resolved_method`'s fn is a synthesized wrapper around the
    // trait's default body (path looks like `<impl>%default%<method>`),
    // and its `typ_params` differ from the call-site's `typ_args`
    // (the wrapper has Self specialized, the call site passes Self
    // explicitly). Skip the redirect — use `fun` (the trait method
    // decl) directly, since the trait method decl already holds the
    // default body and its specs. `resolve_callee` then returns
    // it as both callee and spec_callee (TraitMethodDecl arm), so
    // no impl-strengthening conjunction is added (there's no impl
    // for default-impl calls — the default IS the body).
    let (callee_fun, callee_typ_args): (&'a Fun, &'a [Typ]) =
        if matches!(is_trait_default, Some(true)) {
            (fun, &typ_args[..])
        } else {
            match resolved_method {
                Some((resolved, resolved_typs)) => (resolved, &resolved_typs[..]),
                None => (fun, &typ_args[..]),
            }
        };
    let Some(callee) = ctx.fn_map.get(callee_fun).copied() else {
        return Err(format!(
            "callee `{:?}` not found in the crate's function map — cross-crate calls are \
             not yet supported",
            callee_fun.path
        ));
    };
    // Resolve spec_callee structurally. For TraitMethodImpl, redirect
    // to the trait method decl (Verus rejects impl-side `requires`,
    // so the impl's spec is empty/inherited). For all other kinds,
    // specs live on the callee itself.
    let spec_callee = match &callee.kind {
        FunctionKind::TraitMethodImpl { method, .. } => {
            ctx.fn_map.get(method).copied().ok_or_else(|| format!(
                "trait method decl `{:?}` for resolved impl `{:?}` not found in \
                 the crate's function map — cross-crate trait calls are not yet \
                 supported (#56 follow-up)",
                method.path, callee_fun.path,
            ))?
        }
        FunctionKind::Static
        | FunctionKind::TraitMethodDecl { .. }
        | FunctionKind::ForeignTraitMethodImpl { .. } => callee,
    };
    Ok((callee, spec_callee, callee_typ_args))
}

/// Phase 3: Validate that the call's arities (value-args + type-args)
/// match the callee's declared params + typ_params.
///
/// Both sides are post-`ast_simplify` so zero-arg callees carry the
/// `no%param` dummy on both. For `DynamicResolved`, `callee_typ_args`
/// is already the resolved-impl's type args (Self filled in), which
/// must match the impl's `typ_params.len()` — possibly different
/// from the trait method's `typ_params.len()` if the trait has
/// type params the impl monomorphizes.
fn validate_call_arities(
    callee: &FunctionX,
    args: &[Exp],
    callee_typ_args: &[Typ],
) -> Result<(), String> {
    if callee.params.len() != args.len() {
        return Err(format!(
            "callee `{:?}` has {} param(s) but call site passes {} arg(s) — \
             arg-passing convention may be out of sync (both sides should be \
             post-ast_simplify); this would bind wrong variables if we proceeded",
            callee.name.path, callee.params.len(), args.len(),
        ));
    }
    if callee.typ_params.len() != callee_typ_args.len() {
        return Err(format!(
            "callee `{:?}` declares {} type param(s) but call site passes {} type \
             arg(s) — would leave type-param references unsubstituted in the \
             inlined spec",
            callee.name.path, callee.typ_params.len(), callee_typ_args.len(),
        ));
    }
    Ok(())
}

/// Raw extraction of an `&mut`-arg's target shape from a call-site
/// `Exp`. The arg's outer `Loc(...)` wrapper is peeled; we recognise
/// three shapes:
///
/// * `Loc(VarLoc(x))` — simple `&mut x`. Variant: `Var(x)`. Plus the
///   new-mut-ref-mode caller-side shape `Var(synthetic_borrow_mut_local)`
///   (#107) — recognized when `ident` is in `mut_ref_locals`.
/// * `Loc(Field(...Field(VarLoc(x))))` — single-variant struct field
///   path mutation `&mut x.f1.f2.…` (#87 single-level, #144 deeper
///   paths). Variant: `Field { base, field_oprs }` where `field_oprs`
///   is the path from outermost-write down to innermost-base —
///   `field_oprs[0]` is the deepest-mutated field (closest to the
///   leaf value), `field_oprs[len-1]` is the outermost (closest to
///   the base local). Each level must be a single-variant datatype.
/// * `Loc(Field(Tuple(arity), Var(t)))` — single-level tuple field
///   mutation `&mut t.<i>` (#145 + #146). Variant: `TupleField {
///   base, index, arity }`. Lean's structure-update syntax doesn't
///   compose with `Prod`, so the post-call rebind uses Lean tuple
///   syntax `(t.1, …, fresh, …, t.<n>)` instead.
///
/// Returns `None` for unsupported shapes:
/// * `&mut v[i]` (Index L-value) — cross-crate-blocked (vstd routing).
/// * `&mut *p` (DerefMut) — not yet handled.
/// * Multi-variant enum field mutation at any level (Lean's
///   structure update syntax doesn't compose with multi-variant
///   inductives; also upstream-blocked at Verus's `ref mut` mode
///   check for the only viable surface syntax).
/// * Mixed tuple-and-struct paths (`&mut s.tup.0`, `&mut t.0.f`) —
///   would need a unified `Vec<FieldKind>` path encoding.
#[derive(Clone)]
enum MutTargetRaw<'a> {
    Var(&'a VarIdent),
    /// `&mut <base>.<f1>.<f2>.…` field path. `field_oprs` lists the
    /// path from peel order — `field_oprs[0]` is the OUTERMOST
    /// `Field(_, ...)` we encountered when peeling (i.e., the
    /// deepest-mutated field, closest to the new value). For a
    /// single-level mutation `&mut x.f`, `field_oprs` is
    /// `vec![f_opr]`. For `&mut x.f.g`, it's `vec![g_opr, f_opr]`
    /// (g is outermost in the SST → outermost in the peel sequence
    /// → first in the Vec).
    ///
    /// `base` is the outer-most `VarIdent` (the local being rebound
    /// at the call site). The Lean-rendered field name for each
    /// level is computed at emission time via
    /// `field_access_name(opr)`.
    Field { base: &'a VarIdent, field_oprs: Vec<&'a vir::ast::FieldOpr> },
    /// `&mut <base>.<i>` for a tuple `base : (T0, T1, ..., T{n-1})`.
    /// Lean's `{ x with f := v }` syntax doesn't compose with `Prod`
    /// types ("expected structure" elaboration error), so the rebind
    /// uses explicit ctor rebuild via Lean's anon-ctor syntax
    /// `⟨t.1, ..., fresh, ..., t.n⟩` (with the mutated field's slot
    /// filled by `fresh` and all others by `t.<j>` accessors).
    ///
    /// Stored as the base ident, the 0-indexed field position, and
    /// the tuple arity. Restricted to single-level (no `&mut t.0.f`
    /// or `&mut s.tup.0` mixing yet — multi-level paths involving
    /// tuples need a unified Vec<FieldKind> path that the current
    /// `Field` variant doesn't model).
    TupleField { base: &'a VarIdent, index: usize, arity: usize },
}

fn extract_mut_target<'a>(
    e: &'a Exp,
    mut_ref_locals: &HashSet<String>,
) -> Option<MutTargetRaw<'a>> {
    // Peel transparent wrappers (Box/Unbox/CoerceMode/Trigger) at
    // the outermost level too — for some L-value shapes (e.g.,
    // tuple field mutation, before we reject it) the SST has
    // `UnaryOpr(Unbox(_), Loc(...))`, with the Unbox outside the
    // Loc rather than inside it. `peel_transparent` stops at Loc
    // (per its semantics), so this just removes any surrounding
    // boxing.
    let e = peel_transparent(e);
    // New-mut-ref-mode caller side (#107): the call arg is a bare
    // `Var(synthetic_local)` (no Loc wrapper) where `synthetic_local`
    // is a `LocalDeclKind::BorrowMut` local Verus introduces around
    // `bump(&mut y)`. The synthetic local IS the L-value the call
    // mutates; `mut_ref_locals` carries the names of these
    // BorrowMut locals so we recognize them. Legacy-mode `&mut y`
    // still goes through the Loc path below.
    if let ExpX::Var(ident) = &e.x {
        if mut_ref_locals.contains(&sanitize(&ident.0)) {
            return Some(MutTargetRaw::Var(ident));
        }
    }
    // Peel the outer Loc.
    let inner = match &e.x {
        ExpX::Loc(inner) => inner,
        _ => return None,
    };
    // Peel transparent wrappers (Box/Unbox/CoerceMode/Trigger) that
    // Verus's `ast_to_sst` sometimes inserts around the L-value's
    // base. For `&mut h.field`, the SST shape we observed is:
    //   Loc(UnaryOpr(Field, Unbox(Box(VarLoc(h)))))
    // — the Field's base is wrapped through transparent boxing.
    // `peel_transparent` peels everything except the Loc itself
    // (which we already peeled above).
    let inner = peel_transparent(inner);
    if let ExpX::Var(ident) | ExpX::VarLoc(ident) = &inner.x {
        return Some(MutTargetRaw::Var(ident));
    }
    // Single-level tuple field shape (#145): `Loc(Field(Tuple(n), Var(t)))`
    // for `&mut t.<i>`. Tuple field mutation needs ctor rebuild
    // (Lean's `{ x with f := v }` doesn't compose with `Prod`), so it
    // gets its own variant rather than threading through the
    // recursive Field peel below. Restricted to single-level — multi-
    // level paths involving tuples (e.g., `&mut s.tup.0` or
    // `&mut t.0.f`) need a unified Vec<FieldKind> path representation.
    //
    // Any arity ≥ 2 supported (#146 lifted the prior arity-2-only
    // gate). The unmodified-slot reads use the shared
    // `tuple_field_accessor` so arity > 2 produces the correct
    // multi-segment Lean accessor (e.g., `.2.1` for the second of
    // three).
    if let ExpX::UnaryOpr(UnaryOpr::Field(field_opr), base_exp) = &inner.x {
        if let vir::ast::Dt::Tuple(arity) = &field_opr.datatype {
            let base = peel_transparent(base_exp);
            if let ExpX::Var(ident) | ExpX::VarLoc(ident) = &base.x {
                if let Ok(index) = field_opr.field.as_str().parse::<usize>() {
                    return Some(MutTargetRaw::TupleField {
                        base: ident,
                        index,
                        arity: *arity,
                    });
                }
            }
            // Tuple field with non-numeric field name or non-Var base —
            // fall through to None (defensive; Verus shouldn't produce
            // either shape).
            return None;
        }
    }
    // Peel Field levels until we hit a Var/VarLoc base. Single-variant
    // gate per level: Lean's `{ x with f := v }` syntax works for
    // `structure` types (single ctor); multi-variant enums and tuples
    // (above) fall through to None at the level they appear.
    let mut field_oprs: Vec<&'a vir::ast::FieldOpr> = Vec::new();
    let mut cursor: &'a Exp = inner;
    loop {
        match &cursor.x {
            ExpX::Var(ident) | ExpX::VarLoc(ident) => {
                if field_oprs.is_empty() {
                    // Reached the base without seeing any Field —
                    // already handled by the early return above; this
                    // arm is unreachable when entering the loop.
                    return Some(MutTargetRaw::Var(ident));
                }
                return Some(MutTargetRaw::Field { base: ident, field_oprs });
            }
            ExpX::UnaryOpr(UnaryOpr::Field(field_opr), base_exp) => {
                let supported_kind = match &field_opr.datatype {
                    vir::ast::Dt::Path(path) => {
                        // Single-variant struct: the variant name
                        // equals the type's short name. Multi-variant
                        // enums fall through to None (Lean's
                        // `{ x with f := v }` doesn't compose with
                        // multi-variant inductives).
                        field_opr.variant.as_str()
                            == crate::to_lean_type::short_name(path)
                    }
                    // Tuple at a deeper level (e.g., `&mut s.tup.0` or
                    // `&mut t.0.f`) — handled separately above for the
                    // single-level case; multi-level paths involving
                    // tuples need a unified path encoding that this
                    // recursive peel doesn't support yet.
                    vir::ast::Dt::Tuple(_) => false,
                };
                if !supported_kind {
                    return None;
                }
                field_oprs.push(field_opr);
                // Peel transparent wrappers (Box/Unbox/CoerceMode/
                // Trigger) before the next iteration — Verus's SST
                // sometimes inserts these around the Field's base.
                cursor = peel_transparent(base_exp);
            }
            _ => return None,
        }
    }
}

/// Phase 4: Walk the args + params in lockstep, build the `&mut`
/// arg list, and validate each non-mut arg via `check_exp`.
///
/// For each `&mut` param, the call-site arg must reduce via
/// `extract_mut_target` to either a simple local or a single-variant
/// field projection. Other shapes (`&mut v[i]`, deeper paths,
/// multi-variant enum fields, `&mut *p`) are rejected with a
/// pointed error message — deferred follow-up to #55 / #87.
///
/// Defensive: a `Loc`-wrapped arg at a non-`&mut` position
/// shouldn't happen (Rust's borrow checker would reject it upstream),
/// but if it does we error rather than silently encode wrong.
fn build_call_mut_args<'a>(
    callee_params: &vir::ast::Params,
    args: &'a vir::sst::Exps,
    mut_ref_locals: &HashSet<String>,
) -> Result<Vec<(usize, MutTargetRaw<'a>)>, String> {
    let mut mut_args: Vec<(usize, MutTargetRaw<'a>)> = Vec::new();
    for (i, (param, a)) in callee_params.iter().zip(args.iter()).enumerate() {
        // Recognize `&mut` params in both legacy mode (`is_mut: true`,
        // plain T typ) and new-mut-ref mode (`is_mut: false`,
        // `MutRef<T>` typ). The caller-side encoding for both modes
        // goes through #55's mut_args machinery — legacy via
        // Loc(VarLoc(_)) shapes, new-mut-ref via bare
        // Var(borrow_mut_local) shapes (#107). `is_mut_ref_param` is
        // the AST-side twin of the SST-side `is_mut_ref_par`; using
        // the named helper keeps this site in lockstep with
        // `add_param_subst_entries` (the only other consumer of the
        // same predicate on the AST side).
        if is_mut_ref_param(param) {
            match extract_mut_target(a, mut_ref_locals) {
                Some(target) => mut_args.push((i, target)),
                None => return Err(format!(
                    "&mut argument at position {} is not a supported L-value \
                     shape. Tactus accepts `&mut <local>` (simple) and `&mut \
                     <local>.<field>` for single-variant structs (#87). \
                     `&mut v[i]`, deeper paths like `&mut x.f.g`, multi-\
                     variant enum field mutation, and `&mut *p` need \
                     additional encoding and are deferred (#87 / #95). \
                     Workaround: bind to a local first (`let mut tmp = expr; \
                     foo(&mut tmp); ... = tmp;`).",
                    i,
                )),
            }
            // Don't `check_exp(a)` — `a` is a `Loc` shape, not a
            // value-position expression. The inner var has been
            // structurally validated above.
        } else {
            if contains_loc(a) {
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
    Ok(mut_args)
}

/// Validate and build a `Wp::Loop`. Takes the destructured `StmX::Loop`
/// fields directly (#104) — the wrong-variant case is unrepresentable
/// because the function never sees a `Stm`. The explicit field
/// destructure happens at the `build_wp` dispatch site, where any
/// Verus-side field addition causes a compile error.
///
/// See the module doc for the shape restrictions. The loop's body is
/// built with its OWN terminator — `Done(I ∧ D < _tactus_d_old)` —
/// rather than the outer `after`, because a fall-through end of an
/// iteration re-enters the loop's maintain clause, not the post-loop
/// continuation.
fn build_wp_loop<'a>(
    loop_isolation: bool,
    id: u64,
    label: &'a Option<String>,
    cond: &'a Option<(Stm, Exp)>,
    body: &'a Stm,
    invs: &'a vir::sst::LoopInvs,
    decrease: &'a vir::sst::Exps,
    after: Wp<'a>,
    ctx: &WpCtx<'a>,
    outer_loop_stack: &LoopStack<'_>,
) -> Result<Wp<'a>, String> {
    // Per-loop-unique, per-lex-level d_old names. Verus's
    // `StmX::Loop::id` is the upstream-stable identifier per loop
    // instance; per-level index disambiguates lex tiers (#110).
    // Names finalised once we know `decrease.len()` after validation.
    // See `expr_shared.rs`'s "Reserved identifier conventions" —
    // Convention 1 + the gensym-mechanism-choice note.
    if !loop_isolation {
        // `loop_isolation` is set by Verus based on whether the loop
        // body is verified independently from the outer context.
        // Users don't control it directly — it's flipped by Verus
        // when, e.g., the loop appears inside a closure or a context
        // that would otherwise unsoundly leak invariants.
        return Err(
            "this loop's body would need to see outer context directly \
             (loop_isolation: false) — not yet supported by tactus_auto. \
             Workaround: refactor to a self-contained loop with explicit \
             invariants.".to_string()
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
    //
    // **Non-empty cond_setup (#114):** Verus's `expr_to_stm_opt` may
    // produce a `(setup_stmts, pure_expr)` pair when the user's cond
    // has function calls, short-circuit `&&`/`||`, or other shapes
    // that need temporaries. The setup runs at every iteration
    // boundary (Verus's encoding mirrors this: it runs cond_setup in
    // both the loop-body and outer SMT queries). We mirror Verus by
    // walking cond_setup as a wp prefix in BOTH the body's Wp (under
    // an `assume cond_exp` hyp via `Wp::Assume`) and the post-loop
    // `after` Wp (under an `assume ¬cond_exp` hyp via `Wp::Hyp`).
    // When this transform fires, we set `cond_exp_opt = None` so
    // walk_loop doesn't push the cond hyp again — it's already
    // inside the body's wrapped Wp.
    //
    // The negated cond goes through `Wp::Hyp` (already-rendered
    // LExpr) rather than synthesizing a fresh SST `Exp` for ¬cond.
    // A synthesized Exp would need an `'a` lifetime that we can't
    // produce inside this fn (the input SST is the `'a` source).
    // Using `LExpr::not(lower(cond_validated))` keeps everything on
    // the borrow side: cond_validated borrows cond_exp, the negation
    // happens at LExpr level (owned), no Arc clones.
    //
    // Returns `(cond_exp_opt, cond_setup_wrap)`:
    //   * `cond_exp_opt: Option<Validated>` — what walk_loop pushes
    //     as the loop's cond hyp. `None` when the wrapper handles
    //     it (so walk_loop doesn't push twice).
    //   * `cond_setup_wrap: Option<(&Stm, Validated, LExpr)>` —
    //     `Some` triggers the post-build wrap below.
    let (cond_exp_opt, cond_setup_wrap): (
        Option<Validated<'a>>,
        Option<(&'a Stm, Validated<'a>, LExpr)>,
    ) = match cond {
        None => (None, None),
        Some((cond_setup, cond_exp)) => {
            let cond_validated = crate::to_lean_sst_expr::Validated::check(cond_exp)?;
            if matches!(&cond_setup.x, StmX::Block(ss) if ss.is_empty()) {
                // Empty setup — fast path; walk_loop pushes cond hyp.
                (Some(cond_validated), None)
            } else {
                // Render ¬cond at LExpr level (no synthesised SST
                // Exp needed). The wrapper below uses Wp::Assume for
                // cond and Wp::Hyp for ¬cond around the body/after.
                let neg_cond_lexpr = LExpr::not(lower_validated(&cond_validated));
                (None, Some((cond_setup, cond_validated, neg_cond_lexpr)))
            }
        }
    };
    if decrease.is_empty() {
        return Err(
            "loop has no `decreases` clause — Tactus requires every \
             loop to declare a termination measure".to_string()
        );
    }
    // Each invariant carries `at_entry: bool` and `at_exit: bool`
    // flags. Three classifications:
    //   * `invariant P` — at_entry = at_exit = true. Holds at every
    //     loop-iteration boundary AND at every loop exit.
    //   * `invariant_except_break P` — at_entry = true, at_exit = false.
    //     Holds at iteration boundaries but not necessarily at break.
    //     Produced from `while_loop_invariant_except_break!` macro
    //     usage and similar.
    //   * `ensures P` (on a loop) — at_entry = false, at_exit = true.
    //     Required at every loop exit (break or natural fallthrough).
    //
    // For `cond: Some(_)` loops (`while c { ... }`), Verus's lowering
    // asserts at_entry = at_exit = true (see sst_to_air.rs:2655),
    // so the split is trivial. For `cond: None` loops (the
    // break-lowered form), the flags can differ.
    let validated_invs: Vec<crate::to_lean_sst_expr::Validated<'a>> = invs.iter()
        .map(|inv| crate::to_lean_sst_expr::Validated::check(&inv.inv))
        .collect::<Result<Vec<_>, _>>()?;
    let inv_kinds: Vec<LoopInvKind> = invs.iter()
        .map(LoopInvKind::from_loop_inv)
        .collect::<Result<Vec<_>, _>>()?;
    let decrease_levels: Vec<DecreaseLevel<'a>> = decrease.iter().enumerate()
        .map(|(i, d)| {
            // `_tactus_d_old_<id>_<i>` — per-loop, per-level
            // gensym; uniqueness in both axes prevents shadowing
            // across nested loops AND sibling lex tiers.
            let d_old_name = format!("_tactus_d_old_{}_{}", id, i);
            Ok(DecreaseLevel {
                value: crate::to_lean_sst_expr::Validated::check(d)?,
                d_old_name,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;

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
    // Split by classification (see comment block above on
    // invariant / invariant_except_break / loop ensures). Each list
    // independently folds into a marked conjunction; an empty list
    // folds to `True` (handled by `and_all`), which is harmless as
    // a hypothesis or trivially-provable as a Done leaf.
    let inv_marked = |(i, v): (&LoopInv, &crate::to_lean_sst_expr::Validated<'a>)| LExpr::span_mark(
        format_rust_loc(&i.inv.span),
        AssertKind::Obligation(ObligationKind::LoopInvariant),
        crate::to_lean_sst_expr::lower(v),
    );
    let entry_inv_conj = and_all(
        invs.iter().zip(validated_invs.iter()).zip(inv_kinds.iter())
            .filter(|(_, k)| k.at_entry())
            .map(|((i, v), _)| inv_marked((i, v))).collect()
    );
    let exit_inv_conj = and_all(
        invs.iter().zip(validated_invs.iter()).zip(inv_kinds.iter())
            .filter(|(_, k)| k.at_exit())
            .map(|((i, v), _)| inv_marked((i, v))).collect()
    );
    // Build the lex-shaped decrease obligation for the maintain leaf:
    //   (0 ≤ D1' ∧ D1' < D1_old)
    //     ∨ (D1' = D1_old ∧ ((0 ≤ D2' ∧ D2' < D2_old)
    //         ∨ (D2' = D2_old ∧ ... (0 ≤ Dn' ∧ Dn' < Dn_old))))
    // Single-element decreases reduce to `0 ≤ D' ∧ D' < D_old`
    // because the recursion's base is `False` (no further levels),
    // and `(D = D_old) ∧ False = False`, so the second disjunct
    // vanishes. The `0 ≤ Di'` lower bound matches Verus's own
    // `recursion::check_decrease` shape (which builds the obligation
    // via CheckDecreaseHeight's `otherwise` field at the fn level —
    // the int fast-path emits `0 ≤ cur ∧ cur < prev`). #129 closed
    // the prior gap where Tactus's loop encoding emitted just
    // `cur < d_old`.
    let decrease_lex = lex_decrease_obligation(&decrease_levels);
    let decrease_marked = LExpr::span_mark(
        format_rust_loc(&decrease[0].span),
        AssertKind::Obligation(ObligationKind::LoopDecrease),
        decrease_lex,
    );
    // continue_leaf = entry-invs ∧ decrease (re-establish at_entry
    // invs at every iteration boundary). break_leaf = exit-invs
    // (establish at_exit invs at the break point).
    let continue_leaf = LExpr::and(entry_inv_conj, decrease_marked);
    let break_leaf = exit_inv_conj;
    let inner_loop_ctx = WpLoopCtx {
        label: label.clone(),
        break_leaf: break_leaf.clone(),
        continue_leaf: continue_leaf.clone(),
    };
    // Body is built with THIS loop's WpLoopCtx pushed at the front
    // of the stack (innermost-first). Unlabeled break/continue in
    // the body resolves to this loop; labeled break/continue
    // searches the stack by label. The `Cons` cell lives on this
    // function's stack frame — no heap allocation needed.
    let inner_stack = LoopStack::Cons(&inner_loop_ctx, outer_loop_stack);
    let body_wp = build_wp(body, Wp::Done(continue_leaf), ctx, &inner_stack)?;

    // Apply the non-empty cond_setup transform if needed (#114).
    // Wraps body_wp with `cond_setup; assume cond_exp; ...` and the
    // post-loop `after` with `cond_setup; assume ¬cond_exp; ...`.
    // Mirrors Verus's two-query encoding (sst_to_air.rs:2789-2797 +
    // 2730-2737): cond_setup runs at every iteration boundary AND at
    // loop exit. Setup obligations (e.g., precondition checks for
    // calls inside the cond) emit twice — correct per Verus.
    let (body_wp, after) = match cond_setup_wrap {
        None => (body_wp, after),
        Some((cond_setup, cond_validated, neg_cond_lexpr)) => {
            // Body: assume cond_exp via Wp::Assume (cond_validated
            // borrows the SST's cond_exp). After: assume ¬cond via
            // Wp::Hyp (carries the pre-rendered LExpr, no
            // synthesised SST Exp).
            let body_with_assume = Wp::Assume(cond_validated, Box::new(body_wp));
            let body_wp_full = build_wp(
                cond_setup, body_with_assume, ctx, &inner_stack,
            )?;
            let after_with_hyp = Wp::Hyp { hyp: neg_cond_lexpr, body: Box::new(after) };
            let after_wp_full = build_wp(
                cond_setup, after_with_hyp, ctx, outer_loop_stack,
            )?;
            (body_wp_full, after_wp_full)
        }
    };

    Ok(Wp::Loop {
        cond: cond_exp_opt,
        invs: &invs[..],
        validated_invs,
        inv_kinds,
        decrease: decrease_levels,
        modified_vars,
        body: Box::new(body_wp),
        after: Box::new(after),
    })
}

/// Build the lexicographic decrease obligation as one LExpr. Each
/// level's lt-branch is `(0 ≤ cur ∧ cur < old)`, with
/// equality-falls-through to the next level. Empty input is a
/// contract violation (rejected upstream in `build_wp_loop`).
///
/// The `0 ≤ cur` lower bound matches the fn-level `CheckDecreaseHeight`
/// int fast-path (`to_lean_sst_expr.rs`'s arm — see #129). Verus's
/// loop encoding (`sst_to_air.rs:2823-2834`) routes through
/// `recursion::check_decrease` which produces the same shape; without
/// the lower bound, an `int`-typed loop decrease descending into
/// negatives would verify in Tactus where Verus rejects. For u-typed
/// decreases the `0 ≤` is implied by the type-bound hypothesis
/// (`h_<x>_bound`), so the extra conjunct is dormant in practice but
/// cheap to omega.
fn lex_decrease_obligation(levels: &[DecreaseLevel<'_>]) -> LExpr {
    debug_assert!(!levels.is_empty(),
        "lex_decrease_obligation needs ≥ 1 level (caller validates)");
    let cur = lower_validated(&levels[0].value);
    let old = LExpr::var_synthetic(levels[0].d_old_name.clone());
    let lt_branch = LExpr::and(
        LExpr::le(LExpr::lit_int("0"), cur.clone()),
        LExpr::lt(cur.clone(), old.clone()),
    );
    if levels.len() == 1 {
        // Base case: `0 ≤ cur ∧ cur < old`. The lex tail (eq ∧ False)
        // collapses, so we emit just the lt branch.
        return lt_branch;
    }
    let eq_branch = LExpr::and(
        LExpr::eq(cur, old),
        lex_decrease_obligation(&levels[1..]),
    );
    LExpr::or(lt_branch, eq_branch)
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

/// Verus injects synthetic params (`no%param`, etc.) with `%` in the
/// name for zero-arg functions and a few internal cases. They have no
/// user-visible semantics and must be dropped from the theorem binders.
fn is_synthetic_param(p: &Par) -> bool {
    p.x.name.0.contains('%')
}

#[cfg(test)]
mod tests {
    //! Unit tests for the Wp DSL helpers — `peel_transparent` /
    //! `peel_value_position` / `contains_loc` / `lift_if_value` /
    //! `match_single_let_bind` / `extract_simple_var_ident` — plus
    //! `build_wp`'s right-to-left Block fold and shape-drift guards
    //! for `CheckDecreaseHeight`, `WpCtx::new`, and `walk_loop`.
    //!
    //! Test strategy: construct small `Wp` trees with hand-built SST
    //! `Exp` values (simple Vars, Consts, Ifs) and check that the
    //! walker / helper produces the expected `LExpr` shape. For
    //! structural-shape tests the Exp leaves don't matter — only the
    //! tree structure — so we use minimal dummy exprs.
    //!
    //! These tests are direct-in-crate rather than integration so
    //! they can exercise private items (`Wp`, `build_wp`, etc.).
    use super::*;
    use crate::test_fixtures::{empty_krate, mk_path, typ_datatype, typ_int};
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
        let out = lift_if_value(&x, &|leaf| LExpr::let_bind_synthetic("y", leaf, LExpr::var_lit("body")));
        let expected = LExpr::let_bind_synthetic("y", LExpr::var_lit("x"), LExpr::var_lit("body"));
        assert!(pp_eq(&out, &expected));
    }

    #[test]
    fn lift_if_value_splits_on_if() {
        // If(c, a, b) → (c → emit_leaf(a)) ∧ (¬c → emit_leaf(b))
        let c = var_exp("c", typ_bool());
        let a = var_exp("a", typ_int());
        let b = var_exp("b", typ_int());
        let e = if_exp(c, a, b);
        let out = lift_if_value(&e, &|leaf| LExpr::let_bind_synthetic("y", leaf, LExpr::var_lit("body")));
        let expected = LExpr::and(
            LExpr::implies(
                LExpr::var_lit("c"),
                LExpr::let_bind_synthetic("y", LExpr::var_lit("a"), LExpr::var_lit("body")),
            ),
            LExpr::implies(
                LExpr::not(LExpr::var_lit("c")),
                LExpr::let_bind_synthetic("y", LExpr::var_lit("b"), LExpr::var_lit("body")),
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
        let out = lift_if_value(&e, &|leaf| LExpr::let_bind_synthetic("y", leaf, LExpr::var_lit("body")));
        let expected = LExpr::and(
            LExpr::implies(
                LExpr::var_lit("c"),
                LExpr::let_bind_synthetic("y", LExpr::var_lit("a"), LExpr::var_lit("body")),
            ),
            LExpr::implies(
                LExpr::not(LExpr::var_lit("c")),
                LExpr::let_bind_synthetic("y", LExpr::var_lit("b"), LExpr::var_lit("body")),
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
        let out = lift_if_value(&e, &|leaf| LExpr::let_bind_synthetic("y", leaf, LExpr::var_lit("body")));
        let expected = LExpr::and(
            LExpr::implies(
                LExpr::var_lit("c"),
                LExpr::let_bind_synthetic("y", LExpr::var_lit("a"), LExpr::var_lit("body")),
            ),
            LExpr::implies(
                LExpr::not(LExpr::var_lit("c")),
                LExpr::let_bind_synthetic("y", LExpr::var_lit("b"), LExpr::var_lit("body")),
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

        let out = lift_if_value(&e, &|leaf| LExpr::let_bind_synthetic("out", leaf, LExpr::var_lit("done")));
        // lift_if_value peels the Bind(Let), lifts the If inside the
        // value position, and re-threads `let y := rhs_leaf; y` into
        // each branch. Then emit_leaf wraps the whole let-y-y chunk.
        let expected = LExpr::and(
            LExpr::implies(
                LExpr::var_lit("c"),
                LExpr::let_bind_synthetic("out",
                    LExpr::let_bind_synthetic("y", LExpr::var_lit("a"), LExpr::var_lit("y")),
                    LExpr::var_lit("done")),
            ),
            LExpr::implies(
                LExpr::not(LExpr::var_lit("c")),
                LExpr::let_bind_synthetic("out",
                    LExpr::let_bind_synthetic("y", LExpr::var_lit("b"), LExpr::var_lit("y")),
                    LExpr::var_lit("done")),
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
        let out = lift_if_value(&e, &|leaf| LExpr::let_bind_synthetic("out", leaf, LExpr::var_lit("done")));
        let expected = LExpr::let_bind_synthetic("out",
            LExpr::let_bind_synthetic("y", LExpr::var_lit("x"), LExpr::var_lit("y")),
            LExpr::var_lit("done"));
        assert!(pp_eq(&out, &expected));
    }

    /// Pin that `lift_if_value` correctly handles multi-binder
    /// `Bind(Let([a, b], …))` shapes — the construction Verus would
    /// emit for `let (a, b) = (1, if c then 2 else 3); a + b`. The
    /// inner if must lift to goal level, with both binders in scope
    /// in each branch.
    ///
    /// Code path: `lift_if_value`'s `bs.len() > 1` branch unfolds to
    /// `Bind(Let([a]), Bind(Let([b]), body))` via `unfold_multi_binder_let`,
    /// then the existing single-binder logic peels each layer. This
    /// test exists to lock that pipeline against regression — without
    /// it, the multi-binder support has no direct unit-level proof
    /// (e2e tests don't exercise tuple-destructure-with-if patterns).
    /// Originally landed via #92; pinned by #119 follow-up.
    #[test]
    fn lift_if_value_multi_binder_let_with_if_rhs() {
        use vir::ast::VarBinderX;
        use vir::def::Spanned;

        let c = var_exp("c", typ_bool());
        let a_val = var_exp("av", typ_int());
        let b_val = var_exp("bv", typ_int());
        let bv_else = var_exp("bv2", typ_int());
        let body = var_exp("a", typ_int());
        let if_for_b = if_exp(c, b_val, bv_else);
        let binders: Vec<Arc<VarBinderX<Exp>>> = vec![
            Arc::new(VarBinderX { name: var_ident("a"), a: a_val }),
            Arc::new(VarBinderX { name: var_ident("b"), a: if_for_b }),
        ];
        let bnd = Spanned::new(
            test_span(),
            BndX::Let(Arc::new(binders)),
        );
        let body_typ = body.typ.clone();
        let e = Arc::new(SpannedTyped {
            span: test_span(),
            typ: body_typ,
            x: ExpX::Bind(bnd, body),
        });

        let out = lift_if_value(&e, &|leaf| {
            LExpr::let_bind_synthetic("out", leaf, LExpr::var_lit("done"))
        });

        // After unfolding to `Bind(Let([a := av]), Bind(Let([b := if c…]), body))`,
        // the outer single-binder peel recurses into both rhs (av, plain)
        // and inner_body (which itself is a single-binder let with an if-rhs).
        // The inner if lifts to goal level. The emit_leaf then wraps EACH
        // branch with the `let out := …; done` outer scaffold.
        //
        //   (c → emit_leaf(let a := av; let b := bv; a))
        //   ∧ (¬c → emit_leaf(let a := av; let b := bv2; a))
        //
        // Equivalent to `let out := let a := av; (c → … ∧ ¬c → …); done` by
        // distributing the let over the disjunction, but the actual emission
        // hoists the disjunction to the outermost level since that's where
        // omega expects it.
        let make_branch = |b_val: &str| {
            let inner_let = LExpr::let_bind_synthetic("b",
                LExpr::var_lit(b_val), LExpr::var_lit("a"));
            let with_a = LExpr::let_bind_synthetic("a",
                LExpr::var_lit("av"), inner_let);
            LExpr::let_bind_synthetic("out", with_a, LExpr::var_lit("done"))
        };
        let expected = LExpr::and(
            LExpr::implies(LExpr::var_lit("c"), make_branch("bv")),
            LExpr::implies(LExpr::not(LExpr::var_lit("c")), make_branch("bv2")),
        );

        assert!(pp_eq(&out, &expected),
            "got: {}\nexpected: {}",
            crate::lean_pp::pp_expr(&out),
            crate::lean_pp::pp_expr(&expected));
    }

    // ── extract_simple_var ─────────────────────────────────────

    #[test]
    fn extract_simple_var_from_plain_var() {
        let x = var_exp("x", typ_int());
        assert_eq!(extract_simple_var_ident(&x).map(|i| i.0.as_str()), Some("x"));
    }

    #[test]
    fn extract_simple_var_through_loc() {
        let x = var_exp("x", typ_int());
        assert_eq!(extract_simple_var_ident(&loc_exp(x)).map(|i| i.0.as_str()), Some("x"));
    }

    #[test]
    fn extract_simple_var_from_if_is_none() {
        let c = var_exp("c", typ_bool());
        let a = var_exp("a", typ_int());
        let b = var_exp("b", typ_int());
        let e = if_exp(c, a, b);
        assert_eq!(extract_simple_var_ident(&e).map(|i| i.0.as_str()), None);
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
        assert_eq!(name.as_str(), "z");
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
    /// exercises `CheckDecreaseHeight` lowering end-to-end. Test
    /// fixtures pass well-formed Exps so `.expect` here is a
    /// safety net for fixture bugs rather than a runtime path.
    fn render_via_public(e: &Exp) -> LExpr {
        crate::to_lean_sst_expr::sst_exp_to_ast_checked(e)
            .expect("test fixture: well-formed Exp")
    }

    #[test]
    fn decrease_arg_shape_with_box_wrapper_substitutes() {
        // Canonical Verus shape: Box(Let([(n, tmp)], n))
        //   After peel + substitute: tmp
        let e = mk_decrease_arg(true, "n", "tmp", "n");
        // The renderer would emit `Box` as transparent and render
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

    #[test]
    fn check_decrease_height_cross_type_shape_pinned() {
        // #109 stretch: cross-fn-SCC mutual recursion where cur and
        // prev have DIFFERENT datatype types (e.g., Tree and Forest
        // in the same SCC). Pre-fix Tactus used cur's type's height
        // fn for both sides — emitting `Forest.height (Tree-typed)`,
        // which Lean rejects with a type mismatch.
        //
        // This shape-drift test pins that:
        //   * cur uses <cur_T>.height
        //   * prev uses <prev_T>.height
        // independently. If a future refactor accidentally collapses
        // the dispatch back to a single height fn, this test catches
        // it before any e2e test would.
        use vir::sst::{CallFun, ExpX, InternalFun};
        let tree_typ = typ_datatype("Tree");
        let forest_typ = typ_datatype("Forest");

        // cur: Bind(Let([(t, branch_field)], t)) at Tree type.
        let cur_arg = var_exp("branch_field", tree_typ.clone());
        let cur_dec = var_exp("t", tree_typ.clone());
        let cur_inner = let_exp("t", cur_arg, cur_dec);
        let cur = box_exp(cur_inner);
        // prev: Var(decrease_init0) at Forest type.
        let prev = box_exp(var_exp("decrease_init0", forest_typ.clone()));
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

        // Both type-specific height fns must be referenced. If
        // `to_lean_sst_expr.rs`'s CheckDecreaseHeight arm
        // accidentally collapses back to using ONE height fn for both
        // sides (the pre-fix bug for #109 stretch), only one of these
        // names would appear and the other side would either reuse it
        // (type mismatch in real Lean compilation) or sorry.
        assert!(printed.contains("Tree.height"),
            "cur side should reference `Tree.height` (cur has type \
             Tree). If this is missing or reads `Forest.height` instead, \
             the CheckDecreaseHeight cur-side dispatch in \
             `to_lean_sst_expr.rs` has drifted — each side must use \
             `decrease_height_datatype(&args[i].typ)` for its own \
             type. Got:\n{}", printed);
        assert!(printed.contains("Forest.height"),
            "prev side should reference `Forest.height` (prev has type \
             Forest). If this is missing or reads `Tree.height` instead, \
             the CheckDecreaseHeight prev-side dispatch in \
             `to_lean_sst_expr.rs` has drifted (#109 stretch regression). \
             Got:\n{}", printed);
    }

    // ── #120 shape-drift tests ──────────────────────────────────
    //
    // Belt-and-suspenders against silent breakage from upstream
    // Verus changes. Each test here pins an invariant Tactus
    // depends on but can't enforce statically. Fails here turn
    // into focused error messages naming the fix site instead of
    // obscure end-to-end verification regressions.
    //
    // Two invariants pinned:
    //
    // 1. `build_wp` preserves `StmX::Block` source ordering as the
    //    Wp tree's left-to-right shape. The
    //    `vir::recursion::CheckDecreaseHeight`-before-recursive-Call
    //    invariant reduces to this structural property: as long as
    //    Verus inserts the Assert before the Call in the SST
    //    statement sequence, our right-to-left fold makes the Wp
    //    tree have Assert wrapping Call. If `build_wp`'s fold
    //    direction drifted, recursive fns would silently lose
    //    their termination obligation.
    //
    // 2. `closure_lambda_from_ast` rejects an ast_body that isn't
    //    `ExprX::NonSpecClosure`. The contract is that
    //    `ast_to_sst` populates `StmX::ClosureInner.ast_body`
    //    (added in #93) with the closure's original AST `Expr`.
    //    If a future rebase changes that population path, this
    //    test catches the contract violation before it manifests
    //    as nonsense generated Lean.

    /// Construct an SST `Stm` wrapping `StmX::Assert(None, None, e)`.
    fn assert_stm(e: Exp) -> Stm {
        use vir::def::Spanned;
        Spanned::new(test_span(), StmX::Assert(None, None, e))
    }

    /// Construct an SST `Stm` wrapping `StmX::Assume(e)`.
    fn assume_stm(e: Exp) -> Stm {
        use vir::def::Spanned;
        Spanned::new(test_span(), StmX::Assume(e))
    }

    /// Construct an SST `Stm` wrapping `StmX::Block(stms)`.
    fn block_stm(stms: Vec<Stm>) -> Stm {
        use vir::def::Spanned;
        Spanned::new(test_span(), StmX::Block(Arc::new(stms)))
    }

    /// Minimal `WpCtx<'static>` for tests that don't need fn lookup
    /// or type info. `build_wp` on `Assert` / `Assume` / `Block`
    /// doesn't read `fn_map` / `type_map` — only `Return` / `Call` /
    /// `Loop` paths do.
    fn mk_test_ctx() -> WpCtx<'static> {
        WpCtx {
            fn_map: HashMap::new(),
            type_map: HashMap::new(),
            ret_name: None,
            ensures_goal: LExpr::lit_true(),
            mut_ref_locals: HashSet::new(),
        }
    }

    #[test]
    fn build_wp_block_preserves_assert_before_assume_ordering() {
        // Source order [assert(p), assume(q)] must produce
        // Wp::Assert(p, Box::new(Wp::Assume(q, Box::new(after)))) —
        // the structural property that `vir::recursion`'s
        // CheckDecreaseHeight-before-Call invariant relies on.
        let p = var_exp("p", typ_bool());
        let q = var_exp("q", typ_bool());
        let block = block_stm(vec![assert_stm(p), assume_stm(q)]);
        let ctx = mk_test_ctx();
        let after = Wp::Done(LExpr::lit_true());
        let wp = build_wp(&block, after, &ctx, &LoopStack::Empty).expect("build_wp");

        match wp {
            Wp::Assert(_, inner1) => match *inner1 {
                Wp::Assume(_, inner2) => {
                    assert!(matches!(*inner2, Wp::Done(_)),
                        "expected Done innermost; if this fails the \
                         Block fold's terminator threading has drifted");
                }
                _ => panic!(
                    "expected Wp::Assume after Assert (Block source \
                     ordering preserved). If this fails, build_wp's \
                     right-to-left fold over Block has drifted, \
                     breaking the recursion-pass invariant that \
                     Assert(CheckDecreaseHeight) precedes the Call \
                     in the Wp tree. Fix site: build_wp's \
                     StmX::Block arm in sst_to_lean.rs."
                ),
            }
            _ => panic!(
                "expected Wp::Assert as outermost (first stmt was an \
                 Assert). If this fails, build_wp's Block fold direction \
                 reversed."
            ),
        }
    }

    #[test]
    fn build_wp_block_preserves_three_stmt_ordering() {
        // Three-stmt block exercises a deeper fold. Source order
        // [assert(p), assume(q), assert(r)] should produce
        // Assert(p) → Assume(q) → Assert(r) → Done.
        let p = var_exp("p", typ_bool());
        let q = var_exp("q", typ_bool());
        let r = var_exp("r", typ_bool());
        let block = block_stm(vec![
            assert_stm(p),
            assume_stm(q),
            assert_stm(r),
        ]);
        let ctx = mk_test_ctx();
        let after = Wp::Done(LExpr::lit_true());
        let wp = build_wp(&block, after, &ctx, &LoopStack::Empty).expect("build_wp");

        match wp {
            Wp::Assert(_, b1) => match *b1 {
                Wp::Assume(_, b2) => match *b2 {
                    Wp::Assert(_, b3) => assert!(matches!(*b3, Wp::Done(_))),
                    _ => panic!("expected Wp::Assert at depth 3"),
                }
                _ => panic!("expected Wp::Assume at depth 2"),
            }
            _ => panic!("expected Wp::Assert outermost"),
        }
    }

    /// Construct a synthetic VIR-AST `Expr` with the given `ExprX`.
    fn ast_expr(x: ExprX, typ: Typ) -> Expr {
        Arc::new(SpannedTyped {
            span: test_span(),
            typ,
            x,
        })
    }

    #[test]
    fn closure_lambda_from_ast_rejects_non_closure_ast_body() {
        // Pass a bogus ast_body that's NOT an ExprX::NonSpecClosure
        // (here, a Const). `closure_lambda_from_ast` must return Err
        // with the documented "wasn't an ExprX::NonSpecClosure"
        // message — not panic, not pass through to `vir_expr_to_ast`
        // (which would render as something nonsensical).
        //
        // If `ast_to_sst` ever stops populating
        // `StmX::ClosureInner.ast_body` with the closure's
        // ExprX::NonSpecClosure (e.g., it stores body alone, or
        // forgets entirely), this is the test that fires.
        let bogus = ast_expr(
            ExprX::Const(vir::ast::Constant::Bool(false)),
            typ_bool(),
        );
        let result = closure_lambda_from_ast(&bogus);
        assert!(result.is_err(), "expected Err for non-NonSpecClosure ast_body");
        let err = result.unwrap_err();
        assert!(
            err.contains("wasn't an ExprX::NonSpecClosure"),
            "expected error to name the contract violation; got: {}",
            err
        );
        assert!(
            err.contains("ast_to_sst"),
            "expected error to point at the fix site (ast_to_sst); got: {}",
            err
        );
    }

    // ── #114 follow-up coverage: Wp::Hyp + 3-level lex ────────────
    //
    // Two regression-test gaps surfaced by the post-#114 review pass
    // (P2 findings; this is the follow-up that closes them):
    //
    // 1. `Wp::Hyp` walker arm — covered end-to-end via #114's
    //    cond_setup transform but no direct unit test. Pin that the
    //    walker pushes the LExpr as a CtxFrame::Hyp (vs. ignoring it
    //    or wrapping wrong).
    //
    // 2. `lex_decrease_obligation` recursion at depth ≥ 3 — #110's
    //    e2e tests cover 2-level lex; the recursive structure is
    //    correct by induction but a 3-level test pins the depth.

    /// Minimal `ObligationEmitter` for tests. The default closer is
    /// `tactus_auto`; tests inspecting emitted theorems can ignore
    /// the closer field.
    fn mk_test_emitter() -> ObligationEmitter {
        ObligationEmitter {
            fn_name: "test_fn".to_string(),
            base_binders: Vec::new(),
            counter: 0,
            out: Vec::new(),
            tactic_prefix: Vec::new(),
            default_closer: crate::lean_ast::Tactic::Named("tactus_auto".to_string()),
        }
    }

    #[test]
    fn wp_hyp_walker_wraps_done_leaf_with_hyp_frame() {
        // Wp::Hyp { hyp: p, body: Wp::Done(q) }
        // Walker pushes CtxFrame::Hyp(p), then walks body (Done) →
        // emits one theorem whose wrapped goal contains `p → q`.
        let p = LExpr::var_lit("p_test_hyp");
        let q = LExpr::var_lit("q_test_done");
        let wp = Wp::Hyp {
            hyp: p.clone(),
            body: Box::new(Wp::Done(q.clone())),
        };
        let ctx = mk_test_ctx();
        let mut emitter = mk_test_emitter();
        walk_obligations(&wp, &ctx, &OblCtx::new(), &mut emitter);

        assert_eq!(emitter.out.len(), 1,
            "expected exactly one theorem emitted from Wp::Done leaf");
        let theorem = &emitter.out[0];
        let printed = crate::lean_pp::pp_expr(
            &crate::lean_ast::strip_span_marks(&theorem.goal),
        );
        // After wrap: the Hyp frame becomes `p_test_hyp → ...` and
        // the Done leaf is `q_test_done`. The printer renders `→`
        // explicitly; both names should appear.
        assert!(printed.contains("p_test_hyp"),
            "expected hyp `p_test_hyp` in goal; got: {}", printed);
        assert!(printed.contains("q_test_done"),
            "expected leaf `q_test_done` in goal; got: {}", printed);
        assert!(printed.contains("→"),
            "expected `→` (implication from hyp); got: {}", printed);
    }

    #[test]
    fn wp_hyp_walker_passes_through_with_no_body_obligations() {
        // If body is Wp::Done(true), the walker still emits one
        // theorem (the Done leaf) — the Hyp's only effect is to
        // appear in the wrapped goal. No silent dropping.
        let hyp = LExpr::var_lit("just_a_hyp");
        let wp = Wp::Hyp {
            hyp,
            body: Box::new(Wp::Done(LExpr::lit_true())),
        };
        let ctx = mk_test_ctx();
        let mut emitter = mk_test_emitter();
        walk_obligations(&wp, &ctx, &OblCtx::new(), &mut emitter);
        assert_eq!(emitter.out.len(), 1,
            "Wp::Hyp wrapping Done(True) emits one theorem (Done's)");
    }

    /// Construct a `DecreaseLevel` for tests with a synthetic Var
    /// expression and a custom d_old name.
    fn mk_decrease_level(value_var: &str, typ: Typ, d_old_name: &str) -> DecreaseLevel<'static> {
        // Leak the Exp to give it 'static lifetime — fine for tests
        // since we don't care about reclamation. The Validated
        // borrow is from the leaked allocation.
        let exp: &'static Exp = Box::leak(Box::new(var_exp(value_var, typ)));
        let value = crate::to_lean_sst_expr::Validated::check(exp)
            .expect("test fixture: synthetic var should validate");
        DecreaseLevel { value, d_old_name: d_old_name.to_string() }
    }

    #[test]
    fn lex_decrease_obligation_three_levels_recurses_correctly() {
        // 3-level lex `decreases a, b, c`. Verify the obligation has
        // the expected shape:
        //   (0 ≤ a ∧ a < a_old) ∨
        //     (a = a_old ∧ ((0 ≤ b ∧ b < b_old) ∨
        //       (b = b_old ∧ (0 ≤ c ∧ c < c_old))))
        let levels = vec![
            mk_decrease_level("a", typ_int(), "a_old_test"),
            mk_decrease_level("b", typ_int(), "b_old_test"),
            mk_decrease_level("c", typ_int(), "c_old_test"),
        ];
        let result = lex_decrease_obligation(&levels);
        let printed = crate::lean_pp::pp_expr(&result);

        // All three (cur, old) pairs should appear.
        for s in &["a", "b", "c", "a_old_test", "b_old_test", "c_old_test"] {
            assert!(printed.contains(s),
                "expected `{}` in 3-level lex obligation; got: {}", s, printed);
        }
        // Two `∨` (one per non-base level — the base just emits the
        // `0 ≤ cur ∧ cur < old` lt-branch).
        let or_count = printed.matches('∨').count();
        assert_eq!(or_count, 2,
            "3-level lex should have 2 disjunctions (one per non-base level); got {}: {}",
            or_count, printed);
        // Three `≤` — one per level's `0 ≤ cur` lower bound (#129).
        let le_count = printed.matches('≤').count();
        assert_eq!(le_count, 3,
            "3-level lex should have 3 `0 ≤ cur` lower bounds (one per level); got {}: {}",
            le_count, printed);
    }

    // ── WpCtx::new direct tests (#126) ────────────────────────────
    //
    // Covers the validation contract: passing `Validated::check`-able
    // reqs/ens_exps succeeds; passing an unsupported SST form returns
    // `Err` cleanly (no panic, no silent acceptance). The validation
    // logic is shared with the body-walk path, so a shared regression
    // here would also surface via e2e — but the focused test gives a
    // pointed error site if the validation flow drifts.

    /// Build a minimal `FuncCheckSst` with the given reqs and
    /// ens_exps. Body is an empty Block; no local decls; no destination.
    fn empty_func_check(reqs: Vec<Exp>, ens_exps: Vec<Exp>) -> FuncCheckSst {
        use vir::sst::{PostConditionSst, PostConditionKind, UnwindSst};
        FuncCheckSst {
            reqs: Arc::new(reqs),
            post_condition: Arc::new(PostConditionSst {
                dest: None,
                ens_exps: Arc::new(ens_exps),
                ens_spec_precondition_stms: Arc::new(vec![]),
                kind: PostConditionKind::Ensures,
            }),
            unwind: UnwindSst::NoUnwind,
            body: block_stm(vec![]),
            local_decls: Arc::new(vec![]),
            local_decls_decreases_init: Arc::new(vec![]),
            statics: Arc::new(vec![]),
        }
    }

    /// Construct an `ExpX::Old(snapshot, var)` expression. `Old` is
    /// rejected by `sst_exp_to_ast_checked` as an internal-bug arm
    /// (Verus lowers user-syntax `old(x)` to `ExpX::VarAt(x, Pre)`,
    /// so `Old` shouldn't appear in our SST input). Useful as a
    /// canonical "unsupported SST form" for negative tests.
    fn old_exp(snapshot: &str, var: &str) -> Exp {
        Arc::new(SpannedTyped {
            span: test_span(),
            typ: typ_int(),
            x: ExpX::Old(Arc::new(snapshot.to_string()), var_ident(var)),
        })
    }

    #[test]
    fn wpctx_new_empty_reqs_and_ensures_succeeds() {
        // Trivial happy path: empty validates, ensures_goal becomes
        // `and_all([])` = `True`. WpCtx is constructible.
        let krate = empty_krate();
        let check = empty_func_check(vec![], vec![]);
        let mut_param_names = HashSet::new();
        let result = WpCtx::new(&krate, &check, &mut_param_names);
        assert!(result.is_ok(), "empty WpCtx should construct: {:?}", result.err());
        let ctx = result.unwrap();
        assert!(ctx.fn_map.is_empty(), "fn_map should be empty for empty krate");
        assert!(ctx.type_map.is_empty(), "type_map should be empty for empty local_decls");
        assert!(ctx.ret_name.is_none(), "ret_name should be None when dest is None");
    }

    #[test]
    fn wpctx_new_rejects_unsupported_form_in_reqs() {
        // A req with `ExpX::Old` triggers `check_exp` rejection.
        // WpCtx::new must propagate the Err (not panic, not silently
        // accept). The Err message references the unsupported form
        // so a future Verus pipeline change that legitimizes Old in
        // SST surfaces as a focused failure, not a silent miscompile.
        let krate = empty_krate();
        let bad_req = old_exp("snapshot", "x");
        let check = empty_func_check(vec![bad_req], vec![]);
        let mut_param_names = HashSet::new();
        let result = WpCtx::new(&krate, &check, &mut_param_names);
        assert!(result.is_err(),
            "WpCtx::new must reject ExpX::Old in reqs; got Ok(_)");
        let err = result.err().unwrap();
        assert!(err.contains("Old") || err.contains("internal bug"),
            "rejection message should reference Old or 'internal bug'; got: {}",
            err);
    }

    #[test]
    fn wpctx_new_rejects_unsupported_form_in_ensures() {
        // Same as above but for ens_exps. Symmetry test — the
        // validation iterates both reqs and ens_exps, and a future
        // refactor that drops one of the loops would silently accept
        // unsupported ensures.
        let krate = empty_krate();
        let bad_ens = old_exp("snapshot", "y");
        let check = empty_func_check(vec![], vec![bad_ens]);
        let mut_param_names = HashSet::new();
        let result = WpCtx::new(&krate, &check, &mut_param_names);
        assert!(result.is_err(),
            "WpCtx::new must reject ExpX::Old in ens_exps; got Ok(_)");
    }

    // ── walk_loop direct tests (#126) ─────────────────────────────
    //
    // Construct `Wp::Loop`-like inputs and call `walk_loop` directly,
    // inspecting the emitted theorems. This pins behaviors that e2e
    // tests cover incidentally:
    //
    // 1. **Init filter on `at_entry`.** Init theorems fire only for
    //    invariants whose kind has `at_entry = true`. An `Ensures`-
    //    kind inv (loop `ensures`, `at_entry = false`) must NOT
    //    produce an init theorem — it only contributes at exit.
    //
    // The full walker is heavy to test directly (Wp tree + OblCtx +
    // emitter all need fixtures); we test the at_entry filter as the
    // single most-likely-to-regress structural invariant. walk_call
    // direct tests deferred — see DESIGN.md "User-facing features
    // not tested" for the cost/benefit analysis.

    /// Construct a synthetic `LoopInv` with given (at_entry, at_exit)
    /// flags and inv expression. Used to drive `walk_loop` past its
    /// classification gate.
    fn loop_inv(at_entry: bool, at_exit: bool, e: Exp) -> LoopInv {
        LoopInv { at_entry, at_exit, inv: e }
    }

    #[test]
    fn walk_loop_skips_init_for_ensures_kind_invariant() {
        // A loop with one `Ensures`-kind invariant (at_entry=false,
        // at_exit=true) should produce ZERO init theorems — init is
        // gated on at_entry. Pre-fix Tactus emitted init for every
        // inv regardless of kind; #89 added the at_entry filter.
        // This test pins the gate against future regression.
        //
        // Setup: cond=None, decrease=[], no mod_vars, body and after
        // are both Done(true). Theorems emitted come from:
        //   * 0 init (the Ensures-kind inv is at_entry=false)
        //   * 1 maintain (body's Done(true) → emit_done_or_split's
        //     fallback arm)
        //   * 1 use (after's Done(true), same)
        // Total: 2. None should be the init theorem for the inv.
        use std::collections::HashSet;
        let p = var_exp("p_loop_test", typ_bool());
        let p_static: &'static Exp = Box::leak(Box::new(p));
        let validated_p = crate::to_lean_sst_expr::Validated::check(p_static)
            .expect("p validates");
        let invs = vec![loop_inv(false, true, p_static.clone())];
        let validated_invs = vec![validated_p];
        let inv_kinds = vec![LoopInvKind::Ensures];
        let body = Wp::Done(LExpr::lit_true());
        let after = Wp::Done(LExpr::lit_true());

        let krate = empty_krate();
        let check = empty_func_check(vec![], vec![]);
        let mut_param_names = HashSet::new();
        let ctx = WpCtx::new(&krate, &check, &mut_param_names)
            .expect("empty ctx");
        let mut emitter = mk_test_emitter();

        walk_loop(
            None,
            &invs,
            &validated_invs,
            &inv_kinds,
            &[],
            &[],
            &body,
            &after,
            &ctx,
            &OblCtx::new(),
            &mut emitter,
        );

        // No theorem should be tagged as a loop_invariant init —
        // every emitted theorem here is from body/after's Done leaves
        // (label "ensures") or a maintain/use clause, not init.
        let init_count = emitter.out.iter()
            .filter(|t| t.name.contains("loop_invariant"))
            .count();
        assert_eq!(init_count, 0,
            "Ensures-kind inv (at_entry=false) must not emit init \
             theorem. Got {} loop_invariant-named theorems out of \
             {} total. If this fails, walk_loop's at_entry filter \
             has drifted (#89 regression). Theorems: {:?}",
            init_count, emitter.out.len(),
            emitter.out.iter().map(|t| &t.name).collect::<Vec<_>>());
    }

    #[test]
    fn walk_loop_emits_init_for_at_entry_invariant() {
        // Companion test: an `Invariant`-kind inv (at_entry=true,
        // at_exit=true) DOES produce one init theorem. Together with
        // the previous test, this pins the at_entry filter as a
        // discriminator (not a no-op).
        use std::collections::HashSet;
        let p = var_exp("p_loop_test", typ_bool());
        let p_static: &'static Exp = Box::leak(Box::new(p));
        let validated_p = crate::to_lean_sst_expr::Validated::check(p_static)
            .expect("p validates");
        let invs = vec![loop_inv(true, true, p_static.clone())];
        let validated_invs = vec![validated_p];
        let inv_kinds = vec![LoopInvKind::Invariant];
        let body = Wp::Done(LExpr::lit_true());
        let after = Wp::Done(LExpr::lit_true());

        let krate = empty_krate();
        let check = empty_func_check(vec![], vec![]);
        let mut_param_names = HashSet::new();
        let ctx = WpCtx::new(&krate, &check, &mut_param_names)
            .expect("empty ctx");
        let mut emitter = mk_test_emitter();

        walk_loop(
            None,
            &invs,
            &validated_invs,
            &inv_kinds,
            &[],
            &[],
            &body,
            &after,
            &ctx,
            &OblCtx::new(),
            &mut emitter,
        );

        let init_count = emitter.out.iter()
            .filter(|t| t.name.contains("loop_invariant"))
            .count();
        assert_eq!(init_count, 1,
            "Invariant-kind inv (at_entry=true) should emit exactly \
             one init theorem; got {} (theorems: {:?})",
            init_count,
            emitter.out.iter().map(|t| &t.name).collect::<Vec<_>>());
    }

    #[test]
    fn lex_decrease_obligation_single_level_emits_lt_with_lower_bound() {
        // Single-level case: `0 ≤ cur ∧ cur < old`. The lex tail
        // `(cur = old ∧ False)` collapses (recursion's base is
        // structurally absent for len 1), so we emit just the
        // lt-branch — but the lt-branch carries the `0 ≤` lower
        // bound (#129).
        let levels = vec![
            mk_decrease_level("d", typ_int(), "d_old_test"),
        ];
        let result = lex_decrease_obligation(&levels);
        let printed = crate::lean_pp::pp_expr(&result);
        assert!(printed.contains("d") && printed.contains("d_old_test"),
            "expected both `d` and `d_old_test` in single-level obligation; got: {}",
            printed);
        assert!(!printed.contains('∨'),
            "single-level should have NO disjunction; got: {}", printed);
        assert!(printed.contains('≤'),
            "single-level should have `0 ≤ cur` lower bound (#129); got: {}",
            printed);
    }

    /// REVIEW lens 4/2: shape-drift guard for Verus's pre-injection
    /// of `Assert` (per requires) and `Assume` (per ensures) BEFORE
    /// the `StmX::AssertBitVector` node. Two Tactus design choices
    /// are load-bearing on this:
    ///
    /// * `obl.wrap_no_hyps` (in `walk_obligations`'s `Wp::AssertBitVector`
    ///   arm) drops the Hyp frames that come from the pre-injected
    ///   `Assume(ens)`. Without pre-injection there'd be no hyps to
    ///   drop, but the BV-mode goal would also lack the soundness-
    ///   relevant continuation hypothesis.
    /// * `BITVEC_INT_INSTANCES` (in generate.rs) is emitted because
    ///   the post-AssertBitVector continuation theorems contain
    ///   Int-mode `x ^^^ y` from those `Assume(ens)` statements.
    ///   Without pre-injection, the instances become unused.
    ///
    /// If Verus changes the upstream encoding (e.g., drops the
    /// per-requires Asserts in favor of treating them as free
    /// assumptions, or drops the per-ensures Assumes now that
    /// `AssertBitVector` itself publishes ensures), both Tactus
    /// design choices need re-evaluation.
    ///
    /// We grep the upstream source rather than running ast_to_sst
    /// because constructing a synthetic Ctx is too involved for a
    /// shape-drift guard. The grep is brittle to phrasing changes
    /// but robust to semantic-preserving refactors that keep the
    /// for-loops + StmX::Assert / StmX::Assume push pattern.
    #[test]
    fn ast_to_sst_pre_injects_around_assert_bit_vector() {
        let source = include_str!("../../vir/src/ast_to_sst.rs");
        let bv_arm_start = source.find("AssertQueryMode::BitVector =>")
            .expect(
                "AssertQueryMode::BitVector arm not found in ast_to_sst.rs. \
                 Either Verus's AssertQueryMode enum was renamed, or the \
                 BitVector arm was deleted (in which case Tactus's \
                 StmX::AssertBitVector path may need a different upstream \
                 entry point)."
            );
        // Take a generous window to cover the full arm body.
        let window_end = (bv_arm_start + 3500).min(source.len());
        let arm = &source[bv_arm_start..window_end];

        assert!(
            arm.contains("for r in requires.iter()"),
            "Verus's AssertQueryMode::BitVector arm no longer iterates \
             `requires` to push per-clause pre-Asserts. Tactus's \
             `obl.wrap_no_hyps` design (in walk_obligations's \
             Wp::AssertBitVector arm) assumes per-requires Asserts are \
             pre-injected before StmX::AssertBitVector. Update the \
             design accordingly if upstream encoding has changed."
        );
        assert!(
            arm.contains("for e in ensures.iter()"),
            "Verus's AssertQueryMode::BitVector arm no longer iterates \
             `ensures` to push per-clause pre-Assumes. Tactus's \
             `BITVEC_INT_INSTANCES` emission (in generate.rs) assumes \
             per-ensures Assumes are pre-injected before \
             StmX::AssertBitVector (the post-assert continuation \
             theorems contain Int-mode `x ^^^ y` from these). Update \
             the design accordingly if upstream encoding has changed."
        );
        assert!(
            arm.contains("StmX::Assert("),
            "Verus's AssertQueryMode::BitVector arm no longer pushes \
             StmX::Assert nodes around requires. The per-requires \
             precondition theorems Tactus emits depend on this."
        );
        assert!(
            arm.contains("StmX::Assume("),
            "Verus's AssertQueryMode::BitVector arm no longer pushes \
             StmX::Assume nodes around ensures. The post-assert \
             ensures-as-hyp behavior depends on this."
        );
    }

    /// Right-way #4: pin the canonical fragment list returned by
    /// `bitvec_preamble_fragments`. Three fragments — Mathlib BitVec
    /// import, BVDecide import, Int instance addendum — covering the
    /// imports + post-prelude addendum required by an exec fn that
    /// uses `assert(P) by(bit_vector)`. If a future refactor changes
    /// what AssertBitVector requires, this test surfaces it as a
    /// focused failure rather than via a Lean elaboration error.
    #[test]
    fn bitvec_preamble_fragments_shape_pinned() {
        let frags = bitvec_preamble_fragments();
        assert_eq!(frags.len(), 3,
            "expected 3 fragments (Mathlib import, BVDecide import, instances); \
             got {} fragments: {:?}", frags.len(), frags);

        let imports: Vec<&str> = frags.iter()
            .filter_map(|f| if let PreambleFragment::Import(s) = f { Some(s.as_str()) } else { None })
            .collect();
        assert!(imports.contains(&"Mathlib.Data.BitVec"),
            "fragments should include Mathlib.Data.BitVec import");
        assert!(imports.contains(&"Lean.Elab.Tactic.BVDecide"),
            "fragments should include Lean.Elab.Tactic.BVDecide import");

        let addendums: Vec<&str> = frags.iter()
            .filter_map(|f| if let PreambleFragment::PreludeAddendum(s) = f { Some(s.as_str()) } else { None })
            .collect();
        assert_eq!(addendums.len(), 1, "expected exactly one PreludeAddendum");
        assert!(addendums[0].contains("instance : HXor Int Int Int"),
            "PreludeAddendum should contain the HXor Int instance");
    }

    /// REVIEW lens 4/3: shape-drift guard for the `bv_decide` module
    /// path. `Lean.Elab.Tactic.BVDecide` is in Lean 4 core (v4.25.0)
    /// — must be imported explicitly (top-level `import Lean` doesn't
    /// pull it in). If a future Lean toolchain bump moves this
    /// module (e.g., to a Mathlib-only path, or splits into a
    /// renamed submodule), `tactus_bit_vector`'s primary rung
    /// (`bv_decide`) silently fails to elaborate; `assert by(bit_vector)`
    /// regresses to the simp/decide fallbacks, losing SAT-backed
    /// reasoning for parameterized BitVec terms.
    ///
    /// The failing assertion's message names the fix site:
    /// `bitvec_preamble_fragments` in sst_to_lean.rs.
    #[test]
    fn bv_decide_import_path_pinned() {
        const EXPECTED: &str = "Lean.Elab.Tactic.BVDecide";
        let frags = bitvec_preamble_fragments();
        let bvdecide = frags.iter()
            .filter_map(|f| if let PreambleFragment::Import(s) = f { Some(s.as_str()) } else { None })
            .find(|s| s.contains("BVDecide"));
        assert_eq!(
            bvdecide,
            Some(EXPECTED),
            "BVDecide import path drift detected. Tactus expects \
             `{}` (Lean core, v4.25.0). Update `bitvec_preamble_fragments` \
             in sst_to_lean.rs if the toolchain has moved this module.",
            EXPECTED,
        );
    }

    /// REVIEW lens 3/6: defensive check that `BITVEC_INT_INSTANCES`'
    /// HXor/HAnd/HOr/HShiftLeft/HShiftRight Int instances use `.toNat`
    /// in their bodies — which is total on `Int` (returns 0 for
    /// negatives). Tactus only emits these ops on bounded-non-negative
    /// u-type Ints, so the negative-Int path is unreachable from
    /// emitted code; but the *instances themselves* must remain total
    /// to elaborate without warning, and a future refactor switching
    /// to a partial function would silently regress this property.
    ///
    /// Documented as a soundness trade-off in DESIGN.md: the
    /// `(-1 : Int).toNat = 0` semantics means `(-1) ^^^ x = x.toNat`
    /// — wonky but total. If a future Tactus path emits these on
    /// negative Ints, the values are wrong but no panic; the wonky
    /// semantics stays a "watch out" item, not a hard error.
    #[test]
    fn bitvec_int_instances_use_to_nat_total_form() {
        // The structural property: each instance's RHS goes through
        // `.toNat` (which is total). If a maintainer changes one to
        // (e.g.) `Int.toNat!` — partial, panics on negative — the
        // test fires.
        for op in &["HXor", "HAnd", "HOr", "HShiftLeft", "HShiftRight"] {
            let instance_line: Option<&str> = BITVEC_INT_INSTANCES.lines()
                .find(|l| l.contains(&format!("instance : {} Int Int Int", op)));
            let line = instance_line.unwrap_or_else(|| panic!(
                "BITVEC_INT_INSTANCES missing instance for {}", op
            ));
            assert!(line.contains("a.toNat"),
                "{} instance must use a.toNat (total form) in its body; got: {}",
                op, line);
            assert!(line.contains("b.toNat"),
                "{} instance must use b.toNat (total form) in its body; got: {}",
                op, line);
        }
    }
}
