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
//! 3. `walk_obligations(&body_wp, &ctx, &OblCtx::new(closer), &mut emitter)`
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
    AssertQueryMode, BinaryOp, Expr, ExprX, Fun, FunctionKind, FunctionX,
    KrateX, SpannedTyped, TactusKind, Typ, UnaryOp, UnaryOpr,
    VarBinder, VarIdent,
};
use vir::ast_visitor::map_expr_visitor;
use vir::messages::Span;
use crate::lean_ast::{
    and_all, substitute, AssertKind, Binder as LBinder, BinderKind, Expr as LExpr,
    ExprNode, HypothesisKind, ObligationKind,
    PreambleFragment, Tactic, Theorem,
};
use crate::expr_shared::{is_mut_ref_typ, varat_pre_name};
use std::sync::Arc;
use crate::to_lean_expr::{vir_expr_to_ast, vir_expr_to_ast_for_inlining_with_ctx};
use crate::to_lean_sst_expr::{lower as lower_validated, lower_with_ctx as lower_validated_with_ctx, sst_exp_to_ast_checked, sst_exp_to_ast_checked_with_ctx, type_bound_predicate, Validated};
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

/// Preamble fragments required by an `assert(P) by(nonlinear_arith)`
/// scope. `nlinarith` lives in Mathlib's Linarith module (it's
/// `linarith` extended with nonlinear preprocessing). Attached to
/// every theorem emitted inside a `Wp::AssertQuery` scope via
/// `OblCtx::closer_preamble`; `krate_preamble` aggregates and dedups
/// across the file.
pub(crate) fn nonlinear_preamble_fragments() -> Vec<PreambleFragment> {
    vec![PreambleFragment::Import("Mathlib.Tactic.Linarith".to_string())]
}

/// Render a `Tactic` as a Lean tactic text snippet. `Named` emits
/// the bare name; `Raw` wraps in parens to keep precedence stable
/// when the snippet is embedded inside a `first | ... | ...`
/// composition. Used by the `Wp::AssertQuery` walker to compose
/// `first | (intros; primary) | <outer_closer>`.
fn tactic_as_str(t: &Tactic) -> String {
    match t {
        Tactic::Named(s) => s.clone(),
        Tactic::Raw(s) => format!("({})", s),
    }
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
    /// Locals of kind `LocalDeclKind::AssertByVar` — the skolem
    /// variables of `assert forall |x| … by { … }` proof bodies. The
    /// `StmX::DeadEnd` arm binds the ones its block references as
    /// ∀-binders on the scope's theorems (they have no `Wp::Let` —
    /// Verus declares them fn-wide and scopes them syntactically;
    /// F4, DESIGN-lean-all-proofs-followons.md).
    pub assert_by_var_typs: HashMap<&'a VarIdent, &'a Typ>,
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
    /// Map from a BorrowMut local's sanitized name to the user-local
    /// `VarIdent` it bridges. Populated by walking the SST body
    /// looking for `Assign(user_local, Var(borrow_mut_local))` —
    /// Verus's new-mut-ref encoding for `bump(&mut y)` emits this
    /// assignment as the forward-forward linkage between `y` and
    /// the synthetic BorrowMut local.
    ///
    /// `extract_mut_target` consults this map to redirect the call's
    /// mut-arg from the BorrowMut local to the user-local directly,
    /// so Phase 4 rebinds the user-local to the post-state. The
    /// body's linkage `Assign` is dropped in `build_wp` so the let
    /// frame doesn't double-bind.
    ///
    /// This eliminates Verus's BorrowMut indirection for the simple
    /// `&mut <local>` case — the indirection exists for SMT
    /// bookkeeping that Lean doesn't need. See HANDOFF.md 2026-05-26
    /// session note "BorrowMut elimination" for the rationale.
    pub borrow_mut_links: HashMap<String, VarIdent>,
    /// Caller fn's params at their body-shadow Lean typ — used by
    /// `walk_call` to compute the actual Lean typ of each caller arg
    /// when building typed value_subst entries. For body-shadowed
    /// `&mut` params, the stored typ has one outer ref decoration
    /// stripped (matching what `binder_ctx_from_params` records); for
    /// other params, the typ is as-declared.
    ///
    /// This is the source-of-truth for "what is the rendered LExpr's
    /// actual Lean typ at this caller site?" — answers the question
    /// that `a.typ` can't (Verus's AST typ is the spec-level annotation,
    /// not the body-shadow result). Without this, typed substitution
    /// at call sites would over-wrap or under-wrap args.
    pub caller_param_typs: HashMap<VarIdent, Typ>,
    /// Declared Lean typ of the return value (the `-> (r: T)` `T`), or
    /// `None` for unit returns / when the dest var has no local decl.
    /// The `Return` arm coerces the returned expr to this typ before
    /// the `let r := …` binding — Verus keeps a returned `&`-value at
    /// its reference typ (e.g. `**b : &Box<u8>`), so without the
    /// coercion `r` would bind at `Tactus.Ref (Box Int)` while the
    /// ensures (now binop-reconciled) expects inner `Int`. Coercing
    /// `let r := <e>.deref.deref` keeps body and ensures symmetric.
    pub ret_typ: Option<Typ>,
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
        // BorrowMut elimination map (caller-side new-mut-ref).
        // Walked from the SST body before WpCtx construction. Maps
        // each sanitized BorrowMut-local name to the user-local
        // VarIdent it bridges. Empty for fns without BorrowMut
        // indirection (the common case).
        borrow_mut_links: HashMap<String, VarIdent>,
        // Caller fn's params at body-shadow Lean typ — populated by
        // the caller (`exec_fn_theorems_to_ast`) from `fn_sst.x.pars`.
        // Used by `walk_call` to compute caller_arg actual Lean typ
        // for typed value_subst entries.
        caller_param_typs: HashMap<VarIdent, Typ>,
    ) -> Result<Self, String> {
        // Validate the *rewritten* expressions — every mut-ref shape
        // Verus might emit (legacy `VarAt(x, Pre)` or new-mode
        // `MutRefCurrent`/`MutRefFuture`/`MutRefFinal`) is rewritten
        // to its canonical destination shape before validation.
        // Without this, `check_exp` would reject any MutRef-wrapped
        // reference even though we handle it correctly downstream.
        for req in check.reqs.iter() {
            let rewritten = rewrite_mut_ref_in_exp(
                req,
                mut_param_names,
                RewritePhase::Reqs,
            );
            check_exp(&rewritten)?;
        }
        for ens in check.post_condition.ens_exps.iter() {
            let rewritten = rewrite_mut_ref_in_exp(
                ens,
                mut_param_names,
                RewritePhase::Ensures,
            );
            check_exp(&rewritten)?;
        }
        let fn_map: FnMap = krate.functions.iter().map(|f| (&f.x.name, &f.x)).collect();
        // RenderCtx with the fn_map for class-method-call coercion at
        // trait dispatch sites in the ensures rendering below (cross-crate
        // trait method decls aren't in fn_map and gracefully fall back to
        // no-coerce), plus the params' Lean-level typs so a Field access
        // on a `&self` receiver in the ensures derefs correctly. The
        // ensures is unshadowed (unlike requires), so it needs the same
        // binder-aware deref the body does.
        let render_ctx = crate::expr_shared::RenderCtx::with_fn_map(&fn_map)
            .with_binder_typs(&caller_param_typs);
        let type_map: HashMap<&VarIdent, &Typ> =
            check.local_decls.iter().map(|d| (&d.ident, &d.typ)).collect();
        let assert_by_var_typs: HashMap<&VarIdent, &Typ> = check.local_decls.iter()
            .filter(|d| matches!(d.kind, vir::sst::LocalDeclKind::AssertByVar { .. }))
            .map(|d| (&d.ident, &d.typ))
            .collect();
        let ret_name = check.post_condition.dest.as_ref().map(|v| v.0.as_str());
        // Declared Lean typ of the return value, looked up via the dest
        // VarIdent (post_condition.dest carries only the name) against
        // the local-decl type map. `None` for unit returns or when the
        // dest has no decl entry.
        let ret_typ: Option<Typ> = check
            .post_condition
            .dest
            .as_ref()
            .and_then(|dest| type_map.get(dest).map(|t| (*t).clone()));
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
                // Single-pass rewrite — handles every mut-ref shape
                // Verus emits in either mode, producing the canonical
                // destination form for ensures evaluation:
                //   * legacy `VarAt(x, Pre)`            → `Var(<x>_at_pre_tactus)`
                //   * new-mode `MutRefCurrent(Var(x))`  → `Var(<x>_at_pre_tactus)` (pre-state)
                //   * new-mode `MutRefFuture(Var(x))`   → `Var(x)` (post-state)
                //   * new-mode `MutRefFinal(Var(x))`    → `Var(x)`
                let rewritten = rewrite_mut_ref_in_exp(
                    ens,
                    mut_param_names,
                    RewritePhase::Ensures,
                );
                // The mut-ref rewrite preserves ExpX shape, so validation
                // that succeeded on the pre-rewrite Exp succeeds here too;
                // propagating `Validated::check`'s Err handles any drift.
                // (`uN -> nat` casts are kept as Clip{Nat} by Verus's
                // `--lean-backend` lowering — no Tactus coercion needed.)
                Ok(LExpr::span_mark(
                    format_rust_loc(&ens.span),
                    Some(ens.span.clone()),
                    AssertKind::Obligation(ObligationKind::Postcondition),
                    // Lower with the RenderCtx so trait method calls
                    // in the ensures get correct receiver coercion.
                    lower_validated_with_ctx(&Validated::check(&rewritten)?, &render_ctx),
                ))
            }).collect::<Result<Vec<_>, String>>()?
        );
        Ok(Self {
            fn_map,
            type_map,
            assert_by_var_typs,
            ret_name,
            ensures_goal,
            mut_ref_locals: mut_param_names.clone(),
            borrow_mut_links,
            caller_param_typs,
            ret_typ,
        })
    }

    /// The binder-aware `RenderCtx` for rendering THIS fn's body and
    /// ensures: the `fn_map` (for trait-dispatch receiver coercion) plus
    /// the params' Lean-level typs (`caller_param_typs`) so Field /
    /// IsVariant projections deref the receiver to the right depth (the
    /// `self.v` → `self.deref.v` fix). NOT used for requires rendering,
    /// which unwraps params via `let x := x.deref` shadows instead — see
    /// `build_req_binders` — so adding the binder map there would
    /// double-deref.
    fn render_ctx(&self) -> crate::expr_shared::RenderCtx<'_> {
        crate::expr_shared::RenderCtx::with_fn_map(&self.fn_map)
            .with_binder_typs(&self.caller_param_typs)
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
    // Cross-crate broadcast lemmas the fn brings into scope via
    // `broadcast use <group>;` (#122), resolved by
    // `collect_broadcast_lemma_funs`. Each is emitted as a Lean axiom
    // in the preamble (by `krate_preamble`) and injected here as a
    // `have _tactus_bc_<i> := <axiom>` tactic prefix so the closer can use
    // it. Empty for fns without `broadcast use` (the common case).
    broadcast_lemmas: &[&'a Fun],
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
        .filter(|p| is_mut_ref_typ(&p.x.typ, p.x.is_mut))
        .map(|p| sanitize(&p.x.name.0))
        .collect();
    for decl in check.local_decls.iter() {
        if matches!(decl.kind, LocalDeclKind::BorrowMut) {
            mut_param_names.insert(sanitize(&decl.ident.0));
        }
    }

    // Single-pass rewrite (#95+#94 collapse): convert every mut-ref
    // shape Verus emits to its canonical destination form, regardless
    // of which mode (legacy vs new-mut-ref) the upstream used.
    //   * legacy `VarAt(x, Pre)`            → `Var(<x>_at_pre_tactus)`
    //   * new-mode `MutRefCurrent(Var(x))`  → `Var(x)` (post-state shadow)
    //   * new-mode `MutRefFuture(Var(x))`   → `Var(x)`
    //   * new-mode `MutRefFinal(Var(x))`    → `Var(x)`
    // Body-phase only (assignments + reads); the ensures-phase form
    // (which also rewrites `MutRefCurrent` → pre-state) runs separately
    // inside `WpCtx::new`.
    let rewritten_body: Stm = rewrite_mut_ref_in_stm(&check.body, &mut_param_names);

    // BorrowMut elimination: walk the body (post mut-ref rewrites)
    // collecting `Assign(user_local, Var(borrow_mut_local))` linkage
    // patterns. The map is consulted at call sites to redirect
    // mut-args from the BorrowMut local to the user-local (so Phase
    // 4 rebinds the user-local) and at Assign handling to drop the
    // linkage statements. Set is the BorrowMut subset of
    // `mut_param_names` — fn-level &mut params and BorrowMut locals
    // both live in mut_param_names but only the latter have the
    // forward-forward linkage shape we want to detect.
    // Keys are LeanName-style (disambiguator-aware) so multiple
    // BorrowMut locals sharing a base name (`tmp%` with `VirTemp(0)`
    // / `VirTemp(1)` for `bump_both(&mut x, &mut y)`) stay distinct.
    // The existing `mut_ref_locals` set uses bare `sanitize(...)`
    // — fine for the single-mut-arg case but collapses multi-arg.
    // We use a separate disambig-aware set here so the linkage map
    // doesn't lose entries to key collisions.
    // Include every local declared with `MutRef T` typ — both
    // `LocalDeclKind::BorrowMut` (Verus's synthetic for `&mut y`
    // setup) and `LocalDeclKind::StmCallArg` (the call-argument
    // temporary that holds the borrow when the call fires). Same
    // typ check as `is_mut_ref_typ` uses elsewhere.
    //
    // We need StmCallArgs too because Verus's SST has:
    //   Assign(tmp_call_arg, Var(tmp_borrow_mut))  -- alias / copy
    //   bump_both(tmp_call_arg, ...)               -- call uses StmCallArg
    //   Assign(user_local, Var(tmp_borrow_mut))    -- forward-forward linkage
    //
    // The alias `tmp_call_arg = tmp_borrow_mut` is what `aliases`
    // captures (both ends in `borrow_mut_only`). The linkage
    // `Assign(user_local, ...)` is what `links` captures. After
    // `resolve_borrow_mut_aliases`, tmp_call_arg resolves to the
    // same user_local that tmp_borrow_mut links to.
    // `LocalDeclKind` filter: include only Verus-internal mut-ref
    // intermediates that participate in the BorrowMut indirection
    // — `BorrowMut` (the synthetic for `&mut y` setup) and
    // `StmCallArg` (the call-argument temporary that holds the
    // borrow at the call site). Fn params with MutRef typ are NOT
    // included: they're the user-level locals we LINK TO; treating
    // them as part of the borrow-mut-chain would misclassify the
    // forward-forward `Assign(y, Var(tmp_borrow_mut))` as an alias.
    // Explicit-by-name destructure on `StmCallArg`'s fields (per
    // DESIGN.md upstream-robustness pattern): any Verus-side field
    // addition becomes a compile error here instead of silently
    // flowing through `..`. `StmCallArg { native }` exists today; if
    // a new field is added upstream, this pattern fires and forces
    // us to decide whether it changes the borrow-mut-elim eligibility.
    let borrow_mut_only: HashSet<String> = check.local_decls.iter()
        .filter(|d| matches!(d.kind,
            LocalDeclKind::BorrowMut
            | LocalDeclKind::StmCallArg { native: _ }
        ))
        .filter(|d| crate::expr_shared::is_mut_ref_typ(&d.typ, false))
        .map(|d| borrow_mut_key(&d.ident))
        .collect();
    let mut borrow_mut_links: HashMap<String, VarIdent> = HashMap::new();
    let mut borrow_mut_aliases: HashMap<String, String> = HashMap::new();
    if !borrow_mut_only.is_empty() {
        collect_borrow_mut_links(
            &rewritten_body,
            &borrow_mut_only,
            &mut borrow_mut_links,
            &mut borrow_mut_aliases,
        );
        resolve_borrow_mut_aliases(&mut borrow_mut_links, &borrow_mut_aliases);
    }
    // `fn_map` lets the call-arg bridge look up callee param types
    // (consumed by `build_req_binders` + `WpCtx::new`). `uN -> nat` casts
    // are kept as Clip{Nat} upstream by Verus's `--lean-backend` lowering,
    // so the body needs no Tactus-side coercion pass.
    let fn_map: FnMap = krate.functions.iter().map(|f| (&f.x.name, &f.x)).collect();

    // `WpCtx::new` validates reqs / ens_exps before rendering them.
    // It also applies the same rewrites to each ens_exp so the
    // `ensures_goal` LExpr already has the synthetic names baked in.
    // Caller's params at body-shadow Lean typ. Mirrors what
    // `binder_ctx_from_params` records: strip one outer ref decoration
    // for `&mut`-style mutation params (their bodies get a `let p :=
    // p.deref;` shadow making p bare); other params stay as-declared.
    // Threaded into WpCtx so `walk_call` can compute the actual Lean
    // typ of each caller arg when building typed value_subst entries.
    let caller_param_typs: HashMap<VarIdent, Typ> = fn_sst.x.pars.iter()
        .map(|p| {
            let typ = if is_mut_ref_typ(&p.x.typ, p.x.is_mut) {
                crate::to_lean_expr::strip_one_ref_decoration(&p.x.typ)
            } else {
                p.x.typ.clone()
            };
            (p.x.name.clone(), typ)
        })
        .collect();

    let ctx = WpCtx::new(krate, check, &mut_param_names, borrow_mut_links, caller_param_typs)?;

    let mut binders = build_param_binders(fn_sst);
    binders.extend(build_borrow_mut_binders(check));
    binders.extend(build_req_binders(fn_sst, check, &mut_param_names, &fn_map));

    // Build the whole WP tree from the (mut-ref-rewritten) body,
    // with the fn's ensures as the natural continuation at the leaves.
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

    // `lean_name_relative`: `fn_name` only feeds `build_theorem_name`
    // (synthetic obligation-theorem names) — a naming key, not a Lean
    // reference. The root-anchor prefix must not appear mid-name.
    let fn_name = crate::to_lean_type::lean_name_relative(&fn_sst.x.name.path);
    let default_closer = match &fn_sst.x.attrs.tactus_tactic {
        Some(tac) => Tactic::Raw(tac.clone()),
        None => Tactic::Named("tactus_auto".to_string()),
    };
    // Seed the tactic prefix with `have`-bindings for each in-scope
    // broadcast lemma (#122). The lemma is emitted as a top-level
    // `axiom` in the preamble; `have _tactus_bc_<i> := <axiom>` brings it
    // into the obligation's local context so the closer (omega /
    // simp_all) can use it — equation-shaped lemmas (`len(push s a)
    // = len s + 1`) become simp rewrites. This is the sound form:
    // it *uses* the trusted axiom rather than adding the lemma as an
    // unproven antecedent (which would be the False-hypothesis
    // anti-pattern). Applies to every theorem the fn emits (fn-scoped
    // broadcast); unused haves are harmless.
    // `@`-form (N1, DESIGN-nonempty-axioms.md): axioms bracketed with
    // `[Nonempty A]` make the bare `have h := f` form fail — instance
    // implicits are maximally inserted, so Lean eagerly creates a
    // `Nonempty ?A` goal that can't synthesize against a metavar
    // ("typeclass instance problem is stuck"). `@f` binds the full ∀
    // without instantiation, and the @-bound hypothesis remains
    // simp_all-usable at concrete instantiations (N0 probe). Uniform:
    // harmless for unbracketed axioms.
    let mut tactic_prefix: Vec<String> = Vec::new();
    if !broadcast_lemmas.is_empty() {
        let haves: String = broadcast_lemmas.iter().enumerate()
            .map(|(i, f)| format!("have _tactus_bc_{} := @{}", i, lean_name(&f.path)))
            .collect::<Vec<_>>()
            .join("\n");
        tactic_prefix.push(haves);
    }
    let mut emitter = ObligationEmitter {
        fn_name,
        base_binders: binders,
        counter: 0,
        out: Vec::new(),
        tactic_prefix,
        default_closer,
        heartbeats: fn_sst.x.attrs.tactus_heartbeats,
    };

    // Initial OblCtx frames per `&mut` param. Two frames per:
    //
    //   let x := x.deref;                    -- body-shadow: makes Var(x)
    //                                           in the rewritten body
    //                                           resolve to inner T. Needed
    //                                           because mutation `*x = e`
    //                                           lowers to Lean let-shadow.
    //   let <x>_at_pre_tactus := x.deref;   -- captures pre-state inner
    //                                           before any body writes
    //                                           shadow x.
    //
    // The binder `(x : Tactus.MutRef T)` survives at param position for
    // trait dispatch; the body's WP sees `x : T`.
    //
    // BorrowMut locals (#107 synthetic `mut_ref` from `bump(&mut y)`
    // lowering) are MutRef-typed; they get the same two frames.
    //
    // β refactor Piece 1 (LANDED): non-mut wrapper params (`&Stack`,
    // `Box<u8>`, `Rc<T>`, `Arc<T>`) get NO body-shadow. The wrapper
    // type stays in scope at Lean level; uses go through use-site
    // `.deref` coercions in `to_lean_sst_expr.rs`'s IsVariant, Field,
    // and CheckDecreaseHeight arms (driven by `count_ref_decorations`).
    // This is what closes cluster A's "Invalid field `deref`" type
    // errors — pre-Piece-1, the body shadow stripped one wrapper, so
    // aliased locals derived from the param had Lean type T but SST
    // typ &T, and count_ref_decorations overcounted by one.
    //
    // The fn's requires stay in theorem-level binders
    // (`build_req_binders` above) and get their own per-req
    // `let x := x.deref` wrapping there.
    let mut initial_obl_ctx = OblCtx::new(emitter.default_closer.clone());
    // B2b (finding #6): witness facts for chooses inline in the fn's
    // OWN requires / ensures — Wp::Done leaves (postcondition theorems,
    // Return-replaced leaves, loop-body ensures conjuncts) inherit them
    // through the root context, mirroring the per-choose skolem axiom
    // Verus's Z3 path gets regardless of position.
    for req in check.reqs.iter() {
        initial_obl_ctx = obl_with_choose_hyps(req, &ctx, &initial_obl_ctx);
    }
    for ens in check.post_condition.ens_exps.iter() {
        initial_obl_ctx = obl_with_choose_hyps(ens, &ctx, &initial_obl_ctx);
    }
    let add_pre_capture = |obl: OblCtx, raw_name: &str, lean_name: &crate::lean_name::LeanName| -> OblCtx {
        let pre_name = crate::lean_name::LeanName::synthetic(varat_pre_name(raw_name));
        let inner = LExpr::field_proj(LExpr::var(lean_name.clone()), "deref");
        obl.with_frame(CtxFrame::Let(pre_name, inner))
    };
    let add_body_shadow = |obl: OblCtx, lean_name: crate::lean_name::LeanName| -> OblCtx {
        let inner = LExpr::field_proj(LExpr::var(lean_name.clone()), "deref");
        obl.with_frame(CtxFrame::Let(lean_name, inner))
    };
    for par in fn_sst.x.pars.iter() {
        let lean_name = crate::lean_name::LeanName::from_var_ident(&par.x.name);
        let raw_name = sanitize(&par.x.name.0);
        let is_mut_ref = is_mut_ref_typ(&par.x.typ, par.x.is_mut);
        if is_mut_ref {
            initial_obl_ctx = add_pre_capture(initial_obl_ctx, &raw_name, &lean_name);
            initial_obl_ctx = add_body_shadow(initial_obl_ctx, lean_name);
        }
    }
    for decl in check.local_decls.iter() {
        if matches!(decl.kind, LocalDeclKind::BorrowMut) {
            let lean_name = crate::lean_name::LeanName::from_var_ident(&decl.ident);
            let raw_name = sanitize(&decl.ident.0);
            initial_obl_ctx = add_pre_capture(initial_obl_ctx, &raw_name, &lean_name);
            initial_obl_ctx = add_body_shadow(initial_obl_ctx, lean_name);
        }
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

// Obligation naming/classification helpers live in
// `crate::obligation_naming`. Re-export the pub entry points used by
// other modules (format_span_loc by generate, kind_to_name by
// sourcemap) and import the rest for this module's walkers.
pub use crate::obligation_naming::{format_span_loc, kind_to_name};
// `sanitize_loc_for_name` is exercised only by the unit tests (internal
// code calls `build_theorem_name`, which wraps it); re-export it, gated
// on test builds, so the tests reach it via `use super::*`.
#[cfg(test)]
pub(crate) use crate::obligation_naming::sanitize_loc_for_name;
use crate::obligation_naming::{build_theorem_name, detect_assert_kind, format_rust_loc};

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
    /// The Tactic that closes goals emitted under this context.
    /// Seeded at the top from the fn-level default (`tactus_auto`
    /// or whatever `#[verifier::tactus_tactic(...)]` set), then
    /// overridden by `new_scope()` for AssertQuery modes that
    /// switch the discharger (e.g., `nlinarith` for `by(nonlinear_arith)`).
    closer: Tactic,
    /// Preamble fragments required for `closer` to elaborate (e.g.,
    /// `Mathlib.Tactic.Linarith` for `nlinarith`). Empty when the
    /// closer is part of the bundled prelude (`tactus_auto`).
    /// Every theorem emitted under this context attaches these to
    /// its `requires_preamble`; `krate_preamble` aggregates +
    /// dedups so the file picks them up once.
    closer_preamble: Vec<PreambleFragment>,
    /// Returned-mut-ref prophecies in scope. Key: a caller-local
    /// (sanitized `VarIdent` name) that a prior call returned as a
    /// `&mut T` (e.g. `let e = vec_index_mut(&mut v, i)` binds `e`).
    /// Value: the prophecy variable `P` for `*final(e)` — minted +
    /// ∀-bound at the introducing call, used by that call's inlined
    /// ensures (`final(vec)@ == update(old@, i, P)`), and *resolved*
    /// when `e` is later passed as a `&mut` arg (`bump(e)` constrains
    /// `P == *old(e) + 1` instead of minting a fresh post-state).
    ///
    /// This is the "returned-mut-ref prophecy composition" map: the
    /// downstream call reuses the SAME variable the introducing call's
    /// ensures referenced, so the chain `final(vec)@[i] == P == old+1`
    /// closes. Flows with the walk (OblCtx is the accumulating context),
    /// so its scope matches exactly where the returned ref is live.
    /// Plain `HashMap` (not `im`): `clone()` is a full copy, but the map is
    /// tiny (typically 0–1 entries), so the per-`with_frame` clone is cheap.
    prophecies: HashMap<String, crate::lean_name::LeanName>,
    /// Let-bound locals' believed Lean typs (P2,
    /// DESIGN-typed-renderer.md): recorded by `walk_let` as it pushes
    /// `Let` frames, consumed by `exp_to_typed`'s Var arm via
    /// `RenderCtx::with_let_binder_typs`. Entry = (typ the binding was
    /// coerced into, D3-trusted bit). `im::HashMap` — O(1) clone in
    /// the walker's extend-per-frame pattern; inner shadowing
    /// overrides correctly because the walk descends scope-wise.
    let_binder_typs: im::HashMap<crate::lean_name::LeanName, (Typ, bool)>,
}

impl OblCtx {
    /// Top-level OblCtx for an exec fn. Seeds the closer from the
    /// fn's default (carrying `#[verifier::tactus_tactic(...)]` if
    /// the user set one); the preamble is empty until a scope
    /// changes it.
    fn new(closer: Tactic) -> Self {
        Self {
            frames: im::Vector::new(),
            closer,
            closer_preamble: Vec::new(),
            prophecies: HashMap::new(),
            let_binder_typs: im::HashMap::new(),
        }
    }

    /// Register a returned-mut-ref prophecy: `local`'s `*final` is `p`.
    /// Mutates in place (caller owns a fresh OblCtx being built up).
    /// Keyed disambiguator-aware via `borrow_mut_key` (NOT `sanitize`):
    /// two returned refs can share a base name (`tmp%` with `VirTemp(1)`
    /// / `VirTemp(2)`) and must stay distinct — same reason
    /// `borrow_mut_links` is disambig-keyed.
    fn register_prophecy(&mut self, local: &VarIdent, p: crate::lean_name::LeanName) {
        self.prophecies.insert(borrow_mut_key(local), p);
    }

    /// Look up a registered prophecy for a caller-local, if any.
    fn prophecy_for(&self, local: &VarIdent) -> Option<&crate::lean_name::LeanName> {
        self.prophecies.get(&borrow_mut_key(local))
    }

    /// Invalidate a prophecy once its returned ref has been RESOLVED (passed
    /// to a `&mut`-arg call). Defense-in-depth (review 2026-05-31): a single
    /// returned `&mut` must be resolved at most once — resolving it twice
    /// would reuse the same `P` and produce a `P == P+1` False hypothesis
    /// (unsound). The frontend already blocks the only triggering surface
    /// syntax (`let e = &mut v[i]; bump(e); bump(e)` — the named binding is
    /// rejected as `MutRefCurrent` in an exec body; pinned by
    /// `adversarial_probe_double_bump_named`). Clearing on resolution makes
    /// the gate hold by its OWN logic, not by the luck of that upstream
    /// rejection: a second resolution then mints a fresh existential instead.
    fn clear_prophecy(&mut self, local: &VarIdent) {
        self.prophecies.remove(&borrow_mut_key(local));
    }

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

    /// Record a let-bound local's believed Lean typ (see
    /// `let_binder_typs`). Returns a fresh OblCtx (O(1) via `im`).
    fn with_let_binder(
        &self,
        name: crate::lean_name::LeanName,
        typ: Typ,
        trusted: bool,
    ) -> Self {
        let mut new = self.clone();
        new.let_binder_typs.insert(name, (typ, trusted));
        new
    }

    /// Enter a new verification scope: like Verus's `AssertQuery`,
    /// the new ctx starts fresh (enclosing-scope Hyps shed — they
    /// aren't part of the query's input), with `closer` discharging
    /// and `preamble` attached to every theorem emitted under it.
    ///
    /// Let / Binder frames are kept because they bind names the
    /// scope's body may reference; only Hyp frames are dropped —
    /// matching Verus's NonLinear/BitVector semantics that the
    /// query only sees its own declared requires + typ invariants.
    ///
    /// Exhaustive match (not `!matches!(_, Hyp(_))`) so a new
    /// `CtxFrame` variant must consciously decide "does this
    /// survive a scope boundary?" rather than silently being kept.
    fn new_scope(&self, closer: Tactic, preamble: Vec<PreambleFragment>) -> Self {
        let frames: im::Vector<CtxFrame> = self
            .frames
            .iter()
            .filter(|f| match f {
                CtxFrame::Let(..) | CtxFrame::Binder(..) => true,
                CtxFrame::Hyp(..) => false,
            })
            .cloned()
            .collect();
        // Prophecies survive a scope boundary like Let/Binder frames:
        // they name a bound variable the scope's body may reference.
        // The let-binder typ env survives for the same reason: it
        // describes Let frames, which are kept.
        Self {
            frames,
            closer,
            closer_preamble: preamble,
            prophecies: self.prophecies.clone(),
            let_binder_typs: self.let_binder_typs.clone(),
        }
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

    /// Build an explicit-named `intro` list for any frames that did
    /// NOT extract to theorem level. Each Let / Binder contributes
    /// its source name; each Hyp contributes `_` (anonymous, gets a
    /// Lean-side fresh name). Used by `emit_with_closer` to inject
    /// `intro <names>;` before user-supplied tactic bodies so that
    /// frames blocked from extraction (typically Let frames for
    /// outer non-modified vars) still come into the local context
    /// under their source names rather than as inaccessible `i✝`
    /// daggers. Empty result means no injection is needed.
    fn intro_names_for_user_tactic(&self) -> Vec<String> {
        self.frames.iter().map(|f| match f {
            CtxFrame::Let(name, _) => name.as_str().to_string(),
            CtxFrame::Binder(b) => b.name.as_ref()
                .map(|n| n.as_str().to_string())
                .unwrap_or_else(|| "_".to_string()),
            CtxFrame::Hyp(_) => "_".to_string(),
        }).collect()
    }

    /// Split: pull leading `Binder` frames out as theorem-level binders,
    /// leaving the rest of the frames to wrap into the goal via the
    /// returned `OblCtx`. Used to make loop-modified-var names directly
    /// accessible at the tactic body's entry point (theorem-level
    /// binders are in the local context immediately; `∀`-in-goal
    /// binders require `intros` and Lean's auto-naming uses
    /// inaccessible `i✝` names that user tactics can't reference).
    /// See `BUG-loop-local-names-alpha-renamed.md`.
    ///
    /// Only LEADING Binders are extracted — Hyp frames immediately
    /// after the last extracted Binder also extract (they're the
    /// bounds + invariants + cond that go with the modified-vars).
    /// Stopping at the first Let preserves the source ordering of
    /// `_tactus_d_old := D` lets and any other let-bound context.
    /// Hyps get synthetic names so they're addressable.
    fn split_leading_binders(&self) -> (Vec<LBinder>, OblCtx) {
        let mut binders: Vec<LBinder> = Vec::new();
        let mut remaining = self.clone();
        let mut hyp_counter: usize = 0;
        let mut saw_binder = false;
        loop {
            match remaining.frames.front() {
                Some(CtxFrame::Binder(b)) => {
                    binders.push(b.clone());
                    remaining.frames.pop_front();
                    saw_binder = true;
                }
                Some(CtxFrame::Hyp(p)) if saw_binder => {
                    binders.push(LBinder::explicit(crate::lean_name::LeanName::synthetic(format!("_h_ctx_{}", hyp_counter)), p.clone()));
                    hyp_counter += 1;
                    remaining.frames.pop_front();
                }
                _ => break,
            }
        }
        (binders, remaining)
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
    /// Per-fn `maxHeartbeats` override from
    /// `#[verifier::heartbeats(N)]`. When `Some(N)`, every theorem
    /// emitted from this fn gets the heartbeats value attached
    /// (rendered as `set_option maxHeartbeats N in` by the pp).
    heartbeats: Option<u32>,
}

impl ObligationEmitter {
    fn next_id(&mut self) -> usize {
        self.counter += 1;
        self.counter
    }

    /// Emit a theorem with explicit closer override (used by
    /// `Wp::AssertByTactus` when the user wrote
    /// `assert(P) by { tac }` — `tac` is the closer, not the obl
    /// default). Preamble still flows from obl so an enclosing
    /// scope's imports remain in effect. Also extracts leading
    /// Binder / Hyp frames from `obl` to theorem-level binders
    /// (via `split_leading_binders`) AND injects explicit-named
    /// `intro <names>;` for any frames that didn't extract — so
    /// user tactics can name loop locals directly without daggers.
    /// See `BUG-loop-local-names-alpha-renamed.md` and
    /// `BUG-multi-var-loop-alpha-rename.md`.
    fn emit_with_closer(
        &mut self, name: String, leaf: LExpr, closer: Tactic, obl: &OblCtx,
    ) {
        let (extras, remaining) = obl.split_leading_binders();
        let goal = remaining.wrap(leaf);
        // For user-tactic emission (assert-by), inject explicit
        // `intro <names>;` for any frames that COULDN'T extract to
        // theorem level (typically: Let frames for non-modified outer
        // vars, plus any Binders/Hyps that came after them and got
        // blocked). Without injection, those frames stay as `let`/`→`
        // in the goal, and the user's tactic must `intros` itself —
        // which produces inaccessible `i✝` dagger names rather than
        // source names. Injection uses the names we DO have
        // (Let.name, Binder.name) and `_` for anonymous Hyps. See
        // `BUG-multi-var-loop-alpha-rename.md`.
        let intro_names = remaining.intro_names_for_user_tactic();
        // The rule: Tactus injects `intro <names>;` ONLY to give a `Binder`
        // frame a source name. Everything else is the user tactic's own job.
        //
        // A `Binder` blocked behind a `Let` couldn't extract to theorem level,
        // and without an explicit intro it gets an inaccessible `i✝` dagger
        // name the user's tactic can't reference (BUG-loop-local-names,
        // BUG-multi-var-loop-alpha-rename) — so a `Binder` in `remaining` is the
        // one case Tactus MUST intro.
        //
        // `Let` and `Hyp` frames are NOT a reason to intro:
        // * `Let` frames are synthetic temps the user never names — and
        //   intro-ing a *tuple*-typed let makes it an opaque `ldecl` omega
        //   can't project through (`let tmp := ret; let b := tmp.2; b ≤ K` →
        //   omega can't reach `ret.2`). Left goal-position, omega's own zeta
        //   reduces it and `by { omega }` runs on the real goal.
        // * `Hyp` frames are anonymous `→` antecedents (e.g. a prior assert's
        //   result); omega/simp_all intro them themselves.
        //
        // Consequence — the user tactic owns its own intro (matches DESIGN §
        // "tactic-text prepending" + the `intros; nlinarith` idiom): intro-aware
        // tactics (omega, simp_all) need nothing; non-intro-aware ones
        // (nlinarith / linarith / ring — Mathlib tactics that act on the
        // current goal, not goal-position binders) write `by { intros; tac }`.
        // This is the deliberate trade chosen over a type-aware "intro all but
        // tuple lets" gate (general rule > special case; the user's intro is
        // visible, not a hidden Tactus step). See
        // BUG-tuple-destructure-alias-temps-block-omega.md.
        let needs_intro = remaining.frames.iter()
            .any(|f| matches!(f, CtxFrame::Binder(..)));
        let final_closer = if !needs_intro {
            closer
        } else {
            // No indent on the continuation: `compose_tactic` re-indents
            // every line of a Raw closer uniformly inside its paren
            // block. A DEEPER-indented continuation here rendered as
            // `(intro …;\n  <text>)` with the text SHALLOWER than the
            // intro — Lean's column-sensitive tactic parser reads that
            // as a dedent and errors "expected ')'"
            // (found via find_cancellation_exec's in-loop assert-by).
            let intros = format!("intro {};", intro_names.join(" "));
            let body = match closer {
                Tactic::Named(n) => format!("{}\n{}", intros, n),
                Tactic::Raw(s) => format!("{}\n{}", intros, s),
            };
            Tactic::Raw(body)
        };
        self.emit_with_extras(
            name, goal, final_closer, obl.closer_preamble.clone(), extras,
        );
    }

    /// Emit a theorem using the closer/preamble from `obl`, with
    /// leading Binder + Hyp frames extracted from `obl` to theorem-
    /// level binders. Makes loop-modified-var names directly
    /// accessible at the tactic body's entry point (no `intros`
    /// needed). Used by all per-obligation emit sites — assert
    /// theorems, loop invariants, init obligations, call
    /// preconditions. The closer is `obl.closer` (typically
    /// `tactus_auto`, or whatever `#[verifier::tactus_tactic("...")]`
    /// set; overridden inside `AssertQuery` scopes via
    /// `obl.new_scope(...)`). See `BUG-loop-local-names-alpha-renamed.md`.
    fn emit_split(&mut self, name: String, leaf: LExpr, obl: &OblCtx) {
        let (extras, remaining) = obl.split_leading_binders();
        let goal = remaining.wrap(leaf);
        self.emit_with_extras(
            name, goal, obl.closer.clone(), obl.closer_preamble.clone(), extras,
        );
    }

    /// Emit a theorem with explicit closer + preamble + extra binders.
    /// Lower-level entry point; callers usually want `emit_split` or
    /// `emit_with_closer` instead. The `requires_preamble` field carries
    /// per-theorem preamble fragments (imports / instance blocks) that
    /// `generate.rs::krate_preamble` aggregates across all theorems and
    /// emits once at file top, deduped — used by `Wp::AssertBitVector`
    /// (#130) for BitVec instance Int wrappers.
    fn emit_with_extras(
        &mut self,
        name: String,
        goal: LExpr,
        closer: Tactic,
        requires_preamble: Vec<PreambleFragment>,
        extra_binders: Vec<LBinder>,
    ) {
        let tactic = self.compose_tactic(closer);
        let mut binders = self.base_binders.clone();
        binders.extend(extra_binders);
        self.out.push(Theorem {
            name,
            binders,
            goal,
            tactic,
            requires_preamble,
            heartbeats: self.heartbeats,
            // Exec-fn obligation theorems are flat (recursion lives in the
            // `CheckDecreaseHeight` obligation, not the theorem), so
            // `termination_by` is always empty and `decreasing_by` is `None`.
            termination_by: Vec::new(),
            decreasing_by: None,
        });
    }

    fn compose_tactic(&self, closer: Tactic) -> Tactic {
        if self.tactic_prefix.is_empty() {
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
                // Block-render raw closers — `(\n  <lines at uniform
                // col>\n)` — instead of inlining `({})`. Inlined
                // multi-line raw text puts its first line at the
                // paren's column and later lines wherever the user
                // wrote them; any line shallower than the first is a
                // dedent to Lean's tactic parser ("expected ')'").
                // The uniform re-indent makes every line, including
                // an `intro …;` prefix line, column-consistent.
                Tactic::Raw(s) => {
                    body.push_str("(\n");
                    for line in s.lines() {
                        if line.trim().is_empty() {
                            body.push('\n');
                        } else {
                            body.push_str("  ");
                            body.push_str(line.trim_end());
                            body.push('\n');
                        }
                    }
                    body.push(')');
                }
            }
            Tactic::Raw(body)
        }
    }

    fn emit_with_preamble(
        &mut self,
        name: String,
        goal: LExpr,
        closer: Tactic,
        requires_preamble: Vec<PreambleFragment>,
    ) {
        self.emit_with_extras(name, goal, closer, requires_preamble, Vec::new());
    }
}

/// Walk a `Wp` tree, emitting one Lean theorem per obligation. See
/// the doc on [`exec_fn_theorems_to_ast`] for the staging plan and
/// the per-Wp-variant behaviour.
/// Push the witness-fact hypothesis for every binder-free `choose` in
/// `exp` onto a copy of `obl` (B2b — see
/// `to_lean_sst_expr::collect_choose_witness_hyps`). Identity when the exp
/// has no such choose — the overwhelmingly common case.
fn obl_with_choose_hyps(exp: &Exp, ctx: &WpCtx, obl: &OblCtx) -> OblCtx {
    // Best-effort: the hypothesis is optional proof HELP — a cond that
    // fails to re-render (e.g. root-level ensures shapes that aren't
    // Validated-witnessed) must not panic the emission; the goal just
    // proceeds without the witness fact, as it did pre-B2b.
    let hyps = crate::to_lean_sst_expr::collect_choose_witness_hyps(
        exp,
        &ctx.render_ctx().with_let_binder_typs(&obl.let_binder_typs),
    )
    .unwrap_or_default();
    let mut out = obl.clone();
    for h in hyps {
        out = out.with_frame(CtxFrame::Hyp(h));
    }
    out
}

fn walk_obligations<'a>(
    wp: &Wp<'a>,
    ctx: &'a WpCtx<'a>,
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
            // B2b: witness facts for chooses inline in the goal.
            let obl = &obl_with_choose_hyps(asserted_exp, ctx, obl);
            let kind = detect_assert_kind(asserted_exp);
            let loc = format_rust_loc(&asserted_exp.span);
            let cond_ast = lower_validated_with_ctx(
                asserted,
                &ctx.render_ctx().with_let_binder_typs(&obl.let_binder_typs),
            );
            let goal = LExpr::span_mark(
                loc.clone(),
                Some(asserted_exp.span.clone()),
                kind,
                cond_ast.clone(),
            );
            let id = e.next_id();
            let name = build_theorem_name(
                kind_to_name(kind), &e.fn_name, &loc, id,
            );
            e.emit_split(name, goal, obl);
            // Reuse cond_ast for the body's hypothesis frame —
            // rendering is deterministic, so re-running it on the
            // same Exp would only repeat work.
            let new_obl = obl.with_frame(CtxFrame::Hyp(cond_ast));
            walk_obligations(body, ctx, &new_obl, e);
        }
        Wp::Assume(p, body) => {
            // No theorem; the assumption just enters the context.
            // B2b: witness facts for chooses inline in the assumption.
            let obl = &obl_with_choose_hyps(p.raw(), ctx, obl);
            let new_obl = obl.with_frame(CtxFrame::Hyp(lower_validated_with_ctx(
                p,
                &ctx.render_ctx().with_let_binder_typs(&obl.let_binder_typs),
            )));
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
        Wp::AssertBitVector { req_conj, ens_conj, rust_loc, rust_span, body } => {
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
                rust_span.clone(),
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
        Wp::AssertQuery { primary, preamble, surface_label, body, after } => {
            // Compose the scope's closer as `first | (intros;
            // primary) | <outer> | fail "scope message"` —
            //
            // * `(intros; primary)` — the mode-specific tactic
            //   (e.g., `nlinarith`) after intro-ing the
            //   theorem-level binders + Hyps that the OblCtx
            //   wraps around the goal. Most refutation-based
            //   tactics like `nlinarith` don't intro on their
            //   own.
            // * `<outer>` — the enclosing scope's closer. Used
            //   for trivial `True` theorems the recursive walk
            //   still emits (e.g., from `Wp::Done` leaves at the
            //   end of the body block) — refutation-based
            //   tactics can't close `True`. Reading from
            //   `obl.closer` preserves any fn-level override
            //   (`#[verifier::tactus_tactic("...")]`) and
            //   composes correctly for nested scopes.
            // * Trailing `fail` — overrides Lean's default
            //   "last-failure" reporting (which would otherwise
            //   show `<outer>`'s message, e.g., `tactus_auto:
            //   auto-tactic failed`) with a scope-specific
            //   message pointing at the surface syntax. Users
            //   debugging an unprovable goal know to look for
            //   a `proof { }` block, not a misdirected
            //   automation failure.
            let outer = tactic_as_str(&obl.closer);
            let primary_str = tactic_as_str(primary);
            let composed = Tactic::Raw(format!(
                "first | (intros; {}) | ({}) | \
                 fail \"{} scope: could not close — \
                 add an explicit `proof {{ … }}` block with a stronger tactic\"",
                primary_str, outer, surface_label,
            ));
            let inner_obl = obl.new_scope(composed, preamble.clone());
            walk_obligations(body, ctx, &inner_obl, e);
            walk_obligations(after, ctx, obl, e);
        }
        Wp::Let(name, val, dest_typ, body) => {
            // B2b: a choose in the RHS carries its witness fact — push it
            // before the let frame so every downstream obligation sees it
            // (mirrors AIR's per-choose skolem axiom on the Z3 path).
            let obl = obl_with_choose_hyps(val.raw(), ctx, obl);
            walk_let(name, val.raw(), dest_typ, body, ctx, &obl, e);
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
        Wp::Scope { scope_vars, body, after } => {
            // Body obligations verify under the CURRENT context —
            // outer hypotheses and lets stay visible inside the proof
            // body — plus ∀-binders for this scope's assert-forall
            // skolems (minus names an enclosing scope already bound;
            // see the variant docstring). Effects are discarded:
            // `after` walks under the SAME original obl (the proven
            // fact re-enters via the `Assume` statement Verus emits
            // after the DeadEnd, which lives in `after`'s tree).
            let already_bound: std::collections::HashSet<&crate::lean_name::LeanName> =
                obl.frames.iter().filter_map(|f| match f {
                    CtxFrame::Binder(b) => b.name.as_ref(),
                    _ => None,
                }).collect();
            let fresh: Vec<(&VarIdent, &Typ)> = scope_vars.iter()
                .filter(|(v, _)| {
                    !already_bound.contains(
                        &crate::lean_name::LeanName::from_var_ident(v))
                })
                .cloned()
                .collect();
            let mut scope_obl = obl.clone();
            push_mod_var_frames(&mut scope_obl, &fresh);
            walk_obligations(body, ctx, &scope_obl, e);
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
            // B2b: witness facts for chooses inline in the branch cond.
            let obl = &obl_with_choose_hyps(cond.raw(), ctx, obl);
            let cond_marked = LExpr::span_mark(
                format_rust_loc(&cond.raw().span),
                Some(cond.raw().span.clone()),
                AssertKind::Hypothesis(HypothesisKind::BranchCondition),
                lower_validated_with_ctx(
                    cond,
                    &ctx.render_ctx().with_let_binder_typs(&obl.let_binder_typs),
                ),
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
            // B2b (2026-07-09 review, finding #6): witness facts for
            // chooses inline in call ARGUMENTS — the precondition
            // theorem and everything after the call see them.
            let mut obl_c = obl.clone();
            for a in args.iter() {
                obl_c = obl_with_choose_hyps(a.raw(), ctx, &obl_c);
            }
            walk_call(
                callee, spec_callee, args, typ_args, *dest, call_span, mut_args, after, ctx, &obl_c, e,
            );
        }
        Wp::Loop { cond, invs, validated_invs, inv_kinds, decrease, modified_vars, body, after } => {
            // B2b (finding #6): witness facts for chooses inline in the
            // loop invariants / condition — entry, preservation, and
            // after-loop obligations all see them.
            let mut obl_c = obl.clone();
            for iv in validated_invs.iter() {
                obl_c = obl_with_choose_hyps(iv.raw(), ctx, &obl_c);
            }
            if let Some(c) = cond {
                obl_c = obl_with_choose_hyps(c.raw(), ctx, &obl_c);
            }
            walk_loop(
                *cond, invs, validated_invs, inv_kinds, decrease, modified_vars, body, after, ctx, &obl_c, e,
            );
        }
        Wp::AssertByTactus { cond, tactic_text, body } => {
            // B2b (finding #6): a choose inline in a raw-tactic assert's
            // cond still gets its witness fact — the user tactic can
            // then use it instead of hand-applying epsilon_spec.
            let obl_c = match cond {
                Some(c) => obl_with_choose_hyps(c.raw(), ctx, obl),
                None => obl.clone(),
            };
            walk_assert_by_tactus(*cond, tactic_text, body, ctx, &obl_c, e);
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
    ctx: &'a WpCtx<'a>,
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
            let cond_ast = lower_validated_with_ctx(
                &c,
                &ctx.render_ctx().with_let_binder_typs(&obl.let_binder_typs),
            );
            let goal = LExpr::span_mark(
                loc.clone(),
                Some(c.raw().span.clone()),
                AssertKind::Obligation(ObligationKind::Plain),
                cond_ast.clone(),
            );
            let id = e.next_id();
            let name = build_theorem_name(
                kind_to_name(AssertKind::Obligation(ObligationKind::Plain)), &e.fn_name, &loc, id,
            );
            if user_tactic_present {
                e.emit_with_closer(
                    name, goal, Tactic::Raw(tactic_text.to_string()), obl,
                );
            } else {
                e.emit_split(name, goal, obl);
            }
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
    e.emit_split(name, leaf.clone(), obl);
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
    ctx: &'a WpCtx<'a>,
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
    // Render ctx for invariants/cond: the fn's params PLUS the loop-
    // modified locals, at their Lean binder typs. A modified local
    // (`out : Vec`, built in-loop) is bound BARE at binder frames, but
    // a spec `out@` auto-refs it in VIR (claims `&Vec`) — so the
    // class-method receiver coercion must know `out`'s ACTUAL bare typ
    // to insert the `Tactus.Ref.mk` for `View::view`. Without the
    // modified vars in `binder_typs`, the coercion runs off the lying
    // `a.typ` claim and emits ill-typed Lean (bare Vec at View::view's
    // Ref slot — copy_word's invariants,
    // BUG-call-arg-temp-claimed-typ.md family). Params keep whatever
    // `caller_param_typs` recorded (ref-decorated for `&`-only).
    let mut inv_binder_typs: HashMap<VarIdent, Typ> = ctx.caller_param_typs.clone();
    for (ident, typ) in modified_vars {
        inv_binder_typs.entry((*ident).clone()).or_insert_with(|| (*typ).clone());
    }
    let inv_rctx = crate::expr_shared::RenderCtx::with_fn_map(&ctx.fn_map)
        .with_binder_typs(&inv_binder_typs);
    let inv_marked = |(i, v): (&LoopInv, &Validated<'a>)| LExpr::span_mark(
        format_rust_loc(&i.inv.span),
        Some(i.inv.span.clone()),
        AssertKind::Obligation(ObligationKind::LoopInvariant),
        lower_validated_with_ctx(v, &inv_rctx),
    );
    let cond_marked = |c: &Validated<'a>| LExpr::span_mark(
        format_rust_loc(&c.raw().span),
        Some(c.raw().span.clone()),
        AssertKind::Hypothesis(HypothesisKind::LoopCondition),
        lower_validated_with_ctx(c, &inv_rctx),
    );
    // Each invariant clause becomes its OWN hypothesis frame, NOT one
    // glued `∧` conjunction. `split_leading_binders` then names them
    // `_h_ctx_N` individually, so a user tactic's `intros; nlinarith`
    // (and `linarith` / `assumption` / `exact`) sees each fact
    // directly. Those tactics do NOT decompose a conjunction
    // hypothesis, so gluing the clauses into one `(P1 ∧ P2 ∧ …)` frame
    // buried facts (e.g. an overflow bound) that were "right there".
    // (`omega`/`simp_all` in the default closer DO split conjunctions,
    // so this mainly unblocks user-written closers and asserts.)
    // See BUG-ch5-pow-iter-lowering-frictions.md (Friction 1).
    let entry_invs_marked: Vec<LExpr> =
        invs.iter().zip(validated_invs.iter()).zip(inv_kinds.iter())
            .filter(|(_, k)| k.at_entry())
            .map(|((i, v), _)| inv_marked((i, v))).collect();
    let exit_invs_marked: Vec<LExpr> =
        invs.iter().zip(validated_invs.iter()).zip(inv_kinds.iter())
            .filter(|(_, k)| k.at_exit())
            .map(|((i, v), _)| inv_marked((i, v))).collect();

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
        e.emit_split(name, inv_marked((inv, v)), obl);
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
    for inv in &entry_invs_marked {
        maintain_obl.frames.push_back(CtxFrame::Hyp(inv.clone()));
    }
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
    for inv in &exit_invs_marked {
        use_obl.frames.push_back(CtxFrame::Hyp(inv.clone()));
    }
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
    // Before pushing ∀-binders for modified vars, drop any prior Let
    // frames that bind the same names. The Let frames came from the
    // source (e.g., `let mut i: u64 = 0;` before the loop), and their
    // initial values are irrelevant to the maintain/use obligations —
    // those reason about the current iteration's value of `i`, which
    // the ∀-binder provides. Without this filter, the emitted theorem
    // looks like `let i := 0; ∀ (i : Int), ... → goal` — Lean lets
    // the inner `i` shadow inside the goal but tactic-mode `intro` /
    // `intros` then can't reach the source name `i`, because there
    // are TWO `i`s and Lean auto-disambiguates the introduced one as
    // `i✝¹`. Users can't type the dagger character, so naming the
    // loop variable in tactic bodies becomes impossible.
    // Per `BUG-loop-local-names-alpha-renamed.md`.
    let mod_names: std::collections::HashSet<crate::lean_name::LeanName> =
        modified_vars.iter()
            .map(|(ident, _)| crate::lean_name::LeanName::from_var_ident(ident))
            .collect();
    // Also drop prior `Hyp` frames that MENTION a modified var. Such a hyp is
    // a fact about the PRE-LOOP state — e.g. a pre-loop `assert(result ==
    // fact(i))`, or a `let (a,b) = …; assert(..)` result — referencing a
    // variable the loop changes. Per Hoare logic it isn't an assumption of the
    // maintain/use obligation (only the invariant + cond are), and the var is
    // re-quantified by the ∀-binder pushed below — so keeping the hyp dangles
    // the reference (an UNBOUND `i` in the emitted theorem). The debug sanity
    // check rejects that ("unresolved i"); release silently rebinds it via
    // Lean's autoImplicit, masking the bug — the divergence that surfaced this.
    // Dropping is sound: a maintain proof can't legitimately depend on a
    // pre-loop fact about a variable the loop mutates. See
    // BUG-preloop-assert-modvar-unbound.md.
    let mod_name_strs: std::collections::HashSet<&str> =
        mod_names.iter().map(|n| n.as_str()).collect();
    obl.frames.retain(|frame| match frame {
        CtxFrame::Let(name, _) => !mod_names.contains(name),
        CtxFrame::Hyp(p) => !mod_name_strs.iter()
            .any(|n| crate::lean_ast::mentions_free_var(p, n)),
        CtxFrame::Binder(_) => true,
    });
    for (ident, typ) in modified_vars {
        // Modified-var binders carry the user's local-var VarIdent
        // verbatim. `from_var_ident` is the canonical entry point; it
        // includes the disambiguator id when needed (synthetic temps),
        // and falls through to plain `sanitize` for user-named locals.
        let name = crate::lean_name::LeanName::from_var_ident(ident);
        obl.frames.push_back(CtxFrame::Binder(LBinder::explicit(name.clone(), typ_to_expr(typ))));
        if let Some(pred) = type_bound_predicate(&LExpr::var(name.clone()), typ) {
            obl.frames.push_back(CtxFrame::Hyp(pred));
        }
        // Ledger the binder's typ (the ∀-binder IS the storage truth):
        // without an entry, typed-spine Var lookups inside the loop's
        // invariant/body render at per-use CLAIMS — a borrow of a
        // modified local claims Ref while the binder holds the bare
        // value, and the identity-coerce emits ill-typed Lean (bare
        // Vec at View.view's Ref slot — copy_word's invariants,
        // BUG-call-arg-temp-claimed-typ.md family).
        *obl = obl.with_let_binder(name, (*typ).clone(), true);
    }
}

// The unified mut-ref rewrite pass lives in `crate::mut_ref_normalize`.
// Import the entry points so this module's bare-name call sites
// (callee-spec inlining, WpCtx::new, push_post_call_frames) keep working.
use crate::mut_ref_normalize::{
    rewrite_mut_ref_in_exp, rewrite_mut_ref_in_stm, rewrite_return_final_ref,
    rewrite_varat_for_mut_params, RewritePhase,
};

// The BorrowMut indirection-elimination pass lives in
// `crate::mut_ref_normalize` (sibling to the mut-ref rewrite).
// Re-export its entry points so this module's call sites + the
// unit tests (`use super::*`) keep working.
pub(crate) use crate::mut_ref_normalize::{
    borrow_mut_key, collect_borrow_mut_links, is_borrow_mut_linkage_assign,
    resolve_borrow_mut_aliases,
};

// Cross-crate broadcast-lemma collection lives in
// `crate::broadcast_collect`; re-export the entry point so
// `crate::sst_to_lean::collect_broadcast_lemma_funs` (used by `generate`)
// stays stable.
pub use crate::broadcast_collect::collect_broadcast_lemma_funs;

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
    ctx: &'a WpCtx<'a>,
    obl: &OblCtx,
    e: &mut ObligationEmitter,
) {
    // `spec_callee` was resolved at build time (see `resolve_callee`)
    // and threaded through `Wp::Call`. No re-derivation, no `expect()`
    // — the type system guarantees it's present.

    // Binder-aware render ctx for the call args (typed spine): params
    // from `caller_param_typs`, WP temps from the walk's
    // `let_binder_typs` ledger — so substitution entries record the
    // typ the rendered LExpr ACTUALLY has, not the arg exp's claim.
    let arg_rctx = ctx.render_ctx().with_let_binder_typs(&obl.let_binder_typs);
    let subst = build_call_substitutions(
        callee, spec_callee, typ_args, args, mut_args, &ctx.caller_param_typs, &arg_rctx, obl, e,
    );

    // Canonical "what gets inlined at this call site." Single source
    // of truth shared with `dep_order::collect_references`; both
    // sites consult `call_inlining::collect_inlined_at_call` so
    // emission and ref-collection can't drift.
    let inlined = crate::call_inlining::collect_inlined_at_call(callee, spec_callee);

    // Two RenderCtxs for the two inlining paths, each with its own
    // typed value_subst:
    //
    // * Requires (`render_ctx_req`): every param resolves to the
    //   caller's pre-call arg via `req_value_subst`. Post-state
    //   existentials aren't in scope yet, so requires never needs
    //   them. Both `value_subst` and `value_subst_pre` are populated
    //   with the SAME map — requires only sees pre-state, and a
    //   surviving `ExprX::Old(_)` inside requires triggers the
    //   pre-state swap which would otherwise drop the substitution
    //   (rendering `*old(h)` as bare `h_at_pre_tactus`). Pinned by
    //   `test_old_view_pre_post_substitution_probe`'s requires clause
    //   (`old(z).view() < 100` in new-mut-ref mode reaches the
    //   renderer with `ExprX::Old(...)` after Verus's normalization
    //   — without populating both maps, the swap drops `z` and the
    //   sanity check fails with "unresolved `h`").
    //
    // * Ensures (`render_ctx_ens`): mut params via `pname` resolve to
    //   the post-state existential; non-mut params via `pname` resolve
    //   to the caller arg; `<p>_at_pre_tactus` (the rewritten `*old(p)`
    //   form) resolves to the caller pre-call arg. The separate
    //   `ens_value_subst_pre` map handles any surviving `Old(_)`
    //   subtrees — typically eliminated by the ensures preprocessing
    //   rewrite, so this path is rarely exercised.
    let render_ctx_req = crate::expr_shared::RenderCtx::with_fn_map_and_value_subst_pair(
        &ctx.fn_map,
        &subst.req_value_subst,
        &subst.req_value_subst,
    );
    let render_ctx_ens = crate::expr_shared::RenderCtx::with_fn_map_and_value_subst_pair(
        &ctx.fn_map,
        &subst.ens_value_subst,
        &subst.ens_value_subst_pre,
    );

    if !inlined.requires.is_empty() {
        emit_call_precondition_theorem(&inlined.requires, &subst, call_span, obl, &render_ctx_req, e);
    }

    let new_obl = push_post_call_frames(
        callee, &inlined.ensures, &subst, dest, typ_args, obl, &render_ctx_ens, e,
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
    ///
    /// **Returned-mut-ref prophecy composition:** when this `&mut`
    /// arg is a local that an EARLIER call returned as a `&mut T`
    /// (recorded in `OblCtx::prophecies`), `fresh` is that registered
    /// prophecy var `P` — NOT a new gensym. The earlier call's ensures
    /// already referenced `P` (`final(vec)@ == update(old@, i, P)`), so
    /// reusing it here lets this call's `*final(arg) == *old(arg)+1`
    /// constrain the SAME `P` the earlier call's update used; the chain
    /// closes. Phase 1 detects the reuse — `fresh` equals the prophecy
    /// registered for this arg's local — and skips minting a binder (P is
    /// already ∀-bound at the introducing call's frame). Derived at the
    /// skip site rather than stored as a flag (no `value + bool-saying-
    /// which-kind` to desync).
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
        }
    }
}

/// Substitution-related state needed to inline a callee's specs at
/// a call site. Built once by `build_call_substitutions`, used
/// twice — once for the precondition theorem (via `req_value_subst`)
/// and once for the post-call ensures hypothesis (via `ens_value_subst`).
///
/// **Value substitution is render-time and typed.** Each entry stores
/// `(rendered LExpr, actual Lean typ)`. At each use site, the renderer's
/// `RenderCtx::lookup_subst*` returns the value coerced from its storage
/// typ to the surrounding context's slot typ via `coerce_lexpr`. This
/// codifies Rust's auto-borrow analog: a caller-arg at bare typ flowing
/// into a slot expecting `&T` wraps with `Tactus.Ref.mk`; a caller-arg
/// at `Box T` flowing into a bare slot peels with `.deref`. Both bridges
/// compose with the call-site arg bridge in the renderer.
///
/// Type-arg substitution (`typ_subst`) stays at the LExpr-level post-
/// render `lean_ast::substitute`; type params render as `Var("T")` and
/// substitute to typ LExprs (themselves typically `Var`-shaped). No
/// typed bridge needed for type substitution.
///
/// Callee ret-name substitution also stays at LExpr level (`ret_subst`):
/// it's a name-to-name swap, no typ involved.
struct CallSubstitutions<'a> {
    /// Type-arg substitution: `TypParam(T) ↦ Var(rendered_typ_arg)`.
    /// Shared between req and ens. `TypParam` renders as `Var("T")`
    /// so value-level substitution rewrites it. Post-render via
    /// `lean_ast::substitute`.
    typ_subst: HashMap<crate::lean_name::LeanName, LExpr>,
    /// Post-render substitution for the callee's ret name → fresh ret
    /// name. Only applies to ensures (requires doesn't reference ret).
    /// Name-to-name swap; no typing involved.
    ret_subst: HashMap<crate::lean_name::LeanName, LExpr>,
    /// Typed render-time substitution map for the **requires** path.
    /// Every param (mut or non-mut) maps to caller's pre-call arg.
    /// For mut params, both `pname` and `pname_pre` (the rewritten
    /// `<p>_at_pre_tactus` form) point at the same caller arg.
    req_value_subst: HashMap<crate::lean_name::LeanName, (LExpr, Typ)>,
    /// Typed render-time substitution map for the **ensures** path.
    /// * Non-mut params: `pname → (caller_arg, actual_typ)`.
    /// * Mut params: `pname → (post-state existential, p.x.typ)` +
    ///   `pname_pre → (caller_arg, actual_typ)` for the `<p>_at_pre_tactus`
    ///   form.
    ens_value_subst: HashMap<crate::lean_name::LeanName, (LExpr, Typ)>,
    /// Typed render-time substitution map for **pre-state** references
    /// inside Verus `Old(_)` markers in ensures. Same shape as
    /// `ens_value_subst` but maps each mut param to the caller's
    /// pre-call value rather than the post-state existential. The
    /// renderer swaps to this map at the `ExprX::Old` arm via
    /// `RenderCtx::with_pre_state_subst`. Typically unused — ensures
    /// preprocessing rewrites `VarAt(p, Pre)` to `<p>_at_pre_tactus`
    /// before render, so Old(_) rarely survives.
    ens_value_subst_pre: HashMap<crate::lean_name::LeanName, (LExpr, Typ)>,
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
    arg_actual_typs: &[Typ],
    mut_args: &[MutArgInfo<'a>],
    // For requires: pname → caller pre-call arg (for ALL params).
    // Mut params and non-mut params share the same pre-state value.
    req_value_subst: &mut HashMap<crate::lean_name::LeanName, (LExpr, Typ)>,
    // For ensures: pname → post-state existential (mut) or caller arg
    // (non-mut); pname_pre → caller pre-call arg (mut only).
    ens_value_subst: &mut HashMap<crate::lean_name::LeanName, (LExpr, Typ)>,
    // For Old(_) context swap inside ensures: pname → caller pre-call
    // arg (mut only). Typically unused — ensures preprocessing
    // rewrites `VarAt(p, Pre)` to `<p>_at_pre_tactus` before render,
    // so Old(_) rarely survives.
    ens_value_subst_pre: &mut HashMap<crate::lean_name::LeanName, (LExpr, Typ)>,
    mut_param_names: &mut HashSet<String>,
) {
    for (i, p) in params.iter().enumerate() {
        // Subst keys must match what `to_lean_expr::vir_expr_to_ast`
        // produces for `ExprX::Var(p.name)` — i.e., go through the
        // canonical `LeanName::from_var_ident` (includes the
        // disambiguator id when needed).
        let pname = crate::lean_name::LeanName::from_var_ident(&p.x.name);
        let pname_pre = crate::lean_name::LeanName::synthetic(varat_pre_name(pname.as_str()));
        // Requires: every param (mut or non-mut) resolves to the
        // caller's pre-call arg. For mut params, `*old(p)` refs in
        // requires would also resolve to the same value (the rewrite
        // turns them into <p>_at_pre_tactus, which we also key).
        req_value_subst.insert(
            pname.clone(),
            (arg_lexprs[i].clone(), arg_actual_typs[i].clone()),
        );
        // Both legacy mode (`is_mut: true`) and new-mut-ref mode
        // (`MutRef<T>` typ) need the mut-side subst structure. Going
        // through the named helper keeps this in lockstep with
        // `build_call_mut_args` — both consumers ask "is this an
        // &mut param?" the same way, so a future Verus-side change
        // updates both sites at once.
        if is_mut_ref_typ(&p.x.typ, p.x.is_mut) {
            mut_param_names.insert(sanitize(&p.x.name.0));
            // Requires can mention `*old(p)` (rare but legal); the
            // rewrite turns it into <p>_at_pre_tactus. Key it too.
            req_value_subst.insert(
                pname_pre.clone(),
                (arg_lexprs[i].clone(), arg_actual_typs[i].clone()),
            );
            // Ensures: post-state existential at p.x.typ (Verus's
            // declared wrapper typ; the fresh is bound at this typ).
            let info = mut_args.iter().find(|m| m.param_idx == i)
                .expect("MutArgInfo should exist for every &mut param idx — \
                         build_call_mut_args populates one per is_mut param");
            ens_value_subst.insert(
                pname.clone(),
                (LExpr::var(info.fresh.clone()), p.x.typ.clone()),
            );
            // <p>_at_pre_tactus → caller pre-call arg (typed).
            // The rewrite (VarAt(p, Pre) → Var(<p>_at_pre_tactus))
            // runs before render; this entry handles the rewritten
            // form at render time.
            ens_value_subst.insert(
                pname_pre.clone(),
                (arg_lexprs[i].clone(), arg_actual_typs[i].clone()),
            );
            // For Old(_) context swap inside ensures (rare — the
            // preprocessing rewrite typically eliminates these).
            ens_value_subst_pre.insert(
                pname.clone(),
                (arg_lexprs[i].clone(), arg_actual_typs[i].clone()),
            );
        } else {
            // Non-mut params in ensures: same as caller arg (no
            // post/pre distinction).
            ens_value_subst.insert(
                pname.clone(),
                (arg_lexprs[i].clone(), arg_actual_typs[i].clone()),
            );
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
/// Compute the actual Lean-level typ of a caller arg's rendered LExpr.
///
/// **For binder-reference shapes** (`Var(local)`, `VarLoc(local)`,
/// `VarAt(local, _)`) where `local` is a caller fn param: returns the
/// body-shadow typ recorded in `caller_param_typs` (strip one outer ref
/// for `&mut` params; as-declared otherwise). This reflects what the SST
/// renderer's binder-aware path emits for refs to caller-scope locals.
///
/// **For `Loc(inner)`**: recurses into the inner expression — `Loc` is
/// a transparent L-value wrapper at the rendering level (the SST
/// renderer passes through), so the actual rendered typ is whatever the
/// inner produces.
///
/// **For other expressions** (`Call`, `Const`, `Ctor`, `Unary`, etc.):
/// returns `arg.typ` as best effort. The SST renderer's inner bridges
/// normalize to `arg.typ` for most non-binder-ref expressions, so the
/// AST claim is reliable there.
///
/// **Limitations.** The catch-all silently accepts any future binder-
/// aware ExpX variant added upstream. If Verus introduces a new shape
/// (e.g., `Reborrow(local)` or similar) whose rendered typ depends on
/// the caller's binder ctx rather than `arg.typ`, this helper would
/// produce a stale typ and `coerce_lexpr` at use sites would bridge
/// from the wrong source. The downstream symptom would be a Lean type
/// mismatch at the inlined call's arg site, identical in shape to the
/// pre-typed-substitution `claimed-typ-lies` failures (Cluster A's
/// `impl__0.view (Tactus.Ref.mk h)` against a bare-typed `h`).
///
/// Also doesn't consult caller-scope let-bound locals (only fn params).
/// Caller args that are body-let-bound vars (e.g., `tmp__2` from
/// BorrowMut elimination) fall to `arg.typ`. In practice the SST
/// annotation for these locals matches their rendered typ post-shadow
/// because the local's `LocalDecl` records the body-shadow result; if
/// Verus's body-shadow logic diverges from its `LocalDecl` typ, this
/// helper would need to consult `local_decls` instead.
///
/// Used by `build_call_substitutions` to populate typed `value_subst`
/// entries with storage typs that match the rendered LExpr's actual
/// Lean typ. Without this, `coerce_lexpr` at use sites would bridge
/// from the wrong source typ and produce mis-typed wraps or peels.
fn caller_arg_actual_typ(
    arg: &Exp,
    caller_param_typs: &HashMap<VarIdent, Typ>,
    // WP-temp storage typs (`OblCtx::let_binder_typs` — "typ the
    // binding was coerced into"). A temp's Var reference can CLAIM an
    // autoref'd (Ref-decorated) typ while its goal-position `let`
    // bound the bare value; recording the claim makes the use-site
    // `coerce_lexpr` an identity and emits ill-typed Lean (bare Vec at
    // a `Tactus.Ref` slot — test_exec_vec_field_index_clone /
    // apply_hom_symbol_exec).
    let_binder_typs: &im::HashMap<crate::lean_name::LeanName, (Typ, bool)>,
) -> Typ {
    match &arg.x {
        ExpX::Var(v) | ExpX::VarLoc(v) | ExpX::VarAt(v, _) => {
            caller_param_typs.get(v).cloned()
                .or_else(|| {
                    let name = crate::lean_name::LeanName::from_var_ident(v);
                    let_binder_typs.get(&name).map(|(t, _)| t.clone())
                })
                .unwrap_or_else(|| arg.typ.clone())
        }
        // `Loc` is a transparent L-value wrapper — recurse to find the
        // inner's actual typ (typically a VarLoc / Var / UnaryOpr Field).
        ExpX::Loc(inner) => caller_arg_actual_typ(inner, caller_param_typs, let_binder_typs),
        _ => arg.typ.clone(),
    }
}

fn build_call_substitutions<'a>(
    callee: &FunctionX,
    spec_callee: &FunctionX,
    typ_args: &[Typ],
    args: &[Validated<'a>],
    mut_args_raw: &[(usize, MutTargetRaw<'a>)],
    caller_param_typs: &HashMap<VarIdent, Typ>,
    arg_rctx: &crate::expr_shared::RenderCtx,
    obl: &OblCtx,
    e: &mut ObligationEmitter,
) -> CallSubstitutions<'a> {
    // Type-param substitution (shared by req + ens). `TypParam(T)`
    // renders as `Var("T")` so value-level substitute rewrites it.
    let mut typ_subst: HashMap<crate::lean_name::LeanName, LExpr> = HashMap::new();
    for (tp_name, tp_arg) in callee.typ_params.iter().zip(typ_args.iter()) {
        // Match what `typ_to_expr` produces for `TypX::TypParam` —
        // `LeanName::typ_param(name)` (normalizes the trait `Self%` param
        // to `Self`; identity for ordinary `T`/`A` generics).
        typ_subst.insert(crate::lean_name::LeanName::typ_param(tp_name.as_str()), typ_to_expr(tp_arg));
    }

    // Render each arg once + compute its actual Lean typ via
    // `caller_arg_actual_typ`. The actual-typ is what storage typ
    // the value_subst entry uses; together with `coerce_lexpr` at
    // use sites it codifies Rust's auto-borrow analog: the bridge
    // from caller-supplied (possibly body-shadowed) typ to whatever
    // typ the inlined spec slot expects.
    // Typed spine: render each arg ONCE through the binder-aware ctx,
    // yielding the value AND the typ the rendered LExpr actually has
    // (a borrow-of-place renders transparent/bare even when the arg
    // exp CLAIMS the Ref-decorated typ — recording the claim made the
    // use-site coerce_lexpr an identity and emitted ill-typed Lean;
    // see test_exec_vec_field_index_clone). Falls back to the old
    // claimed-typ path for exp shapes exp_to_typed rejects.
    let (arg_lexprs, arg_actual_typs): (Vec<LExpr>, Vec<Typ>) = args.iter().map(|a| {
        match crate::to_lean_sst_expr::exp_to_typed(a.raw(), arg_rctx) {
            Ok(t) => (t.inner, t.typ),
            Err(_) => (
                lower_validated(a),
                caller_arg_actual_typ(a.raw(), caller_param_typs, &obl.let_binder_typs),
            ),
        }
    }).unzip();

    // One MutArgInfo per `&mut` arg — bundles param_idx, target
    // (the L-value shape, post-#87), and the gensym'd fresh post-
    // call name (#105). Replaces the pre-#105 parallel `mut_args`
    // + `mut_idx_to_fresh`. The `_tactus_*` prefix is reserved per
    // Convention 1 in `expr_shared.rs`'s "Reserved identifier
    // conventions" section. `next_id()` is the per-fn counter —
    // sufficient because theorem names are namespaced by fn_name.
    // Returned-mut-ref prophecy composition: if this `&mut` arg is a
    // local an EARLIER call returned as `&mut T` (registered in
    // `obl.prophecies`), reuse that prophecy var `P` as the post-state
    // — so this call's `*final(arg) == *old(arg)+1` constrains the SAME
    // `P` the earlier call's ensures used in `update(old@, i, P)`.
    // Otherwise mint a fresh `_tactus_mut_post_<id>` (the common case).
    let mut_args: Vec<MutArgInfo<'a>> = mut_args_raw.iter()
        .map(|(idx, target)| {
            // Reuse only applies to a WHOLE returned ref (`MutTargetRaw::Var`):
            // the registered `P` is `*final(e)`, NOT `*final(e.field)`. A
            // field-path mutation of a returned ref (`&mut e.field`) must mint
            // its own existential — reusing `P` there would be wrong-typed
            // (P : MutRef Struct vs the field's MutRef FieldT) and
            // wrong-meaning. Sound either way (P stays ∀-bound), but the
            // restriction keeps it correct, not just safe.
            let reused = match target {
                MutTargetRaw::Var(v) => obl.prophecy_for(v),
                MutTargetRaw::Field { .. } => None,
            };
            // `fresh` is the registered prophecy `P` (reused) or a new
            // gensym. Whether it was reused is re-derived at the Phase 1
            // skip site (`fresh` == the local's registered prophecy), so
            // there's no stored flag to fall out of sync with `fresh`.
            let fresh = match reused {
                Some(p) => p.clone(),
                None => crate::lean_name::LeanName::synthetic(
                    format!("_tactus_mut_post_{}", e.next_id()),
                ),
            };
            MutArgInfo { param_idx: *idx, target: target.clone(), fresh }
        })
        .collect();

    // Fresh ret name (gensym to avoid caller-scope collisions). Same
    // convention as mut_post above.
    let fresh_ret_name = crate::lean_name::LeanName::synthetic(format!("_tactus_ret_{}", e.next_id()));

    // Build typed value_subst maps + the LExpr-level ret_subst.
    let mut req_value_subst: HashMap<crate::lean_name::LeanName, (LExpr, Typ)> = HashMap::new();
    let mut ens_value_subst: HashMap<crate::lean_name::LeanName, (LExpr, Typ)> = HashMap::new();
    let mut ens_value_subst_pre: HashMap<crate::lean_name::LeanName, (LExpr, Typ)> = HashMap::new();
    let mut ret_subst: HashMap<crate::lean_name::LeanName, LExpr> = HashMap::new();
    let mut mut_param_names: HashSet<String> = HashSet::new();

    // For non-trait-method-impl calls, `spec_callee == callee` (same
    // `FunctionX` from the same fn_map lookup — see `resolve_callee`),
    // so the spec-side pass would re-insert identical entries. Skip
    // it when we know they're the same. The `matches!` discriminator
    // is the structural predicate from `resolve_callee`'s arms; it's
    // the same check `push_post_call_frames` uses to gate impl-
    // strengthening of ensures (#86).
    let is_trait_method_impl =
        matches!(callee.kind, FunctionKind::TraitMethodImpl { .. });

    // First pass: keys from `callee.params` (the impl's, or the
    // non-trait callee's).
    add_param_subst_entries(
        &callee.params,
        &arg_lexprs,
        &arg_actual_typs,
        &mut_args,
        &mut req_value_subst,
        &mut ens_value_subst,
        &mut ens_value_subst_pre,
        &mut mut_param_names,
    );
    // Second pass: keys from `spec_callee.params` (trait method
    // decl's). Only when trait and impl differ — Rust allows them
    // to use textually different param names (positionally aligned
    // but independent), so trait-side ensures (which use trait
    // names) need their own substitution entries. Needed by #86 so
    // trait-side ensures substitute correctly when we're
    // simultaneously inlining impl-side ensures (which use impl
    // names). For non-trait-impl calls this pass is fully redundant.
    if is_trait_method_impl {
        add_param_subst_entries(
            &spec_callee.params,
            &arg_lexprs,
            &arg_actual_typs,
            &mut_args,
            &mut req_value_subst,
            &mut ens_value_subst,
            &mut ens_value_subst_pre,
            &mut mut_param_names,
        );
    }

    // Callee's ret name → fresh_ret_name in ensures. Same for
    // spec_callee's ret name when trait and impl differ (the impl's
    // ret name may differ textually from the trait's). For non-
    // trait-impl callees, `spec_callee == callee` and the second
    // insert would be identical to the first — skip it. Name-to-name
    // swap, no typing involved — lives in `ret_subst` (LExpr-level
    // post-render substitute).
    let callee_ret = crate::lean_name::LeanName::from_var_ident(&callee.ret.x.name);
    if callee_ret.as_str() != fresh_ret_name.as_str() {
        ret_subst.insert(callee_ret, LExpr::var(fresh_ret_name.clone()));
    }
    if is_trait_method_impl {
        let spec_ret = crate::lean_name::LeanName::from_var_ident(&spec_callee.ret.x.name);
        if spec_ret.as_str() != fresh_ret_name.as_str() {
            ret_subst.insert(spec_ret, LExpr::var(fresh_ret_name.clone()));
        }
    }

    CallSubstitutions {
        typ_subst,
        ret_subst,
        req_value_subst,
        ens_value_subst,
        ens_value_subst_pre,
        mut_param_names,
        mut_args,
        fresh_ret_name,
    }
}

/// Emit the precondition theorem for a call. The `requires` slice
/// holds spec_callee's `require` clauses, pre-extracted by the
/// caller via `call_inlining::collect_inlined_at_call`. Each clause
/// is rewritten (VarAt → varat_pre_name), rendered, substituted with
/// `subst.req_subst`, and wrapped in a `CallPrecondition` SpanMark
/// with the call-site span.
fn emit_call_precondition_theorem(
    requires: &[&Expr],
    subst: &CallSubstitutions,
    call_span: &Span,
    obl: &OblCtx,
    render_ctx: &crate::expr_shared::RenderCtx,
    e: &mut ObligationEmitter,
) {
    let loc = format_rust_loc(call_span);
    let requires_conj = and_all(
        requires.iter()
            .map(|expr| {
                let rewritten = rewrite_varat_for_mut_params(expr, &subst.mut_param_names);
                vir_expr_to_ast_for_inlining_with_ctx(&rewritten, render_ctx)
            })
            .collect()
    );
    // Post-render substitute only handles type-arg substitution
    // (Var(T) → typ_to_expr(arg_typ)). Value-level param substitution
    // happens at render time via `req_value_subst` in the active
    // RenderCtx. The render-time substitution carries typ info, so
    // wrapper bridges fire correctly at each use site via coerce_lexpr.
    let requires_clause = LExpr::span_mark(
        loc.clone(),
        Some(call_span.clone()),
        AssertKind::Obligation(ObligationKind::CallPrecondition),
        substitute(&requires_conj, &subst.typ_subst),
    );
    let id = e.next_id();
    let theorem_name = build_theorem_name(
        kind_to_name(AssertKind::Obligation(ObligationKind::CallPrecondition)), &e.fn_name, &loc, id,
    );
    e.emit_split(theorem_name, requires_clause, obl);
}

// Ret-substitution detection (#128) lives in `crate::ret_subst`.
use crate::ret_subst::is_trivial_true;

/// A returned-mut-ref prophecy for one call whose dest is `MutRef`-typed.
/// Named (vs a positional tuple) per the codebase's convention — each field
/// is read at a different site (`var` at the binder + registration, `final_var`
/// at the ensures rewrite, both + `inner_typ` at the post-render subst), so
/// names beat `_`-heavy destructures.
struct ReturnProphecy {
    /// The prophecy variable `P` (`*final` of the returned ref), ∀-bound at
    /// the call's `MutRef T` wrapper typ.
    var: crate::lean_name::LeanName,
    /// Synthetic VIR-AST `VarIdent` the ensures rewrite produces for
    /// `*final(ret)`; its `from_var_ident` LeanName is the post-render subst key.
    final_var: VarIdent,
    /// The inner `T` (return typ with one ref decoration stripped) — for the
    /// `P.deref` bound and the `*final` inner value.
    inner_typ: Typ,
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
/// top-level shape (Or, Implies, etc.). See `vir_find_ret_eq` (P3 —
/// the single-walk typed extraction).
///
/// This fn is the phase SEQUENCE; each phase's mechanics live in its
/// own helper directly below.
fn push_post_call_frames(
    callee: &FunctionX,
    ensures: &[&Expr],
    subst: &CallSubstitutions,
    dest: Option<&VarIdent>,
    typ_args: &[Typ],
    obl: &OblCtx,
    render_ctx: &crate::expr_shared::RenderCtx,
    e: &mut ObligationEmitter,
) -> OblCtx {
    let mut new_obl = obl.clone();
    let return_prophecy = mint_return_prophecy(callee, dest, e);

    // Phase 1, then the prophecy ∀-bind (BEFORE the ensures Hyp, which
    // references `P`).
    push_mut_arg_binders(callee, subst, obl, &mut new_obl);
    push_prophecy_frames(return_prophecy.as_ref(), callee, subst, dest, &mut new_obl);

    // Phases 2/3 — or the #128 substitution path replacing them.
    // P3 (DESIGN-typed-renderer.md): single-walk ret-eq extraction on
    // the VIR side, where the tree is TYPED. On a hit, the eq conjunct
    // is omitted from the rendered ensures (REST) and E renders
    // separately through the same pipeline, carrying its VIR typ for
    // the #128 sort reconciliation — no rendered-side extraction, no
    // shadow twin, no mirror-matching to keep consistent.
    let ret_eq = vir_find_ret_eq(ensures, subst);
    let substituted_ensures = render_call_ensures(
        ensures,
        subst,
        return_prophecy.as_ref(),
        callee,
        render_ctx,
        ret_eq.as_ref().map(|q| (q.clause_idx, q.conjunct_idx)),
    );
    let eq_extraction: Option<(LExpr, Typ)> = ret_eq.map(|q| {
        (
            render_call_ensure_expr(q.rhs, subst, return_prophecy.as_ref(), callee, render_ctx),
            q.rhs.typ.clone(),
        )
    });
    let (dest_value, use_dest_name) =
        push_ret_frames(substituted_ensures, eq_extraction, callee, subst, dest, &mut new_obl);

    // Phase 4.
    push_mut_rebinds(callee, subst, &mut new_obl);

    // Phase 5: dest binding for the call's return (`let r = foo(…)`).
    // `dest_value` is `Var(fresh_ret_name)` in the ∀-path or `E` in
    // the substitution path (#128). Skipped when `use_dest_name`
    // (Approach A): the ∀-binder already IS the dest, so the alias
    // `let x := x` is trivial and dropped.
    // Ledger the dest's storage typ — the (typ-substituted) declared
    // ret typ, which the #128 bridge / ∀-binder make TRUE by
    // construction (U2). Without this entry, downstream typed-spine
    // Var lookups fall back to per-use claims and the old
    // bare-assumption compensators double-wrap
    // (BUG-call-arg-temp-claimed-typ.md).
    if let Some(dest_ident) = dest {
        let dest_lean = crate::lean_name::LeanName::from_var_ident(dest_ident);
        let ret_typ_subst: Typ = if callee.typ_params.len() == typ_args.len() {
            let map: HashMap<vir::ast::Ident, Typ> = callee.typ_params.iter()
                .cloned()
                .zip(typ_args.iter().cloned())
                .collect();
            vir::sst_util::subst_typ(&map, &callee.ret.x.typ)
        } else {
            callee.ret.x.typ.clone()
        };
        new_obl = new_obl.with_let_binder(dest_lean.clone(), ret_typ_subst, true);
        if !use_dest_name {
            new_obl.frames.push_back(CtxFrame::Let(dest_lean, dest_value));
        }
    }

    new_obl
}

/// Returned-mut-ref prophecy (general over any `MutRef`-typed return,
/// not a `vec_index_mut` special-case). When this call returns a
/// `&mut T` into `dest`, the callee's ensures reference `*final(ret)`
/// — e.g. vstd's `vec_index_mut`: `final(vec)@ == old(vec)@.update(i,
/// *final(element))`. That `*final` is a PROPHECY: its value is fixed
/// by a LATER call on `dest` (`bump(dest)`). We mint a prophecy var
/// `P`, ∀-bind it here, render the ensures' `*final(ret)` AS `P`
/// (`rewrite_return_final_ref` → `Var(<ret>_final_tactus)`, then a
/// post-render subst `<ret>_final_tactus → P`), and register
/// `dest → P` so the resolving call reuses `P` for its post-state
/// (`build_call_substitutions`) instead of a fresh existential. The
/// chain `final(vec)@[i] == P == *old(dest)+1` then closes. Without
/// this, the #95 rewrite collapses `*final(ret)` and `*current(ret)`
/// alike to `Var(ret) → fresh_ret`, so the update inserts the current
/// element and the prophecy is lost.
fn mint_return_prophecy(
    callee: &FunctionX,
    dest: Option<&VarIdent>,
    e: &mut ObligationEmitter,
) -> Option<ReturnProphecy> {
    if dest.is_some() && is_mut_ref_typ(&callee.ret.x.typ, false) {
        let var = crate::lean_name::LeanName::synthetic(
            format!("_tactus_mut_post_{}", e.next_id()));
        let ret_ident = &callee.ret.x.name;
        // Synthetic VIR-AST VarIdent the ensures rewrite produces for
        // `*final(ret)`; the post-render subst key is
        // `from_var_ident(final_var)` (same VarIdent → same LeanName).
        let final_var = VarIdent(
            Arc::new(format!("{}_final_tactus", sanitize(&ret_ident.0))),
            ret_ident.1.clone(),
        );
        let inner_typ =
            crate::to_lean_expr::strip_one_ref_decoration(&callee.ret.x.typ);
        Some(ReturnProphecy { var, final_var, inner_typ })
    } else {
        None
    }
}

/// Phase 1: per-&mut existential binder + type-inv hypothesis.
/// `subst.mut_args` (#105) bundles param_idx, caller_var, and
/// fresh into one struct — no parallel-array lookups.
///
/// **Wrapper-arch typing (TypedExpr migration):** the existential
/// is bound at the callee's declared param typ — which for
/// new-mut-ref `&mut T` is `MutRef T` (wrapper-typed). Use sites
/// (bound predicate, substituted ensures via ens_subst, rebind
/// frame) want the inner-typed view — they reason about the value
/// T, not the wrapper.
///
/// Wrap the existential in `TypedExpr` and use `into_slot(inner)`
/// to produce the deref'd form for each use site. For non-mut args
/// and legacy `is_mut: true` with bare typ, `into_slot` is a no-op
/// (wrapper depth already matches inner). For new-mut-ref the
/// coercion inserts `.deref` to bridge from the wrapper-typed
/// existential to the inner-typed use slot. Mirrors the pattern
/// at `fn_binders` line ~3389 where param-level `&mut` binders
/// emit bounds via `.deref` for the same reason.
///
/// `obl` is the UNMUTATED pre-call ctx (for the reused-prophecy
/// check, which must key off what `build_call_substitutions` saw);
/// frames push onto `new_obl`.
fn push_mut_arg_binders(
    callee: &FunctionX,
    subst: &CallSubstitutions,
    obl: &OblCtx,
    new_obl: &mut OblCtx,
) {
    for info in &subst.mut_args {
        // Reused returned-mut-ref prophecy: `info.fresh` IS the prophecy `P`
        // registered for this arg's local (derived here from `obl`, the
        // unmutated pre-call ctx that `build_call_substitutions` also keyed
        // off — so they agree). `P` is already ∀-bound at the introducing
        // call's frame, so don't re-bind it (double binder); the ens_subst
        // still maps this param's post-state to `P`, and Phase 4 rebinds the
        // local to `P`.
        let reused_prophecy = obl
            .prophecy_for(info.rebind_local())
            .map(|p| p.as_str())
            == Some(info.fresh.as_str());
        if reused_prophecy {
            // Invalidate on resolution (defense-in-depth): a returned ref is
            // resolved at most once — clearing prevents a (frontend-blocked
            // today) double-resolve from reusing `P` and forming `P == P+1`.
            new_obl.clear_prophecy(info.rebind_local());
            continue;
        }
        let typ = &callee.params[info.param_idx].x.typ;
        let lean_typ = substitute(&typ_to_expr(typ), &subst.typ_subst);
        new_obl.frames.push_back(CtxFrame::Binder(LBinder::explicit(info.fresh.clone(), lean_typ)));
        // Bound predicate: pass the inner-typed view via TypedExpr
        // coercion. `type_bound_predicate` already recurses through
        // `MutRef(T)` to emit the bound on T — what was broken was
        // that the value-side was wrapper-typed; bridging via
        // `into_slot(&inner)` produces `fresh.deref` for the
        // wrapper case and `fresh` for the bare case.
        let inner_typ = crate::to_lean_expr::strip_one_ref_decoration(typ);
        let inner_form = crate::typed_expr::TypedExpr::var(
            info.fresh.clone(), typ.clone(),
        ).into_slot(&inner_typ);
        if let Some(pred) = type_bound_predicate(&inner_form, typ) {
            new_obl.frames.push_back(CtxFrame::Hyp(pred));
        }
    }
}

/// Returned-mut-ref prophecy: ∀-bind `P` at the inner T (e.g. `P :
/// Int` for `&mut u8`) + its type-inv bound, and register `dest → P`,
/// BEFORE the ensures Hyp (which references `P` via the rewrite +
/// post-render subst in `render_call_ensures`). The binder lives in
/// `new_obl`, which flows to `after` — so the resolving call
/// (`bump(dest)`) sees `P` in scope and reuses it. No-op when there
/// is no prophecy.
fn push_prophecy_frames(
    return_prophecy: Option<&ReturnProphecy>,
    callee: &FunctionX,
    subst: &CallSubstitutions,
    dest: Option<&VarIdent>,
    new_obl: &mut OblCtx,
) {
    if let Some(rp) = &return_prophecy {
        // Bind `P` at the return's `MutRef T` typ (wrapper) — matching
        // what the resolving call's machinery expects (it `.deref`s the
        // post-state). The bound + the ensures use `P.deref` (the inner
        // T value), via `into_slot(&inner_typ)`. Mirrors Phase 1's
        // wrapper-typed-binder + inner-bound pattern exactly.
        let ret_typ = &callee.ret.x.typ;
        let lean_typ = substitute(&typ_to_expr(ret_typ), &subst.typ_subst);
        new_obl.frames.push_back(CtxFrame::Binder(LBinder::explicit(rp.var.clone(), lean_typ)));
        let inner_form = crate::typed_expr::TypedExpr::var(rp.var.clone(), ret_typ.clone())
            .into_slot(&rp.inner_typ);
        if let Some(pred) = type_bound_predicate(&inner_form, ret_typ) {
            new_obl.frames.push_back(CtxFrame::Hyp(pred));
        }
        if let Some(d) = dest {
            new_obl.register_prophecy(d, rp.var.clone());
        }
    }
}

/// Build the substituted ensures conjunction once (`None` when the
/// callee has no ensures). Used by both the substitution path (#128)
/// and the ∀-path. The `ensures` slice was built by the caller via
/// `call_inlining::collect_inlined_at_call`: spec_callee's
/// ensures, plus callee's own ensures when callee is a
/// TraitMethodImpl (#86 impl-strengthening — caller gets the
/// conjunction of trait and impl contracts). Verus enforces
/// impl ⇒ trait, so the conjunction is satisfiable.
///
/// `subst.ens_subst` includes keys for both callee.params and
/// spec_callee.params (built by the two passes in
/// `build_call_substitutions`), plus both ret names → fresh_ret_name.
/// So substituting either the trait's or the impl's clauses
/// works regardless of whether trait/impl param names match.
/// Post-render substitution for inlined ensures: type-arg substitution
/// and ret-name swap (Var(callee_ret) → Var(fresh_ret_name)), plus the
/// returned-mut-ref `<ret>_final_tactus → P` entry. Value-level param
/// substitution happened at render time via `ens_value_subst` in the
/// active RenderCtx — carries typ info, so wrapper bridges fire
/// correctly at each use site.
fn build_ens_post_render_subst(
    subst: &CallSubstitutions,
    return_prophecy: Option<&ReturnProphecy>,
    callee: &FunctionX,
) -> HashMap<crate::lean_name::LeanName, LExpr> {
    let mut post_render_subst: HashMap<crate::lean_name::LeanName, LExpr> = subst.typ_subst.iter()
        .chain(subst.ret_subst.iter())
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    if let Some(rp) = &return_prophecy {
        // `*final(ret)` is the INNER T value — `P.deref` (P is bound at
        // the `MutRef T` wrapper typ). Same `into_slot` coercion the
        // resolving call uses, so both sides agree on `P.deref`.
        let p_inner = crate::typed_expr::TypedExpr::var(rp.var.clone(), callee.ret.x.typ.clone())
            .into_slot(&rp.inner_typ);
        post_render_subst.insert(
            crate::lean_name::LeanName::from_var_ident(&rp.final_var),
            p_inner,
        );
    }
    post_render_subst
}

/// Render ONE ensures expression (a whole clause, a kept conjunct of
/// the skip clause, or the extracted `E`) through the full inlining
/// pipeline: mut-param VarAt rewrite, returned-mut-ref final rewrite,
/// inlining render, post-render substitution. Applying the post-render
/// substitute per-expression is equivalent to the old whole-conjunction
/// application (substitution distributes over `And`).
fn render_call_ensure_expr(
    expr: &Expr,
    subst: &CallSubstitutions,
    return_prophecy: Option<&ReturnProphecy>,
    callee: &FunctionX,
    render_ctx: &crate::expr_shared::RenderCtx,
) -> LExpr {
    let rewritten = rewrite_varat_for_mut_params(expr, &subst.mut_param_names);
    // Returned-mut-ref: rewrite `*final(ret)` → `Var(final_var)`
    // so it renders distinct from `*current(ret)` (which stays
    // `Var(ret) → fresh_ret`). The `final_var → P` post-render
    // subst sends it to the prophecy var.
    let rewritten = match &return_prophecy {
        Some(rp) => rewrite_return_final_ref(&rewritten, &callee.ret.x.name, &rp.final_var),
        None => rewritten,
    };
    let rendered = vir_expr_to_ast_for_inlining_with_ctx(&rewritten, render_ctx);
    substitute(
        &rendered,
        &build_ens_post_render_subst(subst, return_prophecy, callee),
    )
}

/// Render the callee's ensures clauses for call-site inlining. With
/// `skip_conjunct: Some((clause_idx, conjunct_idx))` (P3 ret-eq
/// extraction), that conjunct is OMITTED: its clause is flattened via
/// `vir_top_conjuncts` (the same walk `vir_find_ret_eq` indexed by)
/// and the kept conjuncts render individually. Returns `None` when
/// nothing remains.
fn render_call_ensures(
    ensures: &[&Expr],
    subst: &CallSubstitutions,
    return_prophecy: Option<&ReturnProphecy>,
    callee: &FunctionX,
    render_ctx: &crate::expr_shared::RenderCtx,
    skip_conjunct: Option<(usize, usize)>,
) -> Option<LExpr> {
    let mut ensures_clauses: Vec<LExpr> = Vec::new();
    for (ci, expr) in ensures.iter().enumerate() {
        match skip_conjunct {
            Some((sc, sk)) if sc == ci => {
                let mut cs = Vec::new();
                vir_top_conjuncts(expr, &mut cs);
                for (ki, c) in cs.iter().enumerate() {
                    if ki == sk {
                        continue;
                    }
                    ensures_clauses.push(render_call_ensure_expr(
                        c, subst, return_prophecy, callee, render_ctx,
                    ));
                }
            }
            _ => ensures_clauses.push(render_call_ensure_expr(
                expr, subst, return_prophecy, callee, render_ctx,
            )),
        }
    }
    if ensures_clauses.is_empty() {
        None
    } else {
        Some(and_all(ensures_clauses))
    }
}

/// Peel the VIR wrappers that render transparently (Trigger /
/// CoerceMode) — a `Clip`-wrapped node would NOT render transparently
/// and correspondingly isn't peeled. Shared by the ret-eq extraction
/// and the skip-conjunct rendering so both flatten identically.
fn vir_peel_transparent(e: &Expr) -> &Expr {
    match &e.x {
        ExprX::Unary(UnaryOp::Trigger(_), inner)
        | ExprX::Unary(UnaryOp::CoerceMode { .. }, inner) => vir_peel_transparent(inner),
        _ => e,
    }
}

/// Flatten the top-level `And`-tree of a VIR ensures clause into its
/// leaf conjuncts (peeled). Top-level only — a conjunct buried inside
/// Or / Implies / quantifiers does NOT uniquely determine anything
/// (#128's conservative scope).
fn vir_top_conjuncts<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    let e = vir_peel_transparent(e);
    if let ExprX::Binary(BinaryOp::And, l, r) = &e.x {
        vir_top_conjuncts(l, out);
        vir_top_conjuncts(r, out);
    } else {
        out.push(e);
    }
}

/// A `ret == E` conjunct found in the callee's VIR ensures.
struct VirRetEq<'a> {
    /// Index into the `ensures` clause slice.
    clause_idx: usize,
    /// Index into that clause's top-level And-flatten
    /// (`vir_top_conjuncts` order).
    conjunct_idx: usize,
    /// E — the value side. TYPED: `rhs.typ` is the VIR typ the #128
    /// sort reconciliation needs.
    rhs: &'a Expr,
}

/// Single-walk ret-eq extraction (#128, P3 DESIGN-typed-renderer.md).
/// Finds a top-level conjunct `Eq(ret, E)` (or commuted) in the
/// callee's ensures ON THE VIR SIDE, where the tree is typed — the
/// successor of the two-walk design (rendered-side
/// `ret_subst::extract_top_level_eq_for` + a VIR "twin" recovering
/// E's typ for sort reconciliation), whose mirror-matching had to stay
/// consistent by hand.
///
/// Match scope mirrors the retired rendered extraction: top-level
/// And-tree only; first match in clause order wins (spec-first for
/// trait-method impls, #86 — if both spec and impl carry `r == E`,
/// the spec's is taken and the impl's lands in REST, substituting to
/// `E_impl == E_spec`, consistent by impl ⇒ trait). Self-referential
/// candidates (`r == E` where E mentions r) are SKIPPED — substituting
/// would loop. The mention scan is scope-UNAWARE (a shadowed rebind of
/// the ret name inside E conservatively rejects that candidate; at
/// worst we fall to the ∀-path — never wrong). The ret is referenced
/// as a plain `Var` or a whole-local place read `ReadPlace(Local(d))`
/// — the same reference shapes `inline_spec::substitute_body` handles
/// for params.
fn vir_find_ret_eq<'a>(ensures: &[&'a Expr], subst: &CallSubstitutions) -> Option<VirRetEq<'a>> {
    let is_ret_ident = |v: &VarIdent| -> bool {
        subst.ret_subst.contains_key(&crate::lean_name::LeanName::from_var_ident(v))
    };
    // MATCHER peel — a place whose base local is the ret through
    // BARE-RENDERING layers only (Local, DerefMut): the mut-ref
    // current-value read `*ret` is `ReadPlace(DerefMut(Local(ret)))`
    // (vstd's `&mut`-returning ensures, e.g. vec_index_mut's
    // `*result == v@[i]`), and it renders as the BARE fresh-ret binder
    // in the inlining ctx — the retired rendered-side extraction
    // matched it, so this walk must too (the raw substitution
    // `dest := E` it produces is the pinned behavior; the ∀-path
    // would type the binder at `MutRef T` and ill-type the eq
    // hypothesis against the value-typed E). Field/Index layers do
    // NOT render bare, so they deliberately don't match here.
    fn place_ret_local<'p>(place: &'p vir::ast::Place) -> Option<&'p VarIdent> {
        match &place.x {
            vir::ast::PlaceX::Local(v) => Some(v),
            vir::ast::PlaceX::DerefMut(inner) => place_ret_local(inner),
            _ => None,
        }
    }
    // MENTION-SCAN base walk — TOTAL over place layers (Field /
    // DerefMut / ModeUnwrap / Index / Local): the self-reference
    // guard must catch a ret hiding under ANY projection (`ret.f`,
    // `ret[i]`), not just the bare-rendering shapes, or a
    // self-referential eq substitutes and leaves `fresh_ret` unbound
    // (a loud Lean unknown-identifier, but the guard should be total
    // — 2026-07-03 self-review finding). `Temporary(expr)`'s inner
    // expr is walked by the visitor's own recursion, so `None` here
    // is complete, not a gap.
    fn place_base_local<'p>(place: &'p vir::ast::Place) -> Option<&'p VarIdent> {
        match &place.x {
            vir::ast::PlaceX::Local(v) => Some(v),
            vir::ast::PlaceX::Field(_, inner)
            | vir::ast::PlaceX::DerefMut(inner)
            | vir::ast::PlaceX::ModeUnwrap(inner, _)
            | vir::ast::PlaceX::Index(inner, _, _, _) => place_base_local(inner),
            _ => None,
        }
    }
    let is_ret_var = |e: &Expr| -> bool {
        match &vir_peel_transparent(e).x {
            ExprX::Var(v) => is_ret_ident(v),
            ExprX::ReadPlace(place, _) => {
                place_ret_local(place).is_some_and(|v| is_ret_ident(v))
            }
            _ => false,
        }
    };
    let mentions_ret = |e: &Expr| -> bool {
        let mut found = false;
        vir::ast_visitor::expr_visitor_walk(e, &mut |sub: &Expr| {
            let hit = match &sub.x {
                ExprX::Var(v) | ExprX::VarLoc(v) | ExprX::VarAt(v, _) => is_ret_ident(v),
                ExprX::ReadPlace(place, _) => {
                    place_base_local(place).is_some_and(|v| is_ret_ident(v))
                }
                _ => false,
            };
            if hit {
                found = true;
                vir::visitor::VisitorControlFlow::Stop(())
            } else {
                vir::visitor::VisitorControlFlow::Recurse
            }
        });
        found
    };
    for (clause_idx, ens) in ensures.iter().enumerate() {
        let mut cs = Vec::new();
        vir_top_conjuncts(ens, &mut cs);
        for (conjunct_idx, c) in cs.iter().enumerate() {
            if let ExprX::Binary(BinaryOp::Eq(_), lhs, rhs) = &c.x {
                let value = if is_ret_var(lhs) {
                    rhs
                } else if is_ret_var(rhs) {
                    lhs
                } else {
                    continue;
                };
                if mentions_ret(value) {
                    continue;
                }
                return Some(VirRetEq { clause_idx, conjunct_idx, rhs: value });
            }
        }
    }
    None
}

/// Phases 2/3 — the ret binder + bound + ensures Hyp — or the #128
/// substitution path replacing them. Returns `(dest_value,
/// use_dest_name)` for Phase 5: the value to bind `dest` to
/// (`Var(fresh_ret_name)` / the dest's own name in the ∀-path, `E` in
/// the substitution path), and whether the ∀-binder already carries
/// the dest's name (Approach A — Phase 5's alias `let` is dropped).
///
/// #128: ret-substitution. When `eq_extraction` is `Some((E, E_typ))`
/// — the VIR-side single-walk extraction found `ret == E` (P3) — we
/// skip the `∀ ret + ret_bound` chain and bind `dest := E` directly;
/// `substituted_ensures` is then REST (the eq conjunct already
/// omitted). E's typ is always known (it rode along from the VIR
/// tree), so the sort reconciliation (2026-07-03) never needs a
/// conservative fallback: `coerce_lexpr` bridges E to the dest's
/// declared render sort unconditionally for integer rets. `None` →
/// the ∀-path, with `substituted_ensures` the full conjunction.
fn push_ret_frames(
    substituted_ensures: Option<LExpr>,
    eq_extraction: Option<(LExpr, Typ)>,
    callee: &FunctionX,
    subst: &CallSubstitutions,
    dest: Option<&VarIdent>,
    new_obl: &mut OblCtx,
) -> (LExpr, bool) {
    let ret = &callee.ret.x;
    // `(raw E, bridged E, rest)`: the BOUND hyp goes on raw E (faithful
    // and strongest — `0 ≤ E` over ℤ is exactly what justifies the
    // `Int.toNat` bridge); the dest binding and rest-ensures
    // substitution use bridged E (the dest's declared render sort, so
    // downstream slots typecheck).
    let ret_substitution: Option<(LExpr, LExpr, LExpr)> = eq_extraction.map(|(e, e_typ)| {
        let rest = substituted_ensures
            .clone()
            .unwrap_or_else(|| LExpr::new(crate::lean_ast::ExprNode::LitBool(true)));
        // Bridge E's render sort (numeric rets, #128) AND wrapper
        // depth to the dest's declared typ — EXCEPT for `&mut T`
        // returns. A mut-ref return (Vec::index_mut → &mut T) is owned
        // by the prophecy / MutArgInfo machinery; bridging E to the
        // MutRef ret.typ would `MutRef.mk`-WRAP it, so `*old(x)` on the
        // substituted mut arg renders undereferenced (`tmp < 100` on a
        // `MutRef Int` — regressed test_exec_call_mut_arg_vec_index).
        // Every OTHER ret — datatype (`Vec` from copy_word /
        // apply_hom, needing the wrapper `.mk` to maintain U2, pinned
        // by test_exec_vec_field_index_clone), Bool/Prop, and integer
        // (needing `Int.toNat`) — DOES get the bridge; coerce_lexpr is
        // an identity when sort and wrappers already match.
        if crate::expr_shared::is_mut_ref_typ(&ret.typ, ret.is_mut) {
            (e.clone(), e, rest)
        } else {
            let bridged = crate::expr_shared::coerce_lexpr(e.clone(), &e_typ, &ret.typ);
            (e, bridged, rest)
        }
    });

    // The value bound to `dest` differs by path: in the ∀-path,
    // `dest := fresh_ret_name` (the ∀-bound); in the substitution
    // path, `dest := E` (the substituted value). Computing it
    // here lets Phase 5 share one code site between paths.
    //
    // Approach A (BUG-call-result-let-unnameable-in-assert.md): in the
    // ∀-path, name the ∀-bound result with the DEST's source name
    // directly instead of the gensym `_tactus_ret_N`, and skip the
    // Phase-5 alias `let`. The theorem then reads `(x : S) (h : … x …)
    // : … x …` — a `by { }` proof can name `x` to apply a lemma to it,
    // rather than `x` being trapped in a goal-position `let x :=
    // _tactus_ret_N` that's not in the local context. omega/assumption
    // both still close (x is a plain binder the ensures references
    // directly — no goal-`let` to zeta), so this is strictly cleaner
    // than the gensym+let shape.
    //
    // Guard: the gensym exists to dodge the self-referential
    // `let x = f(x)` collision (the arg `x` survives in the substituted
    // ensures and would be captured by a `∀ x` binder —
    // test_exec_call_ret_name_collision). So only rename when the dest
    // name is NOT free in the substituted ensures; otherwise keep the
    // gensym + goal-position let. Only the ∀-path (`ret_substitution ==
    // None`) introduces a binder, so the rename is gated on that too.
    let dest_lean = dest.map(crate::lean_name::LeanName::from_var_ident);
    let use_dest_name = ret_substitution.is_none()
        && dest_lean.as_ref().is_some_and(|d| {
            substituted_ensures.as_ref().is_none_or(|ens| {
                !crate::lean_ast::mentions_free_var(ens, d.as_str())
            })
        });
    let dest_value: LExpr = match &ret_substitution {
        Some((raw_e, bridged_e, rest_ensures)) => {
            // Substitution path: drop `∀ ret + ret_bound`; emit
            // `E_bound` and `rest_ensures` as Hyps directly.
            // `type_bound_predicate` returns `None` for non-numeric
            // ret types (Bool, Prop, structs) so the bound Hyp is
            // elided there — the cond_setup case (Bool ret).
            // The bound goes on RAW E: `0 ≤ E ∧ E < hi` over E's own
            // sort is faithful and strongest (for a ℤ-valued E bound
            // into a ℕ dest, `0 ≤ E` is exactly the fact that makes
            // the `Int.toNat E` bridge lossless).
            if let Some(pred) = type_bound_predicate(raw_e, &ret.typ) {
                new_obl.frames.push_back(CtxFrame::Hyp(pred));
            }
            // The eq clause that gave us E has been dropped from
            // `rest_ensures`. Substitute fresh_ret_name → E in the
            // remaining clauses so they reference E directly (at the
            // dest's render sort — occurrences of ret sit in slots
            // typed by the dest). If the result simplifies to `True`
            // (e.g., the eq clause was the only conjunct), skip the
            // Hyp.
            if !is_trivial_true(rest_ensures) {
                let mut ret_to_e = std::collections::HashMap::new();
                ret_to_e.insert(subst.fresh_ret_name.clone(), bridged_e.clone());
                let rest_substituted = substitute(rest_ensures, &ret_to_e);
                if !is_trivial_true(&rest_substituted) {
                    new_obl.frames.push_back(CtxFrame::Hyp(rest_substituted));
                }
            }
            bridged_e.clone()
        }
        None => {
            // ∀-path: ret binder + ret_bound + ensures Hyp. The binder
            // is the dest's source name when `use_dest_name` (Approach
            // A), else the gensym.
            let binder_name = if use_dest_name {
                dest_lean.clone().expect("use_dest_name implies dest is Some")
            } else {
                subst.fresh_ret_name.clone()
            };
            let ret_typ_lean = substitute(&typ_to_expr(&ret.typ), &subst.typ_subst);
            new_obl.frames.push_back(CtxFrame::Binder(LBinder::explicit(binder_name.clone(), ret_typ_lean)));
            if let Some(pred) = type_bound_predicate(
                &LExpr::var(binder_name.clone()), &ret.typ,
            ) {
                new_obl.frames.push_back(CtxFrame::Hyp(pred));
            }
            if let Some(conj) = substituted_ensures {
                // The ensures references `fresh_ret_name`; when we renamed
                // the binder to the dest name, rewrite it to match so the
                // hyp talks about `x`, not the (now-absent) gensym.
                let conj = if use_dest_name {
                    let mut m = std::collections::HashMap::new();
                    m.insert(subst.fresh_ret_name.clone(), LExpr::var(binder_name.clone()));
                    substitute(&conj, &m)
                } else {
                    conj
                };
                new_obl.frames.push_back(CtxFrame::Hyp(conj));
            }
            LExpr::var(binder_name.clone())
        }
    };
    (dest_value, use_dest_name)
}

/// Phase 4: caller-side rebindings for &mut args. Placed AFTER
/// ensures so the ensures Hyp references the fresh existential,
/// not the rebound caller name.
///
/// Three shapes:
/// * Simple `&mut <local>` (#55): `let local := fresh`. The local
///   takes on the post-call value directly.
/// * Single-variant struct field `&mut <local>.<f1>.<f2>.…` (#87
///   single-level, #144 deeper): `let local := { local with f1 :=
///   { local.f1 with f2 := fresh } }`. Lean's structure update
///   preserves all other fields automatically — no havoc-base +
///   assume-other-fields-unchanged dance needed (the syntax IS
///   that semantics, in the type system).
/// * Tuple field `&mut <local>.<i>` (#145 + #146): `let local :=
///   (local.1, …, fresh, …, local.<n>)`. Lean's tuple syntax IS
///   `Prod.mk` sugar; the unmodified slots read via the
///   multi-segment `tuple_field_accessor` (`.2.1` etc. for the
///   nested-Prod representation of arity > 2 tuples).
fn push_mut_rebinds(
    callee: &FunctionX,
    subst: &CallSubstitutions,
    new_obl: &mut OblCtx,
) {
    for info in &subst.mut_args {
        let local_name = crate::lean_name::LeanName::from_var_ident(info.rebind_local());
        // Wrapper-arch typing: the fresh existential is wrapper-typed
        // for new-mut-ref. The caller's local is body-shadowed to
        // inner-typed in body scope. Coerce fresh to inner before
        // rebinding so `let local := fresh.deref` matches local's
        // body-scope typ. (For legacy is_mut + bare typ, this is a
        // no-op — wrapper depths already match.)
        let param_typ = &callee.params[info.param_idx].x.typ;
        let inner_typ = crate::to_lean_expr::strip_one_ref_decoration(param_typ);
        let coerced_fresh = crate::typed_expr::TypedExpr::var(
            info.fresh.clone(), param_typ.clone(),
        ).into_slot(&inner_typ);
        let new_value = match &info.target {
            MutTargetRaw::Var(_) => coerced_fresh,
            // The deepest-level value substituted at the field slot is the
            // coerced existential — inner-typed to match the field's typ
            // (shares the wrapper-arch coercion with the simple-Var path).
            MutTargetRaw::Field { field_oprs, .. } => {
                build_nested_field_update(LExpr::var(local_name.clone()), field_oprs, coerced_fresh)
            }
        };
        new_obl.frames.push_back(CtxFrame::Let(local_name, new_value));
    }
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
    // Dest local's declared SST typ — the rendered RHS is coerced to
    // it (see `Wp::Let` doc). Threads unchanged through the if-fork and
    // inner-let-chain recursion: those rebind the same `name` to a
    // lifted value, so the coercion target is the same.
    dest_typ: &Typ,
    body: &Wp<'a>,
    ctx: &'a WpCtx<'a>,
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
            // P2: cond renders with the walk's binder-aware ctx + the
            // obl's let-binder env (a fork condition can reference
            // let-bound locals, e.g. `if pair.0 > 5`).
            let c_ast = sst_exp_to_ast_checked_with_ctx(
                cond,
                &ctx.render_ctx().with_let_binder_typs(&obl.let_binder_typs),
            )
            .expect("walk_let if-cond: sub of validated Exp tree");
            walk_let(name, then_e, dest_typ, body, ctx,
                &obl.with_frame(CtxFrame::Hyp(c_ast.clone())), e);
            walk_let(name, else_e, dest_typ, body, ctx,
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
                        // NB: these inner multi-binder binders bind at
                        // `b.a.typ` (the claimed contract) — `VarBinder`
                        // carries `b.a` (value) but not the binder's
                        // declared typ, so there's no separate coercion
                        // target. Harmless today: multi-binder
                        // `let (a,b) = …` is a defensive/unreached path
                        // (Verus destructures via Ctor + projection, not
                        // `Bind(Let([..]))` — see DESIGN #92).
                        //
                        // P2: rendered through the typed spine with the
                        // walk's ctx and RECORDED in the let-binder env
                        // at `b.a.typ` with the RHS's D3 trust bit.
                        let rctx = ctx
                            .render_ctx()
                            .with_let_binder_typs(&chain_obl.let_binder_typs);
                        let b_name = crate::lean_name::LeanName::from_var_ident(&b.name);
                        let b_typed = crate::to_lean_sst_expr::sst_exp_to_typed(&b.a, &rctx)
                            .expect("walk_let binder rhs: sub of validated Exp tree");
                        let b_trusted =
                            crate::to_lean_sst_expr::sst_actual_is_trusted(&b.a, &rctx);
                        let b_value = b_typed.into_slot(&b.a.typ);
                        chain_obl = chain_obl
                            .with_frame(CtxFrame::Let(b_name.clone(), b_value))
                            .with_let_binder(b_name, b.a.typ.clone(), b_trusted);
                    }
                    walk_let(name, inner_body, dest_typ, body, ctx, &chain_obl, e);
                    return;
                }
            }
        }
        _ => {}
    }
    // Plain let with no peelable structure — push the let frame
    // and continue walking the body. Coerce the rendered RHS to the
    // dest's SST typ: when Rust auto-ref'd the binding (`copy : &Box<T>`
    // bound from `rest : Box<T>`), this inserts the `Tactus.Ref.mk` so
    // the local's Lean value matches its declared typ — maintaining the
    // U2 invariant so downstream `count_ref(dest.typ)` deref sites are
    // correct. No-op when `val.typ == dest_typ` (the common case).
    //
    // P2 (DESIGN-typed-renderer.md): the RHS renders through the typed
    // spine with the walk's binder-aware ctx (was: empty-ctx +
    // claimed-typ coerce_lexpr — identical output when actual ==
    // claimed), bridges into the dest typ, and the binding is RECORDED
    // in the obl's let-binder env at `dest_typ` with its D3 trust bit —
    // so downstream Var uses know the binder's believed typ, and
    // trusted entries lift `exp_to_typed`'s Box/Unbox resets.
    let rctx = ctx.render_ctx().with_let_binder_typs(&obl.let_binder_typs);
    let val_typed = crate::to_lean_sst_expr::sst_exp_to_typed(val, &rctx)
        .expect("walk_let val: validated upstream via Wp::Let.value");
    let trusted = crate::to_lean_sst_expr::sst_actual_is_trusted(val, &rctx);
    let coerced = val_typed.into_slot(dest_typ);
    let new_obl = obl
        .with_frame(CtxFrame::Let(name.clone(), coerced))
        .with_let_binder(name.clone(), dest_typ.clone(), trusted);
    walk_obligations(body, ctx, &new_obl, e);
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
        // Ordinary generics (`T`, `A`) pass through unchanged; the
        // trait `Self%` param normalizes to `Self` to match the class
        // binder and the param types that reference it.
        out.push(LBinder::typ_param(tp.as_str(), BinderKind::Explicit));
    }
    for p in fn_sst.x.pars.iter().filter(|p| !is_synthetic_param(p)) {
        let name = crate::lean_name::LeanName::from_var_ident(&p.x.name);
        // `param_binder_typ` wraps `&mut` legacy params (is_mut: true
        // with plain typ) through `Tactus.MutRef`, matching what
        // new-mut-ref-mode params get from `TypX::MutRef`'s arm in
        // `typ_to_node`. Both modes converge at the binder level.
        out.push(LBinder::explicit(name.clone(), crate::to_lean_type::param_binder_typ(&p.x.typ, p.x.is_mut)));
        // For wrapper-bound params the bound applies to the inner value
        // via `.deref` (the wrapper itself has no numeric instance).
        let bound_value = if is_mut_ref_typ(&p.x.typ, p.x.is_mut) {
            LExpr::field_proj(LExpr::var(name.clone()), "deref")
        } else {
            LExpr::var(name.clone())
        };
        if let Some(pred) = type_bound_predicate(&bound_value, &p.x.typ) {
            // `h_<name>_bound` is a synthesized hypothesis name —
            // already a valid Lean identifier, no further
            // sanitization needed.
            out.push(LBinder::explicit(
                crate::lean_name::LeanName::synthetic(format!("h_{}_bound", name.as_str())),
                pred,
            ));
        }
    }
    out
}

/// `(<name> : Tactus.MutRef <inner>)` for each `LocalDeclKind::BorrowMut`
/// local. These are synthetic `MutRef<T>`-typed locals Verus
/// introduces around exec calls in new-mut-ref mode (#107):
/// `bump(&mut y)` lowers to
/// `let mut_ref: MutRef<u8>; assume(MutRefCurrent(mut_ref) == y);
///  bump(mut_ref); y = MutRefFuture(mut_ref);` — the synthetic
/// `mut_ref` has no body-level initializer, only the assume
/// constraining its pre-call value.
///
/// Without a binder, references to `mut_ref` would reach the renderer
/// as unresolved. Binding it at theorem level lets Lean treat it as
/// an ∀-bound variable, with the assume entering as a hypothesis.
///
/// **Wrapper-typed binder + body-shadow** (collapsed unified path):
/// The binder is `Tactus.MutRef T` (matching fn-param `&mut`s — see
/// `build_param_binders`). The body-deref shadow `let mut_ref :=
/// mut_ref.deref` makes subsequent `Var(mut_ref)` resolve to inner T,
/// which is what the SST rewrite produces after stripping
/// `MutRefCurrent`/`MutRefFuture`/`MutRefFinal` ops.
///
/// `#55`'s caller-side mut-arg machinery treats `Var(mut_ref)` as the
/// L-value at the call site, introducing a fresh existential for the
/// post-call inner value and Let-rebinding `mut_ref` to it after the
/// call's ensures Hyp. The binder here gives the PRE-call wrapper;
/// the body-shadow gives the PRE-call inner; the rebind shadows again
/// with the post-call inner.
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
        // Wrapper-typed binder (matches `param_binder_typ` for fn
        // `&mut` params). `decl.typ` is `TypX::MutRef(T)` so
        // `typ_to_expr(&decl.typ)` already renders `Tactus.MutRef T`.
        out.push(LBinder::explicit(name.clone(), typ_to_expr(&decl.typ)));
        // Type-bound predicate on the inner value (`.deref`), not the
        // wrapper — same convention as fn-param `&mut` bounds.
        let bound_value = LExpr::field_proj(LExpr::var(name.clone()), "deref");
        if let Some(pred) = type_bound_predicate(&bound_value, inner_typ) {
            out.push(LBinder::explicit(crate::lean_name::LeanName::synthetic(format!("h_{}_bound", name.as_str())), pred));
        }
    }
    out
}

/// `(h_req<i> : <req_i>)` for each requires clause.
///
/// `mut_param_names` carries the &mut params so we can rewrite their
/// mut-ref shapes uniformly to the canonical destination form. In the
/// `Body` phase (= reqs evaluated at fn entry), `MutRefCurrent(Var(x))`
/// and `VarAt(x, Pre)` both collapse to `Var(x)` because at fn entry
/// the param's pre-state IS its current state.
///
/// Each req body is then wrapped with `let x := x.deref` per mut-ref
/// param so that the binder name `x : Tactus.MutRef T` shadows to the
/// inner T inside the req — matching the same shadow the OblCtx
/// applies to the body's WP. This keeps `Var(x)` in the rewritten req
/// expression type-checking against inner T at the theorem-binder
/// position (which is outside the OblCtx wrap).
fn build_req_binders(
    fn_sst: &FunctionSst,
    check: &FuncCheckSst,
    mut_param_names: &HashSet<String>,
    fn_map: &FnMap,
) -> Vec<LBinder> {
    // Build the per-req let-shadow prefix once. Order matches
    // `build_param_binders`: each `&mut` param + each BorrowMut local
    // contributes one `let x := x.deref` frame; non-mut params don't
    // contribute. Inner-most shadow ends up applied last (innermost
    // in the let-chain), so source order is preserved.
    let mut shadow_pairs: Vec<crate::lean_name::LeanName> = Vec::new();
    for p in fn_sst.x.pars.iter().filter(|p| is_mut_ref_typ(&p.x.typ, p.x.is_mut)) {
        shadow_pairs.push(crate::lean_name::LeanName::from_var_ident(&p.x.name));
    }
    for decl in check.local_decls.iter() {
        if matches!(decl.kind, LocalDeclKind::BorrowMut) {
            shadow_pairs.push(crate::lean_name::LeanName::from_var_ident(&decl.ident));
        }
    }
    let wrap_with_shadows = |body: LExpr| -> LExpr {
        // Iterate in reverse so the first param's let ends up
        // outermost — matching `wrap_body_with_param_derefs`.
        let mut out = body;
        for name in shadow_pairs.iter().rev() {
            let wrapper = LExpr::var(name.clone());
            let inner = LExpr::field_proj(wrapper, "deref");
            out = LExpr::let_bind(name.clone(), inner, out);
        }
        out
    };
    check.reqs.iter().enumerate().map(|(i, req)| {
        // `Reqs` phase: at fn entry pre IS current, so `VarAt(x, Pre)`
        // and `MutRefCurrent(Var(x))` both collapse to `Var(x)`. The
        // per-req `let x := x.deref` shadow (applied below by
        // `wrap_with_shadows`) then resolves `Var(x)` to inner T at the
        // theorem-binder position (which is outside the OblCtx that
        // would otherwise bind `<x>_at_pre_tactus`).
        let rewritten = rewrite_mut_ref_in_exp(
            req,
            mut_param_names,
            RewritePhase::Reqs,
        );
        // The same `rewritten` shape was validated in `WpCtx::new` (the
        // same caller that just succeeded earlier in this fn), and
        // `rewrite_mut_ref_in_exp` is deterministic, so re-running here
        // produces an identical Exp. (`uN -> nat` casts are kept as
        // Clip{Nat} upstream by Verus's `--lean-backend` lowering.)
        // Use the fn_map-backed RenderCtx so trait method calls in the
        // requires get correct receiver coercion; the fn_map is already
        // a parameter of this function.
        let render_ctx = crate::expr_shared::RenderCtx::with_fn_map(fn_map);
        let rendered = sst_exp_to_ast_checked_with_ctx(&rewritten, &render_ctx)
            .expect("build_req_binders: req validated by WpCtx::new");
        LBinder::explicit(crate::lean_name::LeanName::synthetic(format!("h_req{}", i)), wrap_with_shadows(rendered))
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
    /// The third field is the dest local's declared SST typ. At walk
    /// time the rendered RHS is coerced to it via `coerce_lexpr` — Rust
    /// can auto-ref a `let` binding (e.g. `let copy = rest` where
    /// `rest : Box<Stack>` but `copy : &Box<Stack>`, taken so `copy`
    /// can pass to a `&`-param), and without the coercion `copy`'s Lean
    /// value would stay at `rest`'s typ while its SST typ claims the
    /// extra `&` — the over-deref bug behind `aliased_arg`. Coercing at
    /// the binder maintains the U2 invariant "a local's Lean value
    /// matches its SST typ", so every downstream `count_ref(copy.typ)`
    /// site is correct with no binder map. No-op when RHS typ == dest
    /// typ (the common case).
    Let(crate::lean_name::LeanName, crate::to_lean_sst_expr::Validated<'a>, Typ, Box<Wp<'a>>),

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

    /// Scoped proof block whose state effects are discarded —
    /// `StmX::DeadEnd`, Verus's desugar of `assert(P) by { <verus
    /// proof> }` / `assert forall … by { … }` (`vir/ast_to_sst.rs`
    /// ~2270): `DeadEnd(Block([Assume(require), …proof…,
    /// Assert(ensure)]))` followed by a separate
    /// `Assume(∀ vars, require ⇒ ensure)` that re-introduces the
    /// proven fact into the main flow — so this node needs no fact
    /// plumbing of its own. The body's obligations are emitted under
    /// the CURRENT context (outer lets/hyps stay visible inside the
    /// proof body); `after` continues under the original obl
    /// unchanged. Same discard shape as `ClosureBody` minus the param
    /// binders — a dedicated variant keeps `ClosureBody`'s contract
    /// closure-specific (F4, DESIGN-lean-all-proofs-followons.md).
    Scope {
        /// The `AssertByVar` skolems this block references — bound as
        /// ∀-binders on the scope's theorems by the walker (minus any
        /// already bound by an enclosing scope; nested assert-forall
        /// proof bodies legally reference outer skolems, and rebinding
        /// would shadow the hypothesis-carrying binder with a fresh
        /// unconstrained one).
        scope_vars: Vec<(&'a VarIdent, &'a Typ)>,
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
        /// Original Verus `Span` of the assertion site, cloned at
        /// `build_wp` time from the first ensure / require clause.
        /// Plumbed through to the emitted theorem's SpanMark so the
        /// rust_verify reporter attaches errors at the assert site.
        rust_span: Option<Span>,
        body: Box<Wp<'a>>,
    },

    /// `assert(P) by(<mode>) requires Q; { proof_stms };` for
    /// AssertQuery modes that re-use the normal renderer but
    /// override the discharger — currently `nonlinear_arith`
    /// (`nlinarith` from Mathlib).
    ///
    /// `primary` is the mode-specific tactic (e.g., `nlinarith`).
    /// The walker composes it with the *enclosing scope's* closer
    /// + a scope-specific failure message as
    /// `first | (intros; primary) | (<outer_closer>) | fail "<scope msg>"`.
    /// Falling back to the outer closer (rather than hardcoding
    /// `tactus_auto`) means a fn-level `#[verifier::tactus_tactic(
    /// "...")]` override still applies to the trivial theorems the
    /// recursive walk emits inside the scope (e.g., `True → ... →
    /// True` from `Wp::Done` leaves that `primary` is too strict
    /// to close). The trailing `fail` overrides Lean's
    /// last-failure-wins reporting so users see "scope: …" instead
    /// of the misdirected `tactus_auto` message.
    ///
    /// The walker also drops enclosing-scope Hyp frames (matching
    /// Verus's NonLinear query semantics — only requires + typ
    /// invariants are available) and attaches `preamble` to every
    /// theorem emitted under the scope. `after` walks under the
    /// ORIGINAL obl; Verus's `ast_to_sst` already pre-injected the
    /// outer `assert(req) / assume(ens)` block so the caller-side
    /// effect is upstream.
    ///
    /// `surface_label` names the surface-syntax that introduced the
    /// scope (e.g., `"by(nonlinear_arith)"`) — embedded in the
    /// composed closer's trailing `fail "<label> scope: could not
    /// close — …"` so the error names the right form. Set per-mode
    /// at `build_wp` time so future modes (Polyrith etc.) report
    /// their own surface syntax without touching the walker.
    AssertQuery {
        primary: Tactic,
        preamble: Vec<PreambleFragment>,
        surface_label: String,
        body: Box<Wp<'a>>,
        after: Box<Wp<'a>>,
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
///
/// Test-only: the un-coerced (`ret_coerce: None`) entry point. Production
/// always has a declared return typ to coerce against, so it calls
/// `lift_if_value_coerced` directly; this thin wrapper exists for the
/// unit tests that pin the bare lifting behaviour.
#[cfg(test)]
fn lift_if_value(e: &Exp, emit_leaf: &dyn Fn(LExpr) -> LExpr) -> LExpr {
    lift_if_value_coerced(e, None, &crate::expr_shared::RenderCtx::empty(), emit_leaf)
}

/// `lift_if_value` plus per-leaf return-typ coercion.
///
/// `ret_coerce: Some(rt)` coerces each actual returned-VALUE leaf from
/// its OWN Exp typ to `rt` (the declared return typ) before `emit_leaf`.
/// This is load-bearing for if-valued returns: `if c { **b } else { 0 }`
/// has branches of DIFFERENT typ (`&Box<u8>` vs `u8`), so coercing
/// against the whole-if typ (as an earlier version did) mis-fires — the
/// `**b` branch stayed `b` while the ensures reconciled to `b.deref.deref`,
/// a silent mismatch (pinned by `test_exec_return_if_wrapper_value_probe`).
/// Each leaf must coerce with its own typ. Let-RHS sub-positions pass
/// `None` (they aren't the return value); the let body / branches carry
/// `ret_coerce` onward. `None` everywhere reduces to the plain lift.
fn lift_if_value_coerced(
    e: &Exp,
    ret_coerce: Option<&Typ>,
    ctx: &crate::expr_shared::RenderCtx,
    emit_leaf: &dyn Fn(LExpr) -> LExpr,
) -> LExpr {
    // `e` was validated upstream: `Return` checks via `check_exp(e)`
    // before calling lift_if_value (sst_to_lean.rs:2793). Sub-
    // expressions are valid by structural induction; the
    // `sst_exp_to_ast_checked(...).expect(...)` calls below re-run
    // the deterministic validator and would only fire if the
    // validator drifted between the upstream check_exp and here.
    let coerce_leaf = |lexpr: LExpr, from_typ: &Typ| -> LExpr {
        match ret_coerce {
            Some(rt) => crate::expr_shared::coerce_lexpr(lexpr, from_typ, rt),
            None => lexpr,
        }
    };
    let peeled = peel_value_position(e);
    match &peeled.x {
        ExpX::If(cond, then_e, else_e) => {
            let c = sst_exp_to_ast_checked_with_ctx(cond, ctx)
                .expect("lift_if_value if-cond: sub of validated Exp tree");
            // Both branches are return values → carry `ret_coerce` so
            // each branch leaf coerces with its own typ.
            LExpr::and(
                LExpr::implies(c.clone(), lift_if_value_coerced(then_e, ret_coerce, ctx, emit_leaf)),
                LExpr::implies(LExpr::not(c), lift_if_value_coerced(else_e, ret_coerce, ctx, emit_leaf)),
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
                    return lift_if_value_coerced(&unfolded, ret_coerce, ctx, emit_leaf);
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
                    // `rhs` is the let-RHS, not the return value → `None`.
                    // `inner_body` IS the return value → carry `ret_coerce`.
                    lift_if_value_coerced(rhs, None, ctx, &|rhs_leaf| {
                        let name = name.clone();
                        lift_if_value_coerced(inner_body, ret_coerce, ctx, &|body_leaf| {
                            emit_leaf(LExpr::let_bind(name.clone(), rhs_leaf.clone(), body_leaf))
                        })
                    })
                } else {
                    // `inner_body` is the return value (rendered as-is for
                    // the match-shape) → coerce it to the ret typ.
                    let body_ast = coerce_leaf(
                        sst_exp_to_ast_checked_with_ctx(inner_body, ctx)
                            .expect("lift_if_value let-body: sub of validated Exp tree"),
                        &inner_body.typ,
                    );
                    lift_if_value_coerced(rhs, None, ctx, &|rhs_leaf| {
                        emit_leaf(LExpr::let_bind(name.clone(), rhs_leaf, body_ast.clone()))
                    })
                }
            } else {
                emit_leaf(coerce_leaf(
                    sst_exp_to_ast_checked_with_ctx(e, ctx)
                        .expect("lift_if_value bind-fallthrough: validated upstream"),
                    &e.typ,
                ))
            }
        }
        _ => emit_leaf(coerce_leaf(
            sst_exp_to_ast_checked_with_ctx(e, ctx)
                .expect("lift_if_value leaf: validated upstream"),
            &e.typ,
        )),
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
    ctx: &'a WpCtx<'a>,
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
            // BorrowMut elimination: drop the body's `Assign(user_local,
            // Var(borrow_mut_local))` linkage Assign. Phase 4 of the
            // matching call rebinds the user_local to the post-state
            // existential directly — emitting the let frame here would
            // capture the pre-call value of borrow_mut_local. See
            // `collect_borrow_mut_links` for the linkage discovery.
            if is_borrow_mut_linkage_assign(dest, rhs, &ctx.borrow_mut_links) {
                return Ok(after);
            }
            // Simple `x = e`: rebind `x` (mutation-as-let-shadowing).
            if let Some(ident) = extract_simple_var_ident(dest) {
                return Ok(Wp::Let(
                    crate::lean_name::LeanName::from_var_ident(ident),
                    crate::to_lean_sst_expr::Validated::check(rhs)?,
                    dest.typ.clone(),
                    Box::new(after),
                ));
            }
            // Field-path `x.f = e` / `t.0 = e`: same let-shadowing, but
            // rebind the ROOT var to a functional update of itself with the
            // leaf field replaced by `e` (`let x := { x with f := e }` /
            // tuple reconstruct). The rhs renders against the pre-rebind
            // root (the let's RHS sees the outer binding), so a `t.0 = t.1`
            // reads the old `t.1`. Reuses the same nesting as the
            // `&mut x.field` call-rebind. `Wp::LetRaw` because the update is
            // an already-rendered LExpr, not an SST Exp.
            if let Some((root, field_oprs)) = decompose_assign_lvalue(dest) {
                let rhs_lexpr = lower_validated_with_ctx(
                    &crate::to_lean_sst_expr::Validated::check(rhs)?,
                    &ctx.render_ctx(),
                );
                let update = build_nested_field_update(
                    LExpr::var(crate::lean_name::LeanName::from_var_ident(root)),
                    &field_oprs,
                    rhs_lexpr,
                );
                return Ok(Wp::LetRaw {
                    name: crate::lean_name::LeanName::from_var_ident(root),
                    value: update,
                    body: Box::new(after),
                });
            }
            Err(format!(
                "assignment with {} (got {:?}) is not yet supported",
                vir::tactus_messages::ASSIGN_NON_SIMPLE_LHS_TAG,
                dest.x
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
            // Coerce the returned value to the declared return typ via
            // `lift_if_value_coerced` — PER LEAF. Verus keeps a returned
            // `&`-value at its reference typ (e.g. `**b : &Box<u8>`), so
            // binding `let r := b` would give `r : Tactus.Ref (Box Int)`
            // while the ensures — reconciled at the structural binops —
            // expects inner `Int`. Doing the coercion at each leaf (not
            // against the whole expr's typ) is load-bearing for if-valued
            // returns, whose branches have distinct typs (see
            // `lift_if_value_coerced` doc + `_return_if_wrapper_value_probe`).
            // Pairs with the structural-binop operand reconciliation.
            let leaf = lift_if_value_coerced(e, ctx.ret_typ.as_ref(), &ctx.render_ctx(), &|e_ast| match ret_name {
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
            original_cond,
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
            original_cond,
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
        // User-syntax `assert(…) by(bit_vector)` — see the helper.
        StmX::AssertBitVector { requires, ensures } =>
            build_wp_assert_bit_vector(requires, ensures, after),
        // `assert(P) by { lean_tac }` / `proof { lean_tac }` /
        // `assert by(nonlinear_arith)` — dispatch on mode in the helper.
        StmX::AssertQuery { mode, typ_inv_exps: _, typ_inv_vars: _, body } =>
            build_wp_assert_query(mode, body, after, ctx, loop_stack),
        // Scoped proof block, effects discarded — `assert(P) by { … }`
        // / `assert forall … by { … }` in their Verus-proof-body form
        // (the raw-Lean-tactic form is `AssertQuery` above). The
        // block's own `Assert(ensure)` node carries the real
        // obligation, so the inner terminator is a trivially-true
        // leaf — there is no flow-through goal, and the enclosing
        // flow re-acquires the proven fact via the `Assume` statement
        // Verus emits AFTER the DeadEnd (part of `after`'s tree).
        // Matches the `StmX::ClosureInner` construction below.
        // `loop_stack`: EMPTY — break/continue can't legally cross an
        // assert-by boundary (mode checker), so a leak becomes
        // build_wp's existing clean error instead of silently jumping
        // to an outer loop's leaf. (F4,
        // DESIGN-lean-all-proofs-followons.md.)
        StmX::DeadEnd(block) => {
            let scope_vars = collect_assert_by_vars(block, ctx);
            let body =
                build_wp(block, Wp::Done(LExpr::lit_bool(true)), ctx, &LoopStack::Empty)?;
            Ok(Wp::Scope { scope_vars, body: Box::new(body), after: Box::new(after) })
        }
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

/// Build the Wp for a `StmX::AssertBitVector` — user-syntax
/// `assert(…) by(bit_vector)` (#111 / #130).
///
/// Bit-vector mode: render requires + ensures via the BitVec-mode
/// renderer (#130 first cut). u-typed variables get wrapped as
/// `BitVec.ofInt n x`, so the resulting LExpr's bitwise ops resolve
/// to BitVec instances and Lean's BitVec tactics (`decide`,
/// `simp [BitVec.*]`) can reason about the goal.
///
/// Note: we deliberately do NOT publish the ensures as an Int-mode
/// hypothesis to the body's ctx. Lean lacks an `HXor Int Int Int`
/// instance (and similar for `HAnd`/`HOr`), so an Int-mode `x ^^^ y`
/// doesn't typecheck. The bit_vector assertion verifies in BV mode;
/// users who need the fact in Int-mode body context can re-derive it
/// via `assert(P) by { ... }` with their own tactic. Future work
/// (#130 follow-up): either render bitwise ops via `Int.xor` etc.,
/// or add `HXor Int Int Int` instances in TactusPrelude that
/// delegate to the function form.
/// Collect the `AssertByVar`-kind locals (assert-forall skolems) that
/// `stm` references, in deterministic (name-sorted) order. Used by the
/// `StmX::DeadEnd` arm: these vars have no `Wp::Let` (Verus declares
/// them fn-wide, scoped syntactically to the assert-by block), so the
/// scope's theorems must ∀-bind them explicitly. Read-only use of the
/// map visitors — the `let _ =` discards the rebuilt trees (same idiom
/// as the synthetic-assume scan above).
fn collect_assert_by_vars<'a>(
    stm: &Stm,
    ctx: &WpCtx<'a>,
) -> Vec<(&'a VarIdent, &'a Typ)> {
    use vir::sst::ExpX as X;
    let mut used: std::collections::HashSet<VarIdent> = std::collections::HashSet::new();
    let _ = vir::sst_visitor::map_exps_in_stm_visitor(stm, &mut |e: &Exp| {
        let _ = vir::sst_visitor::map_exp_visitor(e, &mut |inner: &Exp| {
            match &inner.x {
                X::Var(v) | X::VarLoc(v) | X::VarAt(v, _) => {
                    used.insert(v.clone());
                }
                _ => {}
            }
            inner.clone()
        });
        e.clone()
    });
    let mut out: Vec<(&'a VarIdent, &'a Typ)> = ctx.assert_by_var_typs.iter()
        .filter(|(v, _)| used.contains(**v))
        .map(|(v, t)| (*v, *t))
        .collect();
    out.sort_by_key(|(v, _)| format!("{:?}", v));
    out
}

fn build_wp_assert_bit_vector<'a>(
    requires: &[Exp],
    ensures: &[Exp],
    after: Wp<'a>,
) -> Result<Wp<'a>, String> {
    let req_lexprs: Vec<LExpr> = requires.iter()
        .map(|r| crate::to_lean_sst_expr::sst_exp_to_bit_vector_ast(r))
        .collect::<Result<Vec<_>, _>>()?;
    let ens_lexprs: Vec<LExpr> = ensures.iter()
        .map(|e| crate::to_lean_sst_expr::sst_exp_to_bit_vector_ast(e))
        .collect::<Result<Vec<_>, _>>()?;
    let req_conj = and_all(req_lexprs);
    let ens_conj = and_all(ens_lexprs);
    // Use the first ensure's span when present — that's the
    // user's `assert(…) by(bit_vector)` site. Falls back to
    // the stm's span via the caller-side wrapping if absent.
    let rust_loc = ensures.first()
        .map(|e| format_rust_loc(&e.span))
        .or_else(|| requires.first().map(|r| format_rust_loc(&r.span)))
        .unwrap_or_default();
    let rust_span = ensures.first()
        .map(|e| e.span.clone())
        .or_else(|| requires.first().map(|r| r.span.clone()));
    Ok(Wp::AssertBitVector {
        req_conj,
        ens_conj,
        rust_loc,
        rust_span,
        body: Box::new(after),
    })
}

/// Build the Wp for a `StmX::AssertQuery`, dispatching on mode.
///
/// `AssertQueryMode::Tactus` is how `ast_to_sst` encodes an
/// `assert(P) by { lean_tac }` (or a `proof { lean_tac }`) inside a
/// `tactus_auto` fn (see `ExprX::AssertBy` handling there). We read
/// the verbatim Lean tactic text from the original file via the
/// `tactic_span` and produce a `Wp::AssertByTactus` node;
/// `walk_assert_by_tactus` then either emits a single theorem with
/// the user's tactic as the closer (`assert(P) by` form) or pushes
/// the tactic as a prefix applied via `<;>` to every body theorem
/// (`proof` form).
///
/// **Shape**: `body` is a single `StmX::Assert(_, _, P)` — the
/// asserted condition, produced by `ast_to_sst`'s Tactus-shortcut
/// emission. `typ_inv_*` are intentionally empty (other AssertQuery
/// modes use them for NonLinear/BitVector context). Extracting `P`
/// from `body` keeps `AssertQueryMode::Tactus` itself small — no
/// generic `Exp` field forcing derive-juggling on the enum.
///
/// `AssertQueryMode::NonLinear` is `assert by(nonlinear_arith)`.
/// `AssertQueryMode::BitVector` should never reach here — `ast_to_sst`
/// converts user `by(bit_vector)` to `StmX::AssertBitVector` upstream.
fn build_wp_assert_query<'a>(
    mode: &AssertQueryMode,
    body: &'a Stm,
    after: Wp<'a>,
    ctx: &'a WpCtx<'a>,
    loop_stack: &LoopStack<'_>,
) -> Result<Wp<'a>, String> {
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
        AssertQueryMode::NonLinear => {
            // Verus's `ast_to_sst` (vir/src/ast_to_sst.rs:2322)
            // builds the body as a Block: `[Assume(req)*,
            // proof_stms*, Assert(ens)*]`. The body is the
            // inner verification query (Verus's "separate query
            // for NonLinear" semantics). We recurse `build_wp`
            // on it with a `Done(LitBool(true))` terminator
            // (proof scope has no return value); the resulting
            // Wp tree carries all obligations the body
            // generates. The walker enters a new OblCtx scope
            // for `body_wp` that switches the closer to
            // `nlinarith` and drops enclosing-scope Hyps,
            // matching Verus's NonLinear semantics.
            let body_wp = build_wp(
                body,
                Wp::Done(LExpr::lit_true()),
                ctx,
                loop_stack,
            )?;
            Ok(Wp::AssertQuery {
                primary: Tactic::Named("nlinarith".to_string()),
                preamble: nonlinear_preamble_fragments(),
                surface_label: "by(nonlinear_arith)".to_string(),
                body: Box::new(body_wp),
                after: Box::new(after),
            })
        }
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
    ctx: &'a WpCtx<'a>,
) -> Result<Wp<'a>, String> {
    reject_unsupported_call_shapes(split)?;

    let (callee, spec_callee, callee_typ_args) =
        resolve_callee(fun, resolved_method, is_trait_default, typ_args, ctx)?;

    validate_call_arities(callee, args, callee_typ_args)?;

    let mut_args = build_call_mut_args(&callee.params, args, &ctx.mut_ref_locals, &ctx.borrow_mut_links)?;

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
    ctx: &'a WpCtx<'a>,
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
    // Resolve spec_callee structurally via the shared abstraction:
    // for TraitMethodImpl, redirect to the trait method decl (Verus
    // rejects impl-side `requires`, so the impl's spec is
    // empty/inherited); for all other kinds, specs live on the
    // callee itself. See `call_inlining` module for the canonical
    // definition.
    let spec_callee = crate::call_inlining::spec_source(callee, &ctx.fn_map)
        .map_err(|method| format!(
            "trait method decl `{:?}` for resolved impl `{:?}` not found in \
             the crate's function map — cross-crate trait calls are not yet \
             supported (#56 follow-up)",
            method.path, callee_fun.path,
        ))?;
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
#[derive(Clone)]
enum MutTargetRaw<'a> {
    Var(&'a VarIdent),
    /// `&mut <base>.<f1>.<f2>.…` field path, where each step is
    /// either a single-variant struct field or a tuple slot. Steps
    /// may interleave freely — `&mut s.tup.0`, `&mut t.0.f`,
    /// `&mut a.b.c` all live here. The per-step datatype kind
    /// (`Dt::Path` vs `Dt::Tuple`) is already carried on each
    /// `FieldOpr`; the rebind loop dispatches on it.
    ///
    /// `field_oprs` is in peel order — `field_oprs[0]` is the
    /// OUTERMOST `Field(_, ...)` we encountered (i.e., the
    /// deepest-mutated step, closest to the new value);
    /// `field_oprs[len-1]` is innermost (closest to the base).
    /// For `&mut a.b.c` it is `[c_opr, b_opr]`.
    Field { base: &'a VarIdent, field_oprs: Vec<&'a vir::ast::FieldOpr> },
}

fn extract_mut_target<'a>(
    e: &'a Exp,
    mut_ref_locals: &HashSet<String>,
    borrow_mut_links: &'a HashMap<String, VarIdent>,
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
    //
    // BorrowMut elimination: when the BorrowMut local has a known
    // user-local linkage (recorded in `borrow_mut_links` via the
    // body's `Assign(user_local, Var(borrow_mut_local))` forward-
    // forward statement), redirect the mut target to the user-local
    // directly. Phase 4 then rebinds the user-local to the post-state
    // existential, and the body's linkage Assign is dropped — see
    // `collect_borrow_mut_links` / `is_borrow_mut_linkage_assign`.
    if let ExpX::Var(ident) = &e.x {
        let san_name = sanitize(&ident.0);
        if mut_ref_locals.contains(&san_name) {
            // Linkage lookup uses `borrow_mut_key` (disambig-aware,
            // matches what `collect_borrow_mut_links` inserts) so
            // multi-mut-arg calls with same-base-name BorrowMut locals
            // stay distinct. SSA-renamed BorrowMut locals also resolve
            // via `resolve_borrow_mut_aliases`.
            if let Some(user_local) = borrow_mut_links.get(&borrow_mut_key(ident)) {
                return Some(MutTargetRaw::Var(user_local));
            }
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
    // Peel `Field` levels until we hit a Var/VarLoc base. Each step
    // is either a single-variant struct field (`Dt::Path` with
    // matching variant name) or a tuple slot (`Dt::Tuple` with a
    // numeric field name); the FieldOpr already carries the
    // discriminator, so the rebind loop dispatches on it directly.
    // Multi-variant enums and tuples with non-numeric fields fall
    // through to None.
    let mut field_oprs: Vec<&'a vir::ast::FieldOpr> = Vec::new();
    let mut cursor: &'a Exp = inner;
    loop {
        match &cursor.x {
            ExpX::Var(ident) | ExpX::VarLoc(ident) => {
                if field_oprs.is_empty() {
                    return Some(MutTargetRaw::Var(ident));
                }
                return Some(MutTargetRaw::Field { base: ident, field_oprs });
            }
            ExpX::UnaryOpr(UnaryOpr::Field(field_opr), base_exp) => {
                match &field_opr.datatype {
                    vir::ast::Dt::Path(path) => {
                        if field_opr.variant.as_str()
                            != crate::to_lean_type::short_name(path)
                        {
                            return None;
                        }
                    }
                    vir::ast::Dt::Tuple(_) => {
                        if field_opr.field.as_str().parse::<usize>().is_err() {
                            return None;
                        }
                    }
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
    borrow_mut_links: &'a HashMap<String, VarIdent>,
) -> Result<Vec<(usize, MutTargetRaw<'a>)>, String> {
    let mut mut_args: Vec<(usize, MutTargetRaw<'a>)> = Vec::new();
    for (i, (param, a)) in callee_params.iter().zip(args.iter()).enumerate() {
        // Recognize `&mut` params in both legacy mode (`is_mut: true`,
        // plain T typ) and new-mut-ref mode (`is_mut: false`,
        // `MutRef<T>` typ). The caller-side encoding for both modes
        // goes through #55's mut_args machinery — legacy via
        // Loc(VarLoc(_)) shapes, new-mut-ref via bare
        // Var(borrow_mut_local) shapes (#107). The shared
        // `is_mut_ref_typ` predicate in `expr_shared` keeps this site
        // in lockstep with `add_param_subst_entries` (the other
        // consumer that asks "is this param &mut?").
        if is_mut_ref_typ(&param.x.typ, param.x.is_mut) {
            match extract_mut_target(a, mut_ref_locals, borrow_mut_links) {
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
    original_cond: &'a Option<(Stm, Exp)>,
    body: &'a Stm,
    invs: &'a vir::sst::LoopInvs,
    decrease: &'a vir::sst::Exps,
    after: Wp<'a>,
    ctx: &'a WpCtx<'a>,
    outer_loop_stack: &LoopStack<'_>,
) -> Result<Wp<'a>, String> {
    // Per-loop-unique, per-lex-level d_old names. Verus's
    // `StmX::Loop::id` is the upstream-stable identifier per loop
    // instance; per-level index disambiguates lex tiers (#110).
    // Names finalised once we know `decrease.len()` after validation.
    // See `expr_shared.rs`'s "Reserved identifier conventions" —
    // Convention 1 + the gensym-mechanism-choice note.
    // `loop_isolation` defaults to true; users opt out via
    // `#[verifier::loop_isolation(false)]` on a loop, fn, module, or
    // crate. The false mode lets the body see the outer function's
    // context directly without restating it in invariants — useful
    // when invariants would be tedious to restate.
    //
    // Tactus's per-obligation encoding handles both modes uniformly:
    // every emitted theorem inherits the full accumulated `OblCtx`
    // (fn params, fn requires, prior lets/hyps), so the body's
    // obligations always see the outer ctx. The mod_vars are still
    // quantified-over (havoc'd) inside the body's ctx via
    // `push_mod_var_frames`, matching both Verus modes' "the
    // iteration could be any one" treatment.
    //
    // For `#127`'s acceptance of isolation=false, no encoding change
    // is needed — Tactus's body/after ctx is already isolation=false-
    // shaped. Tactus is therefore strictly more permissive than
    // Verus's isolation=true (proofs that rely on outer ctx beyond
    // what invs cover still verify in Tactus). Not unsoundness; the
    // outer ctx hyps are true facts. See DESIGN.md § "Loop-shape
    // restrictions".
    let _ = loop_isolation; // both modes accepted; flag preserved for future divergence
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
    // For Tactus #127: when `cond` is None but `original_cond` is Some,
    // Verus's break-lowering converted the while loop to a `loop { if
    // !c { break; } body }` shape. For Tactus's WP encoding we can
    // recover the cond:Some path: walk_loop pushes `c` in maintain
    // (under which the body's inserted if-not-c-break then-branch is
    // contradictorily unreachable, so its obligation discharges
    // vacuously) and pushes `¬c` in use_obl (recovering the natural-
    // exit fact). Matches Verus's isolation=false semantics for
    // post-loop reasoning.
    //
    // Soundness gates (refuse recovery, fall through to cond:None
    // encoding — user must encode post-loop facts via
    // `allow_complex_invariants` + loop `ensures`):
    //   * **single-break check**: if the user body has its own breaks
    //     alongside the inserted one, push `¬c` post-loop would be
    //     unsound (user breaks may fire while `c` is still true).
    //   * **unlabeled loop**: labeled loops would need cross-label
    //     break counting, deferred.
    //   * **empty cond_setup**: non-empty setup (cond with calls /
    //     short-circuits) would need scoping work for the temp
    //     bindings.
    let original_cond_recoverable = match original_cond {
        Some((orig_setup, _)) if cond.is_none() => {
            label.is_none()
                && matches!(&orig_setup.x, StmX::Block(ss) if ss.is_empty())
                && count_breaks_targeting_this_loop(body, None) == 1
        }
        _ => false,
    };
    let effective_cond: &'a Option<(Stm, Exp)> =
        if original_cond_recoverable { original_cond } else { cond };

    let (cond_exp_opt, cond_setup_wrap): (
        Option<Validated<'a>>,
        Option<(&'a Stm, Validated<'a>, LExpr)>,
    ) = match effective_cond {
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
    // Render invariants (the continue/break-leaf GOALS the body must
    // re-establish) with the fn's params PLUS the loop-modified locals
    // in `binder_typs` — so `out@` on a bare-bound modified local
    // wraps to `View::view (Tactus.Ref.mk out)` instead of coercing
    // off the lying auto-ref `a.typ`. Mirrors `walk_loop`'s `inv_rctx`
    // for the init/hyp side; both must agree
    // (BUG-call-arg-temp-claimed-typ.md).
    let mut inv_binder_typs: HashMap<VarIdent, Typ> = ctx.caller_param_typs.clone();
    for (ident, typ) in &modified_vars {
        inv_binder_typs.entry((*ident).clone()).or_insert_with(|| (*typ).clone());
    }
    let inv_rctx = crate::expr_shared::RenderCtx::with_fn_map(&ctx.fn_map)
        .with_binder_typs(&inv_binder_typs);
    let inv_marked = |(i, v): (&LoopInv, &crate::to_lean_sst_expr::Validated<'a>)| LExpr::span_mark(
        format_rust_loc(&i.inv.span),
        Some(i.inv.span.clone()),
        AssertKind::Obligation(ObligationKind::LoopInvariant),
        crate::to_lean_sst_expr::lower_with_ctx(v, &inv_rctx),
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
        Some(decrease[0].span.clone()),
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
            // A field-path assignment (`x.f = …`, `t.0 = …`) modifies its
            // ROOT var — fold it in alongside the simple-LHS case so the
            // root is tracked as modified (it gets rebound to a functional
            // update in `build_wp`). A field write is never an init.
            let ident = extract_simple_var_ident(dest)
                .or_else(|| decompose_assign_lvalue(dest).map(|(root, _)| root));
            if let Some(ident) = ident {
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

/// Count `BreakOrContinue { is_break: true }` statements in `body`
/// that target THIS loop. Used by `build_wp_loop`'s `original_cond`
/// recovery (Tactus #127) — we can only treat Verus's break-lowered
/// while as a cond:Some shape if the inserted break (the one Verus's
/// lowering put at body[0..1]) is the ONLY break targeting this loop.
///
/// Targeting rules:
/// * Unlabeled break inside this loop (not inside a nested loop) →
///   targets this loop. Counts.
/// * Unlabeled break inside a nested loop → targets the nested loop.
///   Does NOT count for the outer.
/// * Labeled break with this loop's label → targets this loop. Counts.
/// * Labeled break with a different label → targets some outer loop.
///   Does NOT count.
///
/// `this_loop_label` is the current loop's label (None if unlabeled).
/// `inside_nested_loop` is the state we track during recursion.
fn count_breaks_targeting_this_loop(body: &Stm, this_loop_label: Option<&str>) -> usize {
    fn walk(stm: &Stm, this_label: Option<&str>, inside_nested: bool) -> usize {
        match &stm.x {
            StmX::BreakOrContinue { label, is_break } => {
                if !*is_break {
                    return 0;
                }
                match (label.as_deref(), this_label) {
                    (None, _) => {
                        // Unlabeled break targets innermost enclosing
                        // loop. Counts only if we're not in a nested loop.
                        if inside_nested { 0 } else { 1 }
                    }
                    (Some(l), Some(this_l)) if l == this_l => 1,
                    _ => 0, // labeled break for some other loop
                }
            }
            StmX::Block(stms) => {
                stms.iter().map(|s| walk(s, this_label, inside_nested)).sum()
            }
            StmX::If(_, t, e) => {
                let tc = walk(t, this_label, inside_nested);
                let ec = e.as_ref().map_or(0, |e| walk(e, this_label, inside_nested));
                tc + ec
            }
            StmX::Loop { body, .. } => {
                // Inside a nested loop: unlabeled breaks target the
                // nested loop, but labeled ones with `this_label`
                // still target us.
                walk(body, this_label, true)
            }
            _ => 0,
        }
    }
    walk(body, this_loop_label, false)
}

pub(crate) fn extract_simple_var_ident<'a>(e: &'a Exp) -> Option<&'a VarIdent> {
    match &e.x {
        ExpX::Var(ident) | ExpX::VarLoc(ident) => Some(ident),
        ExpX::Loc(inner) => extract_simple_var_ident(inner),
        _ => None,
    }
}

/// Decompose an assignment L-value `dest` into its root variable and the
/// field-projection path (peel order, `[0]` = leaf-most field), e.g.
/// `(*h).v` → `(h, [Holder.v])` and `t.0` → `(t, [Tuple.0])`. Peels the
/// transparent wrappers Verus inserts around L-values (`Loc` / `Unbox` /
/// `Box` / `CoerceMode` / `Trigger`). Returns `None` for shapes that
/// aren't a chain of struct/tuple field accesses bottoming out at a Var
/// (those stay rejected by `StmX::Assign`). Mirrors `extract_mut_target`'s
/// field walk — same single-variant-struct / numeric-tuple gate — minus
/// the call-site BorrowMut handling, since an assignment dest never
/// carries that indirection.
fn decompose_assign_lvalue<'a>(dest: &'a Exp) -> Option<(&'a VarIdent, Vec<&'a vir::ast::FieldOpr>)> {
    let mut oprs: Vec<&'a vir::ast::FieldOpr> = Vec::new();
    let mut cur = dest;
    loop {
        cur = peel_transparent(cur);
        match &cur.x {
            ExpX::Loc(inner) => cur = inner,
            ExpX::UnaryOpr(UnaryOpr::Field(opr), base) => {
                match &opr.datatype {
                    vir::ast::Dt::Path(path) => {
                        if opr.variant.as_str() != crate::to_lean_type::short_name(path) {
                            return None; // multi-variant enum field — not supported
                        }
                    }
                    vir::ast::Dt::Tuple(_) => {
                        if opr.field.as_str().parse::<usize>().is_err() {
                            return None;
                        }
                    }
                }
                oprs.push(opr);
                cur = base;
            }
            ExpX::Var(ident) | ExpX::VarLoc(ident) => {
                return if oprs.is_empty() { None } else { Some((ident, oprs)) };
            }
            _ => return None,
        }
    }
}

/// Build the inside-out functional-update value for a field-path
/// assignment / rebind: given the root local's expr, the field path
/// (peel order, `[0]` = leaf-most), and the new value at the leaf,
/// produce the whole new root value. Each level is a Lean structure
/// update (`{ base with f := … }`) for a `Dt::Path` step or an explicit
/// ctor (`(base.0, …, value, …)`) for a `Dt::Tuple` step; steps may
/// interleave (`&mut s.tup.0`). Shared by the `&mut x.field` call-rebind
/// (`push_post_call_frames`) and the `x.field = e` assignment
/// (`build_wp`'s `StmX::Assign`).
fn build_nested_field_update(
    local_expr: LExpr,
    field_oprs: &[&vir::ast::FieldOpr],
    leaf_value: LExpr,
) -> LExpr {
    // `field_oprs[0]` is the leaf-most step; top-to-bottom (base→leaf) is
    // the reverse.
    let oprs_ttb: Vec<&vir::ast::FieldOpr> = field_oprs.iter().rev().copied().collect();
    let mut current = leaf_value;
    for i in (0..oprs_ttb.len()).rev() {
        let mut base = local_expr.clone();
        for prior in &oprs_ttb[..i] {
            base = crate::expr_shared::field_proj_opr(base, prior);
        }
        let opr = oprs_ttb[i];
        current = match &opr.datatype {
            vir::ast::Dt::Path(_) => LExpr::new(ExprNode::StructUpdate {
                base: Box::new(base),
                // `Dt::Path` always yields a field accessor (never the 1-tuple
                // identity case, which is `Dt::Tuple`).
                updates: vec![(
                    crate::expr_shared::field_access_name(opr)
                        .expect("Dt::Path field always has a Lean accessor"),
                    current,
                )],
            }),
            vir::ast::Dt::Tuple(arity) => {
                let index: usize = opr.field.as_str().parse()
                    .expect("tuple index validated at decompose time");
                let new_value = current;
                let elems: Vec<LExpr> = (0..*arity)
                    .map(|j| if j == index {
                        new_value.clone()
                    } else {
                        LExpr::field_proj(
                            base.clone(),
                            crate::expr_shared::tuple_field_accessor(*arity, j),
                        )
                    })
                    .collect();
                LExpr::tuple(elems)
            }
        };
    }
    current
}

/// Verus injects synthetic params (`no%param`, etc.) with `%` in the
/// name for zero-arg functions and a few internal cases. They have no
/// user-visible semantics and must be dropped from the theorem binders.
fn is_synthetic_param(p: &Par) -> bool {
    p.x.name.0.contains('%')
}

#[cfg(test)]
#[path = "tests/sst_to_lean.rs"]
mod tests;
