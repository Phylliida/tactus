//! tactus-core: reference-semantics mirror types (bootstrap N2 / N2.1 / W1).
//!
//! These datatypes ARE the certificate vocabulary: their crate-defs
//! emission produces the Lean inductives that (a) the SST serializer
//! (N3) targets when printing per-fn SST literals and (b) the reference
//! WP (W2) consumes and produces. Single source of truth — no
//! hand-written Lean mirror, no O2 sync problem.
//!
//! Design constraints (probe-validated, DESIGN-bootstrap.md §11-12):
//! * OWN datatypes only — never Seq/Map (opaque axiom types: no match,
//!   no kernel reduction).
//! * No MUTUAL recursion between datatypes: `structural_decreases`
//!   covers only single-fn recursion, so statement sequencing is
//!   binary `Seq`/`Skip` (matching WP composition) instead of a
//!   statement list — the one cycle a Block list would create.
//!   One-way nesting (StmData → BinderList/LeafList, GoalList → GoalData)
//!   is fine.
//! * Every recursive spec fn carries `#[verifier::structural_decreases]`
//!   so the emitted defs kernel-compute (decide/rfl) with an empty
//!   axiom closure.
//! * Stage A (W2): expressions, types, locals, and binder names
//!   embedded in statements are OPAQUE LEAF IDS (u64) resolved through
//!   the serializer's side table of production-rendered Lean terms.
//!
//! N2.1 amendments (DESIGN-W2-refwp.md §0 / §2.1 — the fields refWp's
//! equations need, added BEFORE the serializer freezes the literal shape):
//! * `If` carries a rendered `¬cond` leaf (the else-branch hypothesis;
//!   refWp cannot synthesize leaf ids).
//! * `Loop` carries a `neg_cond` leaf and a `BinderList` of loop-state
//!   binders (the maintain/use telescopes quantify over the modified
//!   locals — production computes the set, the literal must carry it).
//! * `Call` carries the result binder `dest` + its `dest_typ` leaf
//!   (ensures-hypotheses bind the call result).
//! * `Ret` carries a `LeafList` — one instantiated-ensures leaf per
//!   postcondition, rendered at the return site.
//! * `FnCtxData` (context seed for refWp): typ-param telescope, value
//!   params, per-param optional bound-hyp leaves, requires, ensures.
//! * `FrameList` / `CtxFrame`: the ONE ordered goal-spine frame the
//!   worker folds (interleaved binders/hyps/lets — three parallel lists
//!   cannot reproduce `∀x, h → let y := e; h2 → …` ordering; DESIGN
//!   §2.1 review fix).
//!
//! Covered vir::sst::StmX subset (tripwire test:
//! lean_verify/src/tests/bootstrap_coverage.rs): Assert, Assume,
//! Assign, Call (contract view), DeadEnd, Return, If, Loop, Block (as
//! Seq/Skip). Uncovered (stage B+): AssertBitVector, AssertQuery,
//! AssertCompute, Fuel, RevealString, BreakOrContinue, OpenInvariant,
//! ClosureInner, Air.
//!
//! Canonical check (live Lean, package gate — the M6.5 default):
//!   TACTUS_LEAN_OUT=$PWD/out ../source/target-verus/release/verus \
//!     --crate-type=lib --lean-backend --lean-all-proofs lib.rs

use vstd::prelude::*;

verus! {

// ── Leaf lists (self-recursive only) ────────────────────────────────

pub enum LeafList {
    Nil,
    Cons(u64, Box<LeafList>),
}

// ── Binder lists: (binder id, typ/kind leaf) pairs, self-recursive ──
// Reused for value-param telescopes, typ-param telescopes (kind leaf in
// the second slot), and Loop loop-state binders.

pub enum BinderList {
    Nil,
    Cons(u64, u64, Box<BinderList>),
}

// ── Per-param optional bound-hypothesis leaves ──────────────────────
// Parallel to `FnCtxData.params`. `NoBound` = this param has no range
// hypothesis (e.g. a datatype-typed param); `Bound(leaf)` = the rendered
// `h_x_bound` leaf for an int-typed param (P6/P7). Distinct constructors
// rather than a sentinel leaf id, since 0 is a valid interned leaf.

pub enum ParamBoundList {
    Nil,
    NoBound(Box<ParamBoundList>),
    Bound(u64, Box<ParamBoundList>),
}

// ── Statements: the Wp-input mirror (stage-A subset) ────────────────

pub enum StmData {
    /// StmX::Assert — obligation leaf.
    Assert(u64),
    /// StmX::Assume.
    Assume(u64),
    /// StmX::Assign — (dest local leaf, rhs leaf).
    Assign(u64, u64),
    /// StmX::Call, contract view: instantiated requires (obligations)
    /// and ensures (assumptions after the call), plus the result binder
    /// `dest` and its type leaf `dest_typ` (frameAfter binds the result).
    Call { reqs: Box<LeafList>, enss: Box<LeafList>, dest: u64, dest_typ: u64 },
    /// StmX::DeadEnd — verify inside, discard facts after.
    DeadEnd(Box<StmData>),
    /// StmX::Return — one instantiated-ensures obligation leaf per
    /// postcondition (rendered at the return site).
    Ret(Box<LeafList>),
    /// StmX::If — (cond leaf, ¬cond leaf, then, else); absent else = Skip.
    /// The `neg_cond` leaf is the RENDERED else-branch hypothesis text.
    If(u64, u64, Box<StmData>, Box<StmData>),
    /// StmX::Loop — invariant leaves, condition leaf, ¬condition leaf,
    /// loop-state binders (the modified locals the telescopes quantify
    /// over), body.
    Loop { invs: Box<LeafList>, cond: u64, neg_cond: u64, binders: Box<BinderList>, body: Box<StmData> },
    /// Empty StmX::Block.
    Skip,
    /// StmX::Block, right-nested pairwise — avoids the StmData/StmList
    /// mutual-recursion cycle and matches WP composition:
    /// wp(s1; s2, post) = wp(s1, wp(s2, post)).
    Seq(Box<StmData>, Box<StmData>),
}

// ── Goals: the refWp output shape ───────────────────────────────────

pub enum GoalData {
    /// A rendered obligation leaf.
    Leaf(u64),
    /// hypothesis leaf → goal.
    Imp(u64, Box<GoalData>),
    /// (binder id, typ leaf, body) — ∀-introduction.
    All(u64, u64, Box<GoalData>),
    /// (binder id, value leaf, body) — let-binding.
    Let(u64, u64, Box<GoalData>),
}

/// One-way nesting (GoalList → GoalData, never back): plain recursion.
pub enum GoalList {
    Nil,
    Cons(Box<GoalData>, Box<GoalList>),
}

// ── The refWp context frame (the ONE ordered goal spine) ────────────
// `CtxFrame` is a SINGLE ordered entry list, NOT three parallel lists:
// the production telescope interleaves binders, hypotheses, and lets
// (`∀ x, h → let y := e; h2 → …`) and three separate lists cannot
// reproduce the interleave order (DESIGN-W2-refwp.md §2.1 review fix).
// wpStm folds this frame entry-by-entry around each obligation leaf.

pub enum FrameList {
    FNil,
    /// (binder id, typ leaf, tail) — ∀-binder in the spine.
    FBind(u64, u64, Box<FrameList>),
    /// (hyp leaf, tail) — an implication hypothesis in the spine.
    FHyp(u64, Box<FrameList>),
    /// (binder id, value leaf, tail) — a let-binding in the spine.
    FLet(u64, u64, Box<FrameList>),
}

pub type CtxFrame = FrameList;

// ── The refWp seed context (per-fn signature data) ──────────────────
// Not recursive: holds other datatypes by value. `typ_params` reuses
// BinderList with the kind leaf in the second slot; instance binders
// (`[Nonempty A]`) ride as ordinary entries with distinguished kind
// leaves. `param_bounds` is parallel to `params`.

pub struct FnCtxData {
    pub typ_params: BinderList,
    pub params: BinderList,
    pub param_bounds: ParamBoundList,
    pub reqs: LeafList,
    pub enss: LeafList,
}

// ── Skeleton spec fns (all structural, all kernel-computable) ───────

#[verifier::structural_decreases]
pub open spec fn leaf_len(l: LeafList) -> nat
    decreases l
{
    match l {
        LeafList::Nil => 0,
        LeafList::Cons(_h, t) => 1 + leaf_len(*t),
    }
}

#[verifier::structural_decreases]
pub open spec fn binder_len(b: BinderList) -> nat
    decreases b
{
    match b {
        BinderList::Nil => 0,
        BinderList::Cons(_id, _typ, t) => 1 + binder_len(*t),
    }
}

#[verifier::structural_decreases]
pub open spec fn param_bound_len(p: ParamBoundList) -> nat
    decreases p
{
    match p {
        ParamBoundList::Nil => 0,
        ParamBoundList::NoBound(t) => 1 + param_bound_len(*t),
        ParamBoundList::Bound(_leaf, t) => 1 + param_bound_len(*t),
    }
}

#[verifier::structural_decreases]
pub open spec fn frame_len(f: FrameList) -> nat
    decreases f
{
    match f {
        FrameList::FNil => 0,
        FrameList::FBind(_id, _typ, t) => 1 + frame_len(*t),
        FrameList::FHyp(_h, t) => 1 + frame_len(*t),
        FrameList::FLet(_id, _v, t) => 1 + frame_len(*t),
    }
}

#[verifier::structural_decreases]
pub open spec fn stm_size(s: StmData) -> nat
    decreases s
{
    match s {
        StmData::Assert(_e) => 1,
        StmData::Assume(_e) => 1,
        StmData::Assign(_d, _r) => 1,
        StmData::Call { reqs, enss, dest: _, dest_typ: _ } => 1 + leaf_len(*reqs) + leaf_len(*enss),
        StmData::DeadEnd(b) => 1 + stm_size(*b),
        StmData::Ret(es) => 1 + leaf_len(*es),
        StmData::If(_c, _nc, t, e) => 1 + stm_size(*t) + stm_size(*e),
        StmData::Loop { invs, cond: _, neg_cond: _, binders, body } =>
            1 + leaf_len(*invs) + binder_len(*binders) + stm_size(*body),
        StmData::Skip => 1,
        StmData::Seq(a, b) => 1 + stm_size(*a) + stm_size(*b),
    }
}

#[verifier::structural_decreases]
pub open spec fn goal_size(g: GoalData) -> nat
    decreases g
{
    match g {
        GoalData::Leaf(_e) => 1,
        GoalData::Imp(_h, b) => 1 + goal_size(*b),
        GoalData::All(_x, _t, b) => 1 + goal_size(*b),
        GoalData::Let(_x, _v, b) => 1 + goal_size(*b),
    }
}

#[verifier::structural_decreases]
pub open spec fn goal_count(gs: GoalList) -> nat
    decreases gs
{
    match gs {
        GoalList::Nil => 0,
        GoalList::Cons(_g, t) => 1 + goal_count(*t),
    }
}

/// Value-param arity of a context (non-recursive projection).
pub open spec fn fnctx_arity(c: FnCtxData) -> nat {
    binder_len(c.params)
}

// ── In-crate kernel-computation sanity (decide через structural) ────

proof fn skeleton_kernel_computes()
    ensures
        stm_size(StmData::Seq(
            Box::new(StmData::Assert(0)),
            Box::new(StmData::If(1, 2, Box::new(StmData::Skip),
                Box::new(StmData::Ret(Box::new(LeafList::Nil))))),
        )) == 5,
        goal_size(GoalData::Imp(7, Box::new(GoalData::All(8, 9, Box::new(GoalData::Leaf(10)))))) == 3,
        leaf_len(LeafList::Cons(1, Box::new(LeafList::Cons(2, Box::new(LeafList::Nil))))) == 2
by {
    decide
}

proof fn seq_size_unfolds()
    ensures
        stm_size(StmData::Seq(Box::new(StmData::Skip), Box::new(StmData::Skip))) ==
            1 + stm_size(StmData::Skip) + stm_size(StmData::Skip),
        goal_count(GoalList::Cons(
            Box::new(GoalData::Leaf(0)),
            Box::new(GoalList::Cons(Box::new(GoalData::Leaf(1)), Box::new(GoalList::Nil))),
        )) == 2
by {
    decide
}

// N2.1: the amended shapes kernel-compute (If/Loop/Call/Ret + the new
// BinderList/ParamBoundList/FrameList/FnCtxData vocabulary).
proof fn amended_shapes_kernel_compute()
    ensures
        // Loop: 1 + |invs=1| + |binders=1| + size(Skip=1) == 4
        stm_size(StmData::Loop {
            invs: Box::new(LeafList::Cons(0, Box::new(LeafList::Nil))),
            cond: 1,
            neg_cond: 2,
            binders: Box::new(BinderList::Cons(3, 4, Box::new(BinderList::Nil))),
            body: Box::new(StmData::Skip),
        }) == 4,
        // Call: 1 + |reqs=1| + |enss=0| == 2
        stm_size(StmData::Call {
            reqs: Box::new(LeafList::Cons(0, Box::new(LeafList::Nil))),
            enss: Box::new(LeafList::Nil),
            dest: 5,
            dest_typ: 6,
        }) == 2,
        // Ret: 1 + |es=2| == 3
        stm_size(StmData::Ret(Box::new(LeafList::Cons(0,
            Box::new(LeafList::Cons(1, Box::new(LeafList::Nil))))))) == 3,
        binder_len(BinderList::Cons(1, 2, Box::new(BinderList::Nil))) == 1,
        param_bound_len(ParamBoundList::Bound(5,
            Box::new(ParamBoundList::NoBound(Box::new(ParamBoundList::Nil))))) == 2,
        frame_len(FrameList::FBind(1, 2,
            Box::new(FrameList::FHyp(3, Box::new(FrameList::FLet(4, 5, Box::new(FrameList::FNil))))))) == 3,
        // FnCtxData projection: 2 value params.
        fnctx_arity(FnCtxData {
            typ_params: BinderList::Cons(0, 100, Box::new(BinderList::Nil)),
            params: BinderList::Cons(1, 101,
                Box::new(BinderList::Cons(2, 102, Box::new(BinderList::Nil)))),
            param_bounds: ParamBoundList::Bound(200,
                Box::new(ParamBoundList::NoBound(Box::new(ParamBoundList::Nil)))),
            reqs: LeafList::Nil,
            enss: LeafList::Cons(300, Box::new(LeafList::Nil)),
        }) == 2
by {
    decide
}

} // verus!
