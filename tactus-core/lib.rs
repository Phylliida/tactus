//! tactus-core: reference-semantics mirror types (bootstrap N2 / W1).
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
//!   One-way nesting (GoalList → GoalData) is fine.
//! * Every recursive spec fn carries `#[verifier::structural_decreases]`
//!   so the emitted defs kernel-compute (decide/rfl) with an empty
//!   axiom closure.
//! * Stage A (W2): expressions, types, locals, and binder names
//!   embedded in statements are OPAQUE LEAF IDS (u64) resolved through
//!   the serializer's side table of production-rendered Lean terms.
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

// ── Statements: the Wp-input mirror (stage-A subset) ────────────────

pub enum StmData {
    /// StmX::Assert — obligation leaf.
    Assert(u64),
    /// StmX::Assume.
    Assume(u64),
    /// StmX::Assign — (dest local leaf, rhs leaf).
    Assign(u64, u64),
    /// StmX::Call, contract view: instantiated requires (obligations)
    /// and ensures (assumptions after the call).
    Call { reqs: Box<LeafList>, enss: Box<LeafList> },
    /// StmX::DeadEnd — verify inside, discard facts after.
    DeadEnd(Box<StmData>),
    /// StmX::Return — the ensures-instantiation leaf.
    Ret(u64),
    /// StmX::If — (cond leaf, then, else); absent else = Skip.
    If(u64, Box<StmData>, Box<StmData>),
    /// StmX::Loop — invariant leaves, condition leaf, body.
    Loop { invs: Box<LeafList>, cond: u64, body: Box<StmData> },
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
pub open spec fn stm_size(s: StmData) -> nat
    decreases s
{
    match s {
        StmData::Assert(_e) => 1,
        StmData::Assume(_e) => 1,
        StmData::Assign(_d, _r) => 1,
        StmData::Call { reqs, enss } => 1 + leaf_len(*reqs) + leaf_len(*enss),
        StmData::DeadEnd(b) => 1 + stm_size(*b),
        StmData::Ret(_e) => 1,
        StmData::If(_c, t, e) => 1 + stm_size(*t) + stm_size(*e),
        StmData::Loop { invs, cond: _, body } => 1 + leaf_len(*invs) + stm_size(*body),
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

// ── In-crate kernel-computation sanity (decide через structural) ────

proof fn skeleton_kernel_computes()
    ensures
        stm_size(StmData::Seq(
            Box::new(StmData::Assert(0)),
            Box::new(StmData::If(1, Box::new(StmData::Skip), Box::new(StmData::Ret(2)))),
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

} // verus!
