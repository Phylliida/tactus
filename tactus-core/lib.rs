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
// hypothesis (e.g. a datatype-typed param); `Bound(name, prop)` = an
// int-typed param's range hypothesis, rendered by production as a NAMED
// ∀-binder `∀ (h_x_bound : 0≤x∧x<2^64)` — `name` is the `h_<param>_bound`
// name leaf, `prop` the range-predicate leaf (finding-2). Distinct
// constructors rather than a sentinel leaf id, since 0 is a valid
// interned leaf.

pub enum ParamBoundList {
    Nil,
    NoBound(Box<ParamBoundList>),
    Bound(u64, u64, Box<ParamBoundList>),
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
    // `reqs`: (h_req<i> name leaf, req-prop leaf) pairs. Production renders
    // each requires as a NAMED ∀-binder `∀ (h_req0 : x < 1000)` (finding-2),
    // so `reqs` is a `BinderList` (name, prop) — folded via binders_to_frame
    // into `FBind` spine entries, not anonymous `FHyp`s.
    pub reqs: BinderList,
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
        ParamBoundList::Bound(_name, _prop, t) => 1 + param_bound_len(*t),
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
// ── W2a: the reference WP (refWp) and its first-order workers ───────
// DESIGN-W2-refwp.md §2. These emitted defs ARE the checker the
// certificate runs. Authored snake_case (file convention); the DESIGN
// names map as: close, frame_after=`frameAfter`, wp_stm=`wpStm`,
// ref_wp=`refWp`, goal_eq/goals_eq. Every recursive worker is single-
// datatype structural recursion (no spec_fn continuations — closures are
// trigger/kernel-hostile, memory: closure-identity arc) with
// `#[verifier::structural_decreases]` so the defs kernel-compute.
//
// Shape decisions (grounded in the on-disk fixture certs — see the W2a
// board writeup for the full empirical read):
//  * The frame IS the goal spine (DESIGN §2.1): `close` folds it entry-
//    by-entry around one obligation leaf. First (outermost) frame entry =
//    outermost GoalData constructor.
//  * `StmData::Assert(e)` emits `close(frame, e)` AND `frame_after` adds
//    hyp `e`: the fixture certs show TWO `Imp e` after an Assert/Assume
//    pair — the Assert's forward hyp plus the following Assume's hyp.
//  * Signature bound-hyps and requires render as NAMED ∀-binders
//    (`All 19 2` = ∀ (h_x_bound : …), `All 17 5` = ∀ (h_req0 : …)), NOT
//    arrows (finding-2, LANDED). `ParamBoundList::Bound` now carries the
//    `h_<param>_bound` name leaf and `FnCtxData.reqs` is a `BinderList` of
//    (h_req<i>, prop); seed_params/seed_frame fold both via `FBind` → `All`.

// Concatenate two frames (structural on the first).
#[verifier::structural_decreases]
pub open spec fn frame_append(f: FrameList, g: FrameList) -> FrameList
    decreases f
{
    match f {
        FrameList::FNil => g,
        FrameList::FBind(id, typ, t) => FrameList::FBind(id, typ, Box::new(frame_append(*t, g))),
        FrameList::FHyp(h, t) => FrameList::FHyp(h, Box::new(frame_append(*t, g))),
        FrameList::FLet(id, v, t) => FrameList::FLet(id, v, Box::new(frame_append(*t, g))),
    }
}

// A LeafList rendered as a chain of anonymous FHyp entries.
#[verifier::structural_decreases]
pub open spec fn hyps_of_leaves(l: LeafList) -> FrameList
    decreases l
{
    match l {
        LeafList::Nil => FrameList::FNil,
        LeafList::Cons(h, t) => FrameList::FHyp(h, Box::new(hyps_of_leaves(*t))),
    }
}

// A BinderList rendered as a chain of FBind entries.
#[verifier::structural_decreases]
pub open spec fn binders_to_frame(b: BinderList) -> FrameList
    decreases b
{
    match b {
        BinderList::Nil => FrameList::FNil,
        BinderList::Cons(id, typ, t) => FrameList::FBind(id, typ, Box::new(binders_to_frame(*t))),
    }
}

// Fold a frame around an obligation leaf → one GoalData spine.
#[verifier::structural_decreases]
pub open spec fn close(f: FrameList, obligation: u64) -> GoalData
    decreases f
{
    match f {
        FrameList::FNil => GoalData::Leaf(obligation),
        FrameList::FBind(id, typ, t) => GoalData::All(id, typ, Box::new(close(*t, obligation))),
        FrameList::FHyp(h, t) => GoalData::Imp(h, Box::new(close(*t, obligation))),
        FrameList::FLet(id, v, t) => GoalData::Let(id, v, Box::new(close(*t, obligation))),
    }
}

// close(frame, ·) mapped over a LeafList → one goal per leaf (Call reqs,
// Ret enss, Loop init/maintain invariants).
#[verifier::structural_decreases]
pub open spec fn close_each(f: FrameList, l: LeafList) -> GoalList
    decreases l
{
    match l {
        LeafList::Nil => GoalList::Nil,
        LeafList::Cons(h, t) => GoalList::Cons(Box::new(close(f, h)), Box::new(close_each(f, *t))),
    }
}

// Append two goal lists (the `++` of DESIGN §2.1).
#[verifier::structural_decreases]
pub open spec fn goals_append(a: GoalList, b: GoalList) -> GoalList
    decreases a
{
    match a {
        GoalList::Nil => b,
        GoalList::Cons(h, t) => GoalList::Cons(h, Box::new(goals_append(*t, b))),
    }
}

// frameAfter: the frame extension visible to whatever FOLLOWS `s`.
// (DESIGN §2.2. `If` join frames are NOT merged at stage A: the
// continuation sees the pre-if frame — §5.1.)
#[verifier::structural_decreases]
pub open spec fn frame_after(f: FrameList, s: StmData) -> FrameList
    decreases s
{
    match s {
        StmData::Assert(e) => frame_append(f, FrameList::FHyp(e, Box::new(FrameList::FNil))),
        StmData::Assume(e) => frame_append(f, FrameList::FHyp(e, Box::new(FrameList::FNil))),
        StmData::Assign(x, rhs) => frame_append(f, FrameList::FLet(x, rhs, Box::new(FrameList::FNil))),
        StmData::Call { reqs: _, enss, dest, dest_typ } =>
            frame_append(f, FrameList::FBind(dest, dest_typ, Box::new(hyps_of_leaves(*enss)))),
        StmData::DeadEnd(_b) => f,          // facts discarded
        StmData::Ret(_es) => f,             // control does not continue
        StmData::If(_c, _nc, _t, _e) => f,  // stage A: join frames not merged (§5.1)
        StmData::Loop { invs, cond: _, neg_cond, binders, body: _ } =>
            // use: frame ++ binders ++ (invs as hyps) ++ ¬cond hyp
            frame_append(f, frame_append(binders_to_frame(*binders),
                frame_append(hyps_of_leaves(*invs),
                    FrameList::FHyp(neg_cond, Box::new(FrameList::FNil))))),
        StmData::Skip => f,
        StmData::Seq(a, b) => frame_after(frame_after(f, *a), *b),
    }
}

// wpStm: the goals of `s` given the frame that precedes it.
#[verifier::structural_decreases]
pub open spec fn wp_stm(f: FrameList, s: StmData) -> GoalList
    decreases s
{
    match s {
        StmData::Assert(e) =>
            GoalList::Cons(Box::new(close(f, e)), Box::new(GoalList::Nil)),
        StmData::Assume(_e) => GoalList::Nil,
        StmData::Assign(_x, _rhs) => GoalList::Nil,
        StmData::Call { reqs, enss: _, dest: _, dest_typ: _ } => close_each(f, *reqs),
        StmData::DeadEnd(b) => wp_stm(f, *b),
        StmData::Ret(es) => close_each(f, *es),
        StmData::If(c, nc, t, e) =>
            goals_append(
                wp_stm(frame_append(f, FrameList::FHyp(c, Box::new(FrameList::FNil))), *t),
                wp_stm(frame_append(f, FrameList::FHyp(nc, Box::new(FrameList::FNil))), *e)),
        StmData::Loop { invs, cond, neg_cond: _, binders, body } => {
            // init: each inv closed under the pre-loop frame; maintain:
            // body goals ++ each inv re-closed at body end, under
            // frame ++ binders ++ invs-as-hyps ++ cond-hyp. (`use` is a
            // frameAfter extension, not a goal.) NOTE: the SST Loop node
            // currently carries `binders = Nil` (the modified-var havoc set
            // is not populated at the snapshot — board writeup finding-3),
            // so this maintain telescope is under-populated vs production;
            // the decreases/termination obligation is also not synthesized
            // here (no `decreases` leaf on the Loop node).
            let mframe = frame_append(f, frame_append(binders_to_frame(*binders),
                frame_append(hyps_of_leaves(*invs),
                    FrameList::FHyp(cond, Box::new(FrameList::FNil)))));
            let body_goals = wp_stm(mframe, *body);
            let endf = frame_after(mframe, *body);
            let maintain_post = close_each(endf, *invs);
            goals_append(close_each(f, *invs), goals_append(body_goals, maintain_post))
        },
        StmData::Skip => GoalList::Nil,
        StmData::Seq(a, b) =>
            goals_append(wp_stm(f, *a), wp_stm(frame_after(f, *a), *b)),
    }
}

// Seed the value-param telescope: each param binder immediately followed
// by its own bound hyp (empirical spine: ∀x, ∀(h_x_bound), ∀y, ∀(h_y_bound),
// …). Params → FBind; bound hyps → FBind too (finding-2: production renders
// them as NAMED ∀-binders `∀ (h_x_bound : …)`, so `close` must fold them
// into `All`, not `Imp`).
#[verifier::structural_decreases]
pub open spec fn seed_params(params: BinderList, bounds: ParamBoundList) -> FrameList
    decreases params
{
    match params {
        BinderList::Nil => FrameList::FNil,
        BinderList::Cons(id, typ, t) => match bounds {
            ParamBoundList::Bound(hname, prop, bt) =>
                FrameList::FBind(id, typ, Box::new(FrameList::FBind(hname, prop, Box::new(seed_params(*t, *bt))))),
            ParamBoundList::NoBound(bt) =>
                FrameList::FBind(id, typ, Box::new(seed_params(*t, *bt))),
            ParamBoundList::Nil =>
                FrameList::FBind(id, typ, Box::new(seed_params(*t, ParamBoundList::Nil))),
        },
    }
}

// Seed the initial frame from the signature (DESIGN §2.2): typ-params,
// then value params interleaved with bound hyps, then reqs. reqs are NAMED
// ∀-binders (finding-2), so they fold in via `binders_to_frame`, not
// `hyps_of_leaves`.
pub open spec fn seed_frame(c: FnCtxData) -> FrameList {
    frame_append(binders_to_frame(c.typ_params),
        frame_append(seed_params(c.params, c.param_bounds),
            binders_to_frame(c.reqs)))
}

// refWp: the certificate LHS. Seed the frame, then walk the body. The
// serializer emits an explicit `Ret` leaf list (all fixtures end in Ret),
// so refWp does not synthesize a fall-through Ret (§5.2).
pub open spec fn ref_wp(c: FnCtxData, s: StmData) -> GoalList {
    wp_stm(seed_frame(c), s)
}

// Structural equality for the `decide` bridge (DESIGN §2.3). STRICT:
// every leaf id and binder id must match. A strict checker keeps the TCB
// honest — where a fixture bridge fails to close it indicts an unfaithful
// serializer/shape (board writeup), NOT a lax comparison.
//
// IMPORTANT (finding-5): these return `nat` (1 = equal, 0 = not), NOT
// `bool`. The tactus Lean backend lowers a `bool`-returning spec fn to a
// NONCOMPUTABLE `Prop` def, for which `Decidable (goal_eq a b)` resolves
// to `Classical.propDecidable` and `decide` gets STUCK on `Classical.choice`.
// A `nat`-returning def gives the `= 1` conjuncts a concrete `Nat.decEq`
// instance, and the kernel then reduces the body (nested numeral-`ite`s).
// The W2b bridge line is therefore `goals_eq (refWp …) production = 1 := by
// decide`, not `= true` as DESIGN §2.3 sketched.
// The structural checkers must (a) recurse structurally on their first
// argument and (b) emit unambiguously. A nested `match a { … match b …}`
// keeps (a) but breaks (b): the tactus Lean backend flattens the inner
// match so later outer arms bind past its wildcard ("redundant
// alternative"). A tuple `match (a, b)` fixes (b) but breaks (a): the
// child `t1.deref` is no longer seen as a structural subterm of `a`. So
// match `a` ALONE (single match → structural + unambiguous) and read `b`
// through NON-recursive projections (a nat constructor tag + field
// accessors), keeping every arm body a chain of `if`s, never a match.

pub open spec fn gd_tag(g: GoalData) -> nat {
    match g {
        GoalData::Leaf(_) => 0,
        GoalData::Imp(_, _) => 1,
        GoalData::All(_, _, _) => 2,
        GoalData::Let(_, _, _) => 3,
    }
}
pub open spec fn gd_leaf_id(g: GoalData) -> u64 { match g { GoalData::Leaf(x) => x, _ => 0 } }
pub open spec fn gd_imp_hyp(g: GoalData) -> u64 { match g { GoalData::Imp(h, _) => h, _ => 0 } }
pub open spec fn gd_all_name(g: GoalData) -> u64 { match g { GoalData::All(x, _, _) => x, _ => 0 } }
pub open spec fn gd_all_typ(g: GoalData) -> u64 { match g { GoalData::All(_, t, _) => t, _ => 0 } }
pub open spec fn gd_let_name(g: GoalData) -> u64 { match g { GoalData::Let(x, _, _) => x, _ => 0 } }
pub open spec fn gd_let_val(g: GoalData) -> u64 { match g { GoalData::Let(_, v, _) => v, _ => 0 } }
// The single child of a non-leaf node (self for a leaf — never recursed on).
pub open spec fn gd_child(g: GoalData) -> GoalData {
    match g {
        GoalData::Imp(_, t) => *t,
        GoalData::All(_, _, t) => *t,
        GoalData::Let(_, _, t) => *t,
        GoalData::Leaf(x) => GoalData::Leaf(x),
    }
}

#[verifier::structural_decreases]
pub open spec fn goal_eq(a: GoalData, b: GoalData) -> nat
    decreases a
{
    match a {
        GoalData::Leaf(x) =>
            if gd_tag(b) == 0 { if x == gd_leaf_id(b) { 1 } else { 0 } } else { 0 },
        GoalData::Imp(h1, t1) =>
            if gd_tag(b) == 1 {
                if h1 == gd_imp_hyp(b) { goal_eq(*t1, gd_child(b)) } else { 0 }
            } else { 0 },
        GoalData::All(x1, ty1, t1) =>
            if gd_tag(b) == 2 {
                if x1 == gd_all_name(b) {
                    if ty1 == gd_all_typ(b) { goal_eq(*t1, gd_child(b)) } else { 0 }
                } else { 0 }
            } else { 0 },
        GoalData::Let(x1, v1, t1) =>
            if gd_tag(b) == 3 {
                if x1 == gd_let_name(b) {
                    if v1 == gd_let_val(b) { goal_eq(*t1, gd_child(b)) } else { 0 }
                } else { 0 }
            } else { 0 },
    }
}

pub open spec fn gl_tag(g: GoalList) -> nat {
    match g {
        GoalList::Nil => 0,
        GoalList::Cons(_, _) => 1,
    }
}
pub open spec fn gl_head(g: GoalList) -> GoalData {
    match g { GoalList::Cons(h, _) => *h, GoalList::Nil => GoalData::Leaf(0) }
}
pub open spec fn gl_tail(g: GoalList) -> GoalList {
    match g { GoalList::Cons(_, t) => *t, GoalList::Nil => GoalList::Nil }
}

#[verifier::structural_decreases]
pub open spec fn goals_eq(a: GoalList, b: GoalList) -> nat
    decreases a
{
    match a {
        GoalList::Nil => if gl_tag(b) == 0 { 1 } else { 0 },
        GoalList::Cons(h1, t1) =>
            if gl_tag(b) == 1 {
                if goal_eq(*h1, gl_head(b)) == 1 { goals_eq(*t1, gl_tail(b)) } else { 0 }
            } else { 0 },
    }
}

// ── W2a: graded reduction probes (isolate what kernel-computes) ─────

proof fn probe_goal_eq_leaf()
    ensures
        goal_eq(GoalData::Leaf(5), GoalData::Leaf(5)) == 1,
        goal_eq(GoalData::Leaf(5), GoalData::Leaf(6)) == 0
by { decide }

proof fn probe_goal_eq_nested()
    ensures
        goal_eq(GoalData::All(0, 1, Box::new(GoalData::Leaf(9))),
                GoalData::All(0, 1, Box::new(GoalData::Leaf(9)))) == 1,
        goal_eq(GoalData::All(0, 1, Box::new(GoalData::Leaf(9))),
                GoalData::All(7, 1, Box::new(GoalData::Leaf(9)))) == 0
by { decide }

proof fn probe_goals_eq_lit()
    ensures
        goals_eq(GoalList::Nil, GoalList::Nil) == 1,
        goals_eq(GoalList::Cons(Box::new(GoalData::Leaf(9)), Box::new(GoalList::Nil)),
                 GoalList::Cons(Box::new(GoalData::Leaf(9)), Box::new(GoalList::Nil))) == 1
by { decide }

proof fn probe_close()
    ensures
        goal_size(close(FrameList::FNil, 9)) == 1,
        goal_size(close(FrameList::FBind(0, 1, Box::new(FrameList::FNil)), 9)) == 2
by { decide }

proof fn probe_wp_stm()
    ensures
        goal_count(wp_stm(FrameList::FNil, StmData::Assert(9))) == 1,
        goal_count(wp_stm(FrameList::FNil, StmData::Skip)) == 0
by { decide }

proof fn probe_ref_wp()
    ensures
        goal_count(ref_wp(FnCtxData {
            typ_params: BinderList::Nil,
            params: BinderList::Nil,
            param_bounds: ParamBoundList::Nil,
            reqs: BinderList::Nil,
            enss: LeafList::Nil,
        }, StmData::Assert(9))) == 1
by { decide }

// ── W2a: end-to-end refWp unit examples (against hand-computed goals) ──

// Minimal context: one int param `x` (name leaf 0, type leaf 1) with a
// bound hyp (name leaf 19 = h_x_bound, prop leaf 2), no reqs. seed_frame =
// FBind(0,1, FBind(19,2, FNil)) — the bound hyp is now a NAMED ∀ (finding-2).
proof fn ref_wp_seed_and_assert()
    ensures
        // refWp folds the seed around a single Assert obligation:
        //   ∀ (x:Int), ∀ (h_x_bound:2), <9>
        goals_eq(
            ref_wp(
                FnCtxData {
                    typ_params: BinderList::Nil,
                    params: BinderList::Cons(0, 1, Box::new(BinderList::Nil)),
                    param_bounds: ParamBoundList::Bound(19, 2, Box::new(ParamBoundList::Nil)),
                    reqs: BinderList::Nil,
                    enss: LeafList::Nil,
                },
                StmData::Assert(9),
            ),
            GoalList::Cons(
                Box::new(GoalData::All(0, 1, Box::new(GoalData::All(19, 2, Box::new(GoalData::Leaf(9)))))),
                Box::new(GoalList::Nil)),
        ) == 1,
        // A Ret of two ensures leaves → two goals sharing the seed spine
        // (the max_u64 multiplicity, minus the branch-in-leaf divergence).
        goal_count(ref_wp(
            FnCtxData {
                typ_params: BinderList::Nil,
                params: BinderList::Cons(0, 1, Box::new(BinderList::Nil)),
                param_bounds: ParamBoundList::Bound(19, 2, Box::new(ParamBoundList::Nil)),
                reqs: BinderList::Nil,
                enss: LeafList::Cons(5, Box::new(LeafList::Cons(6, Box::new(LeafList::Nil)))),
            },
            StmData::Ret(Box::new(LeafList::Cons(5, Box::new(LeafList::Cons(6, Box::new(LeafList::Nil)))))),
        )) == 2
by { decide }

// Seq threads frameAfter: the second Assert sees the first as a forward
// hyp (Assert-then-Assume behaviour, one hyp here from the Assert alone).
// The seed bound hyp is a NAMED ∀ (h_x_bound = 19); the Assert forward hyp
// stays an anonymous Imp (it is not a signature binder).
proof fn ref_wp_seq_threads_frame()
    ensures
        // ∀x,∀(h_x_bound:2). <9>   then   ∀x,∀(h_x_bound:2). h9 → <10>
        goals_eq(
            ref_wp(
                FnCtxData {
                    typ_params: BinderList::Nil,
                    params: BinderList::Cons(0, 1, Box::new(BinderList::Nil)),
                    param_bounds: ParamBoundList::Bound(19, 2, Box::new(ParamBoundList::Nil)),
                    reqs: BinderList::Nil,
                    enss: LeafList::Nil,
                },
                StmData::Seq(Box::new(StmData::Assert(9)), Box::new(StmData::Assert(10))),
            ),
            GoalList::Cons(
                Box::new(GoalData::All(0, 1, Box::new(GoalData::All(19, 2, Box::new(GoalData::Leaf(9)))))),
                Box::new(GoalList::Cons(
                    Box::new(GoalData::All(0, 1, Box::new(GoalData::All(19, 2,
                        Box::new(GoalData::Imp(9, Box::new(GoalData::Leaf(10)))))))),
                    Box::new(GoalList::Nil)))),
        ) == 1
by { decide }

// Finding-2 payoff: refWp on add_capped's ctx reproduces production goal 0's
// seed telescope EXACTLY — all NAMED ∀-binders, no anonymous arrows. Leaf ids
// are the production ones (bootstrap-fixture/out/lib/cert/add_capped.cert.lean):
//   params x=0:Int=1, y=3:Int=1; bounds h_x_bound=19:prop2, h_y_bound=18:prop4;
//   reqs h_req0=17:(x<1000)=5, h_req1=16:(y<1000)=6; obligation leaf 15.
// Expected spine = All 0 1 (All 19 2 (All 3 1 (All 18 4 (All 17 5
//   (All 16 6 (Leaf 15)))))) — the first assert goal, verbatim. NB: the
// Assert here carries the ANNOTATED obligation leaf 15 directly; the raw SST
// carries the bare leaf 8 (finding-1, separate). This isolates finding-2:
// GIVEN the annotated obligation, the named-binder seed telescope matches.
proof fn ref_wp_add_capped_seed_spine()
    ensures
        goals_eq(
            ref_wp(
                FnCtxData {
                    typ_params: BinderList::Nil,
                    params: BinderList::Cons(0, 1, Box::new(BinderList::Cons(3, 1, Box::new(BinderList::Nil)))),
                    param_bounds: ParamBoundList::Bound(19, 2,
                        Box::new(ParamBoundList::Bound(18, 4, Box::new(ParamBoundList::Nil)))),
                    reqs: BinderList::Cons(17, 5, Box::new(BinderList::Cons(16, 6, Box::new(BinderList::Nil)))),
                    enss: LeafList::Cons(7, Box::new(LeafList::Nil)),
                },
                StmData::Assert(15),
            ),
            GoalList::Cons(
                Box::new(GoalData::All(0, 1, Box::new(GoalData::All(19, 2,
                    Box::new(GoalData::All(3, 1, Box::new(GoalData::All(18, 4,
                        Box::new(GoalData::All(17, 5, Box::new(GoalData::All(16, 6,
                            Box::new(GoalData::Leaf(15)))))))))))))),
                Box::new(GoalList::Nil)),
        ) == 1
by { decide }

// Mutation sensitivity (DESIGN §2.4.2): goal_eq flips on a single leaf-id
// change, a binder-id change, or a constructor (structure) change.
proof fn goal_eq_strictness()
    ensures
        goal_eq(GoalData::Leaf(5), GoalData::Leaf(6)) == 0,
        goal_eq(GoalData::Leaf(5), GoalData::Leaf(5)) == 1,
        // differing binder id
        goal_eq(
            GoalData::All(0, 1, Box::new(GoalData::Leaf(9))),
            GoalData::All(7, 1, Box::new(GoalData::Leaf(9)))) == 0,
        // differing hyp leaf inside an Imp
        goal_eq(
            GoalData::Imp(2, Box::new(GoalData::Leaf(9))),
            GoalData::Imp(3, Box::new(GoalData::Leaf(9)))) == 0,
        // All vs Imp (structure)
        goal_eq(
            GoalData::All(0, 1, Box::new(GoalData::Leaf(9))),
            GoalData::Imp(1, Box::new(GoalData::Leaf(9)))) == 0,
        // goals_eq flips when a goal is dropped (length mismatch)
        goals_eq(
            GoalList::Cons(Box::new(GoalData::Leaf(9)), Box::new(GoalList::Nil)),
            GoalList::Nil) == 0
by { decide }

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
        param_bound_len(ParamBoundList::Bound(4, 5,
            Box::new(ParamBoundList::NoBound(Box::new(ParamBoundList::Nil))))) == 2,
        frame_len(FrameList::FBind(1, 2,
            Box::new(FrameList::FHyp(3, Box::new(FrameList::FLet(4, 5, Box::new(FrameList::FNil))))))) == 3,
        // FnCtxData projection: 2 value params.
        fnctx_arity(FnCtxData {
            typ_params: BinderList::Cons(0, 100, Box::new(BinderList::Nil)),
            params: BinderList::Cons(1, 101,
                Box::new(BinderList::Cons(2, 102, Box::new(BinderList::Nil)))),
            param_bounds: ParamBoundList::Bound(199, 200,
                Box::new(ParamBoundList::NoBound(Box::new(ParamBoundList::Nil)))),
            reqs: BinderList::Nil,
            enss: LeafList::Cons(300, Box::new(LeafList::Nil)),
        }) == 2
by {
    decide
}

} // verus!
