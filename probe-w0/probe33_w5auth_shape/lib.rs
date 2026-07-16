//! probe33 — W5 AUTHORING SHAPE de-risk (board bootstrap-60).
//!
//! probe32 (bootstrap-59) confirmed the oracle-param + recursive-induction
//! mechanisms. Reading probe24 (the W5c frame-carrying formulation) against it,
//! the Seq arm no longer recurses under a lambda — but four mechanism shapes in
//! the REAL model were still untested in tactus authoring:
//!
//!   M1: a spec CLOSURE LITERAL as a first-class value — `upd` returns a new
//!       function-typed state `|k| if k == x { n } else { st(k) }`.
//!   M2: NESTED spec_fn types — the leaf oracle takes the function-typed state
//!       as an argument: `hp : spec_fn(u64, spec_fn(u64) -> int) -> bool`.
//!   M3: recursion UNDER A `forall` BINDER — the FBind/All telescope arms are
//!       `forall|n| holds(hp, *t, upd(st, x, n))`.
//!   M4: an induction proof that relates two such definitions THROUGH the
//!       ∀ arm (pointwise congruence under the binder).
//!
//! RESULTS (see REPORT.md):
//!   M1/M2/M3 — all WORK, first try (spec closures, nested spec_fn types, and
//!   recursion under `forall` author, verify, and emit kernel-clean).
//!   M4 — works ONLY in the state-generic shape below. Two backend facts force
//!   it (both discovered here):
//!     F1. proof-fn CALLS inside an `assert forall ... by` block are DROPPED —
//!         each renders as `True →` in the VC (self-calls additionally emit no
//!         termination VC). Facts cannot be injected under a binder.
//!     F2. facts established in the arm body (outside binders) DO enter the
//!         VC, and simp_all rewrites with ∀st-quantified equations UNDER inner
//!         binders (hand-validated: /tmp shape test → baked in here).
//!   THE IDIOM (freeze for bootstrap-61..64): make every state-dependent
//!   lemma ST-GENERIC — quantify st in the ENSURES (mirroring hand-Lean
//!   theorems, which auto-generalize) — so IHs and unfold lemmas are plain
//!   arm-body calls and their ∀st-equations rewrite pointwise under binders.
//!   One-step u_* unfolds close definitionally with `(intros <;> rfl)`.
//!
//! The model is a MINI-W5c: frame telescope (FNil/FHyp/FBind), goals
//! (Leaf/Imp/All), function-typed St + upd, goal-side close_leaf, semantic-side
//! close_sem_leaf (continuation DEFUNCTIONALIZED to the one shape the real
//! execSafeF needs: "oracle at leaf o"), frame-carrying exec_safe_f, wp_stm,
//! and the two crux lemmas: close_leaf_sem (goal ↔ semantics alignment through
//! the ∀ arm) and wp_stm_sound (the mini soundness induction).
//!
//! Canonical check (mirrors probe32):
//!   TACTUS_LEAN_OUT=$PWD/out ../../source/target-verus/release/verus \
//!     --crate-type=lib --lean-backend --lean-all-proofs lib.rs
//! PASS = 0 errors with a clean axiom closure.

use vstd::prelude::*;

verus! {

// ── mini vocabulary, Box-nested like tactus-core's StmData/FrameList ──

pub enum Goal {
    Leaf(u64),
    Imp(u64, Box<Goal>),
    All(u64, Box<Goal>),
}

pub enum GList {
    Nil,
    Cons(Goal, Box<GList>),
}

pub enum Frame {
    FNil,
    FHyp(u64, Box<Frame>),
    FBind(u64, Box<Frame>),
}

pub enum Stm {
    Skip,
    Assert(u64),
    Seq(Box<Stm>, Box<Stm>),
}

// ── M1: function-typed state + closure-literal update ──
// (hand-Lean: `St := Int → Int`, `upd st x n := fun k => if k = x then n else st k`)

pub open spec fn upd(st: spec_fn(u64) -> int, x: u64, n: int) -> spec_fn(u64) -> int {
    |k: u64| if k == x { n } else { st(k) }
}

// ── goal denotation (M2: oracle over the function-typed state; M3: ∀ arm) ──

#[verifier::structural_decreases]
pub open spec fn holds(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, g: Goal, st: spec_fn(u64) -> int) -> bool
    decreases g
{
    match g {
        Goal::Leaf(id) => hp(id, st),
        Goal::Imp(h, t) => hp(h, st) ==> holds(hp, *t, st),
        Goal::All(x, t) => forall|n: int| #[trigger] holds(hp, *t, upd(st, x, n)),
    }
}

#[verifier::structural_decreases]
pub open spec fn holds_all(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, gs: GList, st: spec_fn(u64) -> int) -> bool
    decreases gs
{
    match gs {
        GList::Nil => true,
        GList::Cons(g, t) => holds(hp, g, st) && holds_all(hp, *t, st),
    }
}

// ── semantic telescope, continuation defunctionalized to "oracle at leaf o"
//    (the one continuation shape the real frame-carrying execSafeF needs) ──

#[verifier::structural_decreases]
pub open spec fn close_sem_leaf(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, f: Frame, st: spec_fn(u64) -> int, o: u64) -> bool
    decreases f
{
    match f {
        Frame::FNil => hp(o, st),
        Frame::FHyp(h, t) => hp(h, st) ==> close_sem_leaf(hp, *t, st, o),
        Frame::FBind(x, t) => forall|n: int| #[trigger] close_sem_leaf(hp, *t, upd(st, x, n), o),
    }
}

// ── goal-side close: wrap the telescope into the goal (head = outermost) ──

#[verifier::structural_decreases]
pub open spec fn close_leaf(f: Frame, o: u64) -> Goal
    decreases f
{
    match f {
        Frame::FNil => Goal::Leaf(o),
        Frame::FHyp(h, t) => Goal::Imp(h, Box::new(close_leaf(*t, o))),
        Frame::FBind(x, t) => Goal::All(x, Box::new(close_leaf(*t, o))),
    }
}

// ── frame algebra + frame-carrying operational safety + reference WP ──

#[verifier::structural_decreases]
pub open spec fn frame_append(f: Frame, g: Frame) -> Frame
    decreases f
{
    match f {
        Frame::FNil => g,
        Frame::FHyp(h, t) => Frame::FHyp(h, Box::new(frame_append(*t, g))),
        Frame::FBind(x, t) => Frame::FBind(x, Box::new(frame_append(*t, g))),
    }
}

#[verifier::structural_decreases]
pub open spec fn frame_after(f: Frame, s: Stm) -> Frame
    decreases s
{
    match s {
        Stm::Skip => f,
        Stm::Assert(o) => frame_append(f, Frame::FHyp(o, Box::new(Frame::FNil))),
        Stm::Seq(a, b) => frame_after(frame_after(f, *a), *b),
    }
}

#[verifier::structural_decreases]
pub open spec fn exec_safe_f(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, f: Frame, s: Stm, st: spec_fn(u64) -> int) -> bool
    decreases s
{
    match s {
        Stm::Skip => true,
        Stm::Assert(o) => close_sem_leaf(hp, f, st, o),
        Stm::Seq(a, b) => exec_safe_f(hp, f, *a, st)
            && exec_safe_f(hp, frame_after(f, *a), *b, st),
    }
}

#[verifier::structural_decreases]
pub open spec fn gappend(a: GList, b: GList) -> GList
    decreases a
{
    match a {
        GList::Nil => b,
        GList::Cons(g, t) => GList::Cons(g, Box::new(gappend(*t, b))),
    }
}

#[verifier::structural_decreases]
pub open spec fn wp_stm(f: Frame, s: Stm) -> GList
    decreases s
{
    match s {
        Stm::Skip => GList::Nil,
        Stm::Assert(o) => GList::Cons(close_leaf(f, o), Box::new(GList::Nil)),
        Stm::Seq(a, b) => gappend(wp_stm(f, *a), wp_stm(frame_after(f, *a), *b)),
    }
}

// ── one-step unfold lemmas (the u_* idiom), ST-GENERIC: the ∀st lives in the
//    ENSURES so callers get a rewrite rule usable under binders (F1/F2).
//    Pointwise the unfold is definitional on a constructor literal, so the
//    closer is `(intros <;> rfl)`. Data-only unfolds (no st) keep empty shape. ──

#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_holds_leaf(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, id: u64)
    ensures forall|st: spec_fn(u64) -> int| #[trigger] holds(hp, Goal::Leaf(id), st) == hp(id, st)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_holds_imp(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, h: u64, t: Box<Goal>)
    ensures forall|st: spec_fn(u64) -> int| #[trigger] holds(hp, Goal::Imp(h, t), st) == (hp(h, st) ==> holds(hp, *t, st))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_holds_all_goal(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, x: u64, t: Box<Goal>)
    ensures forall|st: spec_fn(u64) -> int| #[trigger] holds(hp, Goal::All(x, t), st)
        == (forall|n: int| #[trigger] holds(hp, *t, upd(st, x, n)))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_holds_all_nil(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool)
    ensures forall|st: spec_fn(u64) -> int| #[trigger] holds_all(hp, GList::Nil, st) == true
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_holds_all_cons(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, g: Goal, t: Box<GList>)
    ensures forall|st: spec_fn(u64) -> int| #[trigger] holds_all(hp, GList::Cons(g, t), st)
        == (holds(hp, g, st) && holds_all(hp, *t, st))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csl_nil(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, o: u64)
    ensures forall|st: spec_fn(u64) -> int| #[trigger] close_sem_leaf(hp, Frame::FNil, st, o) == hp(o, st)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csl_hyp(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, h: u64, t: Box<Frame>, o: u64)
    ensures forall|st: spec_fn(u64) -> int| #[trigger] close_sem_leaf(hp, Frame::FHyp(h, t), st, o)
        == (hp(h, st) ==> close_sem_leaf(hp, *t, st, o))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csl_bind(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, x: u64, t: Box<Frame>, o: u64)
    ensures forall|st: spec_fn(u64) -> int| #[trigger] close_sem_leaf(hp, Frame::FBind(x, t), st, o)
        == (forall|n: int| #[trigger] close_sem_leaf(hp, *t, upd(st, x, n), o))
{}
pub proof fn u_close_nil(o: u64)
    ensures close_leaf(Frame::FNil, o) == Goal::Leaf(o)
{}
pub proof fn u_close_hyp(h: u64, t: Box<Frame>, o: u64)
    ensures close_leaf(Frame::FHyp(h, t), o) == Goal::Imp(h, Box::new(close_leaf(*t, o)))
{}
pub proof fn u_close_bind(x: u64, t: Box<Frame>, o: u64)
    ensures close_leaf(Frame::FBind(x, t), o) == Goal::All(x, Box::new(close_leaf(*t, o)))
{}
pub proof fn u_wp_skip(f: Frame)
    ensures wp_stm(f, Stm::Skip) == GList::Nil
{}
pub proof fn u_wp_assert(f: Frame, o: u64)
    ensures wp_stm(f, Stm::Assert(o)) == GList::Cons(close_leaf(f, o), Box::new(GList::Nil))
{}
pub proof fn u_wp_seq(f: Frame, a: Box<Stm>, b: Box<Stm>)
    ensures wp_stm(f, Stm::Seq(a, b)) == gappend(wp_stm(f, *a), wp_stm(frame_after(f, *a), *b))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_es_skip(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, f: Frame)
    ensures forall|st: spec_fn(u64) -> int| #[trigger] exec_safe_f(hp, f, Stm::Skip, st) == true
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_es_assert(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, f: Frame, o: u64)
    ensures forall|st: spec_fn(u64) -> int| #[trigger] exec_safe_f(hp, f, Stm::Assert(o), st)
        == close_sem_leaf(hp, f, st, o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_es_seq(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, f: Frame, a: Box<Stm>, b: Box<Stm>)
    ensures forall|st: spec_fn(u64) -> int| #[trigger] exec_safe_f(hp, f, Stm::Seq(a, b), st)
        == (exec_safe_f(hp, f, *a, st) && exec_safe_f(hp, frame_after(f, *a), *b, st))
{}
pub proof fn u_gappend_nil(b: GList)
    ensures gappend(GList::Nil, b) == b
{}
pub proof fn u_gappend_cons(g: Goal, t: Box<GList>, b: GList)
    ensures gappend(GList::Cons(g, t), b) == GList::Cons(g, Box::new(gappend(*t, b)))
{}

// ── M4 crux: goal ↔ semantics alignment THROUGH the ∀ arm — ST-GENERIC shape.
//    Arm bodies are plain calls (u_* + IH); their ∀st-equations enter the
//    postcondition VC as hyps and simp_all rewrites pointwise under the inner
//    ∀n binder. NO assert-forall-by anywhere (F1). ──
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
#[verifier::structural_decreases]
pub proof fn close_leaf_sem(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, f: Frame, o: u64)
    ensures forall|st: spec_fn(u64) -> int|
        #[trigger] holds(hp, close_leaf(f, o), st) == close_sem_leaf(hp, f, st, o)
    decreases f
{
    match f {
        Frame::FNil => {
            u_close_nil(o);
            u_holds_leaf(hp, o);
            u_csl_nil(hp, o);
        }
        Frame::FHyp(h, t) => {
            u_close_hyp(h, t, o);
            u_holds_imp(hp, h, Box::new(close_leaf(*t, o)));
            u_csl_hyp(hp, h, t, o);
            close_leaf_sem(hp, *t, o);                          // IH (st-generic)
        }
        Frame::FBind(x, t) => {
            u_close_bind(x, t, o);
            u_holds_all_goal(hp, x, Box::new(close_leaf(*t, o)));
            u_csl_bind(hp, x, t, o);
            close_leaf_sem(hp, *t, o);                          // IH (st-generic)
        }
    }
}

// ── recursive append lemma (probe32 shape over structured goals; st stays a
//    PARAM here — no binder is crossed, validating that both shapes coexist) ──
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
#[verifier::structural_decreases]
pub proof fn holds_all_append(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, a: GList, b: GList, st: spec_fn(u64) -> int)
    ensures holds_all(hp, gappend(a, b), st) == (holds_all(hp, a, st) && holds_all(hp, b, st))
    decreases a
{
    match a {
        GList::Nil => {
            u_gappend_nil(b);
            u_holds_all_nil(hp);
        }
        GList::Cons(g, t) => {
            u_gappend_cons(g, t, b);
            u_holds_all_cons(hp, g, t);
            u_holds_all_cons(hp, g, Box::new(gappend(*t, b)));
            holds_all_append(hp, *t, b, st);                    // IH
        }
    }
}

// ── the mini soundness induction (frame-carrying, probe24's theorem shape) ──
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
#[verifier::structural_decreases]
pub proof fn wp_stm_sound(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, f: Frame, s: Stm, st: spec_fn(u64) -> int)
    ensures holds_all(hp, wp_stm(f, s), st) ==> exec_safe_f(hp, f, s, st)
    decreases s
{
    match s {
        Stm::Skip => {
            u_wp_skip(f);
            u_es_skip(hp, f);
        }
        Stm::Assert(o) => {
            u_wp_assert(f, o);
            u_holds_all_cons(hp, close_leaf(f, o), Box::new(GList::Nil));
            u_holds_all_nil(hp);
            close_leaf_sem(hp, f, o);        // st-generic; instantiates at st
            u_es_assert(hp, f, o);
        }
        Stm::Seq(a, b) => {
            u_wp_seq(f, a, b);
            u_es_seq(hp, f, a, b);
            holds_all_append(hp, wp_stm(f, *a), wp_stm(frame_after(f, *a), *b), st);
            wp_stm_sound(hp, f, *a, st);                        // IH
            wp_stm_sound(hp, frame_after(f, *a), *b, st);       // IH (shifted frame)
        }
    }
}

// ── non-vacuity: the theorem BITES through a real FBind telescope ──
// from the emitted goal ∀x. (h → leaf o), safety of `assert o` under
// frame [FBind x, FHyp h] follows.
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])")]
pub proof fn wp_sound_bites(hp: spec_fn(u64, spec_fn(u64) -> int) -> bool, x: u64, h: u64, o: u64, st: spec_fn(u64) -> int)
    requires holds_all(hp, wp_stm(Frame::FBind(x, Box::new(Frame::FHyp(h, Box::new(Frame::FNil)))), Stm::Assert(o)), st)
    ensures close_sem_leaf(hp, Frame::FBind(x, Box::new(Frame::FHyp(h, Box::new(Frame::FNil)))), st, o)
{
    wp_stm_sound(hp, Frame::FBind(x, Box::new(Frame::FHyp(h, Box::new(Frame::FNil)))), Stm::Assert(o), st);
    u_es_assert(hp, Frame::FBind(x, Box::new(Frame::FHyp(h, Box::new(Frame::FNil)))), o);
}

} // verus!
