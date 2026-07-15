//! probe32 — W5 LOOP-CLOSURE AUTHORING FEASIBILITY (board bootstrap-59).
//!
//! The W5 ladder is proven as HAND-LEAN probes (probe21..31). Loop closure
//! requires AUTHORING that soundness as Rust spec/proof fns INSIDE tactus-core,
//! verified by the tactus binary (routed to Lean), emitted as a kernel-checked
//! package. But tactus-core today has ZERO `spec_fn`-typed params and ZERO
//! recursive proof fns — every proof fn is a closed `by { decide }`. So loop
//! closure has two UNTESTED mechanism questions:
//!
//!   Q1: does the tactus Verus→Lean backend accept a `spec_fn` oracle param
//!       (the valuation-parametric leaf oracle, DESIGN-W5-soundness §1 option b)
//!       in a spec fn AND a proof fn, and emit it kernel-clean?
//!   Q2: can it author a RECURSIVE structural-INDUCTION `proof fn` (the analog
//!       of probe21's `wp_stm_sound`) with a recursive helper lemma?
//!
//! This is an ISOLATED scratch crate (touches NO existing crate, no tactus-core
//! rebuild) that tests exactly those two mechanisms, mirroring probe21's
//! `wp_stm_sound` shape but STRIPPED of the frame machinery (frame_after /
//! frame_hyps / close_e), whose soundness the hand-Lean already proved. What
//! remains is the mechanism spine: an oracle-parametric recursive predicate over
//! an OWN Box-nested datatype, a WP that collects obligations, a recursive
//! append lemma, and a recursive-induction soundness proof.
//!
//! Canonical check (mirrors tactus-core's header):
//!   TACTUS_LEAN_OUT=$PWD/out ../../source/target-verus/release/verus \
//!     --crate-type=lib --lean-backend --lean-all-proofs lib.rs
//! PASS = "verified" with a clean axiom closure (no sorryAx / Classical.choice).

use vstd::prelude::*;

verus! {

// ── mini-SST: the W5a-0 straight-line fragment, Box-nested like StmData ──
pub enum Stm {
    Skip,
    Assume(u64),
    Assert(u64),
    Seq(Box<Stm>, Box<Stm>),
}

// obligation list (each obligation is an opaque leaf id — stage-A shape)
pub enum GList {
    Nil,
    Cons(u64, Box<GList>),
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

// ── Q1: the valuation-parametric LEAF ORACLE as a `spec_fn` param ──
// `hp : leaf id → holds?` — the minimal analog of probe21's `hp : Int→St→Prop`
// (St dropped: W5a-0 threads it untouched, so it doesn't affect the mechanism).

#[verifier::structural_decreases]
pub open spec fn all_true(hp: spec_fn(u64) -> bool, gs: GList) -> bool
    decreases gs
{
    match gs {
        GList::Nil => true,
        GList::Cons(g, t) => hp(g) && all_true(hp, *t),
    }
}

// operational safety: every Assert's obligation oracle holds. (Frame-free
// degenerate of probe21's `execSafe`; the hyp-context threading is the part the
// hand-Lean proved — here we test the recursion/oracle mechanism.)
#[verifier::structural_decreases]
pub open spec fn exec_safe(hp: spec_fn(u64) -> bool, s: Stm) -> bool
    decreases s
{
    match s {
        Stm::Skip => true,
        Stm::Assume(_e) => true,
        Stm::Assert(o) => hp(o),
        Stm::Seq(a, b) => exec_safe(hp, *a) && exec_safe(hp, *b),
    }
}

// the reference WP: collect each Assert's obligation as one goal.
#[verifier::structural_decreases]
pub open spec fn wp(s: Stm) -> GList
    decreases s
{
    match s {
        Stm::Skip => GList::Nil,
        Stm::Assume(_e) => GList::Nil,
        Stm::Assert(o) => GList::Cons(o, Box::new(GList::Nil)),
        Stm::Seq(a, b) => gappend(wp(*a), wp(*b)),
    }
}

// ── BUILDING-BLOCK TEST: can the closer discharge a SINGLE isolated one-step
//    constructor-unfold of a recursive `open spec fn`? (the analog of probe21's
//    `u_*` rfl lemmas). Each of these is one equation, no recursion, no context. ──
pub proof fn u_gappend_nil(b: GList)
    ensures gappend(GList::Nil, b) == b
{}
pub proof fn u_gappend_cons(g: u64, t: Box<GList>, b: GList)
    ensures gappend(GList::Cons(g, t), b) == GList::Cons(g, Box::new(gappend(*t, b)))
{}
pub proof fn u_all_true_nil(hp: spec_fn(u64) -> bool)
    ensures all_true(hp, GList::Nil) == true
{}
pub proof fn u_all_true_cons(hp: spec_fn(u64) -> bool, g: u64, t: Box<GList>)
    ensures all_true(hp, GList::Cons(g, t)) == (hp(g) && all_true(hp, *t))
{}

// ── Q2a: RECURSIVE append lemma, discharged by CALLING the unfold lemmas ──
// The default `tactus_auto` closes every ATOMIC step (unfold, single rewrite,
// bridge, ∧-simp) but NOT the compound postcondition (multi-hyp substitution).
// A per-fn `tactus_tactic` custom closer runs `simp_all` over the in-context
// `a`-form equalities we established. (`simp_all` is T2 dev-tier per
// DESIGN-transparent-automation §2; productionizing squeezes it to a T1
// `simp only [named u_* lemmas]` — the same shape probe21 uses in hand-Lean.)
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> simp_all)")]
#[verifier::structural_decreases]
pub proof fn all_true_append(hp: spec_fn(u64) -> bool, a: GList, b: GList)
    ensures all_true(hp, gappend(a, b)) == (all_true(hp, a) && all_true(hp, b))
    decreases a
{
    match a {
        GList::Nil => {
            u_gappend_nil(b);
            u_all_true_nil(hp);
            assert(a == GList::Nil);                       // bridge: variable → constructor
            assert(gappend(a, b) == b);                    // single rewrite a→Nil + unfold
            assert(all_true(hp, a) == true);              // single rewrite a→Nil + unfold
            // postcondition now closes: all_true(gappend a b)=all_true b, all_true a=true, ∧-True
        }
        GList::Cons(g, t) => {
            u_gappend_cons(g, t, b);
            u_all_true_cons(hp, g, t);
            u_all_true_cons(hp, g, Box::new(gappend(*t, b)));
            all_true_append(hp, *t, b);                    // IH
            assert(a == GList::Cons(g, t));                // bridge: variable → constructor
            assert(all_true(hp, a) == (hp(g) && all_true(hp, *t)));
            assert(gappend(a, b) == GList::Cons(g, Box::new(gappend(*t, b))));
            assert(all_true(hp, gappend(a, b))
                == (hp(g) && all_true(hp, gappend(*t, b))));
            // postcondition now closes: substitute IH into the last assert, ∧-assoc
        }
    }
}

// ── Q2b: the RECURSIVE structural-INDUCTION soundness proof ──
// (analog of probe21 `wp_stm_sound`: emitted goals all hold ⟹ safe).
#[verifier::structural_decreases]
pub proof fn wp_sound(hp: spec_fn(u64) -> bool, s: Stm)
    ensures all_true(hp, wp(s)) ==> exec_safe(hp, s)
    decreases s
{
    reveal_with_fuel(wp, 2);
    reveal_with_fuel(all_true, 2);
    reveal_with_fuel(exec_safe, 2);
    match s {
        Stm::Skip => {}
        Stm::Assume(_e) => {}
        Stm::Assert(_o) => {}
        Stm::Seq(a, b) => {
            all_true_append(hp, wp(*a), wp(*b));
            wp_sound(hp, *a);
            wp_sound(hp, *b);
        }
    }
}

// non-vacuity: the theorem BITES on a concrete program with the oracle opaque —
// from the single emitted goal, the Assert's obligation follows.
pub proof fn wp_sound_bites(hp: spec_fn(u64) -> bool, o: u64)
    requires all_true(hp, wp(Stm::Assert(o)))
    ensures hp(o)
{
    reveal_with_fuel(wp, 2);
    reveal_with_fuel(all_true, 2);
    reveal_with_fuel(exec_safe, 2);
    wp_sound(hp, Stm::Assert(o));
}

} // verus!
