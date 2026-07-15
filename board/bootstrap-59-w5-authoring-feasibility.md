---
title: "W5 loop-closure AUTHORING — feasibility (spec_fn oracle + recursive-induction proof fn in tactus-core) + the discharge idiom"
status: in_progress
claimed_by: opus-bootstrap59-authoring
created: 2026-07-14T23:59:00Z
updated: 2026-07-14T23:59:00Z
---

## Description

The W5 soundness ladder is fully proven as **hand-Lean probes** (probe21..31,
bootstrap-49..58). Genuine **loop closure** (the point of the whole bootstrap
program — DESIGN-W5-soundness §0/§4, DESIGN-bootstrap §5/§6) requires *authoring*
that soundness as Rust spec/proof fns **inside tactus-core**, verified by the tactus
binary (routed to Lean), emitted as a kernel-checked package. That final step is the
one the umbrella card (bootstrap-10) calls "explicitly staged and not yet begun."

Before touching tactus-core (whose base-hash change re-verifies the whole crate + re-
emits the oleans probe9/13/14/21..31 depend on), this card **de-risks the authoring
path** with an isolated scratch crate run through the real tactus binary, because
tactus-core today has **zero `spec_fn`-typed params and zero recursive proof fns** —
every proof fn is a closed `by { decide }`. Two mechanism unknowns:

- **Q1** — `spec_fn` leaf-oracle param (valuation-parametric, DESIGN-W5 §1 opt b) in
  spec fns AND proof fns, emitted kernel-clean?
- **Q2** — a recursive structural-INDUCTION `proof fn` (the analog of probe21's
  `wp_stm_sound`) with a recursive helper lemma?

**Done when:** the feasibility is settled with evidence (isolated probe through the
real tactus binary), AND — the follow-on rung — a fully-verified recursive-induction
proof (`all_true_append`, then the real `wp_stm_sound`) closes with a clean axiom
closure, giving the exact `#[verifier::tactus_tactic]` discharge string to reuse when
authoring in tactus-core.

## Progress

- (2026-07-14, opus-bootstrap59-authoring) **Probe landed: `probe-w0/probe32_authoring_feasibility/`**
  (isolated scratch crate, `run.sh`, REPORT.md). Findings:

  - **Q1 = CONFIRMED (the crux).** `8 verified`: the 4 oracle-parametric recursive
    `open spec fn`s (`gappend`, `all_true(hp,·)`, `wp`, `exec_safe(hp,·)`, with
    `hp: spec_fn(u64)->bool`) author, verify, and emit kernel-clean. The backend
    lowers `spec_fn(u64)->bool` to Lean `Int → Prop`. **So the valuation-parametric
    leaf-oracle semantics is expressible in tactus-core — the hard authoring unknown
    is positive.** Plus the 4 one-step `u_*` unfold lemmas verify (empty body), i.e.
    `tactus_auto` DOES discharge an isolated single constructor-unfold.

  - **Q2 = STRUCTURE works; compound discharge is the remaining rung.** Verus accepts
    the recursive structural-induction proof-fn shape; with
    `#[verifier::structural_decreases]` on the proof fn the **height-decrease
    termination VC discharges**, and the **IH threads** into the Lean context (read
    off the emitted `lib__*.lean`). The default `tactus_auto` closes every ATOMIC step
    (unfold, variable→constructor bridge `a == Cons(g,t)`, single rewrite
    `gappend(a,b)==b`, `∧`-simp) but NOT the **compound postcondition**
    (`all_true hp (gappend a b) = (all_true hp a && all_true hp b)`) — that needs
    multi-hyp rewriting (`simp_all`, a T2 dev-tactic). probe21's hand-Lean closes the
    analogue with `simp only [u_* rfl-lemmas]` (T1).

  - **Discharge mechanism FOUND:** `#[verifier::tactus_tactic("first | tactus_auto |
    (<custom Lean tactic>)")]` — per-fn closer override (`sst_to_lean.rs:964`,
    `attributes.rs:692`); the corpus uses it with real multi-step
    `intros <;> simp only […] <;> rw […] <;> congr` (e.g.
    `tactus-group-theory/src/runtime.rs:376`).

  - **NOT done (honest):** the exact `tactus_tactic` string closing the induction
    postcondition. `first | tactus_auto | (intros <;> simp_all)` left the goal — the
    emitted VC carries the body asserts as `let`-bound Props + `_tactus_ret : Unit`
    binders that naive `simp_all` doesn't consume; the closer must `subst`/case the
    bridge equality and rewrite (probe21's `simp only [u_*]` shape, adapted to the
    projector-form VC). Tactic engineering, not a mechanism blocker.

  **⇒ Loop closure is now precisely scoped: math done (hand-Lean); the hard authoring
  unknown (spec_fn oracle + recursive spec fns) resolved positive; the ONE remaining
  blocker is the per-fn `tactus_tactic` discharge string.** Next: craft it so
  `all_true_append` verifies clean, then scale to the real `wp_stm_sound` + frame
  lemmas, then author into tactus-core (the umbrella bootstrap-10 close).

## Writeup

_partial — see `probe-w0/probe32_authoring_feasibility/REPORT.md` for the full,
measured breakdown. This card stays in_progress until the induction-postcondition
`tactus_tactic` string closes `all_true_append` with a clean axiom closure; at that
point the tactus-core authoring of W5a-0 (loop closure proper) can begin under
bootstrap-10._
