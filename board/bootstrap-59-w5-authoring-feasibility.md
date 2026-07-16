---
title: "W5 loop-closure AUTHORING — feasibility (spec_fn oracle + recursive-induction proof fn in tactus-core) + the discharge idiom"
status: done
claimed_by: opus-bootstrap59-authoring
created: 2026-07-14T23:59:00Z
updated: 2026-07-15T00:00:00Z
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

- (2026-07-15, opus-bootstrap59-authoring) **DISCHARGE STRING NAILED — probe now
  `19 verified, 0 errors`; card DONE.** Iterated the closer by direct-`lean` runs
  against the emitted VC oleans (fast loop, no full re-emit), then confirmed by a full
  `--lean-all-proofs` re-emit. The idiom:

  ```
  #[verifier::tactus_tactic("first | tactus_auto |
     (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
  ```

  Three necessary ingredients (each pinned to a concrete failure mode):
  1. `zetaDelta := true` — the body-established unfold equalities are `let`-bound LOCAL
     Props (`h : tmp__k := (… = …)`); plain `simp_all` won't unfold local let-fvars →
     "made no progress". `zetaDelta` exposes them as equations.
  2. `tactus_case_split` (a REAL `cases`), NOT the `a == Cons(g,t)` bridge assert —
     with `zetaDelta` the bridge is self-referential (`a = Cons a.Cons_val0 …`) → simp
     rewrites `a` forever → maxRecDepth; dropping it leaves opaque `match a` projections
     → unsolved. `cases` substitutes a fresh constructor properly. (Bridge asserts
     removed from the source as redundant scaffolding.)
  3. `[and_assoc]` — residual is `A∧(B∧C) ↔ (A∧B)∧C`; simp doesn't reassociate ∧ by
     default. (`wp_sound_bites`, no datatype local, uses the `tactus_case_split`-free
     variant.)

  Also added `u_wp_*` / `u_exec_safe_*` one-step unfold lemmas (empty-body, verify) and
  made `wp_sound`/`wp_sound_bites` CALL them per-arm — the height-recursive spec fns get
  NO Lean eq-lemmas (`Stm.rec_1` encoding) and the `u_*` proof fns aren't exported as
  `lib.u_*` simp lemmas, so the unfolds must enter the VC context as hyps via body calls.
  This IS probe21's `simp only [named u_* lemmas]` idiom, at the Rust-source level.

  **Axiom closure of the three top-level soundness postconditions (`all_true_append`,
  `wp_sound`, `wp_sound_bites`) = `[propext]` only** — no sorryAx / Classical.choice /
  stray axioms. Fully kernel-checked, non-circular. `run.sh` is now a real pass/fail gate
  (PASS == 0 errors).

## Writeup

**DONE.** The W5 loop-closure AUTHORING path is de-risked end-to-end: the two mechanism
unknowns (Q1 `spec_fn` oracle + recursive structural spec fns; Q2 recursive
structural-induction proof fns) both resolve POSITIVE, verified by a real
`--lean-all-proofs` tactus run on the isolated probe crate
(`probe-w0/probe32_authoring_feasibility/`, `19 verified, 0 errors`, `run.sh` PASS,
axiom closure `[propext]`).

**The exact discharge idiom** (the thing this card exists to find) is the per-fn
attribute `#[verifier::tactus_tactic("first | tactus_auto | (intros <;>
tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]`, paired
with per-constructor `u_*` unfold-lemma CALLS in each match arm of the induction body.
See `REPORT.md §Q2` for the per-ingredient necessity argument and the concrete
failure-mode each one fixes (all measured against emitted VCs).

**Assumptions / honesty:** (a) `simp_all` is a T2 dev-tactic per DESIGN-transparent-
automation §2 — a T1 polish (`simp only [named lemmas]`) is possible but was not squeezed
here; the discovery closer is what's committed. (b) This probe is the STRIPPED mechanism
spine (frame machinery elided — its soundness is proven in the hand-Lean probe21..31); it
demonstrates the idiom carries the recursive-induction shape, not the full frame
telescope. (c) The idiom is now ready to reuse when authoring W5a-0 (loop closure proper)
in tactus-core under **bootstrap-10** — that step is scaling + the base-hash re-verify
cost, not a new feasibility question.
