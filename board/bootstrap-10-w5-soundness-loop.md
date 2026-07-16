---
title: "W5 — soundness of the reference WP (the bootstrap loop closes) [staged, very large]"
status: in_progress
claimed_by: opus-w5a-kickoff
created: 2026-07-13T19:38:00Z
updated: 2026-07-16T17:15:00Z
---

## Description

Prove refWp sound against a written-down operational semantics of SST, authored
as tactus proof fns, verified by tactus, emitted as one more kernel-checked
package. This closes the loop non-circularly (the fixed point is checked by the
kernel, not by tactus). **tactus-group-theory-scale formalization** — this is an
umbrella; split into W5a–e sub-tasks when started.

Spec: `DESIGN-bootstrap.md` §5 (W5 row) + §6 (loop diagram);
`DESIGN-W2-refwp.md` §4 open question §5.5.

- `SstSem`: fuel-indexed big-step evaluator over the mirror SST (total spec fn).
  `refWp_sound : (refWp ctx s) all-hold → safe s`, partial correctness first
  (termination obligations as their own family, as Verus splits them).
- **Decide first (open Q §5.5):** a fuel evaluator cannot evaluate opaque
  leaves. Either land stage B (W6) first, OR make `SstSem` VALUATION-PARAMETRIC
  (leaf oracle `LeafId → State → Value`, `refWp_sound` quantified over oracles
  consistent with the leaf-table typing). (b) preserves the planned parallelism
  and front-loads the leaf-typing discipline W6 needs anyway.
- Staging: W5a straight-line + if/else + assert/assume; W5b calls (the exec
  call rule DESIGN-emit-module §4.4 leaves open); W5c loops + havoc; W5d
  &mut/prophecy (∀-quantify the final value); W5e closures.
- Needs R0a-quality lean-only coverage on tactus-core itself (everything routed
  to Lean) for the loop-closure claim.

**Done when (umbrella):** refWp_sound proven for the stage-A fragment and its
package passes the axiom-closure gate; claim becomes "kernel-checked
obligations ⟹ the operational spec".

**Blocked by:** bootstrap-06 (W2a shapes) for authoring; can run long in
parallel with W3/W4. The valuation-parametric decision unblocks starting before
W6.

## Progress

- (2026-07-14, opus-w5a-kickoff) **W5 OPENED.** B1 (bootstrap-48) closed the
  common-mode soundness gap this loop was blocked on. Decided open Q §5.5 =
  **valuation-parametric** (leaf oracle; option b) — preserves W5∥W6 parallelism,
  front-loads leaf-typing, yields the stronger any-oracle theorem (confirmed with
  Danielle's local model). Authored the detailed ladder + semantic model +
  proof skeleton in **`DESIGN-W5-soundness.md`**, and split the umbrella into
  sub-cards: **bootstrap-49 (W5a)**, **-50 (W5b Call/Ret)**, **-51 (W5c Loop)**,
  **-52 (W5d &mut/prophecy)**, **-53 (W5e closures + W5f adequacy spine)**.
- (2026-07-14, cont.) **First rung landed: W5a-0 probe PASS** — the reference WP
  proven sound on `{Skip, Assume, Assert, Seq}` over the REAL emitted `lib.wp_stm`
  (`probe-w0/probe21_w5a_sem/`, rc=0, axiom closure `[propext, Quot.sound]`, no
  tactus-core rebuild). See bootstrap-49. The loop's *math* is now demonstrated on
  its first fragment; the ladder (W5a-1 → W5b → … → tactus-core authoring =
  loop closure) continues from there.
- (2026-07-14, opus-w5a1-if-params) **W5a-1 PASS** (branching fragment + ∀-params,
  arbitrary frame telescope; `isHypFrame` restriction lifted). See bootstrap-49 +
  `probe-w0/probe22_w5a1_sem/`.
- (2026-07-14, opus-w5b-callret) **W5b PASS** (bootstrap-50) — Call + Ret +
  DeadEnd + Assign, and the If fall-through goes LIVE. Fragment now
  `{Skip, Assume, Assert, Assign, Seq, If, Call, Ret, DeadEnd}`. Design lift:
  `addedHyp` → `closeSem (frameDelta a)` (Call's `post` binds variables); Lemma B
  is now a corollary of `frame_after = frame_append ∘ frameDelta`. rc=0, ~3.5s,
  axiom closure `[propext, Quot.sound]`. `probe-w0/probe23_w5b_sem/`. **Ladder
  remaining: W5c Loop (bootstrap-51) → W5d &mut/prophecy → W5e closures → W5f
  adequacy spine → tactus-core authoring (loop closure).**
- (2026-07-14, opus-bootstrap59-authoring) **Loop-closure AUTHORING de-risked
  (bootstrap-59, probe32).** The whole ladder (W5a–f + match/pairing rungs) is now
  proven as hand-Lean probes; the umbrella's remaining step is *authoring* it as
  tactus-core spec/proof fns (this card's "explicitly staged" tail). Before touching
  tactus-core, ran an isolated feasibility probe
  (`probe-w0/probe32_authoring_feasibility/`, real tactus binary, `--lean-all-proofs`):
  **Q1 CONFIRMED** — `spec_fn` leaf-oracle params + recursive structural `open spec
  fn`s (the valuation-parametric model, DESIGN-W5 §1 opt b) author, verify, and emit
  kernel-clean in tactus (8 verified). **Q2** — the recursive-induction proof-fn
  structure is accepted (`structural_decreases` gives termination; the IH threads);
  the one remaining blocker is the **compound-postcondition discharge**, for which the
  mechanism is found (`#[verifier::tactus_tactic]` per-fn custom Lean closer) but the
  exact tactic string is the next rung (bootstrap-59). **So loop closure is now
  precisely scoped, with NO open feasibility question — only the discharge string +
  scaling to `wp_stm_sound`, then the tactus-core authoring itself.**
- (2026-07-15, opus-bootstrap59-authoring) **Q2 discharge string NAILED — bootstrap-59
  DONE** (probe32 now `19 verified, 0 errors`, axiom closure `[propext]` only; both
  `all_true_append` AND the recursive-induction `wp_sound` + `wp_sound_bites` verify).
  The reusable idiom for authoring the tactus-core soundness proofs:
  `#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split
  (simp_all (config := { zetaDelta := true }) [and_assoc]))")]` + per-arm `u_*`
  unfold-lemma CALLS in the induction body (height-recursive spec fns get no Lean
  eq-lemmas, so unfolds must enter the VC as hyps). See bootstrap-59 writeup + probe32
  `REPORT.md §Q2`. **The last open feasibility question is closed** — the umbrella's
  remaining tail is pure authoring/scaling (W5a-0 in tactus-core, then up the ladder),
  bearing the base-hash re-verify cost, not a mechanism unknown.

- (2026-07-16, fable-plan) **Authoring tail decomposed into cards** (board
  session with Danielle): **bootstrap-60** (probe33 — de-risk the one uncovered
  shape question, recursion-under-lambda in execSafeF's Seq arm, + freeze the
  authored model interface) → **bootstrap-61** (semantic model in tactus-core,
  one batched cache-churning edit) → **bootstrap-62** (straight-line + If
  proofs) → **bootstrap-63** (Call/Ret/DeadEnd/Assign + frame algebra) →
  **bootstrap-64** (Loop arm; scaffolds dropped → total `wp_stm_sound`) →
  **bootstrap-65** (prophecy + closure corollaries) → **bootstrap-66** (compose
  with the adequacy spine + permanent runner; closes this umbrella).

## Writeup

_umbrella still in progress. First rung (W5a-0) done + validated — see
bootstrap-49 + `probe-w0/probe21_w5a_sem/REPORT.md` + `DESIGN-W5-soundness.md`.
The loop closes only when the whole ladder is authored as Rust spec/proof fns in
tactus-core and emitted as a kernel-checked package; that final step is
explicitly staged and not yet begun._
