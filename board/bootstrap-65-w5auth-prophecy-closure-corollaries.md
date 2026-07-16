---
title: "W5-auth-5 — model-level corollaries: prophecy + closure theorems (probe25/26 authored)"
status: done
claimed_by: fable-b65
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T22:10:00Z
---

## Description

Author the W5d/W5e results as tactus-core proof fns. Neither adds a StmData
arm (both encodings use existing constructors), so these are corollaries of
`wp_stm_sound` + the frame algebra — no new induction:

- **Prophecy (probe25):** `prophecy_sound` — the reference WP for
  `resolve; assert P(*x)` reduces exactly to `∀ x_fut, resolve(x_fut) →
  P(x_fut)` — plus the temporal-placement discriminator
  `prophecy_swapped_sound` (`assert; resolve` reduces to the ungated form; the
  pair differing is what proves `frame_after` places the resolve pin
  correctly).
- **Closures (probe26):** `closure_creation_sound` — the WP of
  `Seq (DeadEnd body) (Assume ext)` reduces exactly to `execSafeF f body st` —
  plus the isolation pair `closure_deadend_isolates` / `seq_assume_gates`
  (again: the two differing is the check that DeadEnd quarantines).

These are statement-shaped reductions over concrete small literals in the
probes; authored versions should keep the same discriminating-pair structure
(a mutation of either side must flip a decide/verify), since that structure is
the negative control.

**Done when:** tactus-core `--lean-all-proofs` 0 errors with all four
theorems (+ their discriminating pairs) verified; axiom closure clean.

**Blocked by:** bootstrap-64.

## Progress

- (2026-07-16, fable-b65) Landed first try: **138 verified, 0 errors**,
  package gate green (48/50 reused).

## Writeup

All six probe25/probe26 theorems authored as tactus-core proof fns, each a
non-recursive corollary of `wp_stm_sound` + the frame algebra (6 new
frame_after/frame_append u_* unfolds added):

- `prophecy_sound` — `resolve; assert P(*x)` under the `∀ x_fut` borrow
  frame reduces EXACTLY to `∀ n, hp(resolve, upd(st,x,n)) ⟹
  he(P, upd(st,x,n))` — the ∀-final-value reading, gated by the pin.
- `prophecy_swapped_sound` (discriminator) — the swapped program reduces
  to the UNGATED form; the pair differing proves temporal placement.
- `closure_creation_sound` — `Seq (DeadEnd body) (Assume ext)` reduces to
  the body obligation under the enclosing frame (over an OPAQUE body and
  arbitrary frame f — fully general).
- `closure_deadend_isolates` / `seq_assume_gates` (discriminator pair) —
  DeadEnd quarantines the body assumption; bare Assume gates.
- `closure_forwards_contract` — the continuation sees the external spec.

Closer = the bites variant (no case split); bodies = u_* chains with
concrete constructor literals (`#[trigger]` on spec_fn-variable
applications like `hp(resolve, upd(st,x,n))` works fine). The W5
authoring ladder bootstrap-60..65 is now complete; the umbrella's last
rung is bootstrap-66 (adequacy-spine composition + permanent runner).
