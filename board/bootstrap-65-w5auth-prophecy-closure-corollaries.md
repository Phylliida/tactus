---
title: "W5-auth-5 — model-level corollaries: prophecy + closure theorems (probe25/26 authored)"
status: todo
claimed_by:
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T17:15:00Z
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
