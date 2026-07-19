---
title: "bridge ↔ N1-hoist reconciliation — leaf-normal emission reshaped production goals; ALL fixture bridges honest-fail post-merge"
status: todo
claimed_by:
created: 2026-07-18T09:30:00Z
updated: 2026-07-18T09:30:00Z
---

## Description

Post-merge (e2e-speed + leaf-normal emission, `8accb8d`), the W2b
differential gate found exactly what it exists to find: production's
goal emission changed shape under the frozen refWp mirror, and **every
fixture bridge now honest-fails** (`decide` proves `goals_eq … = 1`
false — 13/13 CLOSE-BROKE, probe9).

**Evidence** (use_multiarg, the minimal case):
- refWp reconstruction: `All 0 1 (All 3 2 (Let 7 8 (LeafE …)))`
- production now:       `All 0 1 (All 3 2 (All 17 14 (All 15 16 (All
  13 14 (All 11 12 (All 7 1 (All 9 10 (LeafE …))))))))`

Same params, same final leaf; the single `Let` became THREE
(witness, eq-hyp) binder pairs — DESIGN-leaf-normal-emission §N1:
spine-position lets emit as theorem binders `(tmp : T) (h : tmp = e)`,
and chained lets production formerly SUBSTITUTED now hoist as their own
pairs (hoisting is linear; substitution duplicated). Bool-typed lets
are excluded (stay wrap → still `Let`-shaped). N2 match-splitting
similarly reshapes match goals per-arm.

**Pattern 2 (use_clamped evidence, 2026-07-18):** FHyp rendering
changed UNIFORMLY — production emits hypotheses as NAMED binders
(`All(h, prop)`, the theorem-binder form) where refWp renders
`Imp(prop)`. This is a rendering-layer change, suggesting part of the
reconciliation belongs in tactus-core's `close_e` (mechanical: FHyp →
named All) rather than serializer assembly — the hoisted-let pairs
remain serializer territory (they need production's hoist classifier).

**Reconciliation options:**
- (A) **Serializer assembly (recommended — Option-2 precedent):** the
  serializer's goals/SST transcription re-derives production's hoist
  (same classifier: spine-position + non-Bool → `FBind(tmp, typ_id) ∘
  FBind(h, prop_typ_id)` with the eq-prop interned as a typ; term
  position / Bool → keep `FLet`). refWp stays FROZEN; the decide
  bridge validates the assembly per cert. Precedents: count_down
  If-join desugar (bootstrap-19), #128 ret-eq path, W6e value-if-lift.
- (B) Teach refWp the hoisted rendering — rejected on frozen-refWp
  grounds unless (A) hits a wall.

**Coordination gate:** main-side N1 still has an OPEN nondeterminism
flicker (hoist-order; coercion half fixed — memory
project_tactus_e2e_speedup). Bridging against a flickering emission is
a moving target — confirm with Danielle whether to start now or after
the flicker fix settles the order.

**Also in this arc (probe9/probe11 infra, FIXED 2026-07-18):** the
defs-collapse moved bare `TactusDefs` into the prelude cache with NEW
hashes; both runners' hardcoded `prelude-e81fbf9a86375c12` pin →
probe37-style glob over all `prelude-*` + `$CORE_OUT/pkg` on
`LEAN_PATH`.

**Done when:** probe9 fixture family bridges close again (including F20
mul_bound / AssertQueryNl), honest-fail classification updated for any
documented caveats, probe11 re-run, suite green.

**Blocked by:** possibly the main-side N1 flicker fix (Danielle's
call).
