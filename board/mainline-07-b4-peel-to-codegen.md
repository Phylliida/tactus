---
title: "B4 — tactus_peel → codegen explicit structure; delete the macro"
status: todo
claimed_by:
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
---

## Description

`tactus_peel` exists only because loop goals stack `init ∧ maintain ∧ use` with
data-dependent nesting — but the emitter BUILT that conjunction and knows the
exact tree. Emit the explicit `refine ⟨?_, ?_⟩` / `intro` sequence per subgoal
instead of the recursive macro; then delete `tactus_peel` from the prelude.

Bonus win: each subgoal gets its own tactic position, so sourcemap spans point
at the SPECIFIC conjunct that failed instead of a macro invocation — better
error UX for free.

Spec: `DESIGN-transparent-automation.md` §4. Independent of the S-arc (can land
before or after S2c) — but note S1 currently emits `tactus_peel <;> omega` as a
selected tactic, and F7's biggest cluster validates against peel∘omega, so the
replacement must cover those call sites: the emitter emits the explicit intro/
refine prefix + `omega` per leaf instead.

Also reduces goal-shape degrees of freedom for the bootstrap verified-WP work
(§8 relation) — a side-benefit, not a dependency.

**Done when:** no emitted artifact references `tactus_peel`; macro deleted from
the prelude; suite green, 0 regressions on the 114-fn pool, tutorial 9/9;
sourcemap spans verified on one multi-conjunct loop example.

**Blocked by:** nothing (mutually independent per §9); coordinate with
mainline-05 if concurrent.
