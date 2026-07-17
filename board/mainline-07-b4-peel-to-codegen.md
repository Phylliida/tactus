---
title: "B4 — tactus_peel → codegen explicit structure; delete the macro"
status: in_progress
claimed_by: kimi
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

## Progress

- (2026-07-17 ~01:20Z, kimi) Claimed. Constraint discovered up front:
  user-crate `tactus_peel` references are exactly the 4 S2c residue
  overrides in gt (no others in gt/tutorial); they migrate as part of
  this task.
- (2026-07-17 ~02:30Z, kimi) **Landed after three empirically-falsified
  designs** (the interesting part is WHY they failed):
  1. `refine ⟨by t, by t⟩` flattening — anonymous-constructor flattening
     picks the RIGHT-nested reading; left-nested ∧-trees must be
     mirrored explicitly (generator does).
  2. Unguarded `intro _; intro _` — tactic prefixes (user proof text)
     consume the statement's wrappers; intros then error where the
     macro's `skip`-fallthrough succeeded (is_inverse_pair_exec).
  3. `try`-guards + newline steps — `try` takes the following tactic
     SEQUENCE as its argument (`try (intro _); first | …` parses as
     `try ((intro _); first | …)` and no-ops the whole chain; the
     error presents as an unclosable goal two branches later). And
     newline-separated steps break the layout of parenthesized
     `first`-alternatives (paren content must stay indented past the
     paren's column; `first` alternatives cannot span lines).
  FINAL SHAPE: `first | rfl | decide | omega | (<explicit peel>;
  first | rfl | decide | omega) | (simp_all only [CORE] <;> omega)` —
  the bare kernel ladder runs FIRST (prefix-transformed goals close
  there), the explicit per-shape peel prefix is the second branch
  (unguarded `;`-joined intros + `refine ⟨by …⟩` mirror), CORE last.
  The guard lives in the BRANCH ORDER, not the steps.
- (2026-07-17 ~03:10Z, kimi) **All green:** gt gate 3116/0 (package
  gate live) · tutorial 10/10 · suite 138/140 (same 2 pre-existing
  Z3-path state_machines failures as main-line, verified side-by-side)
  · lean_verify 20/20 tactic_select unit tests (7 new peel-shape pins).
  Prelude `tactus_peel` macro DELETED; sanity allowlists updated;
  gt's 4 residue overrides migrated to peel-free text. Sourcemap win
  confirmed: a deliberately-false middle loop-invariant conjunct
  reports its own Rust span (`at …:13:13 (loop invariant)`) — the
  specific conjunct, not a macro invocation.
