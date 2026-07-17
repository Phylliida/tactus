---
title: "B4 — tactus_peel → codegen explicit structure; delete the macro"
status: done
claimed_by: kimi
created: 2026-07-16T17:28:00Z
updated: 2026-07-17T03:40:00Z
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

## Writeup

**Done-when review, all satisfied:** no emitted artifact references
`tactus_peel` (fresh `--lean-all-proofs` emit, 2956 fns: **0**
references); macro deleted from `TactusPrelude.lean`; suite green at
main-line parity (138/140, the 2 failures being the pre-existing
Z3-path state_machines cases verified identical on main-line); 0
regressions on the pool (gt gate **3116 verified / 0 errors**, package
gate live); tutorial **10/10**; sourcemap spans verified on a
multi-conjunct loop example (false middle conjunct reports its own
Rust span at the specific invariant clause).

**What landed:** `render_peel` in `lean_verify/src/tactic_select.rs` —
walks the goal tree: `intro` per ∀ binder / antecedent / goal-let
(anonymous-constructor patterns for ∧/×-typed hypotheses), `refine
⟨by <leaf>, …⟩` mirroring the conjunction tree exactly (left-nested
trees must be mirrored, not flattened). S1's `PeelOmega` and the
derived closer's second branch use it:
`first | rfl | decide | omega | (<peel>; first | rfl | decide | omega)
| (simp_all only [CORE: 51] <;> omega)`. The AssertQuery fallback is
a marker (`DERIVED_MARKER`) expanded per-goal at the emit chokepoint
(scope composition happens once, goal shapes arrive per-theorem).

**Falsified designs (the transferable lessons):** (1) `refine`
flattening is right-nested-only; (2) `try`-guards — `try` takes the
following tactic SEQUENCE as argument, so `try (intro _); first | …`
no-ops the whole chain; (3) newline-separated steps inside
parenthesized `first`-alternatives break layout (and `first`
alternatives cannot span lines). Final rule: `;`-joined unguarded
steps inside parenthesized alternatives, with the guard living in the
branch ORDER (bare kernel ladder first, so prefix-transformed goals
never need the peel branch).

**Follow-ons noted:** the prelude still carries `tactus_first`,
`tactus_case_split`, `tactus_auto` (discover-mode; B5/B6 territory);
the derived closer's CORE branch and the kernel rungs are the only
default-emission tactics now — the "no search tactic in default
artifacts" gate claim (mainline-09) is one prelude-split away from
being assertable.
