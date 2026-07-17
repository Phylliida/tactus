---
title: "S2a — squeeze spike + derivability census over the 145 T2 theorems"
status: done
claimed_by: kimi
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T22:25:00Z
---

## Description

THE key measurement brick of the squeeze arc — measurement, NOT machinery. Do not
build any persistence layer in this task.

Two halves:

1. **Squeeze spike (empirical-first, scratch Lean before Rust).** Confirm the
   used-lemma extraction API on the pinned toolchain (v4.25.0): `simp_all?` /
   `Simp.Stats` used-theorem tracking (`DESIGN-transparent-automation.md` §3.1
   flags "confirm exact API"). Hand-squeeze a few of the 145 T2 theorems to
   `simp only [named] (<;> omega)` and confirm the minimized forms close.
   Scratch loop: `cd tactus/lean-project && LEAN_PATH=~/.cache/tactus/prelude
   lake env lean file.lean`.

2. **Derivability census.** Extend `tools/rung-attrib/fast_attrib.py` (or a
   sibling harness) to squeeze ALL 145 T2 theorems in the Brick-1 pool and
   classify each minimized lemma list on TWO axes:

   **Axis 1 — derivable?** (LOCALITY CONSTRAINT, 2026-07-16 conversation: the
   candidate lemma set is a function of the obligation's OWN semantic inputs
   only — the goal's mentioned symbols and the callee's spec. NOT "whatever
   `_tactus_bc` hyps happen to be in scope" — ambient-scope dependence means
   distant edits move the derived list, deterministic-but-surprising.)
   - **DERIVABLE**: every lemma is computable from the site's semantic inputs —
     preconditions: callee's requires-mentioned spec-fn defs; postconditions:
     own ensures-mentioned defs; plus named axioms/accessor lemmas OF SYMBOLS
     THE GOAL MENTIONS (e.g. goal mentions Seq.subrange → the named subrange
     axioms).
   - **GOAL-SPECIFIC**: needs lemmas outside that computable set (creative
     choices — inline-proof candidates).

   **Axis 2 — terminal shape** (the predictability ladder):
   - **UNFOLD-THEN-DECIDE**: closes as `simp only [defs] <;> omega/rfl/decide`
     where simp does pure definitional unfolding and a decision procedure
     finishes. Statable spec: "succeeds iff the goal, after unfolding these
     named defs, is in the decided fragment" — fragment-style predictability,
     the strongest tier.
   - **REWRITE-CLOSURE**: needs named-lemma rewriting beyond unfolding
     (quantified seq axiom instantiation etc.) — deterministic and visible,
     but success is rewriting reachability, operationally predicted.
   - **HEURISTIC-NEEDED**: neither → inline proof, no machinery.

   Report per-kind × per-axis rates (preconditions are 81% T2 and the doc
   predicts their lists are "small and formulaic" — test that prediction), plus
   the pred-twin dedup view (~70 effective theorems). The unfold-then-decide
   share is the headline number: it measures how much of T2 gets FULLY
   predictable (not just deterministic) treatment.

Output: `MEASUREMENT-s2a-derivability.md` + per-theorem CSV. This census is the
decision data for mainline-04 — if the derivable share is high, pin STORAGE is
unnecessary and the whole arc stays two-surface.

**Done when:** census doc committed with per-kind derivability table, the
squeeze API confirmed working on our toolchain, and ≥3 hand-validated squeezed
theorems demonstrating the minimized forms elaborate.

**Blocked by:** NOTHING — prerequisite CLEARED 2026-07-16: bootstrap-72 sync
done (merge `a254eb8`, full battery green, tgt package gate live again).
Fresh artifact harvest with the merged binary → `/tmp/census-emit`. Note for
the harness: post-sync artifacts import `TactusDefs_lib_exec`, so elaboration
needs the defs oleans on LEAN_PATH (or harvest from a live run's island
texts); the emit/live-divergence bug from mainline-02's writeup remains real
for trees where defs FAIL, just no longer bites here. Work happens on the
`squeeze` branch (worktree `../tactus-squeeze`, provisioned 2026-07-16: z3 +
tree-sitter + vargo binary copied in; build its own release binary only when
emitter code changes start).

## Progress

- (2026-07-16 ~20:30Z, kimi) Claimed. Starting with the spike half: confirm
  the used-lemma extraction API on the pinned toolchain, then hand-squeeze
  ≥3 T2 theorems before extending the harness.
- (2026-07-16 ~21:00Z, kimi) **Spike DONE, API confirmed.** On v4.25.0,
  swapping a theorem's `tactus_auto` closer for `simp_all?` prints
  `Try this: [apply] simp_all only [...]` — that's the used-lemma
  extraction; no `Simp.Stats` plumbing needed for the census. Scratch
  loop: bare `lean` (nix store 4.25.0) with
  `LEAN_PATH=~/.cache/tactus/prelude:/tmp/w4a-b2-ingate4/lib` (the Jul-14
  `TactusDefs_lib_exec.olean` elaborates the Jul-16 `/tmp/census-emit`
  harvest clean — defs didn't drift across the sync).
  Hand-validated 5 theorems across kinds (base_swap precondition,
  copy_word loop-invariant, reduction postcondition,
  find_cancellation postcondition, tower_peel assert): **every one
  squeezed to the SAME ~12-lemma core-only set** (propositional
  normal forms + Int/Nat cast cleanup; zero `lib.*` lemmas, zero
  `_tactus_bc` axioms used), and every minimized form re-elaborates —
  ~30% faster per theorem (4.2s→2.8s on the spike). If this holds over
  the pool, the headline derivation rule is a fixed site-independent
  `simp_all only [core-normalizer]` line.
- (2026-07-16 ~21:15Z, kimi) Harness built: `tools/rung-attrib/
  squeeze_census.py` (sibling of fast_attrib, same combined-file trick
  ×2 phases: query with `simp_all?`, verify with minimized lists).
  Enumerates REAL dotted theorems under each T2 bucket (145 buckets →
  N≥145 theorems). Three bugs shook out in smoke tests: (1) dropped
  non-target blocks incl. the import; (2) `Try this` messages print
  bare, no file:line — mapped by elaboration order with a per-theorem
  single-spike fallback on count mismatch; (3) verify-phase failure
  detection must match `: error` only — the unusedSimpArgs linter emits
  warnings on minimized lists that still elaborate. base_swap smoke:
  14/14 DERIVABLE. Full census over the 88 files running.
- (2026-07-16 ~21:50Z, kimi) **Census v1 complete: 295 real theorems
  from the 145 buckets.** Raw v1: 90.8% DERIVABLE / 6.4% MIN-FAILS /
  2.7% GOAL-SPECIFIC. Two root causes found on inspection, both
  fixable in-protocol (not in the pool):
  (1) ALL 8 "GOAL-SPECIFIC" theorems are misclassified — their extra
  `lib.*` lemmas are datatype discriminant/accessor lemmas
  (`lib.option.Option.Some_val0`, `lib.runtime.RuntimeSymbol.isGen`)
  whose type IS goal-mentioned → derivable by the task's own "accessor
  lemmas of symbols the goal mentions" clause. Classifier now walks
  the lemma's dotted prefixes against goal-mentioned names.
  (2) The 19 "MIN-FAILS" are a protocol gap: their T2 win came via the
  composed rung/case-split, and `simp_all?`'s suggestion — generated
  against its own progress state — doesn't replay standalone (plain
  `simp_all` also does NOT close the worked example,
  copy_word_444_13_13). But the minimized list + `<;> omega` tail DOES
  close it — exactly §3.1's "+ omega tail when the winning rung was
  the composed one". Verify phase now retries failures with the omega
  tail before declaring MIN-FAILS. Census v2 running with both fixes.
- (2026-07-16 ~22:20Z, kimi) **DONE — census v2 + union validation.**
  v2: 282/295 DERIVABLE (95.6%), 7 GOAL-SPECIFIC, 6 MIN-FAILS.
  Union-set validation: one fixed 43-lemma `simp_all only [CORE]`
  closes 268/280 bare; `<;> omega` tail on failures closes the other
  12 — **280/280, zero residual**. Residue = 13 theorems in 2 clusters
  (Option accessors ×7 in coset_group; no-replay-closes ×6 → 4
  effective after twin dedup). Full tables + interpretation in
  `MEASUREMENT-s2a-derivability.md`; per-theorem data in
  `tools/rung-attrib/results-2026-07-16-squeeze-census.csv`; harness
  `squeeze_census.py` + `union_core_test.py` committed.

## Writeup

**Done-when review:** per-kind derivability table committed ✓
(MEASUREMENT doc §4); squeeze API confirmed working on v4.25.0 ✓
(§2 — `simp_all?` → parseable `Try this: [apply] simp_all only [...]`);
≥3 hand-validated squeezed theorems ✓ (5, across pre/post/loop/assert
kinds, all re-elaborated).

**Headline for mainline-04:** the derivable share is 95.6%, and the
derivation is the strongest possible form — a SINGLE fixed,
site-invariant 43-lemma `simp_all only [CORE]` list (+`<;> omega` on
the 12 composed-rung theorems), validated 280/280. No per-obligation
computation at all, let alone storage. The pin sidecar (candidate 4)
is dead for this pool; candidate 1's rule budget is ONE rule. The
residue (13 theorems, 2 clusters, 3 effective sites) is inline-proof
shaped → candidate 2 exactly. The two-surface end state survives
intact.

**Caveats Danielle should see:** (a) the axis-2 headline is
REWRITE-CLOSURE, 0% UNFOLD-THEN-DECIDE — the pool's goals are already
propositional/arith facts over spec vocabulary, so predictability is
"fixed normalizer + decider tail", not fragment membership; (b)
`simp_all?` suggestions don't always replay standalone (13/295 needed
the omega tail) — the minimized form must be stated as list-plus-tail;
(c) census is gt-corpus only — arithmetic-heavy exec crates may show a
different mix (the emod tail already hints at it); (d) the union list
is empirically closed-world over 280 theorems — new obligation shapes
can fall out of it, which fails LOUD (unclosed goal at the named
obligation), the acceptable failure mode per §3.3.

**Handoff to mainline-05 (if 04 picks derivation-first):** the
43-lemma list and the composed-rung flag are recorded in the
measurement doc §6/§5.1; the emitter already knows the winning rung
per obligation kind (that's how Brick 1 measured it), so the
derivation is one lookup away from the emission path S1 built in
`tactic_select.rs`.
