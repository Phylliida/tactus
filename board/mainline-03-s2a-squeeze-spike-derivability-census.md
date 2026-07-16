---
title: "S2a — squeeze spike + derivability census over the 145 T2 theorems"
status: todo
claimed_by:
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
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
