---
title: "tgt defs family: `m3_blinker` fails — recursive spec fns terminate on `subrange u 2 (len u)` (drop-k, no companion) and `drop_base_run (drop_first W)` (nested/compound measure)"
status: done
claimed_by: opus-bootstrap46-subrange
created: 2026-07-14T21:40:00Z
updated: 2026-07-14T22:35:00Z
---

## Description

Surfaced once **bootstrap-45** unblocked `m1_guard`: with m1_guard building, the
full-krate tgt EXEC defs build reaches `m3_blinker` and fails on TWO recursive
spec-fn termination goals that the current `decreasing_by` menu cannot discharge:

```
TactusDefs_lib_exec__m3_blinker.lean:51: error: failed to prove termination
  h✝¹ : ¬ len u = 0
  h✝  : if h : (if h : len u ≥ 2 then index u 0 = Gen 1 else False)
          then index u 1 = Gen 3 else False
  ⊢ len (subrange u 2 (len u)) < len u

TactusDefs_lib_exec__m3_blinker.lean:68: error: failed to prove termination
  h✝ : ¬ if x : len W = 0 then True else ¬ index W 0 = Gen 2
  after : seq.Seq symbol.Symbol := Seq.drop_first W
  ⊢ len (drop_base_run (Seq.drop_first W)) < len W
```

Both are the EXEC scope (single-attempt ladder), so this sinks the whole exec
defs family ⟹ gate skipped ⟹ no in-gate bridge (blocks **bootstrap-39**).

## Why the current menu can't crack them (two DISTINCT gaps)

The `decreasing_by` menu (`to_lean_fn.rs:decreasing_by_tactic`) has seq-measure
companions ONLY for `Seq.drop_first` (subrange 1 len) and `Seq.drop_last`
(subrange 0 (len-1)), emitted by `seq_measure_companion_cmd` in `generate.rs`.

1. **`ffnf` (line 51) — drop-k recursion.** The recursive call is on
   `subrange u 2 (len u)` — a raw `subrange` with start=2, NOT routed through a
   named `drop_first`/`drop_last` fn. So `apply Seq.drop_first_len_lt` doesn't
   unify (start 1 ≠ 2), and there is no `subrange_len_lt` companion at all. The
   goal `len (subrange u 2 (len u)) < len u` holds because `subrange u 2 (len u)`
   has length `len u - 2` and the guard gives `len u ≥ 2` (in the nested dite
   `h✝`). Needs: a general **`subrange_len_lt`-style companion** (from the vstd
   `axiom_seq_subrange_len` that `seq_measure_companion_cmd` already cites) that
   proves `len (subrange s j (len s)) < len s` given `j ≥ 1 ∧ j ≤ len s` — plus
   an omega step to pull `len u ≥ 2` out of the nested `dite` guard (bootstrap-44/45
   `simp_all <;> omega` territory).

2. **`split_q`/`base_run`-family (line 68) — nested/compound measure.** The call
   is `drop_base_run (Seq.drop_first W)`. The goal
   `len (drop_base_run (drop_first W)) < len W` needs the COMPOSITION of two
   facts: `len (drop_base_run x) ≤ len x` (drop_base_run is length-non-increasing —
   itself a recursive fn returning a suffix of its input) AND
   `len (drop_first W) < len W` (given `len W ≠ 0`, from `h✝`). No companion
   asserts `drop_base_run`'s length-monotonicity, and even with one, the closer
   would need to CHAIN it with the drop_first companion. This is the harder of the
   two — it needs a per-fn "output length ≤ input length" companion for
   `drop_base_run` (an induction on the fn's own recursion), auto-generated.

## Scope of the fix (NOT the same as bootstrap-44/45)

bootstrap-44/45 were pure `decreasing_by` STRING edits (add a `simp_all <;> omega`
rung). This card is different — it needs **new companion-lemma GENERATION** in
`generate.rs` (`seq_measure_companion_cmd` and its dispatch), not just a closer
tweak. Candidate directions (pick the least-magic; consult
[[feedback_minimal_automation]] / [[feedback_transparency_is_faithfulness]]):
- Generalize `seq_measure_companion_cmd` to emit a `{fn}_len_lt` for ANY
  `subrange s j (len s)` measure with `j ≥ 1` (drop-k), keyed on the recursion's
  actual subrange start, and add an `apply` rung citing it.
- For the nested `drop_base_run (drop_first W)` case: emit a length-monotonicity
  companion `len (drop_base_run x) ≤ len x` for suffix-returning recursive fns
  (detectable: every branch returns either the input or a recursive call on a
  strictly-shorter arg), and add a chaining rung
  `(apply Nat.lt_of_le_of_lt <;> (first | apply <mono> | apply drop_first_len_lt | …))`.
- Or (more invasive, cross-cutting): recognize this whole family of Verus spec
  fns as structurally-recursing on a `Seq` suffix and emit a uniform suffix
  measure. Larger; only if the drop-k + mono approach proves too ad hoc.

Prefer verifying against BOTH failing sites, and re-running the bootstrap-39 run
#2 recipe to confirm the exec defs family builds end-to-end (and watch for the
NEXT module the chain reveals — m4_defect_flow is right behind m3_blinker and may
have its own shape).

## Repro / validation

Rebuild the bootstrap binary, run the bootstrap-39 run #2 recipe (no `--emit-lean`,
no `-V cache`); inspect `$TACTUS_LEAN_OUT/lib/TactusDefs_lib_exec__m3_blinker.lean.failed`
and standalone-elaborate it:
```
LEAN_PATH="$OUT/lib:$HOME/.cache/tactus/prelude-<hash>" \
  lean $OUT/lib/TactusDefs_lib_exec__m3_blinker.lean.failed
```
NOTE: unlike m1_guard (bootstrap-45), these may reproduce even standalone (the
termination goals fail on their own math, not just the in-gate `decide` form) —
so a standalone repro is a valid dev loop here.

**Done when:** no `TactusDefs_lib_exec__m3_blinker.lean.failed` dump and no
`m3_blinker` termination errors; the exec defs family builds past m3_blinker.

## Progress

- (2026-07-14, opus-bootstrap45-seqrung) Filed from the post-bootstrap-45 gate run
  (`/tmp/w4a-tgt-ingate7`). m1_guard now builds; m3_blinker is the next exec-chain
  sink. Captured both termination goals from the log. Root-caused to two distinct
  gaps: a missing drop-k (`subrange s j len`) companion and a missing
  length-monotonicity companion for the nested `drop_base_run (drop_first W)`
  measure. Bigger than a closer-string edit — needs `generate.rs` companion
  generation. NOT started.

- (2026-07-14, opus-bootstrap46-subrange) **SCOPE SPLIT + PIECE A (drop-k
  subrange companion) LANDED.** Split the two goals: this card now = the `ffnf`
  drop-k subrange half; the harder `split_q`/`drop_base_run`-monotonicity half
  moved to **bootstrap-47** (fully designed + Lean-prototyped there).
  - Prototyped BOTH fixes standalone against the real emitted oleans (Lean
    4.25.0): `/tmp/probe_ffnf.lean` (subrange, exit 0), `/tmp/probe_splitq.lean`
    + `/tmp/probe_dbr2.lean` (mono, exit 0).
  - Piece A impl: new `seq_subrange_tail_companion_cmd` in `generate.rs` emits a
    general `Seq.subrange_tail_len_lt` (`len (subrange s j (len s)) < len s` for
    `j ≥ 1`, proven from `axiom_seq_subrange_len` + omega), piggy-backed on the
    `Seq.drop_first` emission site (emit-once). Added an `apply {ns}.Seq.subrange_tail_len_lt`
    rung to `decreasing_by_tactic()` in `to_lean_fn.rs`, before the drop_first
    rung (disjoint heads).
  - Rebuilt the binary (fork vargo, 14:44, vstd 1530/0). Re-ran the bootstrap-39
    run #2 gate (`/tmp/w4a-bs46`). CONFIRMED: the regenerated
    `TactusDefs_lib_exec__seq_lib_impl__0.lean:27` carries
    `theorem lib.Seq.subrange_tail_len_lt …`, and its **olean BUILT** (119088 B,
    14:47) — i.e. the companion elaborates in the REAL emission, not just the
    prototype. [m3_blinker olean build in flight; expect only the `split_q`
    line-68 error to remain — see bootstrap-47.]

## Writeup

**PIECE A (drop-k `subrange` companion) DONE + GATE-VALIDATED (2026-07-14,
opus-bootstrap46-subrange).** The `ffnf` termination goal
`len (subrange u 2 (len u)) < len u` now closes in the REAL package gate. The
harder `split_q`/`drop_base_run`-monotonicity half was split out to
**bootstrap-47** (fully designed + Lean-prototyped, not yet implemented), so
`m3_blinker` still has ONE residual termination error (split_q, line 68) and the
module does not yet build — **bootstrap-39 stays blocked on bootstrap-47.**

### What was wrong
`m3_blinker.ffnf` recurses on `u.subrange(2, u.len())` (a drop-2). The Lean
`decreasing_by` menu only had `drop_first`/`drop_last` measure companions
(subrange starts 1 / 0), so `len (subrange u 2 (len u)) < len u` had no
`apply`-able head and fell through to `decreasing_tactic`, which can't crack it.
(A different class from bootstrap-44/45, which were pure closer-string edits —
this needed a NEW companion lemma.)

### The fix (two edits, both additive)
1. **`lean_verify/src/generate.rs` — `seq_subrange_tail_companion_cmd`** (new):
   emits a general
   `theorem lib.Seq.subrange_tail_len_lt (s) (j:Int) (h1:1≤j)(h2:j≤len s): len (subrange s j (len s)) < len s := by have := axiom_seq_subrange_len s j (len s) (by omega); omega`.
   Emitted ONCE, piggy-backed on the `Seq.drop_first` emission site (guarded by
   `rel == "Seq.drop_first"`), where the axiom + `Seq.len` + `Seq.subrange` are
   all in scope. Named in drop_first's own `{ns}.Seq.*` namespace (strip the
   trailing method segment off `lean_name(drop_first.path)`), so the tactic
   citation resolves via the part-import chain like `drop_first_len_lt`. Rides
   drop_first's FnGroup seg (dep-order: drop_first, a vstd primitive, precedes
   user callers). Gated by `push_lenient`.
2. **`lean_verify/src/to_lean_fn.rs` — `decreasing_by_tactic()`**: added
   `(apply {ns}.Seq.subrange_tail_len_lt <;> (first | assumption | omega | (simp_all <;> omega) | simp_all))`
   BEFORE the drop_first rung. `apply` unifies `j` from the literal subrange
   start (2 for ffnf), leaving side goals `1 ≤ j` (omega) + `j ≤ len u` (nested
   dite guard `len u ≥ 2`). Heads disjoint (`subrange` vs `Seq.drop_first`) ⟹
   ordering immaterial.

### Validation
- Standalone prototype `/tmp/probe_ffnf.lean` (companion + termination-only copy
  of ffnf, real guards/recursive-arg shapes) → exit 0 against the real oleans.
- Rebuilt binary (fork vargo, 14:44, vstd 1530/0). Re-ran bootstrap-39 run #2
  gate (`/tmp/w4a-bs46`). Regenerated `…seq_lib_impl__0.lean:27` carries the
  companion + its **olean BUILT** (119088 B). Regenerated `m3_blinker` shows in
  the REAL gate log **exactly ONE** termination error — `m3_blinker.lean:68` =
  split_q; `ffnf`'s decreasing_by (line 51) is CLEAN. Piece A works end-to-end.

### Honest caveats
- **Standalone ≠ in-gate (again).** Elaborating the `m3_blinker.lean.failed`
  dump STANDALONE reports ~8 termination errors (29/33/55/68/72/76/80/84), but
  the REAL in-gate build reports only line 68 — the bootstrap-45 ambient-
  LEAN_PATH / Decidable-resolution divergence. **The gate log is ground truth**;
  don't trust standalone `.failed` elaboration for these files. For bootstrap-47
  dev-looping, prototype against fresh minimal defs (`/tmp/probe_splitq.lean`),
  not the `.failed` dump.
- **Emission-site limitation**: the subrange companion emits only on the
  `Seq.drop_first` site; a crate recursing on `subrange s k (len s)` WITHOUT
  emitting `Seq.drop_first` wouldn't get it. Holds today (ffnf uses drop_first);
  hoisting to the axiom-flush site is an easy follow-up.
- Module still fails (split_q) ⟹ exec defs family can't build past m3_blinker ⟹
  bootstrap-39 blocked. See **bootstrap-47**.
