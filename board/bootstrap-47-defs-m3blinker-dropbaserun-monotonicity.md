---
title: "tgt defs family: `m3_blinker.split_q` fails — nested `drop_base_run (drop_first W)` measure needs a per-fn length-monotonicity companion + chaining rung"
status: todo
claimed_by:
created: 2026-07-14T22:20:00Z
updated: 2026-07-14T22:20:00Z
---

## Description

The SECOND (harder) half of the original bootstrap-46 pair. bootstrap-46
landed the drop-k `subrange` companion (fixes `ffnf`); this card is the
`split_q` termination goal:

```
TactusDefs_lib_exec__m3_blinker.lean:68: error: failed to prove termination
  h✝ : ¬ if x : len W = 0 then True else ¬ index W 0 = Gen 2
  after : seq.Seq symbol.Symbol := Seq.drop_first W
  ⊢ len (drop_base_run (Seq.drop_first W)) < len W
```

`split_q` recurses on `drop_base_run(drop_first W)`. `drop_base_run` is a USER
recursive spec fn (m3_blinker.rs:1721) that returns a **suffix** of its input:

```rust
pub open spec fn drop_base_run(W: Word) -> Word
    decreases W.len()
{ if W.len() == 0 || W[0] == Symbol::Gen(2) { W }
  else { drop_base_run(W.drop_first()) } }
```

The decreasing goal needs the COMPOSITION of two facts:
`len (drop_base_run x) ≤ len x` (drop_base_run is length-non-increasing) AND
`len (drop_first W) < len W` (given `len W ≠ 0`). The current `decreasing_by`
menu has neither the monotonicity fact nor a chaining step.

## VALIDATED design (Lean side proven, exit 0 — see prototypes)

Both halves elaborate standalone against the REAL emitted oleans
(`/tmp/probe_splitq.lean`, Lean 4.25.0, LEAN_PATH = `/tmp/w4a-tgt-ingate7/lib`
+ prelude-c9213499d9bb3fce). Two pieces:

### 1. Per-fn monotonicity companion `{fn}_len_le`

For a "suffix-recursive" spec fn `f : Seq A → Seq A` (every branch returns
either the arg `W` or a recursive call `f(drop_first W)`), emit:

```lean
theorem {fn}_len_le (W : Seq A) : len (f W) ≤ len W := by
  fun_induction f W <;>
    first
      | omega
      | (rename_i x h ih; have hlt := {ns}.Seq.drop_first_len_lt A x (by omega); omega)
```

- `fun_induction f W` uses Lean's auto-generated `f.induct`. Base case →
  goal `len W ≤ len W`, `omega` closes. Step case → `rename_i x h ih` names
  the (inaccessible) recursion var / guard / IH; `drop_first_len_lt x (by omega)`
  supplies `len (drop_first x) < len x` (the `by omega` reads `¬ len x = 0`
  out of the guard `¬(len x = 0 ∨ …)` — omega handles the propositional
  `¬(_ ∨ _)` over an opaque `index`-eq atom); `omega` chains IH + hlt.
- `rename_i` is name-AGNOSTIC (renames "the last N inaccessibles"), robust to
  Lean's `x✝`/`h✝`/`ih1✝` autogen names. Assumes single recursive call
  (arity 3 in the step). NOTE: goal in the step is `len (f (drop_first x)) ≤ len x`
  with IH `len (f (drop_first x)) ≤ len (drop_first x)` — confirmed via
  `trace_state` (`/tmp/probe_dbr2.lean`).

### 2. Chaining rung in `decreasing_by_tactic()`

```
(apply Nat.lt_of_le_of_lt <;> (first | apply {mono_i} | … | apply {ns}.Seq.drop_first_len_lt <;> (first | assumption | omega | (simp_all <;> omega) | simp_all)))
```

`apply Nat.lt_of_le_of_lt` splits `len (g (drop_first W)) < len W` into
`len (g (drop_first W)) ≤ ?b` and `?b < len W`; `<;>` runs the `first` on both.
Subgoal 1 unifies via `apply {g}_len_le` (instantiating `?b := len (drop_first W)`);
subgoal 2 closes via `drop_first_len_lt`. Metavariable ordering is SAFE
(confirmed: prototype elaborates; local model concurred — the `first` bag only
unifies the mono whose `≤`-head matches, and short-circuits).

## THE architecture fork (decided: option a)

The chaining rung cites SPECIFIC mono names (`{g}_len_le`). The shared menu
string is emitted per-fn but is identical for all. Resolution (local model +
my analysis both favor **(a)**):

- **(a) growing bag** — thread a `Set<String>` of emitted mono-companion names
  into `decreasing_by_tactic()`; splice `first | apply mono1 | apply mono2 | …`
  into the chaining rung. Safe because each `apply mono_i` only unifies when
  the goal's `≤`-head matches that fn; `first` short-circuits. Offloads the
  "which mono?" decision to Lean unification — no per-fn recursive-call
  analysis needed. Cost: signature change (thread the name-set through
  `emit_spec_fn`/`emit_proof_fn` → `decreasing_by_tactic`).
- (b) per-fn append — analyze THIS fn's recursive-call args for `g(drop_first W)`
  with a mono-companion'd `g`, append a targeted rung. Cleaner scoping but
  needs recursive-call pattern analysis. REJECTED as more code for no
  robustness gain.

## Implementation steps (NOT started)

1. `generate.rs`: `seq_mono_companion_cmd(f, all_fns, bc_lemma_funcs) -> Option<Command>`
   emitting `{fn}_len_le` as above. Name in the fn's own namespace.
2. `generate.rs`: DETECTION of suffix-recursive fns. A `spec fn f(W: Seq) -> Seq`
   whose every branch is (return `W`) | (return `f(W.drop_first())`). Inspect the
   VIR `FunctionX` body (SST/expr). Must return the SAME elem-type Seq. Be
   conservative — false negatives just leave the fn failing termination as
   today; false positives would emit an unprovable `{fn}_len_le` and poison the
   file (so `push_lenient` must gate it). Consider proving the emitted lemma is
   sound only for the exact shape matched.
3. Emit the mono companion right AFTER the fn's own def (dep-order), so
   `split_q`'s later decreasing_by resolves it via the part-import chain (mirror
   the seq-companion seg tagging).
4. `to_lean_fn.rs`: thread the mono-name set into `decreasing_by_tactic()` and
   splice the chaining rung (option a).
5. Rebuild binary (fork vargo, `tactus-bootstrap/source`, `vargo build --release`);
   run the bootstrap-39 run #2 recipe; confirm no `m3_blinker` termination
   errors and the exec defs family builds past m3_blinker (WATCH the next
   module — `m4_defect_flow` is right behind and may have its own shape).

## Alternative worth weighing (reuse the user's own lemma)

The crate ALREADY proves `lemma_drop_base_run_len : drop_base_run(W).len() ≤ W.len()`
(m3_blinker.rs:1727) and `#[via_fn] split_q_decreases` (1742) is the Verus/Z3
termination proof. If proof fns land in the defs layer as Lean theorems, the
chaining rung could cite the user lemma instead of a generated one — but the
generic menu still can't NAME it (same naming problem → same option-(a) bag).
Generating `{fn}_len_le` is simpler than matching arbitrary user lemma names.
The deepest-but-largest fix (honor the `#[via_fn]`/`decreases_by` proof by
TRANSLATING it to Lean `decreasing_by`) is out of scope — that's the whole
project's hard problem.

## Repro / validation

Same as bootstrap-46: rebuild, run bootstrap-39 run #2, inspect
`$TACTUS_LEAN_OUT/lib/TactusDefs_lib_exec__m3_blinker.lean.failed`. After
bootstrap-46 the ONLY residual error there should be the `split_q` line-68 goal;
this card kills it. Prototypes: `/tmp/probe_splitq.lean`, `/tmp/probe_dbr2.lean`.

## Progress

- (2026-07-14, opus-bootstrap46-subrange) Filed as the split-out harder half of
  bootstrap-46. Lean side FULLY PROTOTYPED + validated (mono lemma via
  `fun_induction <;> rename_i`, chaining rung via `Nat.lt_of_le_of_lt`).
  Architecture fork decided = option (a) (growing mono-name bag). Remaining =
  the Rust generation plumbing (detection + threading). NOT started.

## Writeup

_pending a fix._
