---
title: "tgt defs family: `m3_blinker.split_q` fails — nested `drop_base_run (drop_first W)` measure needs a per-fn length-monotonicity companion + chaining rung"
status: done
claimed_by: opus-bootstrap47-mono
created: 2026-07-14T22:20:00Z
updated: 2026-07-14T23:55:00Z
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

- (2026-07-14, opus-bootstrap47-mono) **IMPLEMENTED + gate-validated the two
  pieces; the mono TACTIC needed a rewrite (the prototype's `rename_i` was
  wrong).**

  **Plumbing landed (generate.rs + to_lean_fn.rs):**
  - `seq_suffix_mono_companion_cmd(f, all_fns)` in `generate.rs` — STRICT
    structural detector for a suffix-recursive spec fn (`spec fn f(W:Seq)->Seq`,
    recursive, body `if <guard> then W else f(W.drop_first())`, guard's
    OR-tree containing `len W == 0`) + emits the `{fn}_len_le` companion. Plus
    small VIR matchers (`peel_mono_expr`, `is_read_of_var`,
    `is_self_drop_first_recursion`, `guard_or_tree_has_len_zero`, …).
  - Emitted right after the fn's own def in the `FnGroup::Single` defs loop,
    riding its FnGroup seg; name registered in a thread-local bag
    (`register_suffix_mono_name`), cleared per emission entry in
    `install_emit_tables`.
  - `decreasing_by_tactic()` splices the `Nat.lt_of_le_of_lt` chaining rung
    citing the bag (option (a) growing bag) — only when the bag is non-empty
    (no cache churn for mono-free files).
  - CONFIRMED in the regenerated `m3_blinker.lean.failed`: the `drop_base_run`
    def, the `drop_base_run_len_le` companion, and split_q's decreasing_by all
    carry the new content.

  **The mono tactic rewrite (the real work).** The prototype's
  `fun_induction f W <;> first | omega | (rename_i x h ih; …)` FAILED in-gate
  (`69:9 too many variable names provided` / `Unknown identifier x`). Root
  cause = the bootstrap-45/46 **prelude divergence**: my probes used
  `~/.cache/tactus/prelude-c9213499d9bb3fce` but **the gate uses
  `prelude-e81fbf9a86375c12`**. Under the gate prelude, (1) the `∨` guard
  elaborates as a `dite` and `fun_induction` leaves `f x` UNFOLDED as
  `len (if <guard> then x else f (drop_first x)) ≤ len x` (omega can't reduce
  it), and (2) the BASE case has only 2 introduced hyps (no IH) → `rename_i x
  h ih` overflows. **The `.failed` dump elaborated with the e81fbf9a prelude
  reproduces the gate error EXACTLY** — that is now the dev loop (NOT
  c9213499).
  - New COUNT-FREE, if-reducing tactic (validated): `fun_induction f W <;>
    (try split) <;> first | omega | (apply Nat.le_trans <;> first | assumption
    | (apply Nat.le_of_lt; apply drop_first_len_lt <;> (…closer…))) |
    (simp_all <;> omega) | simp_all`. `try split` reduces the goal `if`
    (no-op when already reduced); `assumption` finds the IH
    (accessibility-agnostic); `apply` reads `x` off the goal; the vacuous
    guard-contradiction branches fall to `simp_all`.
  - **Validated in-gate FAITHFULLY**: patched the real `m3_blinker.lean.failed`
    (only the mono tactic swapped) and elaborated the WHOLE file under the
    e81fbf9a prelude → **exit 0, no errors** — i.e. the mono companion AND
    split_q's chaining rung both close in-gate. Also passes under c9213499
    (plain-`∨` form) → robust to both.
  - Source updated with the corrected tactic; `cargo check -p lean_verify`
    clean. Rebuilding the binary + re-running the bootstrap-39 run #2 gate to
    confirm end-to-end (WATCH: `m4_defect_flow` is next behind m3_blinker and
    may reveal its own shape).

## Writeup

**DONE + GATE-VALIDATED END-TO-END (2026-07-14, opus-bootstrap47-mono).** The
`m3_blinker.split_q` termination error is gone; the **entire exec defs family
builds** (m3_blinker olean 337 KB, m4_defect_flow olean too, exec umbrella
`TactusDefs_lib_exec.olean` built, **0 `.lean.failed` dumps**), and the
**package gate now RUNS** (`12 modules elaborated … composition + axiom closures
kernel-verified`) — the milestone the bootstrap-40→…→47 defs-blocker chain was
converging on. Runtime module: `24 verified, 0 errors`.

### What was wrong
`split_q` recurses on `drop_base_run(W.drop_first())`; the termination goal
`len (drop_base_run (drop_first W)) < len W` needs the COMPOSITION of
`len (drop_base_run x) ≤ len x` (drop_base_run is length-non-increasing) with
`len (drop_first W) < len W`. The `decreasing_by` menu had neither the
monotonicity fact nor a chaining step.

### The fix (three additive edits)
1. **`generate.rs` — `seq_suffix_mono_companion_cmd(f, all_fns)`** (+ small VIR
   matchers): STRICT structural detector for a "suffix-recursive" spec fn
   (`spec fn f(W: Seq E) -> Seq E`, recursive, body EXACTLY
   `if <guard> then W else f(W.drop_first())`, guard's OR-tree containing
   `len W == 0`). Emits a MONOMORPHIC proven theorem `{fn}_len_le :
   len (f W) ≤ len W`, right after the fn's own def (riding its FnGroup seg).
   Detection is strict-on-purpose: a false positive would emit an unprovable
   theorem and poison the whole defs file (`push_lenient` catches Rust panics,
   NOT Lean elaboration failures); a false negative just leaves the fn failing
   termination as before.
2. **`to_lean_fn.rs` — mono-companion bag + chaining rung**: a thread-local
   `SUFFIX_MONO_NAMES` (cleared per emission entry in `install_emit_tables`,
   populated as each companion lands) that `decreasing_by_tactic()` reads to
   splice a `Nat.lt_of_le_of_lt` chaining rung — option (a) "growing bag":
   `first | apply mono1 | … | (apply drop_first_len_lt <;> …)`. Only spliced
   when the bag is non-empty (no cache churn for mono-free files). Unknown-in-
   file names fail over harmlessly inside `first`, exactly like the existing
   seq-companion rungs.
3. The mono theorem's TACTIC (the real work — the prototype's was wrong).

### The tactic rewrite — and the prelude gotcha that hid it
bootstrap-46 left a "validated" prototype using
`fun_induction f W <;> first | omega | (rename_i x h ih; have := drop_first_len_lt … x (by omega); omega)`.
**It fails in-gate.** Root cause = the bootstrap-45/46 **prelude divergence**:
prototyping used `~/.cache/tactus/prelude-c9213499d9bb3fce`, but **the gate uses
`prelude-e81fbf9a86375c12`**. Under the gate prelude:
- the `∨` guard elaborates as a `dite` (Decidable resolution), and
  `fun_induction` leaves `f x` UNFOLDED as
  `len (if <guard> then x else f (drop_first x)) ≤ len x` — `omega` can't reduce
  the `if`;
- the BASE case has only 2 introduced hyps (var + guard, no IH), so a fixed
  `rename_i x h ih` overflows → `too many variable names provided` /
  `Unknown identifier x`.

**Dev-loop fix for the whole class: elaborate the `.lean.failed` dump with the
`e81fbf9a` prelude — it reproduces the gate error EXACTLY** (c9213499 falsely
passes). This is the reliable repro the bootstrap-46 caveat was groping at.

New COUNT-FREE, if-reducing tactic (emitted by `seq_suffix_mono_companion_cmd`):
```
fun_induction {fn} W <;> (try split) <;>
  first
    | omega
    | (apply Nat.le_trans <;>
        first
          | assumption
          | (apply Nat.le_of_lt; apply {drop_first}_len_lt <;>
              (first | assumption | omega | (simp_all <;> omega) | simp_all)))
    | (simp_all <;> omega)
    | simp_all
```
- `try split` reduces the goal's `if` (no-op when the ambient env already
  reduced it → robust to BOTH prelude forms);
- `omega` closes the trivial `len x ≤ len x`;
- `apply Nat.le_trans <;> (assumption | Nat.le_of_lt ∘ drop_first_len_lt)` chains
  the IH (found by `assumption`, accessibility-AGNOSTIC — no `rename_i`) with
  `len (drop_first x) < len x` (`apply` reads `x` off the goal, `omega` reads
  `¬ len x = 0` off the negated guard). `apply Nat.le_trans` (not `refine`)
  postpones the middle metavar so it binds from the first subgoal;
- `(simp_all <;> omega)` / `simp_all` mop up the vacuous guard-contradiction
  branches `split` can introduce.

### Validation
- **Faithful in-gate repro**: patched the real `m3_blinker.lean.failed` (only the
  mono tactic swapped) and elaborated the WHOLE file under the `e81fbf9a`
  prelude → **exit 0, no errors** — the mono companion AND split_q's chaining
  rung both close. Also passes under `c9213499` (plain-`∨` form).
- **End-to-end gate**: rebuilt the binary; re-ran the bootstrap-39 run #2 recipe
  (`/tmp/w4a-bs47b`, no `--emit-lean`, no `-V cache`). m3_blinker olean present,
  0 `.failed` dumps across the exec defs family, exec umbrella built, package
  gate runs.

### Honest caveats / notes for the next instance
- The gate's package-check now reaches the **bridge**, which reports
  `1 obligations bridge-checked … (0 passed, 1 failed); failed:
  runtime__impl__4__clone`. That is **bootstrap-39's** finish line and a
  SEPARATE concern: the in-gate obligation bridge does NOT reproduce probe11's
  external `close-ok`. My defs-termination change touches neither obligation
  certs nor `ref_wp`, so it is not the cause — but bootstrap-39 is now unblocked
  to the point where THIS is the remaining gap (see that card).
- **Emission-site parity**: the mono companion needs `seq.Seq.len` +
  `Seq.drop_first` in the emission (returns `None` otherwise) — holds for tgt.
- The detector matches ONLY the exact `if g then W else f(drop_first W)` shape.
  `base_run` (else-branch prepends `seq![W[0]]`) is correctly NOT matched (its
  `_len_le` would be unprovable by this tactic), and split_q only needs
  `drop_base_run`'s mono anyway.
