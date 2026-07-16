---
title: "tgt defs family: `word_numbering` fails — emitted `decreasing_by`/omega can't crack a termination guard wrapped in a `dite`/`ite` over Prop"
status: done
claimed_by: opus-bootstrap42-arity
created: 2026-07-14T20:55:00Z
updated: 2026-07-14T21:25:00Z
---

## Description

Surfaced once **bootstrap-42** (pattern-arity) unblocked `britton_via_tower`:
with britton building, the full-krate tgt defs build reaches `word_numbering` and
fails on BOTH sides:

```
TactusDefs_lib_exec__word_numbering.lean.failed:20:296: error: failed to prove termination
TactusDefs_lib__word_numbering.lean.failed:20:296:      error: failed to prove termination
  ...
  h✝ : ¬if x : alpha = 0 then True else m ≤ 1
  ⊢ alpha / m < alpha
```
(2 sites each: `numbers_word` line 20, `w_c` line 26.)

The recursive spec fns `lib.word_numbering.numbers_word` and `w_c` are emitted with
```
termination_by alpha
decreasing_by all_goals (first | omega | (apply Nat.mod_lt <;> omega)
  | (apply Nat.div_lt_self <;> omega) | (apply lib.Seq.drop_first_len_lt <;> ...)
  | (apply lib.Seq.drop_last_len_lt <;> ...) | ((repeat split) <;> omega)
  | decreasing_tactic)
```
The decreasing goal is `alpha / m < alpha`, provable by `Nat.div_lt_self` given
`0 < alpha` and `1 < m`. Both facts ARE derivable from the context guard — the
recursive call sits in the innermost `else` of
`if alpha = 0 then True else if m ≤ 1 then False else (... ∧ recurse (alpha/m))`
— but Lean hands the termination context a SINGLE combined hypothesis
`h✝ : ¬if x : alpha = 0 then True else m ≤ 1` (a `dite`/`ite` over `Prop`).
`apply Nat.div_lt_self <;> omega` then leaves goals `0 < alpha` / `1 < m`, and
`omega` CANNOT extract them from `h✝` because omega does not unfold `ite`/`dite`
over Props into arithmetic. `((repeat split) <;> omega)` doesn't rescue it either
— `split` acts on `ite`/`match` in the GOAL, not in the hypothesis `h✝`.

## Why it matters / what it blocks — now the PRIMARY defs-family blocker

- **bootstrap-39** (in-gate bridge on real tgt): the package gate needs the FULL
  defs module to build; any module-defs failure ⟹ `package gate skipped:
  shared-defs module unavailable` ⟹ islands fallback ⟹ the in-gate bridge never
  fires. `word_numbering` fails in the **exec** defs family (`TactusDefs_lib_exec`,
  single attempt) — so the exec family the bridge imports is broken outright.
- **bootstrap-41** (`coset_group` `Some_val0`): accessor-INDEPENDENT, so
  `word_numbering` also sinks the NON-exec ladder's attempt-1 (accessors ON),
  forcing the fallback to attempt-2 (accessors OFF) — which is exactly what
  drops `Some_val0` and re-triggers coset_group. So bootstrap-41 is now gated on
  THIS card (it took britton's place as the attempt-1 sink). Fixing word_numbering
  should let non-exec attempt-1 win ⟹ coset_group gets its accessor ⟹
  bootstrap-41 auto-resolves.

## Provenance / not a regression

Independent of bootstrap-40 (DeepView Ref-wrap) and bootstrap-42 (ctor-pattern
arity) — this is `decreasing_by` tactic generation, a third mechanism. It was
MASKED by bootstrap-42: the non-exec ladder aborted at britton (attempt-1) before
reaching word_numbering, and on-disk `.failed` dumps are from attempt-2. It is
newly *visible*, not newly *introduced*. Confirmed both sides fail purely on
termination (non-exec `word_numbering.lean.failed` has ONLY the 2 termination
errors, zero accessor errors).

## Scope of the fix (not yet investigated in the emitter)

The fix belongs in how the Lean backend emits `decreasing_by` for recursive spec
fns (grep the emitter for `decreasing_by`, `termination_by`, `Nat.div_lt_self`,
`decreasing_tactic`, the `(repeat split)` menu string). The termination guard is
an `ite`/`dite` over `Prop` that omega can't see through. Candidate remedies (pick
the least-magic, most-transparent one — see [[feedback_transparency_is_faithfulness]],
[[feedback_minimal_automation]]):
- Add a hypothesis-splitting preprocessing step to the tactic menu so the
  `ite`/`dite` in `h✝` is broken down before omega, e.g. an alternative
  `(simp_all only [] <;> omega)` or `(split_ifs at * <;> omega)` /
  `(split at * <;> omega)` rung. Careful: `split_ifs`/`split at *` can blow up on
  fns with many ifs; scope it as its own `first |` alternative so it only runs
  when the cheaper rungs fail.
- Or emit the guards as boolean `decide`-able / already-decomposed hypotheses so
  the `if ... then True else P` Prop-ite never reaches the termination context in
  the first place (more invasive; touches how nested-if spec-fn bodies lower).

Prefer verifying any change against BOTH `numbers_word` and `w_c` (2 sites) and
re-running the bootstrap-39 run #2 recipe to confirm the whole defs family builds
and bootstrap-41 falls out. Watch for further attempt-1 failures the attempt-2
`.failed` dumps still hide.

## Repro

Rebuild the bootstrap binary, then run the bootstrap-39 run #2 recipe
(`--lean-backend --crate-type=lib <tgt>/src/lib.rs --tactus-bridge
--verify-module runtime`, no `--emit-lean`, no `-V cache`). Then standalone-
elaborate the dump:
```
LEAN_PATH="$OUT/lib:<tactus-core/out/lib>:<~/.cache/tactus/prelude-e81fbf9a86375c12>" \
  lean $OUT/lib/TactusDefs_lib_exec__word_numbering.lean.failed
```
(Confirmed working this turn against `/tmp/w4a-tgt-ingate4/lib`.)

**Done when:** `TactusDefs_lib__word_numbering` and
`TactusDefs_lib_exec__word_numbering` build with 0 Lean errors under the bootstrap
fork.

## Progress

- (2026-07-14, opus-bootstrap42-arity) Filed from the post-bootstrap-42 run #4
  (`/tmp/w4a-tgt-ingate4`). Captured the exact termination error by standalone-
  elaborating both `.failed` files. Root-caused to the `dite`/`ite`-over-Prop
  termination guard being opaque to `omega`. Confirmed accessor-independent
  (non-exec side fails on termination only), so it — not coset_group — is the
  current attempt-1 sink for the non-exec ladder.

- (2026-07-14, opus-bootstrap42-arity) **FIX FOUND + APPLIED + COMMITTED
  (`6c0de66`); full-chain gate validation in flight.** Tested candidate
  `decreasing_by` closers by patching the `decreasing_by` line in the REAL
  `word_numbering.lean.failed` and re-elaborating (harness `/tmp/harness*.py`):
  - `split at *` (after `div_lt_self`): FAILS — doesn't crack the negated dite.
  - `apply Nat.div_lt_self <;> simp_all` (no omega): term-error gone but leaves
    `unsolved goals` (simp_all reduces but doesn't close the arithmetic).
  - **`apply Nat.div_lt_self <;> (simp_all <;> omega)`: 0 errors.** ✓ Also
    verified against the FULL production menu (with the seq rungs present): 0
    term-errors, 0 other-errors; and a clean-hypothesis base-conversion case
    still passes (no regression).
  - Applied as an ADDITIVE new `first|` rung in `to_lean_fn.rs:decreasing_by_tactic`,
    placed right after the plain `(apply Nat.div_lt_self <;> omega)` rung so the
    cheap clean path is unchanged and only genuine dite-guard fns fall through.
  - **Local-model consult (Danielle's companion, port 8051):** confirmed safe
    (Lean backtracking prevents context pollution across rungs/goals; the
    apply-before-simp_all ordering is correct — simp_all first could rewrite the
    `div` goal so `Nat.div_lt_self` no longer matches). Flagged one real caveat:
    `simp_all` scans the WHOLE local context, so it's a *performance tax* if many
    goals fall through — and a theoretical loop/over-simplification risk if a
    crate adds cyclic/interacting custom simp lemmas. Suggested hardening: replace
    `simp_all` with a targeted `simp only [<lemma decomposing ¬(ite _ _ _)>]`.
    NOT done now (would need to pin the exact minimal lemma set; premature while
    the rung is a rarely-hit fallback). **Documented hardening follow-up:** if the
    corpus run shows a heartbeat/rlimit tax on this rung, switch to `simp only`.
    (Aligns with [[feedback_minimal_automation]] / [[feedback_transparency_is_faithfulness]].)

## Writeup

**DONE (2026-07-14, opus-bootstrap45-seqrung).** The `6c0de66` fix — the additive
`(apply Nat.div_lt_self <;> (simp_all <;> omega))` div-rung — is CONFIRMED correct
and sufficient for its scope. Two cold gate runs (`/tmp/ingate5.log`,
`/tmp/ingate6.log`) both show **zero** `word_numbering.lean.failed` dump and zero
`word_numbering` termination errors: `numbers_word`/`w_c` now build. The
downstream prediction also held — with word_numbering no longer sinking non-exec
attempt-1, `coset_group` got its `Some_val0` accessor and **bootstrap-41
auto-resolved** (no `coset_group.lean.failed` in either run).

**What the full-chain validation surfaced (the payoff of running it):** the defs
family now fails at exactly ONE remaining site — `m1_guard.lead` in the EXEC defs
family (`TactusDefs_lib_exec__m1_guard.lean:23`, `unsolved goals` on `¬ len w = 0`).
This is the SAME failure class as this card (an omega-opaque termination guard),
but on the **seq-companion** rungs (`apply Seq.drop_first_len_lt <;> …`) rather
than the div rung this card hardened — so the `(simp_all <;> omega)` treatment had
to be extended there too. Filed + fixed as **bootstrap-45**. This card's own
target (word_numbering builds) is fully met; closing it.
