---
title: "tgt defs family: `m1_guard.lead` fails — seq-companion `decreasing_by` rung can't crack a Bool-wrapped `decide (…)=true` termination guard"
status: in_progress
claimed_by: opus-bootstrap45-seqrung
created: 2026-07-14T21:25:00Z
updated: 2026-07-14T21:25:00Z
---

## Description

Surfaced once **bootstrap-44** unblocked `word_numbering`: with word_numbering's
termination fixed, the full-krate tgt EXEC defs build reaches `m1_guard` and fails
on the recursive spec fn `lib.m1_guard.lead`:

```
TactusDefs_lib_exec__m1_guard.lean:23:0: error: unsolved goals
case h
x : Nat
w : seq.Seq symbol.Symbol
h✝ : 0 < seq.Seq.len symbol.Symbol w ∧ seq.Seq.index symbol.Symbol w 0 = symbol.Symbol.Gen x
⊢ ¬seq.Seq.len symbol.Symbol w = 0
```

`lead` recurses on `Seq.drop_first w` with `termination_by len w`. The decreasing
goal `len (drop_first w) < len w` dispatches to the seq measure-companion rung
`(apply lib.Seq.drop_first_len_lt <;> (first | assumption | omega | simp_all))`;
`apply` leaves the side goal `¬ len w = 0`, whose supporting fact `0 < len w` sits
in the THEN-branch guard `h✝ : len w > 0 ∧ index w 0 = Gen x`.

## ROOT CAUSE (reproduced deterministically 2026-07-14)

Same failure CLASS as bootstrap-44 (an omega-opaque termination guard) but on the
**seq-companion** rungs, which bootstrap-44 did NOT harden (it only added
`(simp_all <;> omega)` to the **div** rung).

The subtlety that made this hard to see: the isolated `.failed` dump **compiles
clean standalone** (`omega` reads the plain conjunction and closes `¬ len w = 0`).
The failure only appears IN-GATE. `build_olean` (`crate_defs.rs:973-980`) sets
`LEAN_PATH = prelude : dir : $existing`, where `$existing` is the verus process's
ambient LEAN_PATH. In that richer env, Decidable-instance resolution elaborates
`lead`'s `if C then … else …` guard such that the WF-recursion hands the
termination context a **Bool-wrapped** hypothesis `h✝ : decide C = true` instead
of a clean `h✝ : C`. `omega` cannot read `0 < len w` out of an opaque
`decide … = true`. The closer's terminal `simp_all` then DECODES the decide into a
plain conjunction and normalizes `len w > 0` → `0 < len w` — but STOPS there
(progress made, arithmetic goal not closed). Because `simp_all` is the LAST `first`
alternative, `first` accepts that partial success and leaves `¬ len w = 0`
unsolved ⟹ "unsolved goals". (The `0 < len w` normalization in the gate error —
vs. the raw `len w > 0` from source — is the fingerprint that `simp_all` had run.)

**Minimal deterministic repro** (`/tmp/closer_hard.lean`), the exact goal shape:
```lean
-- (A) CURRENT closer — FAILS with the exact gate error (¬ flen w = 0 left over)
example (w x : Nat) (h : decide (flen w > 0 ∧ findex w 0 = Sym.Gen x) = true)
    : ¬ flen w = 0 := by first | assumption | omega | simp_all
-- (B) FIXED closer — PASSES
example (w x : Nat) (h : decide (flen w > 0 ∧ findex w 0 = Sym.Gen x) = true)
    : ¬ flen w = 0 := by first | assumption | omega | (simp_all <;> omega) | simp_all
```

## Fix (applied, committed)

`to_lean_fn.rs:decreasing_by_tactic` — add a `(simp_all <;> omega)` rung to BOTH
seq-companion closers, BEFORE the terminal `simp_all`:
```
(apply {df} <;> (first | assumption | omega | (simp_all <;> omega) | simp_all))
(apply {dl} <;> (first | assumption | omega | (simp_all <;> omega) | simp_all))
```
`simp_all` decodes `decide … = true` into a plain conjunction and normalizes;
`omega` then closes the arithmetic side goal. Additive and low-blast-radius: the
rung only runs when `apply Seq.drop_{first,last}_len_lt` unifies (a seq measure),
and the cheap `assumption`/`omega` clean path is tried first and unchanged (a
clean-guard `lead` where the context gives `h✝ : C` still closes via bare `omega`,
verified — no regression). Mirrors bootstrap-44's div-rung shape exactly.

## Why it matters / what it blocks

Blocks **bootstrap-39** (in-gate bridge on real tgt). `m1_guard.lead` is the SOLE
remaining defs-family failure after bootstrap-40/42/44 and the auto-resolved
bootstrap-41. It's in the EXEC scope, whose ladder has a SINGLE attempt (full
roots) — so this one failure sinks the whole exec defs family ⟹ `package gate
skipped: shared-defs module unavailable` ⟹ islands fallback ⟹ `run_bridge_step`
never fires. Fixing it should let the full defs family build and the in-gate
bridge finally run over real tgt.

## Repro / validation

Rebuild the bootstrap binary (`cd tactus-bootstrap/source`; fork vargo on PATH;
`vargo build --release`), then the bootstrap-39 run #2 recipe (no `--emit-lean`,
no `-V cache`):
```
TACTUS_CORE_OUT=…/tactus-core/out/lib TACTUS_LEAN_OUT=/tmp/w4a-tgt-ingate7 \
  …/target-verus/release/verus --lean-backend --crate-type=lib \
  …/tactus-group-theory/src/lib.rs --tactus-bridge --verify-module runtime
```
**Done when:** no `TactusDefs_lib_exec__m1_guard.lean.failed` dump and no
`m1_guard.lean:23` unsolved-goals error; the exec defs family builds. Stretch:
the gate reaches the bridge note `"1 obligations bridge-checked … (1 passed, 0
failed)"` (that's bootstrap-39's finish line).

## Progress

- (2026-07-14, opus-bootstrap45-seqrung) **ROOT-CAUSED + FIXED + rebuilt.**
  Detective trail: the `.failed` dump compiles clean standalone (omega closes it),
  which pointed away from a source bug and toward the in-gate ambient env.
  Traced to the `decide … = true` guard form via `build_olean`'s
  `LEAN_PATH=prelude:dir:$existing`, and reproduced the exact gate error shape in
  a 2-line minimal test (`/tmp/closer_hard.lean` (A)) — and the fix passing (B).
  Confirmed deterministic (two independent cold runs, ingate5 + ingate6, both
  fail identically at m1_guard). Applied the additive `(simp_all <;> omega)` rung
  to both seq-companion closers in `to_lean_fn.rs`; rebuilt the binary
  (14:19, vstd 1530/0). Full-gate validation run (`/tmp/ingate7.log`) in flight.

## Writeup

_pending ingate7 confirmation._
