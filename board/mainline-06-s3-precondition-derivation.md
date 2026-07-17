---
title: "S3 — precondition-specific derivation seeding (the 81%-T2 kind)"
status: done
claimed_by: kimi (folded into mainline-05)
created: 2026-07-16T17:28:00Z
updated: 2026-07-17T01:10:00Z
---

## Description

Preconditions are the T2-heaviest obligation kind (74/91 = 81% in Brick 1) and
structurally the most derivable: a precondition theorem states the CALLEE's
requires under the caller's context, and the emitter knows the callee at
emission time. Rule: seed the derived lemma list from the callee's
requires-mentioned spec-fn definitional unfoldings + the in-scope `_tactus_bc`
axioms (measurement doc recommendation #2 — "squeeze lists for these should be
small and formulaic").

NOTE: this may simply BE the first derivation rule of mainline-05 rather than a
follow-on — if S2c starts with preconditions (it should; biggest kind, best
information), fold this task into it and mark this one done with a pointer.
Kept separate so the kind-specific rule has its own acceptance record either way.

**Done when:** precondition-kind T2 share measurably drops in the
rung-attribution re-run (record before/after), 0 regressions on the 114-fn
pool.

**Blocked by:** mainline-05 (or merges into it).

## Writeup

FOLDED INTO mainline-05, and superseded by its result in the best possible
way: preconditions needed NO kind-specific rule at all. The uniform derived
tactic (`first | rfl | decide | (tactus_peel <;> (first | rfl | decide |
omega)) | (simp_all only [CORE: 51] <;> omega)`) covers 174/183 T2
preconditions in the census, and the 6 precondition residue theorems were
closed by kind-AGNOSTIC inline proofs (if_pos/if_neg discharge, structured
assembly, absurdity — see mainline-05's writeup). The callee-specific lemma
seeding this task proposed would have been rule #2; the rule budget stays at
ONE (Danielle's constraint), and the precondition T2 share in default
emission is 0% search by construction (final histogram in mainline-05).
