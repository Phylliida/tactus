---
title: "S2b — settle pin storage: derivation-first vs any persistent store (design, w/ Danielle)"
status: done
claimed_by: kimi + Danielle
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T22:45:00Z
---

## Description

Design decision, made WITH Danielle, informed by mainline-03's census. Danielle
flagged the design doc's §3.2 pin sidecar as suspect ("a lil sussy — I'd like to
do things the right way") — and the suspicion has a precise form: **a committed
sidecar is a THIRD surface**, in tension with the standing two-surface end state
(emitter-derived tactics + inline proofs). Tactic text in a sidecar is neither
derivable nor in the source.

Candidates, ranked by minimality:

1. **No storage — derivation rules** (primary candidate). Pins are a pure
   function of the goal, recomputed at every emission: the emitter derives
   `simp only [site-knowable lemmas] (<;> omega)` per obligation kind. This is
   S1's pattern generalized (S1 derives `omega` for the linear fragment, stores
   nothing, deterministic because derivation is deterministic). Determinism ✓
   (named lemmas break loudly on renames), speed ✓ (no search on the hot path),
   auditability ✓ (artifact reads as a proof). Viable iff mainline-03 shows a
   high derivable share.
2. **Inline proofs for the residue** — the source IS the store, and it already
   exists. Squeeze results that aren't derivable get suggested as inline proof
   text ("this obligation needed `simp only [X, Y]` — consider writing it"),
   user applies. Complements 1; together they preserve two surfaces exactly.
3. **Committed emitted artifacts as the store** — middle ground if the residue
   is large: the .lean artifact already contains the tactic text; committing
   artifacts makes drift a reviewable diff without inventing a new format.
   Costs: generated files in repo, size, merge noise.
4. **Sidecar per §3.2** (fallback only) — obligation-id-keyed JSON, cache-key
   invalidation. Keep only if 1+2 leave an unbearable gap AND 3's costs bite.

Decision criteria: two-surface end state; §3.3 goals (determinism, speed,
auditability); review surface (a pin diff should be reviewable as a proof
change); no ambient context (the guiding rule).

**Transparency constraints on candidate 1** (Danielle probe, 2026-07-16 —
"deterministic and easy for the user to understand and predict"):
- **Locality**: derived list = f(goal's mentioned symbols, callee's spec) ONLY;
  never ambient scope contents. Otherwise distant edits move the list —
  deterministic but surprising, the rlimit cliff in miniature.
- **Rule budget**: derivation rules must be few, kind-indexed, one statable
  line each ("preconditions: unfold callee's requires-mentioned defs, then
  omega"). A rule needing conditionals on goal structure beyond kind +
  mentioned symbols is tactus_auto rebuilt inside the emitter → that goal is
  inline-proof territory. Same discipline as "keep tactus_auto minimal."
- **Predictability honesty**: bare `simp only [list]` is weaker than omega —
  success is rewriting REACHABILITY, not fragment membership; the T1 criterion
  is not met by arbitrary derived rewrite sets. The UNFOLD-THEN-DECIDE shape
  (`simp only [defs] <;> omega`) recovers fragment-style predictability
  ("true linear arith after unfolding these named defs"). Prefer rules whose
  terminal step is a decision procedure; mainline-03's axis-2 census measures
  how far that reaches. Rewrite-closure rules are acceptable only where the
  census shows them formulaic per kind; everything else → inline.

**Done when:** decision recorded in `DESIGN-transparent-automation.md` (amend §3
with the chosen shape + rationale + census numbers), and mainline-05's scope is
rewritten to match.

**Blocked by:** mainline-03 (needs the derivability numbers).

## Writeup

**DECIDED 2026-07-16, Danielle, on the mainline-03 census data** (295 real
theorems: 95.6% derivable; one fixed 43-lemma site-invariant list + omega tail
validated 280/280):

- **Candidate 1 — derivation-first, NO STORE.** The sidecar (candidate 4) and
  committed artifacts (candidate 3) are dead: a store would persist what a
  constant already provides. The derived tactic is the uniform text
  `simp_all only [CORE: 43 fixed core lemmas] <;> omega` — rule budget ONE,
  locality satisfied by construction (the list is site-INVARIANT, stronger
  than "site-computable").
- **Candidate 2 — inline proofs for the residue.** 13 theorems / 2 clusters /
  3 effective sites. The Option-accessor rule exception ("accessor lemmas of
  mentioned symbols' field types") was CONSIDERED AND DECLINED — rule budget
  stays at one; the cluster gets inline proofs in gt source.
- **Predictability honesty accepted:** the pool is REWRITE-CLOSURE, 0%
  unfold-then-decide; the accepted story is "fixed core normalizer + omega
  decider tail". Recorded in DESIGN-transparent-automation.md §3.4 with the
  census numbers and the three protocol facts downstream work must respect.
- mainline-05's scope rewritten to match (uniform derived tactic replacing
  `tactus_auto` as the default closer; suggestion report for residue;
  validation = full-pool 0-regression diff, not just the T2 subset).
- mainline-15 pairing noted: residue inline proofs will cite full dotted
  names; the `open <crate> in` ergonomics question stays open but does NOT
  block 05.
