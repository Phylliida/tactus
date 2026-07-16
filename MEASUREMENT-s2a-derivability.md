# S2a — squeeze + derivability census over the Brick-1 T2 pool

**Date:** 2026-07-16 · **By:** kimi · **Board:** mainline-03
**Status:** measurement complete, decision data for mainline-04

Companion data: `tools/rung-attrib/results-2026-07-16-squeeze-census.csv`
(per real theorem: kind, lemma count, axis verdicts, omega-tail flag,
full lemma list). Harness: `tools/rung-attrib/squeeze_census.py`
(committed with this doc).

---

## 1. What was measured

The Brick-1 pool's 145 T2 buckets (`results-2026-07-11-full-pool.csv`
rows whose minimal rung is `T2 (simp_all/case_split)`). The attribution
harness truncates dotted theorem names at the first `.`, so each bucket
covers 1..N real location-suffixed theorems; this census enumerates and
squeezes **each real theorem individually**: 145 buckets → **295 real
theorems** over 88 artifact files. Pred-twin dedup view: **232 effective
theorems** (67 live in `pred_*` files whose non-pred twin is in the
pool; 2 pred files are untwinned and count in full).

Artifact harvest: `/tmp/census-emit` (post-bootstrap-72 sync binary,
2026-07-16). Elaboration against `~/.cache/tactus/prelude` +
`TactusDefs_lib_exec.olean` from `/tmp/w4a-b2-ingate4/lib` (Jul-14;
verified to elaborate the Jul-16 harvest clean — defs did not drift
across the sync merge).

## 2. Squeeze API — CONFIRMED on v4.25.0

`DESIGN-transparent-automation.md` §3.1 flagged "confirm exact API".
Confirmed: replacing a theorem's `tactus_auto` closer with `simp_all?`
makes Lean print

```
Try this:
  [apply] simp_all only [and_imp, forall_eq, ...]
```

— the used-lemma list, parseable from stdout. No `Simp.Stats` plumbing
needed. Every minimized list in this census was re-elaborated as the
theorem's closer (VERIFY phase), with an `<;> omega` tail retry per
§3.1 ("+ omega tail when the winning rung was the composed one" — see
§5.3). Only verified closings are counted as squeezed.

Harness findings (all fixed in the committed tool):

- `Try this` messages print **bare** (no `file:line:` prefix) in batch
  `lean` output; attribution is by elaboration order (batch elaboration
  is sequential), with a per-theorem single-spike fallback on count
  mismatch.
- The `unusedSimpArgs` linter emits *warnings* on minimized lists that
  still elaborate — failure detection must key on `: error` only.
- Combined-file construction must keep ALL top-level blocks (fast_attrib
  semantics); dropping non-target blocks drops the `import`.

## 3. Headline numbers (295 theorems)

| axis-1 derivability | n | % |
|---|---|---|
| **DERIVABLE** (lemmas site-computable) | **282** | **95.6%** |
| GOAL-SPECIFIC (needs lemmas outside) | 7 | 2.4% |
| MIN-FAILS (no replay closes) | 6 | 2.0% |

| axis-2 terminal shape | n | % |
|---|---|---|
| REWRITE-CLOSURE(fixed-core) | 226 | 76.6% |
| REWRITE-CLOSURE(core-extended) | 42 | 14.2% |
| REWRITE-CLOSURE(core-extended)+omega | 12 | 4.1% |
| REWRITE-CLOSURE(goal-specific) | 8 | 2.7% |
| REWRITE-CLOSURE(goal-specific)+omega | 1 | 0.3% |
| MIN-FAILS | 6 | 2.0% |

Verified column: 276 bare / 13 omega-tail / 6 unclosed.

**The headline:** 95.6% of the T2 pool squeezes to lemma lists that are
computable from the obligation's own semantic inputs — and 94.9%
(280/295) of the pool uses *no lib lemmas at all*, only a fixed,
site-independent core simp vocabulary (§6). Pin STORAGE is unnecessary
for this pool: the derivation is one fixed rule plus two named
exceptions (§7).

## 4. Per-kind tables

### axis-1 × kind

| kind | n | DERIVABLE | GOAL-SPECIFIC | MIN-FAILS |
|---|---|---|---|---|
| precondition | 183 | 174 (95.1%) | 3 | 6 |
| postcondition | 92 | 88 (95.7%) | 4 | 0 |
| loop_invariant | 12 | 12 (100%) | 0 | 0 |
| assert | 8 | 8 (100%) | 0 | 0 |

The Brick-1 prediction — preconditions are 81% of T2 and their squeeze
lists are "small and formulaic" — **holds**: preconditions are 62% of
the real pool (183/295) at 95.1% derivable, and their lists are the
fixed core set with no exceptions beyond the two global clusters (§7).

### axis-2 × kind

| kind | fixed-core | core-ext | core-ext+ω | goal-spec | goal-spec+ω | MIN-FAILS |
|---|---|---|---|---|---|---|
| precondition (183) | 149 | 17 | 8 | 2 | 1 | 6 |
| postcondition (92) | 67 | 18 | 1 | 6 | 0 | 0 |
| loop_invariant (12) | 2 | 7 | 3 | 0 | 0 | 0 |
| assert (8) | 8 | 0 | 0 | 0 | 0 | 0 |

Loop invariants are the one kind where the bare core set is the
minority (2/12) — their goals carry arithmetic residues, so they lean
on the extended core and the omega tail. Still 100% derivable and
still site-independent: the extension is core lemmas, not lib lemmas.

## 5. Three protocol findings that change the squeeze itself

### 5.1 `simp_all?` suggestions do not always replay standalone

13/295 theorems (the composed-rung/case-split winners) get a suggestion
that fails as `simp_all only [...]` — generated against simp_all?'s own
progress state — but closes with `<;> omega` appended. Worked example:
`runtime__copy_word` loop invariant at 444_13_13 (frame goal over
`Seq.push` indexing). **Protocol rule: the minimized form is
`simp_all only [list]` with an `<;> omega` tail when the winning rung
was composed — exactly §3.1's parenthetical, now load-bearing.**

### 5.2 Plain `simp_all` is not a safe proxy for "T2 winner"

The 444_13_13 theorem is labeled T2 yet bare `simp_all` does NOT close
it — the win came from the composed rung or case-split inside
`tactus_auto`. Any future per-rung accounting should not assume
"T2 label ⇒ simp_all closes".

### 5.3 Accessor lemmas need prefix-, not basename-, matching

All 8 first-pass "GOAL-SPECIFIC" rows were misclassified: their extra
lib lemmas were datatype discriminant/accessor lemmas
(`lib.option.Option.Some_val0`, `lib.runtime.RuntimeSymbol.isGen`)
whose type is goal-mentioned — derivable under the task's own
"accessor lemmas of symbols the goal mentions" clause. The classifier
walks each lemma's dotted prefixes against goal-mentioned names.

## 6. The fixed core set (the actual vocabulary)

Union over all 280 fixed-core/core-extended lists: **43 core lemmas**,
zero lib lemmas. Propositional normal forms (`and_imp`, `forall_eq`,
`and_self`, `implies_true`, `eq_iff_iff`, `true_and`, `and_true`,
`iff_true`, `imp_self`, `imp_false`, `not_and`, `not_imp`, `not_or`,
`not_exists`, `not_true_eq_false`, `not_false_eq_true`,
`Classical.not_forall`, `Decidable.not_not`, `forall_const`), Nat/Int
cast-and-zero cleanup (`Nat.zero_add`, `Nat.add_zero`, `Nat.zero_le`,
`Nat.le_refl`, `Nat.not_le`, `Nat.not_lt`, `Nat.add_left_cancel_iff`,
`Nat.le_add_left`, `Nat.le_add_right`, `Nat.add_le_add_iff_right`,
`Nat.sub_le_iff_le_add`, `Nat.reduceLeDiff`, `Int.cast_ofNat_Int`,
`Int.zero_add`, `Int.sub_zero`, `Int.zero_sub`, `Int.natCast_add`,
`Int.ofNat_eq_coe`, `Int.ofNat_zero_le`, `gt_iff_lt`, `ge_iff_le`)
plus a small emod/toNat tail (`Int.add_emod_left`,
`Int.neg_add_emod_self`, `Int.toNat_natCast_add_one`).

**Union-set validation (the decisive number):** one fixed 43-lemma
`simp_all only [CORE]` list run against ALL 280 fixed-core/core-extended
theorems:

| phase | closes | cumulative |
|---|---|---|
| A: `simp_all only [CORE]` (bare) | 268 | 268/280 |
| B: failures retried with `<;> omega` | 12 | **280/280** |

**Residual failures: 0.** One fixed list, with an omega tail on the 12
composed-rung theorems, covers the entire derivable pool. Validator:
`tools/rung-attrib/union_core_test.py` (committed alongside).

## 7. The residue: 13 theorems, 2 clusters (3 sites after twin dedup)

**Cluster A — Option accessors (7 theorems, all coset_group).**
`lib.option.Option.isSome` / `lib.option.Option.Some_val0` where the
Option appears inside structure fields of goal-mentioned symbols, so
the type name never textually appears in the goal statement. One
type-directed step away from derivability — but per the rule-budget
constraint (no conditionals on goal structure beyond kind + mentioned
symbols), this is either a *discussed* one-line rule exception
("accessor lemmas of mentioned symbols' field types") or inline-proof
territory. Effective: 7 theorems, 2 source fns
(`lemma_assoc_lhs`, `lemma_trace_inv_rep_to_zero`).

**Cluster B — no replay closes (6 theorems → 4 effective).**
`britton_via_tower__lemma_stable_pair_inv_gen` ×2 (+2 pred-twins) and
`runtime__apply_hom_symbol_exec` ×2. Worked example (britton 7191_9_5):
goal is a conjunction over `Seq.first`/`Syllable` structure accessors
with negations; the minimized set leaves structure equalities omega
can't touch; the T2 win was case-split-shaped. Genuinely
HEURISTIC-NEEDED → inline proofs. Note `apply_hom_symbol_exec` is the
same fn whose match-refinement drift caused the historical baseline
error (mainline-00) — its obligations are structurally awkward in a
known way.

Everything else in the pool is one fixed rule.

## 8. Interpretation for mainline-04

- **Candidate 1 (no storage, derivation rules) is viable beyond the
  doc's optimism.** The rule budget is: **one** fixed 43-lemma
  site-independent list (+ omega tail per the composed-rung flag the
  emitter already knows), validated to close 280/280 of the derivable
  pool (94.9% of all T2); the residue is 13 theorems in 2 named
  clusters, both inline-proof shaped.
- **Determinism note:** the derived list is constant text — renames of
  core lemmas break loudly, and the list carries no ambient-scope
  dependence at all (it doesn't even read the goal beyond the kind and
  the composed-rung flag). This is the strongest possible form of the
  locality constraint: the list is site-*invariant*.
- **Predictability honesty:** this is REWRITE-CLOSURE, not
  UNFOLD-THEN-DECIDE — success is reachability of a normal form under
  a fixed confluent-ish core set, not fragment membership. The omega
  tail recovers a decision procedure for the arithmetic residue
  (13 theorems). The doc's axis-2 "UNFOLD-THEN-DECIDE share" headline
  is **0% for this pool** — no theorem needed definitional unfoldings
  at all — because the obligations' goals are already propositional/
  arithmetic facts about spec vocabulary, with def expansion happening
  upstream of the closer. Worth a beat of Danielle's attention: the
  predictability story is "fixed normalizer + decider tail", not the
  unfold-then-decide ladder §3 anticipated.
- **F7 (mainline-12) read:** the 41% seq-op auto-bucket cluster
  expected "derived `simp only` lists that name the needed axioms" —
  in THIS pool named seq axioms were never needed (the `_tactus_bc`
  broadcast hypotheses in context do that work inside simp_all). The
  F7 re-taxonomy should not assume named-axiom lists are the common
  case.
