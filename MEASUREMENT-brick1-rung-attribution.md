# Brick 1 measurement: per-theorem rung attribution — findings & analysis

**Date:** 2026-07-11
**Question:** what does the currently-passing Lean-routed corpus actually *need* from
`tactus_auto`? This is Brick 1 of `DESIGN-transparent-automation.md` (§6 —
"instrument before deciding"), feeding the decision on how `tactus_auto` is removed
from artifacts. Standing direction (Danielle): injected proof machinery must be
deterministic and require near-zero user head-state — sharpened during this arc to:
**every injected tactic carries its own specification, readable at the proof site; no
ambient context** (global simp sets, search orders, namespace walks, attribute
side-channels). `tactus_auto` is a search gate and fails that rule; the question is
what replacing it costs.

**Harness:** `tools/rung-attrib/fast_attrib.py` (see its README). Per obligation
theorem, finds the MINIMAL prefix of the chain `rfl` → `+decide` → `+omega` →
`+tactus_peel∘{rfl,decide,omega}` → full `tactus_auto` that closes it. Prefixes 1–4
are fully deterministic, self-specifying tactics; needing step 5 means the goal
depends on default-set `simp_all` / `tactus_case_split` — the **T2** share, which is
exactly the squeeze-and-pin workload.

---

## Population

- Corpus: tactus-group-theory under `--lean-all-proofs`, post-Option-B naming
  (`/tmp/optb-emit`-era artifacts; emitted by the binary at `e926320`..`31f867d`).
- Eligible: per-fn artifacts whose fn is NOT in the overnight real run's
  failing-fn list — i.e., fns that fully pass with today's `tactus_auto`.
  Name-collision over-exclusion makes this conservative (114 files kept of ~517
  nominal passes; every kept file is a true pass).
- **Full pool measured — no sampling:** 215 obligation theorems across 114 fns in 45
  modules. Zero unexplained failures (the earlier 1/75 anomaly was the composed-site
  artifact, now excluded by design — see "Composed sites" below).

## Headline result

| minimal closer | share (215 thms) | count |
|---|---:|---:|
| `rfl` | 6.0% | 13 |
| `omega` | 18.1% | 39 |
| `tactus_peel` ∘ {rfl,decide,omega} | 8.4% | 18 |
| **T2 (`simp_all` / `tactus_case_split`)** | **67.4%** | **145** |

(First 75-theorem sample gave 64% T2 — stable across sample sizes.)

**Decision-table read (§6 of the design doc): the T2 share is large. Outright removal
of the heuristic rungs from the default would be a usability cliff. The indicated
path is squeeze-and-pin (§3):** the ladder stays as a dev-time discovery tool;
`simp_all` winners get minimized to named-lemma `simp only [...]` at the site;
artifacts replay only self-specifying tactics.

Read the other way: **~33% of today's green already needs nothing beyond
deterministic, name-is-spec tactics** — that floor can be emitted directly, with zero
search, today.

## Breakdown by obligation kind

| kind | theorems | of which T2 | T2 rate |
|---|---:|---:|---:|
| precondition | 91 | 74 | **81%** |
| postcondition | 105 | 64 | 61% |
| assert | 14 | 5 | 36% |
| loop | 4 | 2 | 50% |
| ensures (anchor) | 1 | 0 | 0% |

**Preconditions are the T2-heaviest kind.** This makes structural sense: a
precondition theorem states the *callee's* requires under the *caller's* context, so
closing it usually needs the callee-side spec fns unfolded / vstd axioms instantiated
— the same shapes that dominate the failing-bucket taxonomy (46% quantified /
41% seq-op; see `DESIGN-lean-all-proofs.md` §10.2 notes). Squeeze lists for these
should be small and formulaic (the definitions mentioned in the requires plus a few
seq axioms), and the emitter *knows the callee* at emission time — a plausible
follow-on is precondition-specific pin seeding (start the squeeze from the callee's
mentioned spec fns rather than from the whole default set).

## Breakdown by module

Top T2 concentrations: `britton_via_tower` 16/21, `pred_britton_via_tower` 16/21,
`normal_form_afp_textbook` 13/17, `pred_normal_form_afp_textbook` 13/18,
`coset_group` 8/12, `runtime` 7/13, `higman_consequences` 6/10, `base_swap` 4/4.

Two observations:
- **The pred-twin halving applies here too** — `britton_via_tower` and its
  mechanical `pred_` parallel copy have byte-similar profiles (16/21 vs 16/21).
  Whatever pin set closes one closes its twin; effective squeeze work is roughly
  half the raw module count on twin-heavy corpora.
- **8 of 45 modules are already 100% T1-closable** — their fns could switch to
  emitter-selected deterministic tactics with no squeeze machinery at all.

## Composed sites (excluded, and instructive)

Theorems whose tactic is `first | tactus_auto | (explicit user fallback)` — the gt
exec-migration idiom — are excluded from the histogram by design: substituting the
closer inside the composition changes the composition's semantics (a weakened first
arm makes the *user fallback* run, and its errors escape the `first`), and those
sites already carry explicit proofs. This exclusion resolved the one anomalous
"fails even `tactus_auto`" datapoint from the first sample (`runtime__apply_hom_inv`).

Worth noticing: composed sites are already the end-state shape the guiding rule
wants — visible proof text at the site, closer as a first attempt. The squeeze-and-pin
endgame is essentially converting the 67% into that shape, minus the search.

## Caveats / threats to validity

- **One crate.** gt is seq/word/group-theory-heavy; a geometry- or
  arithmetic-heavy crate would likely show a larger omega share.
- **Passing fns only.** This measures what today's *green* depends on. The 24k-goal
  failing bucket (F7) is a different population — its taxonomy (§10.2) suggests
  peel∘omega closes a substantial slice there, so the deterministic floor across the
  WHOLE corpus is likely higher than 33%.
- **Minimal-prefix ≠ unique-closer.** A goal attributed to `omega` might also fall
  to `simp only [x]`; attribution follows the chain order as deployed. The T2 bucket
  is exact though: nothing in it closes under any T1 prefix.
- **Mix of exec-fn obligations and `--lean-all-proofs` proof-fn obligations**; not
  separated in this pass (the CSV has per-file rows if a future pass wants to).
- Artifacts predate the qualified-`decreasing_by` fix; irrelevant here (termination
  replays live in preamble defs, not the measured theorems).

## Reproduction

```bash
cd tactus-group-theory
TACTUS_LEAN_OUT=/tmp/attrib-emit \
  verus --lean-backend --lean-all-proofs --emit-lean --crate-type=lib src/lib.rs
# failing list from a full real run's log:
grep -oE "failed for [a-zA-Z0-9_]+" real-run.log | awk '{print $3}' | sort -u > failing.txt
python3 tools/rung-attrib/fast_attrib.py \
  --lib /tmp/attrib-emit/lib --failing failing.txt --sample 9999 \
  --csv rung-attrib-full.csv
```

Full-pool run ≈ 8 minutes (bare `lean`, preamble-once combined files, 8-way).

## Recommendations (feeding the squeeze-and-pin arc)

1. **Scope**: 145 T2 theorems in the current pool (≈70 effective after pred-twin
   halving) is the initial squeeze workload — small enough to validate the pin
   machinery end-to-end before F7 grows the population.
2. **Precondition pin seeding**: seed squeezes from the callee's mentioned spec fns
   (the emitter knows them) — likely covers the 81%-T2 kind cheaply.
3. **Emit the deterministic floor directly**: the 33% needs no pins; per the guiding
   rule, the emitter should select those single tactics outright (and the same logic
   should replace the `decreasing_by` rung *chain* with per-measure-shape dispatch —
   the emitter knows the measure it just built).
4. **Re-run this measurement after each squeeze milestone** — it's one command now;
   the T2 share trending to zero *is* the tactus_auto removal progress bar.
