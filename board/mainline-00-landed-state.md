---
title: "Main-line landed state (M6 default / F1-F4 / Brick 1 / S1) — context anchor"
status: done
claimed_by: fable
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
---

## Description

Anchor entry: where the main-line (non-bootstrap) work stands before this board's
queue starts. Not a task — a checkpoint. Full history: `DESIGN-transparent-automation.md`,
`DESIGN-lean-all-proofs-followons.md`, `MEASUREMENT-brick1-rung-attribution.md`,
git log on `main`.

## Writeup

As of tactus `f2f80a0` (main) + tactus-group-theory `935179f`:

- **M6 / package-check is the `--lean-backend` DEFAULT** (islands = auto-fallback,
  `--tactus-islands` opt-out). Cold 186s / warm ~82s on tgt. Suite 543/0.
- **tgt gate CLEAN: 2700 verified / 0 errors** — first fully clean gate under the
  package-check default (2026-07-13). The old `apply_hom_symbol_exec` baseline error
  was match-refinement goal-shape drift (package-check abstracts the match
  discriminant behind an antecedent); fixed site-locally with `cases hs : s.deref <;>`
  in tgt runtime.rs.
- **`--lean-all-proofs` coverage arc (B1-B5, F1-F4 + batch) complete**: codegen
  rejections 1,409 → 0 (2,747/2,747 fns emit); corpus re-measure 723/2,953 proof fns
  pass (2.9× from 253). Residual error families (numbers from the §10.2 re-measure,
  PRE-batch/B5 — stale, need re-count): auto bucket ~24,080 goals / ~2,230 fns,
  heartbeats 998, termination 199 (120 = F2c family, since fixed), deref 122 (B5,
  since fixed), tuple-Int type-mismatch 61.
- **Brick 1 measured** (215 theorems / 114 passing fns): minimal-closer histogram =
  rfl 6% / omega 18% / peel∘T1 8% / **T2 (`simp_all`/case_split) 67.4%**.
  Preconditions are the T2-heaviest kind (81%). Pred-twin halving ⇒ ~70 effective
  T2 theorems. 8/45 modules already pure-T1. Decision-table read: squeeze-and-pin,
  not outright T2 removal. Harness: `tools/rung-attrib/fast_attrib.py` (~2 min/run).
- **S1 landed + hardened**: `lean_verify/src/tactic_select.rs` — emitter selects
  `omega` / `tactus_peel <;> omega` over `tactus_auto` when the whole goal is in the
  linear-int-arith fragment. Two-layer term/prop classifier, global-blind (bare Var
  = int atom only if a proven-integer local). 0 regressions over the 114-fn pool;
  24 selections on gt (corpus-dependent — gt is opaque-heavy; S1 scales with
  arithmetic-heavy crates).
- **Standing direction (Danielle)**: `tactus_auto` disappears from artifacts; end
  state is TWO surfaces — emitter-derived tactics + inline proofs. Every injected
  tactic carries its own spec readable at the site; no ambient context.
- **Open design tension (this board's mainline-04)**: the design doc's §3.2 pin
  SIDECAR is a third surface — Danielle flagged it as suspect; the minimal
  alternative (derivation-first, no storage) is what mainline-03's census evaluates.

Next actionable: mainline-01/02 (quick wins), then mainline-03 (S2a census).
