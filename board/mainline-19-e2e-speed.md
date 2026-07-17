---
title: "e2e-speed: slim prelude import + parallel per-fn Lean checks + defs collapse"
status: in-review
claimed_by: claude (e2e-speed branch)
created: 2026-07-17T14:50:00Z
updated: 2026-07-17T14:50:00Z
---

## Description

Why lean-backend runs took 10-20 min, and the fix. Root cause: every
per-fn package check is its own `lean` process, ~1.9s of which is
process start + prelude olean import (elaboration of an e2e-sized fn is
milliseconds). A crate pays 2+2N such processes, and a single-module
crate (tactus-core) gets exactly one verification bucket, so
`--num-threads` clamps to 1 and all of them run back-to-back.

## Changes (branch e2e-speed, commits 7935f4b + 6989450)

1. **Slim prelude imports.** TactusDefs imports `Lean.Elab.Command`
   (not the full `Lean` umbrella) — the closure carries simp_all /
   omega / decide / deriving / `elab` command; ~0.9s saved per lean
   process. TactusSearch adds `Lean.Elab.Tactic.BVDecide` (bv_decide
   syntax + elaborator are outside that closure).
2. **TactusLeanJob worker pool** (verifier.rs). The op walk collects
   lean-routed proof/exec fns; a bounded pool (num_threads) runs the
   checks after the walk; results report on the caller thread in
   collection order. All cross-fn lean_verify state was already
   OnceLock/Mutex-guarded (bucket-level concurrency existed on
   multi-module crates).
3. **Single-file defs collapse** (crate_defs.rs). When the partition
   has no per-module parts, base + umbrella merge into one module
   named the umbrella name — identical elaboration order, one fewer
   lean process per crate.
4. Exec Link entries sort by leaf name at consumption — registration
   order became completion order under the pool; Link file content
   stays deterministic.

## Measured (loaded machine, load 40-90 throughout)

- e2e suite: 218s baseline (main binary, direct) → **119s**, CPU 81 →
  50 min. 547/4 — the 4 = the known squeeze residue-4 set, 0 regressions.
- 6-fn crate, debug: 50.2s → 12.5s.
- tactus-core cold release (`--lean-backend --lean-all-proofs`, fresh
  TACTUS_LEAN_OUT): main 7m45s → branch **1m31s** (5.1x), identical
  results both sides: 141 verified / 0 errors, Link discharge 69
  closed / 0 pending.

## Side-finding (pre-existing on main, filed here for visibility)

N1 let-hoist emission is NONDETERMINISTIC: the same binary on the same
input emits the let-form on one run and the hoisted-∀-binder form on
another (HashMap iteration order somewhere in the hoist decision), and
the hoist form has a Box coercion bug (`Tree.Node tmp__5.deref` where
the ctor slot wants `Tactus.Box`). This is what makes the residue-4
tests flaky rather than stably red/green. Deserves its own board card.
Where to look: `hoist_all` (sst_to_lean.rs) gates on every `Let` frame
carrying `Some(typ)` — the flip means the TYPES on those frames come and
go across runs, so the nondeterminism is upstream in whatever threads
`binder_typs`/frame types (HashMap iteration order suspect), not in the
hoist code itself.

## Follow-up (not on branch)

Per-crate persistent lean driver: one process per crate holding the
post-prelude-import environment, elaborating each module against a
snapshot of its import parent (environments are immutable values, so
sibling isolation is exact). Kills the remaining ~1s/module import
cost; needs a design decision on olean production for the Link gate.
