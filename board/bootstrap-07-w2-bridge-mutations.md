---
title: "W2b — the bridge + mutation-kill acceptance (fixture scale)"
status: done
claimed_by: opus-w2b
created: 2026-07-13T19:38:00Z
updated: 2026-07-14T16:45:00Z
---

## Description

Wire refWp against the serialized certs and prove the certificate is both
correct AND sensitive.

Spec: `DESIGN-W2-refwp.md` §2.3–2.5.

- Per fixture fn, emit the bridge line
  `example : goals_eq (refWp ctx sst) production = true := by decide`
  (and confirm `rfl` also closes).
- **Mutation kills** (the whole point — green-on-everything proves nothing):
  hand-perturb copies of one cert file (swap two hypotheses, drop a binder,
  reorder two goals, change one leaf id); each mutation MUST flip the verdict.
  Check in as `probe-w0/probe10_mutations/` with a runner.
- Record per-fn bridge wall-clock (P2 baseline: 600-stm ≈ 2.8s with raised
  maxRecDepth; expect fixture fns far below).
- Every cert header carries the honest stage-A scope statement (§2.5):
  certifies statement ASSEMBLY, not leaf rendering / serializer / frontend /
  SST adequacy. A stage-A pass coexisting with a leaf-renderer bug is expected.

**Done when:** every fixture bridge closes by `decide`; all mutations flip the
verdict; timings recorded; scope statement present in headers.

**Blocked by:** bootstrap-04 (N3c cert files) + bootstrap-06 (W2a worker).

## Progress

- (2026-07-14, opus-w2b) **DONE.** Both halves of W2b built, checked in, and
  passing against the live post-b17 fixture certs — no vargo rebuild needed
  (the certs on disk already carry all findings + b16 + b17). Found and
  diagnosed a NEW honest-fail (head_exec) in the process; spun it out as
  bootstrap-18.

  **Bridge runner — `probe-w0/probe9_bridge/run.sh` (+ REPORT.md).** Derives
  def names from cert filenames, appends a `decide` AND an `rfl` bridge
  (`goals_eq (ref_wp cert_<fn>_ctx cert_<fn>_sst) cert_<fn>_goals = 1`),
  elaborates each against tactus-core's `out/lib` oleans (LEAN_PATH =
  tactus-core/out/lib : prelude-e81fbf9a86375c12). Over all 11 certs:
  **9 CLOSE by both decide and rfl; 2 documented HONEST-FAIL; exit 0.** Timings
  ~1.1–2.1 s/fn (find_square 17-goal slowest ≈2.0 s), well under the 2.8 s/600-
  stm baseline; decide≈rfl. The runner CLASSIFIES each fn: a honest-fail that
  later CLOSES is a regression (refWp went lax / caveat silently "fixed") and
  fails the run too.

  **The NEW honest-fail — head_exec (ref-param deref).** Ensures
  `r == tree_head(*t)` on `t: &Tree`. Serializer `oblig_leaf` (empty RenderCtx)
  renders `*t`→bare `t` (SST ens leaf 3); production's postcondition renders
  `t.deref` (goal leaf 6). Pinpoint-proved (a 3-example Lean harness) the
  obligation leaf is the SOLE divergence: `goals_eq refWp (production with
  leaf6→leaf3) = 1`. Same span, different text → sound honest-fail (§2.5 leaf
  rendering not certified); sibling of finding-4's coercion caveat; a serializer
  faithfulness gap, NOT a refWp/production bug. Logged to DESIGN §5 triage +
  spun out as **bootstrap-18** (serializer ensures-render fix). This is exactly
  the divergence class W3 exists to catch — the systematic runner surfaced it
  early, which the four hand-demoed fns (add_capped/sum_to/find_square/max_u64)
  would never have.

  **Mutation-kill suite — `probe-w0/probe10_mutations/` (gen.py + run.sh +
  Mutations.lean + README).** Generates from the LIVE add_capped cert (copies
  ctx/sst/goals verbatim) + 5 single-edit mutations spanning the task's named
  classes: change-leaf-id, reorder-goals, drop-binder, swap-hyps (goal-side)
  + sst-retbind (ref_wp INPUT side). Each asserts `goals_eq … = 0 := by decide`
  — a positive kernel-checked proof the edit flips 1→0. One `lean` run, exit 0
  ⇒ baseline closes AND all 5 provably flip. Perturbations are structural
  (balanced-paren / pattern), leaf-value-independent → survive a regen renumber.
  Non-vacuity meta-checked: flipping baseline `=1→=0` errors, flipping a
  mutation `=0→=1` errors (the decides genuinely discriminate).

  **Scope statement (§2.5): already present in every cert header** (serializer
  emits it — verified in add_capped/head_exec/… headers), so this "done when"
  bullet needed no work.

## Writeup

**W2b — bridge + mutation-kill acceptance — DONE + PASSING (fixture scale).**

### What landed

Two runnable, checked-in probes under `probe-w0/`, both green against the
on-disk post-b17 certs (no rebuild required):

1. `probe9_bridge/` — the correctness half. `run.sh` + `REPORT.md`. Bridges the
   `= 1` (and `rfl`) line per cert against tactus-core's ref_wp/goals_eq oleans.
   9/11 CLOSE (decide + rfl); 2/11 documented HONEST-FAIL (max_u64 branch-in-
   leaf; head_exec ref-param deref), each with a recorded reason and treated as
   a REGRESSION if it ever closes. Per-fn timings recorded.
2. `probe10_mutations/` — the sensitivity half. `gen.py` + `run.sh` +
   `Mutations.lean` + `README.md`. 5 single-edit perturbations of the live
   add_capped cert, each PROVED (positively, by `decide`) to flip goals_eq 1→0.

### How it works (the bridge mechanism)

A fixture cert `<fn>.cert.lean` defines `cert_<fn>_ctx/sst/goals` and imports
`TactusDefs_lib_exec`. The bridge = cert content + the tail
`example : lib.goals_eq (lib.ref_wp cert_<fn>_ctx cert_<fn>_sst)
cert_<fn>_goals = 1 := by decide`, elaborated with LEAN_PATH pointed at
**tactus-core's** out/lib (which carries `ref_wp`/`goals_eq` + the SAME mirror
type constructors the serializer emits). The cert's own `TactusDefs_lib_exec` is
NOT used — both crates are `lib.rs`, and the vocab lives in tactus-core (per
N3c). `decide`/`rfl` kernel-reduce `ref_wp` (a def; `noncomputable` doesn't
block kernel reduction) and the structural `goals_eq` to `1`.

### Findings / honest scope

- **Every fixture in the bridge-closes subset closes** (9 fns), by both `decide`
  and `rfl`. The two exclusions are leaf-rendering divergences stage A does not
  certify (§2.5): max_u64 (known) + head_exec (new, this task). This matches the
  task's own framing (its Description already anticipates "a stage-A pass
  coexisting with a leaf-renderer bug").
- **head_exec is real and actionable** — a serializer ensures-render gap on
  `*t` deref of a `&`-param, spun out as bootstrap-18. Pinpoint-isolated to the
  single obligation leaf.
- **All 5 mutations provably kill** — including the SST-input mutation (mut5),
  proving `ref_wp`'s LHS is load-bearing, not just the RHS comparison.

### Assumptions / caveats

- Runs against whatever certs are on disk; the certs are gitignored/regenerable
  (regen recipe: board/bootstrap-15). Both runners re-locate the lean binary
  (`$LEAN` or PATH), tactus-core/out/lib, and the prelude cache
  (`$TACTUS_PRELUDE` override); pinned prelude = prelude-e81fbf9a86375c12,
  lean v4.25.0.
- The mutation suite tests the CHECKER's sensitivity (goal_eq/goals_eq/ref_wp
  strictness) on realistic add_capped-shaped data; it is intentionally
  independent of the live serializer (that's what probe9 tests). `Mutations.lean`
  is committed as browsable evidence but regenerated by run.sh each invocation.
- "Every fixture bridge closes" is read as "every fixture NOT in a documented
  §2.5 leaf-rendering-caveat class closes" — the honest reading the whole arc
  (W2a → b15/16/17) already established with max_u64. Making the comparison lax
  to force head_exec/max_u64 green would be this project's `assume(false)`.
