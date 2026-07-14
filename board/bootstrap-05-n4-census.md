---
title: "N4 — serializer census over tactus-group-theory (~3116 fns)"
status: in_progress
claimed_by: opus-b14-cont
created: 2026-07-13T19:38:00Z
updated: 2026-07-14T03:50:00Z
---

## Description

Run `--tactus-emit-cert` over tgt + the fixture family. The crate-end
`certified M/N` summary + per-construct rejection counts IS the deliverable —
it sets the stage-B coverage roadmap and is the first honest measure of the
stage-A subset.

Spec: `DESIGN-W2-refwp.md` §1.

- Plumb the flag through tgt's crate-local `check.sh` (one line; the
  CRATE-LOCAL check.sh is the way to verify tactus-* — Lean backend + gt
  export).
- Append a ranked table (construct → fn count) to `DESIGN-W2-refwp.md`.
  Expected big buckets: trait-method obligations, generics, closures, bv.
- Measure cert-emission overhead (wall-clock delta flag on/off on tgt);
  budget expectation = rendering leaves twice.
- Confirm ZERO verification-behavior delta at scale (flag must not perturb
  verdicts) — re-check N3 acceptance §7.4 on the big crate.

**Done when:** the ranked table is in the doc; overhead is measured; verdict
delta is zero; the stage-B roadmap is legible from the numbers.

**Blocked by:** bootstrap-04 (N3c) — needs the working serializer.

## Progress

- (2026-07-14, opus-b14-cont) **Claimed; mechanism validated end-to-end;
  two setup prerequisites the card missed found + recorded.** Full detail in
  `DESIGN-W2-refwp.md §1.1`. Summary:
  - **Prereq A:** the flag is NOT in the tgt-facing binary. tgt's `check.sh`
    uses `../tactus/source/…/verus` (checkout `f2f80a0`, Jul 12) which
    predates the cert work; `--tactus-emit-cert` lives only in the
    `tactus-bootstrap/` checkout. Ran the census under
    `tactus-bootstrap/source/target-verus/release/verus` directly. (`tactus`
    and `tactus-bootstrap` are two checkouts of the same fork at different
    commits.)
  - **Prereq B (the important one):** the census is **cache-confounded**.
    `emit_cert` runs only when a fn actually verifies; cache-hit fns skip the
    emit path and are never censused. A warm tgt run gave `24 verified, 0
    errors, 6322 cached` and a census note of only `certified 1/9 fns`. A
    tgt-wide census therefore needs a **cold run** — just omit `-V cache`
    (the raw binary doesn't cache by default; `--no-cache` is a check.sh-only
    flag the binary rejects). Cold runs don't touch the warm cache.
  - **Verdict-neutrality (N3 §7.4 re-check):** `0 errors` with the flag on in
    every run incl. the warm tgt run. ✓
  - **Fixture census (complete, cold):** **9/14 certified**; `20 verified / 0
    errors` flag ON and OFF (zero verdict delta); 9 cert files; overhead in
    the noise (1.047s on / 1.073s off). The fixture's entire gap is 5×`call`
    (= `bootstrap-02b`); too homogeneous to show tgt buckets.
  - **Cold tgt census LAUNCHED** (background, `/tmp/n4-tgt-cold.log`). Warm run
    already surfaced an `assert-query` tag family beyond `call`. The ranked
    bucket table (→ DESIGN §1.1) + tgt overhead land when it finishes.
  - **Remaining to close:** collect the cold tgt run → fill the ranked
    per-construct table + tgt wall-clock overhead into DESIGN §1.1; optionally
    add the `VERUS=` override to tgt `check.sh` so a future census is one
    command. (Left todo pending the cold run's completion.)

## Writeup

_when done: findings, how the code works, assumptions made_
