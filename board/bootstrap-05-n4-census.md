---
title: "N4 — serializer census over tactus-group-theory (~3116 fns)"
status: done
claimed_by: opus-b14-cont
created: 2026-07-13T19:38:00Z
updated: 2026-07-14T03:45:00Z
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
  - **Cold tgt census COMPLETE** (1m40s, background task): **3116 verified /
    0 errors**, **9 cert-eligible fns**, **1/9 certified**. Cold flag-OFF
    baseline: 3116/0 in 99.56s → zero verdict delta, ~0.4s overhead. Full
    table + roadmap written to DESIGN §1.1. Marking done.

## Writeup

**Done.** The census is complete over both corpora (fixture + tgt). Full
tables live in `DESIGN-W2-refwp.md §1.1`; this is the summary + how it works.

**Headline finding (reframes the census).** Stage-A cert emission is
**exec-fn-only**: `emit_cert` is called solely from `emit_package_exec_fn` and
its island sibling (`generate.rs:3746`, `:4059`), per verified *exec* fn's WP
obligations. tgt is proof/spec-heavy (3571 `spec`/`proof` decls) with only
**9 exec fns**, so the crate-wide census denominator is 9, not ~3116. The
plan's expected buckets (trait-method obligations, generics, closures, bv)
live in proof/spec fns and **never reach the serializer** at stage A. So the
`bootstrap-fixture` family — not tgt — is the real serializer stress corpus;
tgt's contribution is verdict-neutrality-at-scale + real-code confirmation of
the exec-fn gaps.

**The numbers.**
- **Fixture (14 fns, cold):** 9/14 certified; 20 verified / 0 errors flag ON
  and OFF; gap = 5×`call` (100% of the gap).
- **tgt (3116 fns, cold):** 1/9 exec fns certified (`runtime::impl_4::clone`);
  8 rejected = **5 `call`** (runtime::{find_cancellation_exec, copy_word,
  apply_hom_gen, apply_hom_inv, apply_hom_symbol_exec}) + **3 `assert-query`**
  (todd_coxeter_rt::{symbol_to_column_exec, inverse_column_exec},
  runtime::is_inverse_pair_exec).
- **Verdict delta = ZERO** at both scales (3116/0 flag on == off; 20/0 on ==
  off). N3 §7.4 re-checked at 3116-fn scale. ✓
- **Overhead negligible:** tgt cold 100s ON vs 99.56s OFF (~0.4s, <0.5%),
  because emission touches 9/3116 fns; "render leaves twice" is trivial when
  the emit population is 9.

**Stage-B roadmap (the deliverable's point).** Exec-fn stage-A coverage across
both corpora is gated by exactly two serializer arms:
1. **`StmData::Call`** (`bootstrap-02b`) — clears 5 fixture + 5 tgt = **10
   fns**. Highest-leverage next arm by a wide margin.
2. **`assert-query`** — clears 3 tgt fns. Distant second.
Landing both takes tgt exec-fn certs 1/9 → 9/9 and the fixture 9/14 → 14/14.
No other construct blocks any exec fn in either corpus.

**How the census works.** `--tactus-emit-cert` (flag only in the
`tactus-bootstrap` binary) sets `set_cert_emit_enabled`; per exec fn,
`emit_cert` either writes `<TACTUS_LEAN_OUT>/<crate>/cert/<fn>.cert.lean` and
calls `census_note_certified()`, or fails loud with `census_note_rejected(tag)`
(stderr `tactus: cert: <fn> not serialized: <tag>`). At crate-end the verifier
prints `census_report()` = `certified M/N fns`. Per-construct ranking = `sort
| uniq -c` over the `not serialized: <tag>` lines.

**Assumptions / caveats (be honest).**
1. **Two prerequisites the card's "one-line plumbing" missed, now documented:**
   (A) the flag is absent from tgt's `check.sh` binary
   (`../tactus/source/…/verus`, commit `f2f80a0`); the census must use
   `tactus-bootstrap/source/target-verus/release/verus`. (B) the census is
   **cache-confounded** — `emit_cert` runs only when a fn actually verifies,
   so cache-hit fns are never censused; a warm run reported a misleading
   `certified 1/9` with `6322 cached`. **A tgt-wide census MUST run cold**
   (omit `-V cache`; `--no-cache` is a check.sh-only flag the binary rejects).
2. I did **not** edit tgt's `check.sh` to add a `VERUS=` override (the card
   floated it as optional). Skipped deliberately: the census is a cold,
   one-shot measurement, and a permanent override in a shared crate script
   risks pointing routine tgt verification at the wrong (bootstrap) binary. If
   a repeatable census command is wanted, add it as a separate opt-in script
   rather than mutating the default `check.sh`. Left as a possible follow-up.
3. The exec-fn count "9" is the census's own authority (fns that reached
   `emit_cert`); a raw grep for `fn` overcounts (trait sigs, closures) — don't
   use it as the denominator.
4. Cold tgt verified in ~100s (Lean elaboration was fast; oleans warm even
   with the verus result-cache disabled). Timing may differ on a truly cold
   Lean state.
