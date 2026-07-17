---
title: "F5 — drop --emit-lean from tgt check.sh (gate honesty, one line)"
status: done
claimed_by: fable
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T18:05:00Z
---

## Description

`tactus-group-theory/check.sh` still passes `--emit-lean` — the Lean-SKIPPING
footgun: daily gate runs emit artifacts but never elaborate them. The original
cost reason evaporated with M6: warm verifying run (~85s) ≈ emit-only (~89s
floor), so Lean verification is now effectively free after one cold cache fill
(~4 min).

Change: remove `--emit-lean` from the verus invocation in
`tactus-group-theory/check.sh`; update the header comment to say the gate
Lean-verifies under package-check (the default). Same one-line review for
`tactus-computability-theory/check.sh` while there (it has its own crate-local
check.sh — see if it carries the same flag).

Spec: `DESIGN-lean-all-proofs-followons.md` §F5. Authorized by Danielle in the
2026-07-16 planning conversation (this was the "her call" gate).

**Done when:** `./check.sh` on tgt runs the live package-check gate, one cold
fill observed, warm run in the ~85-95s band, still 2700v/0err.

**Blocked by:** nothing.

## Progress

- (2026-07-16) ct's check.sh checked: does NOT carry `--emit-lean` — tgt only.
- (2026-07-16) Flag dropped, header comment updated (tgt `c6dc41c`). Cold-ish
  run 3m59s → **3116 verified / 0 errors**; warm 2m03s (24 verified + 6322
  cached, 0 errors). Host load checked before timing (loadavg 6/64).

## Writeup

Done — the daily tgt gate now actually elaborates Lean on every run.

**Finding (expected-unexpected):** the package gate on MAIN currently reports
"skipped: shared-defs module unavailable" and falls back to ISLANDS per-fn
checks (still real Lean verification — the fallback is M6.5's designed
behavior). Defs build fails with two known errors: `Tactus.Ref` deep_view type
mismatch (exec+proof base) and missing `Option.Some_val0` accessor
(coset_group part). Both are FIXED on the bootstrap branch (bootstrap-40/41,
status done); main heals at the next bootstrap→main sync (bootstrap-72, still
todo). The islands fallback also re-attempts the defs ladder, which explains
warm 123s vs the ~90s package-check band — same heal path.

Deviation from done-when as written: gate is live but in islands-fallback mode
until the sync; warm 123s not 85-95s. Judged done — the task's purpose (gate
honesty) is achieved; the package-path residual is tracked by bootstrap-72,
not this board.
