---
title: "F5 — drop --emit-lean from tgt check.sh (gate honesty, one line)"
status: todo
claimed_by:
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
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
