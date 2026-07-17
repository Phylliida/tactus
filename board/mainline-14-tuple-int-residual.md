---
title: "tuple-Int type-mismatch residual (61 errors, tmp__:Int family)"
status: todo
claimed_by:
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
---

## Description

61 type-mismatch errors in the §10.2 re-measure: the `tmp__ : Int` tuple family,
flagged B5-ADJACENT (typed-spine claimed-vs-actual class, but through tuple
temporaries rather than call spines). B5a/B5b landed since — RE-COUNT first;
some may already be dead.

If survivors remain: census-first like B5 (claim-vs-declared eprintln probe
before flipping behavior), then extend the typed-spine bridge to the tuple
temporary path. The B5 spec (`DESIGN-B5-typed-spine-calls.md`) has the
methodology and the decoration-only trust-guard precedent.

Related surfaced-for-F-series item to check while in there: `=~=` in an exec
proof block = parse error + assert-fact reaching the postcondition as True
(from the B5b writeup) — verify current status, file separately if live.

**Done when:** fresh count; either "family closed by B5, 0 remaining" recorded,
or the bridge extension landed with a pinning e2e test and 0 regressions.

**Blocked by:** nothing (re-count is independent; ride mainline-12's re-measure
for the count if convenient).

## Status update (2026-07-17, after S2c/B4/B6/B10)

The `tmp__` family got a big new data point: factorial's 154:18
failure was exactly this shape — `let tmp__1 := result; … 0 ≤ tmp__1 *
(i+1)` with the let-var OPAQUE to omega (context let bindings are
never unfolded by omega). Fixed in B4's peel (Let case now emits
`intro <name>; subst <name>` — zeta-substitution), which may heal
part of the 61. **Re-count first** (as the task says) with the
current binary: any survivor whose goal has a goal-position `let`
should be re-tested, because the zeta fix changes that whole family.
The typed-spine bridge extension remains the fallback for survivors.
The `=~=`-in-exec-proof-block parse-error item (from the B5b writeup)
is unverified since — still needs the status check this task asks for.
