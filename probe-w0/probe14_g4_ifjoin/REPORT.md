# probe14 — W6e G4.2 If-fold probe (max_u64)

**Board:** bootstrap-24 (W6e). **Status:** PASS ✓ (rc=0, ~1.5s).

## What it pins

The last honest-fail in probe9 is `max_u64`: the frontend lifts the fall-through
`if` INTO each ensures leaf, so production emits two *branch-folded implications*

- leaf 15: ` x < y → (let r := (let m := y; m); r≥x ∧ r≥y)`
- leaf 16: `¬(x < y) → (let r := (let m := x; m); r≥x ∧ r≥y)`

whereas the live cert emits an *ensures-split* SST (`Ret([Span 11 (r≥x),
Span 13 (r≥y)], RetLet 10 14)`) whose refWp folds a `Let 10 14` wrapper — a
mismatch on orthogonal axes (branch vs ensures), so the bridge is 0.

G4.2 closes it by (1) recomputing a branch-folded reference SST
`Ret([impl15, impl16], RetNone)` and (2) transcribing production's leaf 15/16 to
deep `ExprData`. **This probe hand-builds both halves and verifies the contract
through the REAL emitted `ref_wp`/`goals_eq`/`render_exp` BEFORE the serializer
is touched** (the "probe first" / silent-divergence discipline).

## What `run.sh` proves (all by `decide`, one elaboration)

| # | claim | result |
|---|-------|--------|
| 0 | current opaque bridge `goals_eq (ref_wp ctx sst_current) goals_current` | **0** (honest-fail is real) |
| A | wired deep bridge `goals_eq (ref_wp ctx sst_wired) goals_wired` | **1** (the fix) + `goal_count = 2` |
| B | `expr_eq (render_exp impl15) deep15` / `impl16 deep16` | **1** / **1** |
| C | 6 single-drop kills (2 goal-side, 4 reference-side) | each flips **1→0** |

Plus a non-vacuity meta-check (decide refuses `¬(render diff)`).

## The one correction for the wiring

Real `SpanMark` loc ids are **11 / 13** (the loc-string leaves `@95:13` / `@95:21`,
reused from the live SST ensures spans), NOT the G4.1 kernel guard's placeholder
**9 / 12** (spanned-node leaf ids). The loc field is a globally-interned
loc-string id, identical wherever `@95:13` appears — so the recompute's `Span
11/13` and the goal transcription's `SpanMark 11/13` agree by construction. Using
9/12 there would break the bridge. (Confirmed with the local model.)

The m-binder id (probe uses 14) is render-transparent — the `Let` arm passes the
name straight through on both sides — so its absolute value is confirmed only at
G4.3 re-emit, without affecting the shape.
