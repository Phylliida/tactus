---
title: "stale unit test: `lexpr_to_exprdata_census_rejects` expects `ed-app-arity` for a 2-arg app, but bootstrap-34 widened that arm to accept AppN"
status: done
claimed_by: opus-bootstrap43-census
created: 2026-07-14T14:40:00Z
updated: 2026-07-14T15:30:00Z
---

## Description

`cargo test -p lean_verify --lib` has ONE failing test:
`sst_serialize::tests::lexpr_to_exprdata_census_rejects`
(`sst_serialize_tests.rs:352`). It asserts a 2-arg application
(`lib.Point.mk a b`) census-rejects with `"ed-app-arity"`, but
`lexpr_to_exprdata` now returns `Ok(ExprData.AppN 0 [Atom 2, Atom 1])`.

This is **stale from commit `d3349be` (bootstrap-34 steps 3+4: "widen 3
fail-loud arms → multi-arg AppN/CallN")**, which deliberately made multi-arg
apps IN-class (they lower to `ExprData::AppN`, see `sst_serialize.rs:1490-1507`).
The test's 2-arg-app example was not updated when that arm was widened, so it has
been failing since d3349be — noticed during bootstrap-40's regression pass (the
other 365 `--lib` tests pass).

## Scope of the fix

Update the test to reflect the post-bootstrap-34 census taxonomy: a 2-arg app is
now ACCEPTED as `AppN`, not rejected. Either move that assertion to the
"accepts" test (`lexpr_to_exprdata_*` positive cases) asserting the `AppN`
`Ok(...)` shape, or replace the middle example with a node that is genuinely
still out-of-class (keeping the `census_rejects` test focused on real
rejections — the `ed-unop` (neg) and `ed-binop-bitand` assertions in the same
test still pass and should stay). Confirm against `sst_serialize.rs`'s current
arity handling which shapes still reject.

**Done when:** `cargo test -p lean_verify --lib` is green (0 failures), with the
census-rejection test still meaningfully checking rejection of out-of-class
nodes.

## Progress

- (2026-07-14, opus-bootstrap40-deepview) Filed. Low priority / low risk; noted
  so a stale red test doesn't mask a future real regression in the `--lib` suite.

- (2026-07-14, opus-bootstrap43-census) DONE. Confirmed the staleness against the
  source, refocused the rejection test onto a genuinely out-of-class node, added
  a positive `AppN`-accept test, and fixed a second stale reference to the dead
  `ed-app-arity` tag. Full `--lib` suite green (367 passed, 0 failed).

## Writeup

**Root cause confirmed.** `census_rejects` (`sst_serialize_tests.rs:352`) asserted
a 2-arg app `lib.Point.mk a b` census-rejects with `ed-app-arity`. But since
bootstrap-34 (`d3349be`) the multi-arg App arm (`sst_serialize.rs:1498-1510`)
accepts a **fn-headed** multi-arg app: `app_head_fn_name(head)` peels the
`Var`/`App{Var,..}` head and it lowers to `Ok(ExprData.AppN fn (ExprList …))`.
`ed-app-arity` is now a **dead tag** — grep finds zero live returns of it in
`src/` (only doc-comment mentions remained).

**Fix (two test edits + one comment fix), all in the "refocus, don't delete"
spirit the card asked for:**

1. **Refocused the rejection** (`census_rejects`): replaced the stale 2-arg-app
   assertion with a multi-arg app whose head is a **field projection** (`(*t) a
   b`), not a fn name. `app_head_fn_name` returns `None` for a non-`Var` head, so
   the AppN arm census-rejects it with `ed-app-head` — a real out-of-class case
   the census still enforces. The `ed-unop` (neg) and `ed-binop-bitand`
   assertions in the same test are untouched and still pass.

2. **Pinned the acceptance** (new `lexpr_to_exprdata_appn_multiarg` test): asserts
   the fn-headed 2-arg app `lib.Point.mk a b` now returns the exact `AppN` Ok
   shape. Interning/ordering verified by hand and confirmed by the runner on
   first try: head `lib.Point.mk`=0 (interned first), then the arm folds args in
   REVERSE (`args.iter().rev()`) so `b`=1, `a`=2 — the cons-list reads
   `a(2) :: b(1) :: Nil` (source order preserved):
   `(lib.ExprData.AppN 0 (Box (ExprList.Cons (Box (Atom 2)) (Box (ExprList.Cons
   (Box (Atom 1)) (Box ExprList.Nil))))))`.

3. **Fixed a second stale `ed-app-arity` reference** (`sst_serialize.rs:3444-3450`,
   the `Xor` doc note on `lean_binop_opcode`): it claimed `Bool.xor a b`
   census-rejects with `ed-app-arity`. Rewrote it to reflect that `Bool.xor a b`
   now lowers to `ExprData.AppN` (not a `BinOp`). The note's *conclusion* — the
   reference's `Xor → 14` BinOp opcode is never consumed by a bridged fn — still
   holds, but for a different reason now: both sides mirror `Bool.xor` through the
   App/AppN path (keyed on the same interned fn id), never through `BinOp 14`.

**Verification:** `cargo test -p lean_verify --lib` → **367 passed; 0 failed**
(was 366 total with 1 failing; +1 for the new positive test). Done-criterion met:
suite green, census-rejection test still meaningfully checks a real rejection.

**Assumptions / honest scope:** no production/semantic code changed — only test
assertions and two doc comments. I did NOT chase whether the `Bool.xor → AppN`
acceptance (a genuine behavior change from bootstrap-34) needs the reference side
to also mirror `Bool.xor` as an `AppN` for the bridge `decide` to agree on a
formula containing `Xor`. It's plausibly fine (symmetric App/AppN on both sides)
and no bridged tgt/fixture fn currently uses `Xor`, but it's an untested corner —
flagged here rather than silently assumed correct.
