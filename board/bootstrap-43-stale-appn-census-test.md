---
title: "stale unit test: `lexpr_to_exprdata_census_rejects` expects `ed-app-arity` for a 2-arg app, but bootstrap-34 widened that arm to accept AppN"
status: todo
claimed_by:
created: 2026-07-14T14:40:00Z
updated: 2026-07-14T14:40:00Z
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

## Writeup

_pending._
