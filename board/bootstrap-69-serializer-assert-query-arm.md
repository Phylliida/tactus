---
title: "serializer arm — assert-query (3 tgt exec fns; top tgt coverage blocker)"
status: todo
claimed_by:
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T17:15:00Z
---

## Description

Widen the stage-A serializer census: the `assert-query` rejection class blocks
3 of tgt's 9 exec fns (per the N4 census / W3 run, e.g. the `todd_coxeter_rt`
exec fns) — after the Call arm landed, this is the largest remaining tgt
coverage blocker for the W4 gate.

- Recon first: what SST shape triggers the `assert-query` fail-loud tag
  (`sst_serialize.rs`), and what does production render for it? Decide whether
  it is (a) a transcribable statement shape → a new `StmData`-level arm +
  refWp equation (cache-churning tactus-core edit — batch it), or (b) an
  obligation-shape variant expressible with existing constructors → serializer
  arm only.
- Keep the discipline: serializer recomputes structure independently, refWp
  stays a dumb checker, the bridge `decide` is the meaningful test; every
  still-unsupported sub-shape keeps a sharp census tag.
- Validate: the 3 tgt fns emit certs and bridge-close (or divergences triaged
  honest-fail with pinpoint evidence, per the probe11 discipline); fixture
  suite + probe runners stay green; mutation-kill on the new arm.

**Done when:** `assert-query` census count on tgt drops to 0 (or the residual
is re-tagged sharper with a written reason), with bridges closing and suite
green.

**Blocked by:** nothing hard; if (a) a mirror change is needed, coordinate the
tactus-core churn with the bootstrap-61 batch to pay the cache invalidation
once.
