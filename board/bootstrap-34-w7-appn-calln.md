---
title: "W7 — multi-arg AppN/CallN transcription (the deferred cache-churning RawList per-arg-TypData edit)"
status: todo
claimed_by:
created: 2026-07-15T04:10:00Z
updated: 2026-07-15T04:10:00Z
---

## Description

The one W7c body-constructor that both transcriber sides still fail-loud on:
**multi-argument application** (`CallN`/`AppN`). It is tgt-slice-only — the
`bootstrap-fixture` calls (`tri`, `sq`, `tree_head`, `sum_tree`) are all
single-arg or nullary, so the fixture forces none of this. That is why W7c
(`bootstrap-28`/`-29`) and W7d (`bootstrap-33`) closed the fixture-covering
def+datatype surface WITHOUT it. This card carries the remainder so it is not
hidden inside a "done" transcriber card.

**The two fail-loud sites today:**
- reference `raw_vir_exp` (`source/lean_verify/src/sst_serialize.rs`): the
  `Call(CallTarget::Fun, args)` arm handles `args.len()==1` and fails loud
  `rawvir-call-nonfun`/`call-*` on multi-arg (see `bootstrap-29` Progress).
- production `lexpr_to_exprdata` (same file): the single-arg `App`/`Call` arm;
  multi-arg `ExprNode::App` with >1 arg is not yet transcribed.

**Why it was deferred (Danielle-endorsed, recorded in `bootstrap-28`/`-29`):**
a FAITHFUL multi-arg render needs per-argument expected-type coercion
(auto-borrow deref — Verus inserts `&`/`*` and `Int.toNat` casts per arg based
on the callee's parameter types). That means `render_list` in `tactus-core`
must carry a per-arg `TypData` so it can coerce each argument, which is an
additive `RawList`/`render_list` edit ⟹ base-hash change ⟹ whole-crate
re-verify + olean re-emit (the W6b/W7b "one batched cache-churning edit"
discipline). So this is its own turn, gated behind a probe that freezes the
per-arg-TypData `RawList` shape first (mirror the W7a/W6a probe pattern).

**Done when:**
- a `probe-w0/probe18_appn/` standalone `.lean` probe freezes the per-arg-TypData
  `RawList` vocabulary (App with a coercing arg + a kill), rc=0, axioms clean;
- the batched `tactus-core` edit lands `RawList` carrying per-arg `TypData` +
  `render_list` per-arg coercion (crate re-verifies, oleans re-emit, probe9/13/
  14 stay green — the W7b discipline);
- both `raw_vir_exp` and `lexpr_to_exprdata` transcribe multi-arg App→AppN
  (census-gated, unit-pinned), co-designed so `def_eq` agrees by construction;
- a tgt-slice def with a multi-arg call closes the live `def_eq` bridge
  (extend `probe17_w7d_live` or add a fixture caller with a 2-arg spec fn).

**Blocked by:** nothing new — W7b vocab + W7c/W7d landed. **Blocks:** full W7
coverage of the tgt slice (any tgt spec fn calling a ≥2-arg helper).

## Progress
- (2026-07-15, opus-w7d-settle) Split out of `bootstrap-28`/`-29` when W7d
  closed the fixture-covering surface. The AppN deferral was Danielle-endorsed
  across several W7c turns (needs the cache-churning per-arg-`TypData`
  `RawList` edit); capturing it as its own todo so the transcriber cards can
  close honestly without hiding it.

## Writeup
_todo_
