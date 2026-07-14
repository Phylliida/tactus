---
title: "W7 — multi-arg AppN/CallN transcription (the deferred cache-churning RawList per-arg-TypData edit)"
status: in_progress
claimed_by: opus-w7-appn
created: 2026-07-15T04:10:00Z
updated: 2026-07-14T00:00:00Z
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
- (2026-07-14, opus-w7-appn step2a) **FORK RESOLVED = WORLD (a); step 2b
  CANCELLED.** Dumped a genuine multi-arg spec-fn call at both levels with the
  existing release binary (no serializer rebuild): `bootstrap-fixture/appn_probe.rs`
  + `verus --lean-backend --log vir --log vir-sst`. Three decisive findings
  (full excerpts in `probe-w0/probe18_appn/STEP2A-DUMP.md`):
  (1) Verus has **no** implicit per-arg coercions — `g2(x,y)` with `x:u64` into a
  `nat` param is a **hard compile error**, so every coercion MUST be a source
  `as` = a `Clip`; world (b) is impossible for the coercion axis. (2) Both VIR
  (`crate.vir`) and SST (`root-sst.vir`) show each coerced arg as
  `Clip{Nat}(Var x:u64)` with the **arg node's own `.typ` already = Nat**; the
  `Call` node has no per-arg-type slot and needs none. (3) A `&Tree`/`*t`
  ref-deref arg arrives as a **bare value-typed `Var t:Tree`** (ref/deref
  resolved away) → `needs_ref_deref` never fires either. ⟹ the single-arg arm's
  `coerce_if` (needs `int`-then-`nat`, but `arg.typ==argTy` always) AND
  `deref_if` (needs `TyRef` tag, never produced) are **both structural no-ops**,
  so the existing no-`TypData` `render_list` is identical to the per-arg chain.
  **Bonus:** `tactus-core` already has the full no-`TypData` spine landed &
  verified (`RawExp::CallN`/`RawList`/`render_exp`CallN→AppN/`render_list`, L332/
  392/405/944/974) — step 2b is not even an additive constructor. Local model
  consulted on the evidence: concurred, "no hole, proceed with widening." **Next
  instance: skip straight to step 3** — widen the 3 fail-loud serializer arms in
  `sst_serialize.rs` (L683 `raw_exp`, L932 `raw_vir_exp`, L1421
  `lexpr_to_exprdata`) to the multi-arg spine (Rust-only rebuild, NO whole-crate
  re-verify); first `--emit-lean`-dump a 2-arg caller to confirm production's
  `LExpr` head/arg shape (flat vs curried) for the `lexpr_to_exprdata` arm.
- (2026-07-15, opus-w7d-settle) Split out of `bootstrap-28`/`-29` when W7d
  closed the fixture-covering surface. The AppN deferral was Danielle-endorsed
  across several W7c turns (needs the cache-churning per-arg-`TypData`
  `RawList` edit); capturing it as its own todo so the transcriber cards can
  close honestly without hiding it.
- (2026-07-14, opus-w7-appn) **Step 1 (design-freeze probe) DONE + a fork found
  that may cancel the cache-churning edit entirely.** Built
  `probe-w0/probe18_appn/` (`run.sh` rc=0, ≈2.1s): 5 cases (A plain multi-arg
  both-coerce, B per-arg-heterogeneous = the load-bearing one, C ref-deref arg
  in list position, D length-3 + nested `callN`, E no-spurious-coercion control)
  — all correct renders close by `decide`+`rfl`, all 4 mutation-kills provably
  unequal, `render_exp`/`render_list` axiom-free, non-vacuity meta-check passes.
  It freezes `RawList.cons (hd) (argTy : TypData) (tl)` + a `render_list` that is
  the single-arg `Call` arm's `coerce_if∘deref_if` chain generalized per element.
- (2026-07-14, opus-w7-appn) ⚠ **FORK — is the per-arg-`TypData` edit even
  needed?** While fact-checking the report I found the single-arg serializer sets
  `arg_ty = typ_data(&arg.typ)` — the **arg's own type**, NOT the callee param
  type (`sst_serialize.rs` L689 + L681 comment). So the single-arg `Call` arm's
  `coerce_if` is a structural **no-op**; real `as nat` casts ride explicit `Clip`
  nodes **inside** the arg and are handled by recursion (the `sum_to` fixture is
  exactly this). Two worlds: **(a)** if Verus materializes per-arg call coercions
  into arg subexprs (like the fixture), the **existing no-`TypData`
  `render_list` already works and the cache-churning edit is UNNECESSARY** — just
  widen the two fail-loud arms to a plain `AppN`/`CallN` spine; **(b)** if Verus
  ELIDES per-arg coercions (as it demonstrably does for multiply operands, W6a
  Case B), the per-arg `TypData` is load-bearing and this probe's Case-B
  machinery is exactly right. The local model concurred: don't churn the crate
  cache until a real multi-arg SST dump settles (a) vs (b). **Next instance:
  START with step 2a below** (dump a genuine ≥2-arg spec-fn call). Full analysis
  in `probe-w0/probe18_appn/REPORT.md` ("Architectural fork" section).

## Writeup
**Partial — step 1 of 4 done; step 2 gated on an SST dump (see fork below).**

**Done:** the design-freeze probe `probe-w0/probe18_appn/` (green, axiom-clean),
which validates that a per-arg-typed `RawList` + a per-element coerce/deref
`render_list` closes the multi-arg bridge and kills mis-coercions. It mirrors the
W7a/W6a probe discipline and freezes the `CallN→AppN` invariants that hold
regardless of the fork (fn-name keying, dropped type-args, `_ret` render-unused,
and the two fail-loud arms to widen).

**Key finding (changes the plan):** the cache-churning per-arg-`TypData` datatype
edit this card assumed necessary may **not** be. It is load-bearing only if Verus
**elides** per-argument call coercions in the SST (world (b)); if Verus
**materializes** them into the argument subexpressions — which is exactly what the
single-arg fixture does, and the single-arg serializer's use of the *arg's own*
`.typ` strongly hints at — then the **existing** no-`TypData` `render_list`
already renders multi-arg calls correctly and the two fail-loud arms just need to
be widened to a plain spine (no datatype change, no whole-crate re-verify). The
right, cheap next step is a W6d.0-style SST/`LExpr` dump of a real ≥2-arg call to
decide before touching `tactus-core`. See the REPORT's "Architectural fork"
section for the full argument and both wiring paths.

**Assumptions/limits:** the probe's Case B assumes world (b) (elided coercions);
it proves the machinery is correct *if* needed, not that it *is* needed. No
`tactus-core` or `sst_serialize.rs` code was touched this turn (zero
shared-crate risk, per the card's step-1 gate).
