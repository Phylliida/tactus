---
title: "W7 — multi-arg AppN/CallN transcription (the deferred cache-churning RawList per-arg-TypData edit)"
status: done
claimed_by: opus-w7-appn
created: 2026-07-15T04:10:00Z
updated: 2026-07-14T12:00:00Z
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
- (2026-07-14, opus-w7-appn steps 3+4) **DONE — three arms widened, live
  `def_eq` bridge over `AppN` closes green.** Reconfirmed the flat-arg shape
  by reading the production construction site directly (stronger than a dump):
  `to_lean_sst_expr.rs` L1228-1259 builds `head = LExpr::app(Var(name),
  [typeargs])` then `LExpr::app(head, [v0..vn])` — value args FLAT in one Vec,
  type args folded into the head, so `app_head_fn_name` peels the SAME head
  shapes as the single-arg arm and there is no curried nesting. Then:
  - **Step 3 — widened all three fail-loud arms** in `sst_serialize.rs` to the
    existing no-`TypData` spine (strict widening: `len == 1` unchanged → `Call`/
    `App`; `len >= 2` → `CallN`/`AppN`; `len == 0` stays census-rejected):
    reference SST `raw_exp` (was `raw-call-arity`) → `RawExp::CallN(fn, ret,
    RawList[args])`; reference VIR `raw_vir_exp` (was `rawvir-call-arity`) →
    same; production `lexpr_to_exprdata` (was `ed-app-arity`) → `ExprData::AppN(
    fn, ExprList[args])`, keyed on the SAME interned fn name so `def_eq` agrees
    by construction. Rust-only rebuild (`vargo build --release`, ~20s incr.);
    vstd re-verified 1530/0 (no whole-crate churn).
  - **Step 4 — live bridge closed.** Added F20 to `bootstrap-fixture/lib.rs`:
    `g2`/`g3` (2-/3-arg all-`nat` spec fns) + `call_g2`/`call_g3` (bodies
    `g2(x,y)` / `g3(x,y,z)` — the only ≥2-arg calls in the fixture) + a
    `use_multiarg` exec keep-alive (`ensures true` + ghost refs) so Verus's
    dead-code pruning doesn't drop them before the def-cert pass (the reason the
    first re-emit emitted no g2 cert). Re-emit (`--tactus-emit-cert`) →
    `call_g2.defcert.lean` shows reference `RawExp.CallN 3 TyNat [Var 1, Var 2]`
    → `render_def` → `AppN 3 [Atom 1, Atom 2]` matching production `AppN 3 [Atom
    1, Atom 2]` — identical fn_id (3) and flat arg order on both sides. Probe17
    live runner: **all 8 def/dt certs positive OK + kill non-vacuous** (new
    call_g2/call_g3/g2/g3 + pre-existing sq/tree_head/tri/Tree unregressed).
  - **⚠ env gotcha for next instance:** probe17 must use the **Nix** `lean`/
    `lake` on PATH (`/nix/store/…lean4-4.25.0/bin/lean` = `command -v lean`),
    which built the `tactus-core/out/lib/*.olean` + the `prelude-e81fbf9a…`
    cache. The elan `~/.elan/toolchains/…v4.25.0` lean has a DIFFERENT build
    hash → "incompatible header" on every olean. Do NOT override `LEAN` or
    `TACTUS_PRELUDE`; the runner's defaults are correct. (None of the 4 elan
    toolchains load these oleans; only the Nix lean does.)
  - **Honest residual:** the def bridge live-tests the VIR (`raw_vir_exp`) +
    production (`lexpr_to_exprdata`) pair. The SST `raw_exp` arm (obligation-
    position multi-arg calls) is the mechanical mirror of the validated VIR arm
    but has no obligation-position ≥2-arg call in the fixture to exercise it
    live this turn — a cheap follow-on is a proof fn with a multi-arg call in
    its ensures (whose goal cert flows through `raw_exp`). Also `sum_tree`-style
    `DefCurried` (structural-recursion) callees still get no def cert (pre-
    existing `maybe_emit_def_cert` gate, orthogonal).
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
**DONE — all four steps complete; multi-arg `AppN`/`CallN` closes the live
`def_eq` bridge; `tactus-core` untouched (world (a), step 2b cancelled).**

**What landed (2 tracked files):**
- `source/lean_verify/src/sst_serialize.rs` — three fail-loud arms widened to
  the *existing* no-`TypData` spine already present & verified in `tactus-core`
  (`RawExp::CallN`/`RawList`/`render_list` → `AppN`, lib.rs L392/405/944/974;
  `ExprData::AppN`/`ExprList` L332/348). Strict widening: single-arg path is
  byte-for-byte unchanged (`Call`/`App`); only `len >= 2` (previously the
  `raw-call-arity`/`rawvir-call-arity`/`ed-app-arity` errors) now transcribes;
  `len == 0` stays rejected. Reference (SST `raw_exp` + VIR `raw_vir_exp`) emits
  `CallN`; production (`lexpr_to_exprdata`) emits `AppN`, keyed on the identical
  interned fn name so `def_eq` agrees by construction.
- `bootstrap-fixture/lib.rs` — F20: `g2`/`g3` + `call_g2`/`call_g3` (the only
  ≥2-arg calls in the fixture) + `use_multiarg` keep-alive.

**How it works:** the step-2a SST/VIR dump proved Verus MATERIALIZES every
call-arg coercion as a `Clip` inside the arg (the arg's own `.typ` already
carries the coerced type) and resolves `&`/`*` ref decorations away before
transcription. So the single-arg arm's per-arg `coerce_if`/`deref_if` are both
structural no-ops, and the plain per-element `render_list` renders every
producible multi-arg shape faithfully — no per-arg `TypData` field, no datatype
edit, no whole-crate re-verify. Production builds multi-arg apps FLAT
(`to_lean_sst_expr.rs` L1228-1259: type args in the head, value args in one
Vec), so `app_head_fn_name` peels the same head shapes as single-arg.

**Verification:** `vargo build --release` (incr. ~20s), vstd 1530/0. Re-emit
`--tactus-emit-cert` over the fixture; probe17 live runner → **8/8 def+dt certs
positive OK, kills non-vacuous**; `call_g2.defcert.lean` shows both sides render
`fn_id=3`, flat arg order `[1,2]`. Pre-existing certs unregressed.

**Assumptions/limits (honest):**
1. Live-tested pair is VIR + production (the def bridge). SST `raw_exp` is the
   mechanical mirror of the validated VIR arm but is exercised only by
   obligation-position ≥2-arg calls, of which the fixture has none this turn —
   a proof-fn ensures with a multi-arg call is the cheap follow-on.
2. Fixture verification-neutrality argued by inspection: `use_multiarg` is
   `ensures true`; `g2`/`call_g2`/… are pure `open spec fn` defs. Emit reported
   SST-level 21 verified/0 errors but `--emit-lean` skips the Lean discharge, so
   full-Lean verification of the fixture goals was not separately run.
3. `DefCurried` (structural-recursion) callees still get no def cert
   (`maybe_emit_def_cert` gate — pre-existing, orthogonal to arity).
4. Env: probe17 needs the **Nix** lean (`command -v lean`), NOT elan v4.25.0 —
   the oleans/prelude were built with the Nix build hash (see Progress ⚠).
