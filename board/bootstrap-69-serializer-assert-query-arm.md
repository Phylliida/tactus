---
title: "serializer arm — assert-query (3 tgt exec fns; top tgt coverage blocker)"
status: in_progress
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

## Progress

- (2026-07-18, fable-b74) **Route (a) LANDED — the full vertical slice,
  gate green FIRST TRY.** Recon: production `build_wp_assert_query`
  (NonLinear) recurses the body under `Done(true)` in `OblCtx::new_scope`
  = keep Let/Binder frames, DROP Hyp frames; main flow re-enters via
  Verus's own Assumes (assert-by pattern). Mirror:
  `StmData::AssertQueryNl(Box<StmData>)` + `strip_hyps` spec fn;
  `wp_stm f (AssertQueryNl b) = wp_stm (strip_hyps f) b`;
  `frame_after = f`; `exec_safe_f` arm carries the SAME stripped frame →
  the soundness arm is a direct IH at `strip_hyps f` (DeadEnd template,
  NO weakening lemma needed — the isolated-query spec is honest).
  u_wp_aqnl/u_esf_aqnl plain-bodied (no tactus_tactic). Gate: 141/0,
  **Link discharge 69/69 closed 0 pending — the R-c machinery absorbed
  the new variant automatically** (wf conjuncts + weave, zero edits).
  probe37 loop closure still PASSES (abbrev design auto-adapts).
  Serializer: NonLinear arm emits the node; Tactus/BitVector modes get
  sharper tags (`assert-query-tactus`/`-bitvector`); stm_size_of counts
  the new head (trailing-space fix: `Assert ` vs `AssertQueryNl` prefix
  double-count).
- (2026-07-18, fable-b74) **Census discoveries from the cold tgt run:**
  (1) todd_coxeter_rt's two exec fns reject as `assert-query-TACTUS` —
  their fn-level tactus_tactic attribute makes the asserts Tactus-mode;
  the NonLinear arm is upstream-correct but THESE two need a Tactus-mode
  design (different goal structure: have-by render). The card's "3
  assert-query" census has shifted since 07-14. (2) **certified 133/825
  fns crate-wide** — cert emission broadened enormously since the 1-cert
  probe11 era; the W3 soak's real corpus is those 133 (full-crate
  emission + bridge sweep = the actual soak, in flight).
- (2026-07-18, fable-b74) **Full-crate census: certified 265/1649;
  exec wp-certs still 1 (runtime clone) — ALL 3 tgt assert-query fns are
  TACTUS-mode** (todd_coxeter_rt ×2 + runtime.is_inverse_pair_exec);
  zero NonLinear-blocked exec fns in tgt today. The arm is complete,
  correct, tgt-neutral: direct tgt unblocking needs bootstrap-70 (Call)
  + a Tactus-mode design. Tactus-mode recon note: production renders
  those inline (`have h : P := by <tactic>`, no separate goal; P enters
  as hyp) — the stage-A mirror looks Assume-like, small design. Suite
  547/4 (known main residue, 0 regressions). Remaining for done:
  fixture fn with by(nonlinear_arith) exercising cert+bridge end-to-end,
  + the Tactus-mode decision.
