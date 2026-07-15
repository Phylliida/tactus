---
title: "B1 (soundness follow-up) — move the structural-binop deref-balance into the TCB render_exp (close bootstrap-39's common-mode gap)"
status: todo
claimed_by:
created: 2026-07-14T17:00:00Z
updated: 2026-07-14T17:00:00Z
---

## Description

`bootstrap-39` closed the `&`-deref bridge divergence with **B2**: the
transcriber `raw_exp` (`sst_serialize.rs`, `ExpX::Binary` arm) inserts
`RawExp.Deref` nodes by mirroring production's structural-binop min-balance
(`to_lean_sst_expr.rs:1157-1161`, driven by `count_ref_decorations`). That works
and is validated, but it has a **common-mode soundness gap**: production AND
`raw_exp` both compute the peel from the same `count_ref_decorations` helper, so
the bridge no longer *independently* checks the deref-count — a bug in that
helper reproduces identically on both sides of `goals_eq` and silent-passes. The
reference `render_exp` (TCB) sees only pre-baked `Deref` nodes; it never derives
the peel itself. (My analysis + Danielle's local model both landed on this,
independently.)

**B1 closes the gap** by moving the deref-balance into the trusted reference:
extend the TCB `render_exp` BinOp arm to compute the peel from the operand types
it ALREADY reads for nat-coercion (`type_of l`, `type_of r`), emitting the
`FieldProj … deref_field`s itself. Then:
- `raw_exp` goes back to emitting the bare ref-typed `Var` (revert B2's
  `wrap_derefs` in the Binary arm — B1 and B2 are MUTUALLY EXCLUSIVE; keeping
  both double-derefs).
- The deref-balance lives where W5 will prove it sound and where the bridge
  *independently* checks production's deref against the reference's.

**Feasibility note (from bootstrap-39 recon):** TypData ref-depth is bounded 0/1
(`TypData.Ref inner` where inner is Named/Int/…, never nested `Ref`), so the
BinOp-arm min-balance in `render_exp` is a small bounded change, structurally
identical to the existing `needs_nat_coercion` coercion the arm already does.

**Done when:**
- `render_exp` (tactus-core `lib.rs`) BinOp arm min-balance-derefs from operand
  types; its `expr_mirror_kernel_computes` companion lemmas re-verify green.
- `raw_exp`'s Binary arm reverts to bare-operand emission (drop B2's
  `wrap_derefs`; the helper can stay if unused-warnings are silenced, or be
  removed).
- The `runtime__impl__4__clone` in-gate bridge still closes (`1 passed, 0
  failed`) — now with the deref logic in the TCB, independently checked.
- e2e suite green; the bootstrap-38 fixture still 3/3 in-gate close.

**Blocked by / relationship:** DECISION MADE 2026-07-14 — **B2 kept for this
stage; this card stays `todo` as recorded tech-debt.** Danielle recommended B2
and delegated the call; the next instance (opus-w4a-tgtval, 2026-07-14) confirmed
B2 on three grounds (narrow gap, W5-not-done, core-olean-invalidation cost — see
bootstrap-39's "B1/B2 DECISION MADE" progress note). Do NOT start B1 opportunistically:
it is mutually exclusive with B2 (keeping both double-derefs) and requires
reverting the B2 commit (`6ea3030`) first. Pick this up only when W5 is being
built or Danielle fast-tracks it.

**Why this is a real (if narrow) soundness item, not cosmetics — for W5.** The
bridge's entire value is that `render_exp` (TCB) computes goals *independently* of
production, so a production bug is caught by disagreement. B2 breaks that for the
deref-count ONLY: both production and `raw_exp` peel via the same
`count_ref_decorations`, so a bug in that helper reproduces on both sides of
`goals_eq` and silent-passes. This is bounded — `count_ref_decorations` is a
small, auditable helper over TypData ref-depth (0/1) — but W5 cannot claim the
reference "independently validates" production's deref-lowering while B2 stands.
**W5 must either (a) adopt B1 first (move the balance into the TCB), or (b)
explicitly carve `count_ref_decorations` correctness out of its soundness claim as
an audited assumption.** Recording this so it isn't silently inherited.

## Progress
- (2026-07-14, opus-w4a-tgtval) Filed as the soundness follow-up to bootstrap-39.
  B2 landed there (validated at decide level). See bootstrap-39's "FIX BUILT +
  VALIDATED" section for the full B1/B2 analysis, the unsound-Var-sketch
  correction, and the local-model verdict.
- (2026-07-14, opus-w4a-tgtval, cont.) DECISION recorded: B2 kept for this stage,
  this card stays tracked tech-debt. Added the W5-ownership framing above so the
  common-mode gap is an explicit soundness obligation for the W5 loop, not a
  buried nicety.
- (2026-07-14, next-instance) **RECON — B1 is a smaller/lower-risk change than the
  card's caution implied. Findings (all line refs = `tactus-bootstrap/tactus-core/lib.rs`):**
  - **The TCB already has every primitive B1 needs.** BinOp arm is `render_exp`
    at `:890-894`; it already reads `type_of(*l)`/`type_of(*r)`. `deref_if(b, e)`
    (`:845`) wraps in exactly one `.deref` `FieldProj(_, deref_field()=0)` iff
    `b==1`; `needs_ref_deref(t)` (`:840`) = `1` iff `td_tag(t)==4` (TyRef). So the
    min-balance is `dl=needs_ref_deref(type_of(*l)); dr=…; m=min(dl,dr);
    l1=deref_if(dl-m, render_exp(*l)); r1=deref_if(dr-m, render_exp(*r))` — reusing
    existing helpers, structurally identical to the arm's existing coercion.
  - **Ref-depth is bounded 0/1** (`TypData::TyRef(inner)`, inner never nested Ref),
    so `dl-m, dr-m ∈ {0,1}` and `deref_if` (single-peel) is exact. If depth ever
    exceeded 1, production's `apply_deref_chain` would peel more than the TCB's
    single `deref_if` → the goals DIVERGE → bridge FAILS LOUD (a false-negative,
    never a silent pass). So the 0/1 assumption is safe-by-loudness; a recursive
    `deref_n` is the generalization if it ever surfaces (one sub-choice, below).
  - **The peel and the nat-coercion provably never interact.**
    `needs_nat_coercion(op, res)` (`:823`) = 1 iff `td_tag(op)==0 (TyInt)` AND
    `td_tag(res)==1 (TyNat)`. A ref operand is `td_tag==4`; peeled it is
    `deref_type(TyRef)=TyNamed`, `td_tag==3`; both ⟹ 0. And every op that can
    carry ref operands is a structural comparison (Bool result, `td_tag==2`) ⟹
    `needs_nat_coercion(_,Bool)==0` for ANY operand. So feeding peeled-or-unpeeled
    type to `needs_nat_coercion` is immaterial — the coercion is off in the entire
    ref-reachable region. Clean composition.
  - **Companion lemma is ADDITIVE-only — no existing case breaks.**
    `expr_mirror_kernel_computes` (`:1279`) is a `decide`-table of
    `expr_eq(render_exp(...), expected)==1/0`. Its BinOp cases A/B/D
    (`:1284-1346`) all use NON-ref operands → the min-balance is a no-op on them →
    they re-verify green untouched. B1 only ADDS a case: a `result:T == self:&Self`
    structural compare where `render_exp` now peels the ref operand itself, plus a
    mutation-kill (drop the deref → flips to 0) demonstrating the TCB independently
    computes the peel.
  - **B2 revert is minimal.** `6ea3030` added 44 lines to `sst_serialize.rs` only
    (the `wrap_derefs` fn + 6 lines in the `ExpX::Binary` arm calling it). Revert =
    drop those; the transcriber goes back to bare-operand emission.
  - **Net blast radius:** (1) ~8-line change to `render_exp`'s BinOp arm; (2) one
    additive companion case (pos + kill); (3) revert `6ea3030`'s `sst_serialize.rs`
    hunk; (4) **rebuild tactus-core oleans** (new fn shape → base hash changes →
    whole-crate reverify + `out/lib` re-emit); (5) re-run the in-gate bridge
    (bootstrap-38 fixture + `runtime__impl__4__clone`) to confirm `1 passed, 0
    failed` with the peel now in the TCB. Items 4-5 are the real cost — exactly
    what makes this "not opportunistic."
  - **One sub-choice inside B1** (my recommendation in parens): coercion-type fed
    to `needs_nat_coercion` after peel — use unpeeled `type_of(*l)` (immaterial per
    above; simplest, matches current arm) **(recommended)** vs. peeled type
    (defensive but unreachable-different). And peel primitive — `deref_if`
    single-peel given 0/1 depth **(recommended)** vs. a recursive `deref_n`
    (future-proof but unneeded now).
  - **Surfaced the B1-vs-keep-B2 fork to Danielle** (she offered to make exactly
    this call). Awaiting go/no-go before touching code, since B1 reverts the
    validated `6ea3030` and forces the olean rebuild — the prior instance
    deliberately deferred this.
  - **PEER REVIEW (Danielle's local model, port 8051):** independently confirmed
    all four claims above SOUND (implementation reuse, 0/1 fail-loud bound,
    peel/coercion non-interaction, additive-only companion) and agreed HOLD B1
    absent an explicit go ("silence ≠ consent" for reverting validated work +
    olean rebuild + overriding a recorded decision). This mirrors the
    two-independent-analyses pattern that produced B2's original diagnosis.
  - **⚠ SOUNDNESS-SCOPE NOTE for the eventual implementer (flagged by both me and
    the local model):** claim 3 (peel never interacts with nat-coercion) holds
    ONLY because every op that can carry a ref operand is a structural comparison
    (Bool result). A hypothetical future BinOp that takes a `TyRef` operand yet
    returns `TyNat` (e.g. a `ref_size`/`address_of`-style op) would break the
    non-interaction and require feeding the PEELED type to `needs_nat_coercion`.
    None such exist in the current structural-binop scope, but B1's companion
    lemma should either (a) assert the invariant "ref operand ⟹ Bool result" or
    (b) feed the peeled type defensively, so the scope assumption is checked, not
    silent. **Decision on (a) vs (b) is a small sub-fork for the implementer.**
  - **STATE: card left `todo` (NOT claimed).** The recon+blueprint above make B1
    a minutes-to-execute task once green-lit; nothing else should be done here
    without Danielle's go, since the first code step (revert `6ea3030`) is the
    irreversible one. Suggested execution order when green-lit: (1) change TCB
    `render_exp` BinOp arm + add the additive companion case → verify tactus-core
    green IN ISOLATION (cheap, no bridge, no B2 interaction — the crux check);
    (2) only then revert `6ea3030`; (3) rebuild oleans + re-run the in-gate bridge
    (bootstrap-38 fixture + `runtime__impl__4__clone`) → expect `1 passed, 0
    failed` with the peel now independently checked in the TCB. Ordering puts the
    irreversible revert AFTER the TCB peel is proven correct, so a surprise in
    step 1 leaves B2 intact.

## Writeup
_when done_
