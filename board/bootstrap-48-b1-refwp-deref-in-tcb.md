---
title: "B1 (soundness follow-up) — move the structural-binop deref-balance into the TCB render_exp (close bootstrap-39's common-mode gap)"
status: done
claimed_by: opus-bootstrap48-b1exec
created: 2026-07-14T17:00:00Z
updated: 2026-07-14T18:05:00Z
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

- (2026-07-14, opus-bootstrap48-b1exec) **GREEN-LIT by Danielle in session; EXECUTING.
  STEP 1 (the crux) DONE — TCB change verified GREEN IN ISOLATION.**
  - `render_exp`'s BinOp arm (`tactus-core/lib.rs:890`) now min-balance-derefs from
    the operand TypData: `dl=needs_ref_deref(type_of *l)`, `dr=…`, peel each by
    `if dl>dr {1} else {0}` / `if dr>dl {1} else {0}` (the 0/1 specialization of
    production's `dl-min(dl,dr)`; avoids nat subtraction so it reduces under
    `decide`). Chose the recon's recommended sub-forks: (a) `deref_if` single-peel
    (0/1 depth), (b) feed UNPEELED `type_of` to `needs_nat_coercion` — proven
    immaterial (a ref operand is tag 4, its peel `TyNamed` tag 3; coercion fires
    only on tag 0 `TyInt`, so it's 0 either way, AND every ref-carrying op is a
    Bool-result structural compare ⟹ coercion off across the whole ref region).
  - `expr_mirror_kernel_computes` (companion `decide` table) gained **4 additive
    cases**: (1) the real clone shape `result:TyNamed(5) == self:TyRef(5)` → RHS
    peeled one `.deref`, LHS bare [==1]; (2) kill: RHS peel dropped [==0]; (3)
    NEGATIVE CONTROL `&Self == &Self` (both depth 1) → min-balance m=1 → NEITHER
    peeled [==1] (this is exactly what an unsound blanket per-operand Var-deref
    would get wrong); (4) kill: one matched-depth operand over-peeled [==0].
  - **`verus --crate-type=lib --lean-backend --lean-all-proofs lib.rs` → 65 verified,
    0 errors** (`/tmp/b1-core-verify.log`; package gate: 50 modules, composition +
    axiom closures kernel-verified). Every EXISTING BinOp case (A/B/D, G6, G2/C
    ref-call) re-verified green untouched → confirms the min-balance is a genuine
    no-op on non-ref operands (additive-only, as the recon predicted). The crux
    check passed with B2 STILL PRESENT (tactus-core verify doesn't invoke the
    serializer, so it's independent of B2 — exactly why the recon ordered it first).
  - **Faithfulness cross-check:** read production `count_ref_decorations`
    (`expr_shared.rs:891`) — it counts REF decorations only (descends `Boxed`
    WITHOUT incrementing, line 902), matching the TCB's `needs_ref_deref` firing on
    tag 4 (`TyRef`) and 0 on tag 5 (`TyBox`). So the mirror is exact for the
    depth-0/1 scope and FAIL-LOUD beyond (TCB underpeels ⟹ goals diverge ⟹ bridge
    fails, never silent-pass).
  - Committed this verified TCB half as a checkpoint BEFORE the irreversible B2
    revert (recon's ordering: a surprise in step 1 leaves B2 intact). NEXT: revert
    `6ea3030`'s `sst_serialize.rs` hunk → rebuild verus binary → re-emit tactus-core
    `out/lib` (`--tactus-emit-module`) → re-run the in-gate bridge (expect `1
    passed, 0 failed` with the peel now independently checked in the TCB).

- (2026-07-14, opus-bootstrap48-b1exec, cont.) **STEPS 2–3 DONE; B1 VALIDATED AT
  THE DECIDE LEVEL WITH THE REAL BINARY OUTPUT. Full tgt in-gate run in flight.**
  - **B2 revert (step 2):** dropped `6ea3030`'s two hunks from `sst_serialize.rs`
    — the 5-line min-balance in the `ExpX::Binary` arm and the `wrap_derefs` fn.
    `git diff 6ea3030^ -- sst_serialize.rs` (code lines only) is EMPTY: the revert
    restored the exact pre-B2 code, differing only in a one-line B1 pointer comment.
    raw_exp now emits BARE operands; the peel lives solely in the TCB.
  - **verus binary rebuild:** fork vargo (`tactus-bootstrap/tools/vargo/…`) from
    `source/`, `vargo build --release` → verus/rust_verify rebuilt 17:40:22,
    **vstd 1530 verified, 0 errors** (`/tmp/b1-verus-rebuild.log`). B2 revert now
    compiled into the binary.
  - **tactus-core out/lib re-emit (step 3):** the earlier isolation verify used no
    `TACTUS_LEAN_OUT`, so it verified but didn't rewrite out/lib. Correct recipe
    (from bootstrap-23:405): `TACTUS_LEAN_OUT=$PWD/out ../source/target-verus/
    release/verus --crate-type=lib --lean-backend --lean-all-proofs lib.rs` from
    `tactus-core/` → **65 verified, 0 errors**; `TactusDefs_lib_exec__root.olean`
    refreshed 17:43 (618416→621056 bytes). Confirmed B1 in the emitted defs:
    `needs_ref_deref`/`deref_if` now appear in `TactusDefs_lib_exec__root.lean`'s
    `render_exp` (7 hits).
  - **⭐ DECIDE-LEVEL BRIDGE VALIDATION (the substance of "1 passed"):** bootstrap-39
    left the REAL bare-`Var` control bridge on disk at
    `/tmp/w4a-bs47b/lib/bridge/Bridge_runtime__impl__4__clone.lean`. Its sst is
    `BinOp Eq (Var 4 : TyNamed 5) (Var 0 : TyRef 5)` — bare, no `Deref` — which is
    EXACTLY what B1's binary now emits (B2 gone). Elaborated it against the FRESH
    B1 olean (`LEAN_PATH=tactus-core/out/lib:prelude`, Nix lean):
    `goals_eq (ref_wp ctx sst) goals = 1 := by decide` → **rc 0, CLOSES** (1223ms).
    Under the OLD olean this same file FAILED (bootstrap-39's recorded control) —
    a clean differential proving the `.deref` peel now lives in and is checked by
    the TCB `render_exp`. **Non-vacuity control:** flipping the expected value
    `1→0` errors (`decide proved … = 0 is false`, rc 1) — the decide genuinely
    evaluates `goals_eq` to 1. This is STRONGER than B2's original validation: the
    sst here is the binary's genuine output, not a hand-edited mock.
  - **Regression (bootstrap-25's designed post-olean-rebuild checks):**
    **probe13 (expr mutations) PASS ✓** (4 deep baselines close; all 4
    coercion-drop kills flip 1→0 — directly exercises the changed `render_exp`);
    **probe9 (bridge) ALL CLOSE ✓** (quad_exec/scope_shape/sum_to/swap_pair/
    tri_one/use_multiarg). So B1's min-balance is a proven no-op on the curated
    non-ref bridges.
  - **⚠ NOTE on the "bootstrap-38 fixture 3/3" done-criterion:** running the FULL
    `bootstrap-fixture/lib.rs` under `--tactus-bridge` errors on `tactus_auto
    failed for sum_to/find_square` + `vec_read` stmt-olean build — but these are
    the FIXTURE'S OWN proof-automation failures (pre-existing; the full fixture is
    not a clean full-package-check target). bootstrap-38's "3/3" was a CURATED
    SUBSET (add_capped/max_u64/double_exec + lemma_dbl), not the full lib.rs. Proof
    it's orthogonal to B1: probe9 shows `sum_to`'s BRIDGE closes fine. The curated
    subset temp-fixture wasn't preserved; probe9/13 are the equivalent (and
    stronger, olean-coupled) regression signal, and they pass.
  - **IN FLIGHT:** full tgt in-gate run (`runtime` module, cold, `--tactus-bridge`,
    recipe = bootstrap-39 run #2) launched (`/tmp/b1-tgt-ingate.log`); expect
    `1 obligation bridge-checked (1 passed, 0 failed)` — the headline done-criterion
    now with the peel independently checked in the TCB. Result recorded next.

- (2026-07-14, opus-bootstrap48-b1exec, FINAL) **DONE.** Two definitive results:
  - **Headline done-criterion — the FRESH B1-binary cert bridges CLEAN.** The
    cold tgt in-gate run (`--emit-lean --tactus-bridge --verify-module runtime`,
    exit 0) emitted `/tmp/b1-tgt-ingate/lib/cert/runtime__impl__4__clone.cert.lean`
    with the sst `BinOp Eq (Var 4 : TyNamed 5) (Var 0 : TyRef 5)` — BARE operand,
    B2 gone. (`--emit-lean` is codegen-only so it didn't run the in-process bridge;
    I ran the identical decide externally, the bootstrap-38-established equivalence.)
    Appended the exact in-gate line `goals_eq (ref_wp ctx sst) goals = 1 := by
    decide` and elaborated against the B1 olean → **rc 0, CLOSES** = `1 passed, 0
    failed`, now with the `.deref` peel derived and checked INDEPENDENTLY in the TCB.
  - **e2e suite: `551 passed; 0 failed` (152s, rc 0)** — the B2 revert regresses no
    test. (Debug rebuild of `lean_verify`/`rust_verify` was clean, warnings only.)

## Writeup

**B1 — structural-binop deref-balance moved into the TCB. DONE + validated
end-to-end.** Closes bootstrap-39's common-mode soundness gap: the bridge now
checks production's `&`-deref count against a reference computed INDEPENDENTLY in
the trusted `render_exp`, instead of both sides sharing production's
`count_ref_decorations` (B2).

**What changed (2 code sites + re-emitted oleans):**
1. `tactus-core/lib.rs:890` — `render_exp`'s `BinOp` arm now min-balance-derefs.
   `dl=needs_ref_deref(type_of *l)`, `dr=needs_ref_deref(type_of *r)`; peel left by
   `if dl>dr {1} else {0}`, right by `if dr>dl {1} else {0}` (the 0/1
   specialization of production's `dl-min(dl,dr)` monus — avoids nat subtraction so
   it reduces under `decide`). Then the existing nat-coercion, unchanged. The peel
   and coercion PROVABLY never co-fire (ref operand tag 4 / its peel `TyNamed` tag
   3 vs coercion-needs tag 0 `TyInt`; and every ref-carrying op is a Bool-result
   structural compare), so feeding the unpeeled `type_of` to `needs_nat_coercion`
   is immaterial.
2. `source/lean_verify/src/sst_serialize.rs` — reverted `6ea3030` (B2): dropped the
   `ExpX::Binary`-arm min-balance and the `wrap_derefs` fn. `raw_exp` emits BARE
   operands again. `git diff 6ea3030^` on code lines is empty (exact revert; only a
   one-line B1 pointer comment differs).
3. `tactus-core/out/lib/*` — re-emitted with the B1 binary so the reference oleans
   carry the new `render_exp` (`TactusDefs_lib_exec__root.olean` grew 618416→621056
   bytes; `needs_ref_deref`/`deref_if` now appear in its `render_exp`).

**Companion (`expr_mirror_kernel_computes`, additive-only):** 4 new `decide` cases
— the real clone shape `result:TyNamed == self:TyRef` peels the RHS [==1]; its
deref-drop kill [==0]; a `&Self == &Self` matched-depth NEGATIVE CONTROL that must
leave BOTH bare (m=1) [==1] (exactly what an unsound blanket per-operand deref
would break); and its over-peel kill [==0]. Every pre-existing BinOp case (A/B/D,
G6, G2/C) re-verified untouched, confirming the min-balance is a genuine no-op on
non-ref operands.

**Faithfulness:** production `count_ref_decorations` (`expr_shared.rs:891`) counts
REF decorations only (descends `Boxed` without incrementing), matching the TCB's
`needs_ref_deref` firing on tag 4 (`TyRef`) and 0 on tag 5 (`TyBox`). Exact for the
depth-0/1 scope; FAIL-LOUD beyond (if production could peel >1 where TypData holds
one `TyRef`, the TCB underpeels ⟹ `goals_eq` diverges ⟹ bridge fails, never
silent-pass). This fail-loud independence is the entire point of B1 over B2.

**Sub-fork decisions (from the recon's two open sub-choices):** (a) `deref_if`
single-peel given 0/1 depth — chosen (recursive `deref_n` unneeded; fail-loud if
depth ever >1); (b) feed UNPEELED type to `needs_nat_coercion` — chosen, proven
immaterial above. The soundness-scope caveat (a hypothetical future op with a
`TyRef` operand yet `TyNat` result) remains only hypothetical: no such op exists;
the `&Self==&Self` control + the non-interaction proof document the assumption. If
one is ever added, feed the peeled type — but note even then it's a no-op, since a
peeled ref is `TyNamed` (tag 3), never `TyInt` (tag 0).

**Validation ladder (all green):**
- tactus-core verify IN ISOLATION (B2 still present, serializer-independent): 65/0.
- verus binary rebuilt (B2 reverted): vstd 1530/0.
- tactus-core re-emit with B1: 65/0.
- decide-level bridge on the on-disk bare control (`/tmp/w4a-bs47b`): CLOSES against
  B1 olean (FAILED under old olean per bootstrap-39 = clean differential); flip
  `1→0` errors (non-vacuous).
- FRESH B1-binary tgt cert bridge: CLOSES (rc 0) = `1 passed, 0 failed`.
- probe13 (expr mutations) PASS; probe9 (bridge) ALL CLOSE.
- e2e suite 551/0.

**Assumptions / honest caveats:**
- The literal "bootstrap-38 fixture 3/3" was NOT reproduced with its exact curated
  temp-fixture (add_capped/max_u64/double_exec/lemma_dbl) — that file wasn't
  preserved, and the FULL `bootstrap-fixture/lib.rs` has PRE-EXISTING `tactus_auto`
  failures (`sum_to`/`find_square`) + a `vec_read` stmt-olean failure that are the
  fixture's own proof-automation, orthogonal to B1 (probe9 shows `sum_to`'s BRIDGE
  closes). Substituted by the equivalent, olean-coupled, MAINTAINED regression:
  probe9 ALL CLOSE + probe13 PASS + e2e's `test_exec_package_check_smoke` /
  `test_bridge_opt_in_verdict_neutral` (in the 551/0). This is a proportionate
  substitution, not a skipped check — but flagged in case a literal 3/3 is wanted.
- The tgt in-gate `1 passed` was validated via the EXTERNAL decide on the fresh
  cert (identical to what the in-gate `check_package` runs in-process), not by
  parsing an in-process "N passed, 0 failed" note — because the `--emit-lean`
  recipe is codegen-only. Same decide, same verdict.

**W5 impact:** the common-mode gap this card recorded is now CLOSED. W5's soundness
claim can state that `render_exp` validates production's deref-lowering
independently — no `count_ref_decorations`-correctness carve-out needed.
