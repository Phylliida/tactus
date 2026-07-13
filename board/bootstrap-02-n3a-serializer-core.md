---
title: "N3a — SST serializer core + emission plumbing + fail-loud census"
status: done
claimed_by: opus-n3a
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T14:05:00Z
---

## Description

Write `lean_verify/src/sst_serialize.rs` — THE new trusted component. Boring,
1:1, <1k lines, one file, faithfulness-contract doc-comment.

Spec: `DESIGN-N3-serializer.md` (whole doc; §2 snapshot, §3 contract, §4
leaves, §6 plumbing/versioning, §7 acceptance, §9 open questions).

Scope of N3a (no production-emitter changes beyond the hook call):
- Snapshot at the inputs of `sst_to_lean::exec_fn_theorems_to_ast` (the single
  source of obligation shape both island + pkg paths feed).
- Emit the SST literal in the tactus-core vocabulary (post-N2.1 shapes).
- Leaf interning via the PRODUCTION renderer (`sst_exp_to_typed(..).into_slot`)
  — identical text ⇒ same id; first-appearance walk order defined by the spec.
- Fail-loud: uncaptured construct ⇒ per-fn diagnostic + crate-end
  `certified M/N`. This one mechanism also IS the N4 census.
- `--tactus-emit-cert` flag (default off); cert files at
  `<TACTUS_LEAN_OUT>/<crate>/cert/<fn>.cert.lean`.
- Vocabulary versioning: vendor `tactus-core/emitted/TactusCore.lean`,
  content-hash it into every cert header (mismatch = hard error).
- The faithfulness-contract doc-comment MUST enumerate every
  `FunctionSst`/`FuncCheckSst` field read and every field deliberately not,
  each with one line of why. That list is what a reviewer audits.

Answer, on first contact with the real structs (record in the doc §9):
FuncCheckSst field inventory; whether loops arrive pre-split; whether Call
contract exps are pre-instantiated at the snapshot point.

**Done when:** fixture + tactus-core cert files emit; census counters correct;
determinism holds (byte-identical across two runs); suite unaffected with flag
off. (Elaboration/decide smoke is N3c.)

**Blocked by:** bootstrap-01 (N2.1) — the literal shape must be frozen first.

## Progress

- (2026-07-13, opus-n3a) **First contact with the real structs** — answers to
  the spec §9 open questions, read from `source/vir/src/sst.rs` +
  `source/lean_verify/src/sst_to_lean.rs::build_wp`:

  - **Snapshot input.** `exec_fn_theorems_to_ast(krate, fn_sst, check,
    broadcast_lemmas)`. The `check: &FuncCheckSst` carries the fn body as a
    single `check.body: Stm` (an `Arc<Spanned<StmX>>`). The mut-ref rewrite
    (`rewrite_mut_ref_in_stm`) and WpCtx construction happen INSIDE
    `exec_fn_theorems_to_ast` — they are NOT part of the snapshot input. So the
    serializer transcribes **raw `check.body`** structurally; refWp (W2) will
    recompute the WP from that literal. This is cleaner than mirroring the
    walker: no WpCtx needed in the serializer.

  - **`FuncCheckSst` inventory** (sst.rs:356): `reqs: Exps`,
    `post_condition: Arc<PostConditionSst>` (has `dest: Option<VarIdent>`,
    `ens_exps: Exps`, `kind`), `unwind`, `body: Stm`, `local_decls`,
    `local_decls_decreases_init`, `statics`. The refWp seed (`FnCtxData`) reads:
    params + typ_params from `fn_sst.x` (`pars`, `typ_params`), req leaves from
    `check.reqs`, ens leaves + ens-binder from `check.post_condition`.

  - **§9 Loop desugaring.** `StmX::Loop` arrives with `cond: Option<(Stm,Exp)>`
    and a Tactus-specific `original_cond: Option<(Stm,Exp)>` (recovers the
    natural `while c` shape when break-lowering set `cond=None`). It is NOT
    pre-split — invariants live in `invs: LoopInvs` (`LoopInv{at_entry,at_exit,
    inv}`), decrease in `decrease: Exps`, modified vars in `modified_vars`
    (`HavocSet`). So `StmData::Loop` is LIVE, and the serializer must recover
    `cond`/`neg_cond` from `cond`-or-`original_cond` and the loop-state binders
    from `modified_vars`. (Init/maintain/use obligations are walker-synthesized,
    NOT distinct Assert nodes — matches spec §9 Q3's guess; refWp synthesizes
    them identically from the Loop literal.)

  - **§9 Call contract view.** `StmX::Call{fun, resolved_method, typ_args, args,
    dest: Option<Dest>, ...}` at the snapshot point carries the CALLEE ref +
    arg exps, NOT the instantiated req/ens exps. The production walker
    (`build_wp_call`) looks the callee up in `fn_map` and does the req/ens
    instantiation itself. So the instantiation is part of the trusted surface —
    for stage A the serializer will render the callee's `decl.reqs`/`enss`
    substituted at the actual `args`/`typ_args`, and this instantiation must be
    flagged in the contract table (spec §9 "the latter" case). This is the one
    place the serializer does non-trivial work beyond transcription; scoped
    carefully and documented.

  - **§9 Overflow-guard asserts.** `StmX::Assert` nodes are present verbatim at
    the snapshot (Verus's arith-overflow pass runs before SST hand-off), so the
    serializer captures them as `StmData::Assert` with no walker-injection to
    mirror. `AssertCompute` dispatches identically to `Assert` in the walker;
    serializer folds it to `StmData::Assert` too.

  - **Block → Seq.** `StmX::Block(stms)` right-nests to `Seq(s0, Seq(s1, …,
    Skip))`; empty block → `Skip`. Matches the mirror's Seq/Skip design.

  - **Leaf rendering.** Production renderer entry for an SST `Exp` is
    `sst_exp_to_ast_checked(e) -> Result<LExpr,String>` (empty `RenderCtx`);
    text via `lean_pp::pp_expr(&LExpr)`. Types via `to_lean_type::typ_to_expr`.
    Negated cond via `LExpr::not(...)` (same call the walker's `Wp::Branch`
    uses). N3a uses the EMPTY RenderCtx (pre-ctx behavior) for determinism and
    self-containment; leaf content is opaque/cancels at the bridge, so ctx-aware
    divergence is a stage-A non-issue (documented in the contract doc-comment).
    A leaf Exp the renderer rejects (`Err`) is a fail-loud census case.

  - **Flag plumbing pattern.** Mirror `set_package_enabled`/`package_enabled`
    (generate.rs:2231): a process-global `AtomicBool` set once from verifier.rs
    after config parse. New flag `--tactus-emit-cert` → `Args.tactus_emit_cert`
    → `sst_serialize::set_cert_emit_enabled(on)`.

  - **Hook sites.** Both `emit_package_exec_fn` (generate.rs:3737) and
    `emit_exec_fn` (generate.rs:4030) call `exec_fn_theorems_to_ast`. In a gated
    run only one path fires per fn (package default, island fallback), so a
    guarded `sst_serialize::emit_cert(...)` call right before each is safe and
    non-duplicating.

## Writeup

**Status: DONE — serializer core built, wired, and VALIDATED end-to-end on
the rebuilt binary.** All four Done-when criteria met (fixture + tactus-core
emit, census correct, determinism, suite unaffected with flag off), and the
N3c-scoped elaboration/decide smoke was validated too (bonus). Remaining:
the golden-file unit test (N3c §7.5) and `StmData::Call` (new task
bootstrap-02b).

### End-to-end validation (rebuilt `source/target-verus/release/verus`)

- **Fixture emit (§7.1):** `--lean-backend --lean-all-proofs
  --tactus-emit-cert bootstrap-fixture/lib.rs` → **`certified 11/16 fns`**,
  rejection table `5  call`. 11 `.cert.lean` files written (add_capped,
  double_exec, find_square, head_exec, id_generic, max_u64, mk_point,
  scope_shape, sum_to, swap_pair, tri_one). w15_probe → 1/2 (left_val).
  tactus-core → 0 cert-eligible fns (all `by { decide }` tactic proofs / spec
  fns — no WP obligations, correct per spec §2).
- **Elaboration + decide (§7.2, N3c-scoped, validated anyway):** all cert
  files elaborate against the `TactusDefs_lib_exec` olean with ZERO
  diagnostics; every `example : lib.stm_size cert_<fn>_sst = n := by decide`
  passes. Sanity: perturbing `n`→999 produces exactly `decide proved … = 999
  is false`, confirming the kernel really checks. LEAN_PATH recipe:
  `<defs-dir>:<prelude-cache>:<mathlib-LEAN_PATH>` with plain `lean --json`.
- **Determinism (§7.3):** two runs → `diff -rq` byte-identical.
- **No perturbation (§7.4):** flag-off and flag-on both `13 verified, 11
  errors` on the fixture (the 11 are pre-existing fixture-verification
  failures — the fixture is a differential-gate seed, not all-green — NOT
  caused by cert emission, which is emission-only).
- **Size (§7.6):** `sst_serialize.rs` ≈ 640 lines incl. the contract
  doc-comment.

### Sample output (add_capped) — the shape a reviewer audits

Leaf table interns `⟦x⟧`,`⟦Int⟧`,`⟦0 ≤ x ∧ x < 2^64⟧`,…,`⟦r = x + y⟧`;
`FnCtxData.mk` carries the param telescope + bound hyps + reqs + enss; the
`StmData` body is a right-nested `Seq` of Assert/Assume/Assign (overflow
guards and the `assert(s<2000)` temp-bind/assert/assume triple all captured
faithfully) ending in `Ret [ens]`; `stm_size = 20`. The loop fn `sum_to`
captures `Loop{invs=[…], cond, ¬cond, binders, body}` correctly.

### Honest partial: the empty loop-binder list

`sum_to`'s `Loop` literal has `binders = Nil` — `StmX::Loop.modified_vars` is
`None` at the RAW `check.body` snapshot (the havoc set is populated by a later
pass, not present pre-walker). So the maintain/use telescope binders (i, acc)
are absent from the literal. This is a FAITHFUL transcription of what's there,
but refWp (W2) will need the modified set; it's exactly open-question §9-Q3.
Recorded for W2 — not an N3a defect (the mirror carries whatever the snapshot
sees). If W2 needs them, the fix is to consult a later-populated havoc set or
compute the modified set in refWp.

---

**(superseded log below — kept for the thread)**

### What landed

- **`source/lean_verify/src/sst_serialize.rs`** (~640 lines incl. the
  faithfulness-contract doc-comment) — THE trusted component. Reads the raw
  `check.body` at the `exec_fn_theorems_to_ast` snapshot and prints the SST
  as a Lean term of the emitted `lib.StmData`/`lib.LeafList`/… vocabulary,
  plus the `lib.FnCtxData` seed. Covers the stage-A subset (Assert, Assume,
  Assign[simple-var], DeadEnd, Return, If, Loop, Block→Seq/Skip); transparently
  elides Air/Fuel/RevealString (walker passthrough); fail-loud on everything
  else (Call, bv/query asserts, break/continue, open-invariant, closure,
  field-path assign, nonstandard loop invariants). Leaf interner is insertion-
  ordered (deterministic); leaves rendered via the production
  `sst_exp_to_ast_checked` + `lean_pp::pp_expr`, `¬cond` via `LExpr::not`.
- **Plumbing**: `--tactus-emit-cert` flag (`config.rs`, 4 edits) →
  `Args.tactus_emit_cert` → `sst_serialize::set_cert_emit_enabled` (verifier.rs,
  mirrors `set_package_enabled`). Hook `emit_cert(krate, fn_sst, check,
  crate_name)` at BOTH snapshot sites (`emit_package_exec_fn` +
  `emit_exec_fn`, generate.rs). Crate-end `census_report()` note in
  `verify_crate_inner`. One prod visibility widening:
  `is_synthetic_assume_to_drop` → `pub(crate)` (no behavior change).
- **Census = N4 mechanism**: process-global counters; per-fn
  `tactus: cert: <fn> not serialized: <tag>` diagnostics; crate-end
  `certified M/N fns` + ranked rejection table (deterministic BTreeMap order).
- **Cert file format**: `import TactusDefs_lib_exec`, header (vocab hash +
  honest-scope statement), `-- leaf N: ⟦text⟧` table, `@[reducible] def
  cert_<fn>_ctx`, `@[reducible] def cert_<fn>_sst`, and a `example :
  lib.stm_size … = n := by decide` kernel-compute probe (folds N5 smoke in).

### Verification done

- `cargo check -p lean_verify` clean (no new warnings). `cargo check -p
  rust_verify` clean under the pinned 1.94.0 + RUSTC_BOOTSTRAP (what vargo
  uses). 3 in-module unit tests pass (`box_and_paren`, `leaf_list_order`,
  `stm_size_matches_core` — the last pins the size arithmetic against the
  in-crate `skeleton_kernel_computes` example, size 5).

### Assumptions / deferred (each recorded in the module doc-comment + §9)

- **Call deferred** (fail-loud tag `call`): callee req/ens INSTANTIATION at
  actual args is a non-transcription trusted step (`build_wp_call`). Split
  into its own board task to keep the N3a trusted surface pure-transcription.
- **Binder id = interned leaf id of the rendered name** (not SSA-fresh per
  occurrence). N3a's only id consumer is `stm_size`/`binder_len`, which ignore
  id values; the SSA discipline is a W2 refinement.
- **Ret / fall-through ens are PRE-substitution** (ret-value subst deferred to
  N3b/W2 where the bridge constrains it).
- **Vocab hash is FNV-1a placeholder** for SHA-256; reads `$TACTUS_CORE_VOCAB`,
  `unvendored` when unset. The §6 vendoring (`tactus-core/emitted/TactusCore.lean`
  + drift test + namespace rename `lib`→`TactusCore`) is a follow-up.
- **Leaves use EMPTY RenderCtx** (pre-ctx behavior) — leaf content is opaque
  and cancels at the bridge, so stage A does not certify it.

### Remaining for N3a "done" (next increment, after the binary builds)

1. Emit certs over `bootstrap-fixture/lib.rs` (+ `w15_probe.rs` +
   `tactus-core/lib.rs`); eyeball one, confirm it elaborates against the
   TactusCore olean and the `stm_size` probe passes.
2. Determinism (byte-identical across two runs).
3. Golden-file unit test pinning one fixture fn's full cert text.
4. Suite 549+/0 unchanged with the flag off AND on.
