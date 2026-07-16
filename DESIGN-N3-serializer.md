# N3: the SST serializer — spec

**Date:** 2026-07-12
**Status:** N3a + N3b + N3c COMPLETE (2026-07-13). Serializer built, goal half
serialized, and acceptance (§7) validated on the rebuilt binary: all fixture +
w15_probe certs elaborate against tactus-core's olean with both `stm_size` and
`goal_count` decide probes kernel-computing; determinism byte-identical; golden
pins the full cert incl. goals; `sst_serialize.rs` 883 lines (tests split to
`sst_serialize_tests.rs`); e2e suite GREEN flag-off (550/0 — the real N3b
regression gate, since goal-shape capture runs unconditionally). Flag-on
(`VERUS_EXTRA_ARGS="--tactus-emit-cert"`) is verified verdict-neutral at scale
— 0/550 verdict changes; the full harness goes red flag-on (380/170) ONLY
because Verus's exact-output test matcher rejects the flag's emission
diagnostics (crate-end census `note: … certified M/N` + `not serialized`
eprintlns landing as `[unexpected json]`); every one of the 170 is
`expected Ok(()) but got Err(no errors)`, i.e. the fn still verifies. Making
emission test-quiet is W4-scoped (the flag goes default-on there) and tracked
in board `bootstrap-14`. §9 open-questions were answered at N3a
first-contact and re-confirmed by the live elaboration. `StmData::Call`
instantiation remains deferred (board `bootstrap-02b`). Next: N4 census + W2
refWp. Parent plan: `DESIGN-bootstrap.md` §12 (N3), §5 (W1).
**Role in the program:** the serializer is THE new trusted component of the R2
certificate architecture. Everything else the bootstrap adds is *checked*; this
is the one piece a skeptic must read. Its design goals are therefore inverted
from normal code: boring beats clever, 1:1 beats abstracted, explicit beats
inferred, and small enough to audit in one sitting (<1k lines, one file).

---

## 1. What it is

A Rust module `lean_verify/src/sst_serialize.rs` that, per verified fn, writes
a **certificate file** `<fn>.cert.lean` containing:

1. **The SST literal** — the fn's post-transform SST (body `Stm` tree + spec
   context), printed as a Lean term of the `tactus-core` mirror types
   (`StmData`/`LeafList`/…). This is the *input* snapshot the reference WP
   (W2) will recompute obligations from.
2. **The production-goal literal** — the goals the production emitter actually
   built for this fn, printed as a `tactus_core.GoalList` term. This is the
   *output* snapshot the reference WP's result will be compared against.
3. **The leaf table** — the id → rendered-Lean-text mapping both literals
   share (as structured comments in stage A; see §4).

W2's bridge then adds, per fn:
`example : refWp <sst literal> = <production-goal literal> := by decide` —
kernel-checked equality of statement structure. Stage A certifies the **WP
assembly** (statement structure: binder telescopes, hypothesis threading,
let-chains, obligation multiplicity/order), NOT expression rendering — leaves
are opaque and identical on both sides by construction, so they cancel.
Expression rendering joins the certificate in stage B (W6).

## 2. Snapshot point (faithfulness anchor #1)

Serialization hooks the inputs of `sst_to_lean::exec_fn_theorems_to_ast(krate,
fn_sst, check, broadcast_lemmas)` — the documented "single source of obligation
shape" that BOTH the island and package paths feed. The serializer reads
exactly the values that call receives, at that call site, after the same krate
transforms (`inline_spec::inline_marked_in_krate`, ambient emit tables
installed). Capturing anywhere earlier or later would certify a pipeline that
isn't the one that ran.

WP-routed proof fns (Verus body, no tactic block) flow through the same entry
and are covered identically. Tactic proof fns have no WP obligations and get
no certificate (their statements are covered by R1's package/Link machinery).

## 3. The faithfulness contract (anchor #2)

The module doc-comment of `sst_serialize.rs` MUST enumerate every field it
reads from `FunctionSst`/`FuncCheckSst` and every field it deliberately does
not, each with one line of why. That list — not the code — is what a reviewer
audits first. Initial capture set (stage A):

| Captured | Mirror | Note |
|---|---|---|
| params (name, typ) | binder leaves | typs are opaque typ-leaves |
| requires exps | leaf list | hypothesis order preserved |
| ensures exps + ens binder | leaf list + binder id | |
| body `Stm` tree | `StmData` | subset per tripwire (9/18 variants) |
| loop invariants/conds | `StmData::Loop` fields | |
| assign dests/rhs | `StmData::Assign` leaves | |
| call req/ens instantiations | `StmData::Call` leaf lists | contract view |
| typ params + instance constraints | `FnCtxData.typ_params` (binder id, kind leaf) | polymorphic telescopes (`∀ (A : Type) [Nonempty A]`) — REQUIRED for any real corpus; see `DESIGN-W2-refwp.md` §0 |

Explicitly NOT captured in stage A (must be listed in the doc-comment):
masks, unwind spec, recommends, fuel/reveal state, decrease measures (exec
termination obligations), bv/compute/query asserts, closures,
break/continue (and therefore `invariant_except_break` loops),
open-invariant blocks, `Air` passthrough, mutual/SCC exec fns, trait-method
obligations (dispatch/impl-subst shapes — sizeable in tgt; census will
quantify). The vir-growth
tripwire (`lean_verify/src/tests/bootstrap_coverage.rs`) pins the variant
split; extending coverage means updating BOTH the tripwire and this table.

**Fail-loud rule:** an in-scope fn containing an uncaptured construct gets a
per-fn diagnostic (`tactus: cert: <fn> not serialized: <construct>`), the
crate run continues, and the crate-end note reports `certified M/N fns`. One
mechanism serves both N3 acceptance and the N4 census (the census is just
this summary over tgt).

## 4. Leaves and the leaf table

* A **leaf** is any embedded expression, type, or binder name: rendered to
  text by the PRODUCTION renderer (`sst_exp_to_typed(..).into_slot(claim)`
  with the site's own `RenderCtx`), then interned: identical text ⇒ same id.
  Ids are assigned in first-appearance order (walk order is defined by this
  spec: params, requires, body pre-order, ensures) — two runs must produce
  byte-identical files (acceptance §7).
* Using the production renderer for leaves is deliberate, not a concession:
  it makes leaf content cancel on both sides of the bridge, isolating the
  stage-A claim to structure. It also means leaf bugs (e.g. the four fixed
  this week) are NOT caught by stage A — stated honestly in the artifact
  header and DESIGN-bootstrap §8's trust table.
* Stage A emits the table as structured comments (`-- leaf 7: ⟦Int.ofNat 0⟧`)
  for human audit; nothing in the bridge reads it. Stage B promotes leaves
  into mirrored expression data.

## 5. Goal-side serialization (N3b — the one production-code touch)

To print the production goals as `GoalData`, the Wp assembly records the
*structured spine* of each obligation (binder telescope, hypothesis arrows,
let-bindings, core leaf) as a `GoalShape`, captured at the walker's single
`OblCtx::wrap` site before the frames fold into the flat statement.
`goal_serialize` then turns each spine into a `GoalData` constructor chain,
interning every spine leaf into the same leaf table as the SST half.

Why provenance instead of shape-directed parsing: a hypothesis can itself BE
an implication or a `∀` (user-written `a ==> b` in an ensures), so shape is
ambiguous at the spine tail. The spine record is not circular: it only records
where the production *claims* structure is; refWp computes structure
independently from the SST literal, and the `decide` equality is what
validates the claim. A mismark surfaces as a bridge failure, never as a silent
pass.

**RESOLVED 2026-07-13 (N3b — mechanism):** the "provenance" is a structured
`GoalShape` side-record (`lean_ast::GoalShape`/`GoalSpine`), NOT a mark/flag on
the shared `lean_ast::Expr`. Two facts made this the right realization:
(1) the `GoalData` mirror is *already* the spine (`All`/`Imp`/`Let`/`Leaf`),
so a structured record maps 1:1 with no re-parse; (2) every WP obligation
statement is built at ONE choke point (`ObligationEmitter::emit_with_extras`),
fed by `emit_split`/`emit_with_closer`, where `(binders, remaining frames,
leaf)` are still separate. The walker accumulates a `Vec<Option<GoalShape>>`
in lockstep with its `Vec<Theorem>` (index-aligned; `None` = bit_vector/query
stage-A exclusion) and returns both in `ExecFnObligations`. This touches the
production emitter ONLY (the two `wrap` sites + the return type + the two
`generate.rs` hook calls), leaving `lean_ast::Expr`'s ~50 match arms and the
pretty-printer untouched — so byte-identical Lean output with the flag off is
guaranteed by construction. Faithfulness invariant worth a test: folding a
`GoalShape` back to an `Expr` reproduces the emitted `Theorem.goal`.

## 6. File format & plumbing

* Flag: `--tactus-emit-cert` (default off until W4). Files land beside the
  fn's island/pkg artifacts: `<TACTUS_LEAN_OUT>/<crate>/cert/<fn>.cert.lean`.
* Header: `import TactusCore` — the tactus-core defs olean, built once from
  `tactus-core/lib.rs` via crate-defs emission and content-addressed like the
  prelude (`~/.cache/tactus/tactus-core-<hash>/`). The vocabulary names in
  cert files are exactly the emitted names (e.g. `tactus_core.StmData.Assert`);
  no hand-maintained Lean vocabulary exists (N2's single-source rule).
* Per-obligation alignment: `GoalList` order = production theorem order, and
  each goal is preceded by a comment carrying the production theorem name
  (`_tactus_postcondition_..._stmt`) — O4's obligation pairing, by id.
* Determinism constraint: no HashMap iteration order anywhere in output paths
  (use insertion-ordered structures); no timestamps.
* **Vocabulary versioning:** cert files are only meaningful against the
  TactusCore build they were emitted for. The emitted `TactusCore.lean` is
  VENDORED at `tactus-core/emitted/TactusCore.lean` (regenerated by script,
  drift-checked by a unit test comparing against a fresh emission — same
  discipline as golden files), and every cert file records the vendored
  file's content hash in its header. Mismatch at bridge time = hard error,
  never a stale-pass. Changing tactus-core (N2.1 or refWp semantics)
  invalidates all outstanding certs by construction.

## 7. Acceptance (definition of done)

1. `bootstrap-fixture/lib.rs` + `w15_probe.rs` + `tactus-core/lib.rs`:
   **every** exec/WP-proof fn either serializes or is a documented stage-A
   exclusion (expect: the two bv fixture fns excluded, everything else in).
2. Every emitted cert file **elaborates** against the TactusCore olean
   (`lean` with LEAN_PATH), and one `#eval`/`decide` probe per file
   (`stm_size <literal> = <n>`) confirms the literal kernel-computes — this
   folds N5's smoke into N3's acceptance.
3. Two consecutive runs produce **byte-identical** cert files.
4. Suite stays 549+/0 with the flag off AND with the flag on (cert emission
   must not perturb verification).
5. Unit: golden-file test pinning one fixture fn's full cert text (drift in
   the serializer = visible diff, reviewed like the trusted code it is).
6. `sst_serialize.rs` under 1k lines including the contract doc-comment,
   plus `goal_serialize` (N3b) as a second, smaller unit.

## 8. Sequencing & estimates

* **N3a** — serializer core + emission plumbing + fail-loud census counters
  (no production-code changes beyond the hook call). ~1 session.
* **N3b** — provenance marks in the Wp assembly + `goal_serialize`. The only
  step that edits production emitter code; keep the diff reviewable alone.
  ~1 session.
* **N3c** — acceptance run (fixture + tactus-core), golden test, doc updates.
  Small; same session as N3b if it fits.
* Then **N4** (census over tgt = run N3a's summary on the big crate) and
  **W2** (refWp authored in tactus-core against the now-frozen literal shape).

## 9. Open questions (decide during N3a, record here)

**ANSWERED 2026-07-13 (N3a first contact — `source/vir/src/sst.rs` +
`sst_to_lean.rs::build_wp`):**

* `FuncCheckSst` field inventory (sst.rs:356): `reqs: Exps`,
  `post_condition: Arc<PostConditionSst>` (`dest: Option<VarIdent>`,
  `ens_exps: Exps`, `ens_spec_precondition_stms`, `kind`), `unwind: UnwindSst`,
  `body: Stm`, `local_decls: Arc<Vec<LocalDecl>>`,
  `local_decls_decreases_init: Stms`, `statics`. **The serializer transcribes
  raw `check.body`** (a single `Stm`) — the mut-ref rewrite and WpCtx build
  happen INSIDE `exec_fn_theorems_to_ast`, downstream of the snapshot, so they
  are not the serializer's input. `FnCtxData` reads: params/typ_params from
  `fn_sst.x` (`pars` filtered by `!is_synthetic_param`, `typ_params`), req
  leaves from `check.reqs`, ens leaves + ens-binder from `check.post_condition`.

* Loop desugaring: **NOT pre-split.** `StmX::Loop` arrives whole —
  `cond: Option<(Stm,Exp)>`, Tactus's `original_cond: Option<(Stm,Exp)>`,
  `invs: LoopInvs` (`LoopInv{at_entry, at_exit, inv}`), `decrease: Exps`,
  `modified_vars: Option<Arc<HavocSet>>`. `StmData::Loop` is LIVE. The
  init/maintain/use obligation TRIPLE is walker-synthesized (`build_wp_loop`),
  not distinct SST Assert nodes (confirms §5-Q3's P7 guess) — refWp will
  synthesize them identically from the Loop literal. Serializer recovers
  `cond`/`neg_cond` from `cond`-or-`original_cond`, loop-state binders from
  `modified_vars`. **CAVEAT found in N3a e2e (W2 must handle):** on the
  fixture's `sum_to`, `modified_vars` is `None` at the RAW `check.body`
  snapshot (the havoc set is populated by a later pass, not present
  pre-walker), so the emitted `Loop` literal has `binders = Nil` — the
  maintain/use telescope binders (i, acc) are absent. Faithful to the
  snapshot, but refWp will need the modified set: either consult a
  later-populated havoc source at the snapshot, or compute the modified set
  inside refWp from the loop body's assigns. Decide at W2.

* Call contract view: **the latter — instantiation IS part of the trusted
  surface.** `StmX::Call` at the snapshot carries only the callee `Fun`,
  `typ_args`, `args`, `dest: Option<Dest>` — NOT instantiated req/ens exps.
  `build_wp_call` performs the instantiation (callee lookup in `fn_map` + arg
  substitution). The serializer must do the same substitution to render the
  `Call{reqs, enss}` leaves, and this is flagged in the contract doc-comment as
  a trusted-surface item (the one non-transcription step). [N3a status: Call is
  captured STRUCTURALLY with placeholder-instantiation deferred — see writeup;
  the substitution helper is the sharpest remaining N3a/N3b edge.]

* Overflow-guard asserts: **present verbatim** as `StmX::Assert` at the
  snapshot (Verus's overflow pass precedes SST hand-off). No walker-injection to
  mirror. `AssertCompute` folds to `StmData::Assert` (walker dispatches them
  identically).
