# N3: the SST serializer — spec

**Date:** 2026-07-12
**Status:** spec'd, not started. Parent plan: `DESIGN-bootstrap.md` §12 (N3), §5 (W1).
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

Explicitly NOT captured in stage A (must be listed in the doc-comment):
masks, unwind spec, recommends, fuel/reveal state, decrease measures (exec
termination obligations), bv/compute/query asserts, closures,
break/continue, open-invariant blocks, `Air` passthrough. The vir-growth
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

To print the production goals as `GoalData`, the Wp assembly marks the LExpr
nodes IT constructs (binder telescope, hypothesis arrows, let-bindings) with a
provenance flag — one added field/mark on `lean_ast` nodes created in the
walker, nothing else changes. `goal_serialize` then walks the theorem
statement: marked node → structural `GoalData` constructor; unmarked subtree →
leaf (interned in the same table).

Why provenance instead of shape-directed parsing: a hypothesis can itself BE
an implication or a `∀` (user-written `a ==> b` in an ensures), so shape is
ambiguous at the spine tail. Provenance is not circular: the marks only record
where the production *claims* structure is; refWp computes structure
independently from the SST literal, and the `decide` equality is what
validates the claim. A mismark surfaces as a bridge failure, never as a silent
pass.

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

* `FuncCheckSst` field inventory: exact names/shapes to be transcribed into
  the contract table on first read of the struct (§3 is the intent, the code
  is the truth).
* Loop desugaring: does `check` present loops as `StmX::Loop` or already
  split (P7 saw loop-triple obligations)? The mirror follows whatever the
  snapshot point sees; if pre-split, `StmData::Loop` may be dead in practice
  and the tripwire note should say so.
* Call contract view: whether instantiated req/ens exps are directly present
  at the snapshot point or need the same instantiation the walker performs —
  if the latter, that instantiation becomes part of the trusted surface and
  must be flagged in the contract table.
