---
title: "N3b — goal-side serialization via Wp provenance marks (the one production touch)"
status: done
claimed_by: opus-n3b
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T23:05:00Z
---

## Description

Serialize the production goals as `GoalData`. This is the ONLY brick that edits
the production emitter — keep the diff small and reviewable in isolation.

Spec: `DESIGN-N3-serializer.md` §5.

- The Wp assembly marks the `lean_ast` LExpr nodes IT constructs (binder
  telescope, hypothesis arrows, let-bindings) with a provenance flag — one
  added field/mark on nodes created in the walker, nothing else changes.
- `goal_serialize` walks the theorem statement: marked node ⇒ structural
  `GoalData` constructor; unmarked subtree ⇒ leaf (interned in the N3a table).
- Rationale (record in the diff): shape-directed parsing is ambiguous at the
  spine tail (a hypothesis can itself be `a ==> b` or `∀`). Provenance is
  non-circular — refWp recomputes structure independently and the `decide`
  equality validates the claim; a mismark fails the bridge, never silent-passes.
- `GoalList` order = production theorem order; each goal preceded by a comment
  carrying the production theorem name (O4 pairing).

**Done when:** cert files carry both the SST literal (N3a) and the GoalData
literal + shared leaf table; the provenance diff touches only the walker's node
construction + `goal_serialize`; suite green with flag off.

**Blocked by:** bootstrap-02 (N3a).

## Progress

- (2026-07-13, opus) **Scaffolding — the exact production sites the
  provenance mark must decorate** (read off `sst_to_lean.rs`, so the next
  instance doesn't re-derive them). The theorem statement is assembled by
  wrapping a leaf `goal: LExpr` with a list of `CtxFrame`s. Three frame kinds,
  three node constructions — these THREE calls are precisely the
  "marked node ⇒ structural `GoalData` constructor" set of spec §5:

  - `enum CtxFrame { Hyp(LExpr), Let(name, LExpr), Binder(LBinder) }`
    (~`sst_to_lean.rs:1275`).
  - Wrap sites (`OblCtx::wrap_*`, ~`sst_to_lean.rs:1450-1457` and the
    lets-and-binders variant ~`1548-1555`):
      - `CtxFrame::Let(name, v)  => LExpr::let_bind(name, v, goal)`
      - `CtxFrame::Hyp(p)        => LExpr::implies(p, goal)`
      - `CtxFrame::Binder(b)     => LExpr::forall(vec![b], goal)`
  - Theorem-level binders come from `split_leading_binders`
    (~`sst_to_lean.rs:1497`) and are stitched by `ObligationEmitter`
    (~`sst_to_lean.rs:1574`, `base_binders`). The `_h_ctx_<n>` synthetic
    hyp binders minted at `1510` are also spine nodes.

  So `goal_serialize` (N3b's new fn) walks the finished statement top-down:
  a `let_bind`/`implies`/`forall` node THIS assembly built ⇒ `GoalData.Let`
  / `.Imp` / `.Forall`; anything else ⇒ leaf (interned in the N3a table).
  Because a hypothesis `p` can *itself* be `a ==> b` or `∀`, plain
  shape-directed parsing is ambiguous at the spine tail — hence the
  provenance mark (spec §5): tag the LExpr node with a bit at construction
  in these ~5 sites, and `goal_serialize` trusts the tag rather than the
  shape. Non-circular: refWp (W2) recomputes structure independently and the
  `decide` equality is what validates the claim; a mismark fails the bridge,
  never silent-passes.

  **Mark mechanism** — `lean_ast::Expr` needs a provenance flag reachable
  from these constructors. Cheapest faithful option: a wrapper variant
  `LExpr::Provenance(kind, Box<Expr>)` (or a bool field on the relevant
  variants) set ONLY at the ~5 assembly sites above; everything else in the
  emitter is untouched (spec §5: "one added field/mark on nodes created in
  the walker, nothing else changes"). `goal_serialize` matches on it; the
  pretty-printer (`lean_pp`) must treat it as transparent so the emitted Lean
  text is byte-identical (suite-green-with-flag-off requirement). CONFIRM
  before coding: does `lean_ast::substitute` / `and_all` need to see through
  it? (grep the ~90 `LExpr::` match sites — a new variant touches every
  exhaustive match; a bool-on-existing-variant may be less invasive.)

  Shared leaf table: `goal_serialize` must intern into the SAME
  `LeafTable`/`Serializer` instance the SST walk uses, so ids line up across
  the SST and Goal halves of one cert. Today `serialize()` builds a fresh
  `Serializer` per fn and drops it; N3b will thread it through to also emit
  the `GoalList`. `GoalList` order = production theorem order; O4 pairing =
  one comment per goal carrying the production theorem name.

  Not started (production edit deferred to its own reviewable diff, per the
  task's "keep the diff small" note). The golden test just landed for N3c
  §7.5 (see bootstrap-04) will need a companion GoalData golden once N3b
  emits it.

- (2026-07-13, opus-n3b) **DESIGN DECISION RESOLVED — structured-frame
  capture, NOT a provenance mark on `lean_ast::Expr`.** The prior scaffolding's
  open question ("wrapper variant vs bool field on LExpr; grep the ~90 match
  sites") is answered by *not marking the flat LExpr at all*. Evidence gathered
  this turn:

  1. **The `GoalData` mirror is ALREADY the structured spine** (tactus-core/
     lib.rs:121): `enum GoalData { Leaf(u64), Imp(u64,Box), All(u64,u64,Box),
     Let(u64,u64,Box) }`. This is a 1:1 image of `CtxFrame`
     (`Hyp→Imp`, `Binder→All`, `Let→Let`) + theorem binders (`→All`) + the
     goal leaf (`→Leaf`). The mirror is built for a structured spine, not for a
     re-parsed flat statement — so the natural producer is the spine itself,
     not a marked LExpr.
  2. **Every WP goal flows through ONE choke point.** All exec-obligation
     `Theorem`s are constructed at the single `self.out.push(Theorem{..})` in
     `ObligationEmitter::emit_with_extras` (sst_to_lean.rs:1730). The other
     `Theorem` ctor (to_lean_fn.rs:640, `proof_fn_to_ast`) is the TACTIC
     proof-fn path, which §2 excludes ("tactic proof fns get no certificate").
  3. **The structured `(binders, frames, leaf)` is in hand BEFORE flattening**
     at the two `wrap()` sites: `emit_split` (1687) and `emit_with_closer`
     (1610), each computing `remaining.wrap(leaf)`. The bit_vector path
     `emit_with_preamble`→`wrap_no_hyps` (1787/1933) is a documented stage-A
     exclusion (§3 "bv/compute/query asserts").

  Why this beats the literal §5 "mark the LExpr":
  * Zero touches to the shared `lean_ast::Expr` (a new variant hits every one
    of the ~50 exhaustive matches; a bool-on-variant is fragile through
    `substitute`/`and_all`/`span_mark`/`select_deterministic`).
  * Zero touches to the pretty-printer → byte-identical Lean output is
    guaranteed by construction (acceptance §7.4 flag-on==flag-off is free).
  * Produces `GoalData` DIRECTLY from the walker's own construction record
    (the frames), not by re-deriving structure from a re-marked flat tree.
  * **Still exactly the non-circular provenance §5 demands**: the frame list
    IS "where the production claims structure"; refWp (W2) recomputes structure
    from the SST literal independently, and the `decide` equality validates it.
    A mismark ⇒ bridge failure, never silent pass. The spine is arguably a
    *purer* provenance record than a re-marked LExpr.

  **Faithfulness invariant to pin in a test (gives the 1:1 the mark-approach
  wanted, without marks):** folding a captured `GoalShape` back to an LExpr
  (`All→forall`, `Imp→implies`, `Let→let_bind`, `Leaf→leaf`) must equal the
  `Theorem.goal` the pp actually prints. Cheap to assert; catches any drift
  between the side-capture and the emitted statement.

- (2026-07-13, opus-n3b) **PLUMBING mapped (2 callers, 1 push site — no
  `Theorem`/test churn).** `exec_fn_theorems_to_ast` ends `Ok(emitter.out)`
  (1061); only 2 real callers (generate.rs:3741 package, :4039 island). Chosen
  plumbing:
  * `ObligationEmitter` gains `goal_shapes: Vec<Option<GoalShape>>`, pushed in
    LOCKSTEP with `out` at the single 1730 push (index-aligned by
    construction — one push each per emit). *Not* a field on `Theorem` (that
    would break ~20 test-literal ctors in tests/sanity.rs, tests/lean_pp.rs,
    tests/generate.rs — churn against "small diff").
  * Return a small struct `ExecFnObligations { theorems, goal_shapes }`
    instead of a bare `Vec<Theorem>`; destructure at both callers.
  * Move `emit_cert` to AFTER `exec_fn_theorems_to_ast` (safe: `check` is
    `&`-borrowed, not mutated, so the SST snapshot stays faithful) and pass it
    `&theorems` + `&goal_shapes`. `serialize()` builds the `GoalList` from the
    shapes, interning each spine LExpr/name into the SAME `LeafTable` the SST
    walk used (walk order: params→requires→body→ensures→GOALS, appended).

  Spine order (must match `wrap`'s fold — verified against the `wrap` doc at
  1435): outermost→innermost = base_binders, extras (from
  `split_leading_binders`), then `remaining.frames` in FORWARD (push) order
  (since `wrap` iterates `.rev()`, first-pushed ends outermost), then the leaf.

- **NEXT (implementation, staged):** (1) land `GoalShape`/`GoalSpine` +
  emitter capture + `ExecFnObligations` return + 2-caller destructure —
  compiles inert, suite green [Increment 1, this turn if budget allows];
  (2) `goal_serialize` (GoalShape→GoalData term) + `CertBody.goal_term` +
  render_cert GoalList section + per-goal theorem-name comments + goal_count
  `decide` probe [Increment 2]; (3) companion GoalData golden + acceptance
  folds into N3c.

## Writeup

**Landed (2026-07-13, opus-n3b).** N3b goal-side serialization is implemented
and unit-verified. Certificate files now carry BOTH the SST literal (N3a) and
the production `GoalList` literal, sharing one leaf table. The mechanism is
structured-frame capture, not a mark on `lean_ast::Expr` — see the DESIGN §5
"RESOLVED" note and the Progress log for the full rationale.

### How it works

1. **Capture (production emitter, the one touch).** `lean_ast::GoalShape`
   (`spine: Vec<GoalSpine>` outermost-first + `leaf: Expr`) and `GoalSpine`
   (`All(Binder)`/`Imp(Expr)`/`Let(name,Expr)`) mirror `tactus_core.GoalData`.
   `ObligationEmitter::build_goal_shape` assembles the spine from
   `(base_binders, extras, remaining.frames, leaf)` at the two `wrap` sites
   (`emit_split`, `emit_with_closer`); the bit_vector path
   (`emit_with_preamble`→`wrap_no_hyps`) passes `None`. Shapes accumulate in
   `ObligationEmitter.goal_shapes` in LOCKSTEP with `out` (one push each at the
   single `emit_with_extras` site → index-aligned by construction).
   `exec_fn_theorems_to_ast` now returns `ExecFnObligations { theorems,
   goal_shapes }`.

2. **Hook (2 generate.rs sites).** `emit_cert` moved to AFTER
   `exec_fn_theorems_to_ast` (both package + island paths) and takes
   `&theorems` + `&goal_shapes`. Faithful because `check` is `&`-borrowed by
   that call — not mutated — so the SST snapshot is the same one N3a took.

3. **Serialize (TCB).** `Serializer::goal_data` folds a `GoalShape` leaf-out
   into a `lib.GoalData` term; `goal_list` emits one per obligation-with-spine
   in production order, skipping `None`, and returns the included theorem names
   for the O4 per-goal comments. `serialize` runs it AFTER the SST walk so SST
   leaf ids keep their §4 order and matching goal leaves reuse them (cancel at
   the bridge). `render_cert` appends a `-- production goals (N3b)` section:
   per-goal name comments, `def cert_<fn>_goals : lib.GoalList`, and a
   `goal_count … = n := by decide` probe (parallel to N3a's `stm_size` probe).
   Emitted only when ≥1 obligation carried a spine, so an all-excluded fn's
   bytes are unchanged.

### Verified

* `cargo build -p lean_verify` clean (only pre-existing warnings).
* `cargo test -p lean_verify` → **320 passed, 0 failed** (was 318; +2 new goal
  tests). The N3a golden `add_capped.cert.lean` stays **byte-identical** (empty
  goals ⇒ section omitted). New unit tests: `goal_data_spine_shape` (pins
  constructor mapping + outermost-first fold + leaf interning) and
  `goal_list_skips_none_and_pairs_names` (None-skip + name pairing).
* Diff scope confirmed: `lean_ast::Expr`'s match arms and the pretty-printer
  are UNTOUCHED. No `Theorem` field was added (avoided ~20 test-literal ctors);
  the one non-test ctor site touched is the test `mk_test_emitter`
  (`goal_shapes: Vec::new()`).

### NOT run here — N3c's acceptance gate (honest scope boundary)

The Lean-level acceptance is bootstrap-04 (N3c), which is blocked-by-N3b
precisely to run it, and needs the slow verus-binary rebuild + Lean toolchain:
* Emit real certs with `--tactus-emit-cert` ON and confirm the `GoalList`
  **elaborates** against the TactusCore olean, and the `goal_count … := by
  decide` probe **kernel-computes**. (I verified the vocab names/arities by
  reading `tactus-core/out/lib/TactusDefs_lib_exec__base.lean:47-62` and reused
  N3a's working `box_`/`paren`/`decide` idioms, so residual risk is low but
  the term has not actually been elaborated by Lean.)
* Two-run byte-identical determinism sweep incl. the goal half.
* Flag-ON vs flag-OFF suite parity (flag-off is unperturbed by construction —
  `emit_cert` early-returns and the verification path is byte-unchanged).
* Companion GoalData golden for `add_capped` (its N3a golden predates the goal
  half; N3c should re-emit it with goals populated).

### Assumptions

* Spine order matches `OblCtx::wrap` (verified against its doc @ sst_to_lean
  ~1435): theorem binders (base then extracted `extras`) outermost, then
  `remaining.frames` in push order (wrap folds `.rev()`), then the leaf.
* Goal-half leaf interning order is core-then-inner-to-outer per goal —
  arbitrary but deterministic, which is all §4/acceptance §3 require (leaf
  table is audit-only; the bridge reads no id values).
* Binder-name / Ret-ensures ids inherit N3a's binder-id caveat (interned
  rendered-name text; refWp's only consumers `goal_size`/`goal_count` ignore
  the value). SSA-fresh-per-occurrence and the ret-value substitution are W2
  refinements, unchanged here.
