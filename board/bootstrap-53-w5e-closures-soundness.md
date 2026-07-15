---
title: "W5e — reference-WP soundness, closures"
status: done
claimed_by: opus-w5e-closures
created: 2026-07-14T21:30:00Z
updated: 2026-07-15T05:10:00Z
---

## Description

Final W5 ladder statement rung (`DESIGN-W5-soundness.md` §4, W5e row).

- **W5e**: model closures in the operational semantics and prove the closure
  `wp_stm` handling sound.
- **W5f** (adequacy spine) has been **spun out to its own card, bootstrap-54**,
  now that W5a–e have all landed.

**Blocked by:** the rest of the W5 ladder (all done: bootstrap-49..52).

## Progress

- (2026-07-15, opus-w5e-closures) Claimed. Read the W5c/W5d core (probe24/25
  `execSafeF`/`wp_stm_sound`, an **iff TOTAL over all 10 StmData constructors,
  arbitrary frame telescope**), `DESIGN-W5-soundness.md`, the emitted
  `lib.StmData` mirror (confirmed: exactly 10 constructors — Assert/Assume/
  Assign/Call/DeadEnd/Ret/If/Loop/Skip/Seq, **NO closure arm**). **Key early
  finding:** like prophecy (W5d), closures must route through existing machinery.
- (2026-07-15, opus-w5e-closures) **Verified the model against the ACTUAL Verus
  source** (not first principles): an exec/proof closure `NonSpecClosure`
  (`ast.rs:1058`) lowers to exactly TWO SST statements (`ast_to_sst.rs:1964`):
  `ClosureInner{body}` — which `sst_to_air.rs:2566` compiles to
  **`StmtX::DeadEnd(body)`** — followed by `Assume(external_spec)`. The body
  (`exec_closure_body_stms`, `ast_to_sst.rs:3556`) is ordinary statements: assume
  each requires, body, then assert each ensures. So a closure ≈ **`Seq (DeadEnd
  body) (Assume ext)`** — both constructors already in the vocabulary, NO new arm.
  Spec closures (`ExprX::Closure`) → a pure `BndX::Lambda` opaque leaf, no new
  statement structure. Load-bearing emitted fact: `frame_after f (DeadEnd b) = f`
  (the DeadEnd quarantines the body's hyps from the continuation).
- (2026-07-15, opus-w5e-closures) **Consulted Danielle's local model** on the
  framing. It flagged the **"creation vs. invocation" quantification worry** (does
  the body get checked for only one param value; does relying on creation-time
  context make a "time bomb"?). Its param premise was **wrong for the reference**
  (params are ∀-bound by the outer `∀ st`), but its structural instinct sharpened
  the write-up: the creation-time-context reliance is sound precisely because
  Verus **forbids mutable capture** (`closures.rs::check_closure_well_formed`),
  freezing the environment — a spec-adequacy point, documented.
- (2026-07-15, opus-w5e-closures) **DONE — probe26 PASS, rc=0, ~3.0s, zero
  warnings.** `probe-w0/probe26_w5e_sem/` (`w5e_sem.lean` + `run.sh` + `REPORT.md`)
  on probe25's proven core. Adds `closure_creation_sound` (closure creation ↔ body
  obligation under enclosing `f`), `closure_deadend_isolates` (DeadEnd-wrapped
  body assumption UNGATES the continuation) vs `seq_assume_gates` (bare assume
  GATES it — the differ-witness), `closure_forwards_contract` (external-spec
  Assume forwards the contract), a ∀-params witness, and a non-vacuity witness.
  Axiom closure `[propext, Quot.sound]` on all six theorems. **Negative control**
  (manual): claiming the *gated* RHS for the DeadEnd-wrapped program fails
  elaboration (`unsolved goals`) ⇒ the isolation bites. Design doc §5 updated.

## Writeup

**W5e DONE (probe, `probe-w0/probe26_w5e_sem/`).** Closures need **no new
`StmData` arm**: a closure IS `Seq (DeadEnd body) (Assume external_spec)`, both
constructors already in the 10-constructor vocabulary — exactly the W5d
(prophecy) situation. rc=0, ~3.0s, zero warnings, axiom closure `[propext,
Quot.sound]` on all six theorems. Full detail in
`probe-w0/probe26_w5e_sem/REPORT.md`.

- **Model, grounded in the ACTUAL Verus encoding** (read off `verus/source/vir`):
  `NonSpecClosure` (`ast.rs:1058`) → `ClosureInner{body}` + `Assume(ext)`
  (`ast_to_sst.rs:1964`); `ClosureInner` compiles to `StmtX::DeadEnd(body)`
  (`sst_to_air.rs:2566`); the body (`exec_closure_body_stms`, `:3556`) is
  assume-requires / body / assert-ensures — pure W5a–c statements. Spec closures
  (`ExprX::Closure`) → a pure `BndX::Lambda` opaque leaf.
- **Why W5c already subsumes it:** the emitted `frame_after f (DeadEnd b) = f` +
  `wp_stm f (DeadEnd b) = wp_stm f b` mean the DeadEnd is isolating and its body's
  obligations are emitted under the enclosing frame. So the W5c `execSafeF` iff
  (total over StmData, arbitrary telescope) instantiates directly.
- **Main result `closure_creation_sound`:** the reference WP for `Seq (DeadEnd
  body) (Assume ext)` reduces EXACTLY to `execSafeF f body st` — the closure
  creation's obligation is precisely the body's obligation under the enclosing
  frame; the DeadEnd wrapper and the external-spec Assume add no obligation.
- **Isolation subtlety, discharged** (the local model's worry): the closure body's
  local assumption does NOT leak. `closure_deadend_isolates` (DeadEnd-wrapped
  assume → UNGATED continuation) vs `seq_assume_gates` (bare assume → GATED
  continuation) DIFFER — impossible if the DeadEnd failed to quarantine. Negative
  control (gated RHS on the DeadEnd program) fails elaboration.
- **Contract forwarding:** `closure_forwards_contract` — after the closure the
  continuation sees `hp ext` (the analog of W5d's resolve pin); the body
  obligation is delivered alongside.
- **Honest scope / caveats:** (1) **No new proof engine** — instantiations of the
  W5c iff at concrete programs+frames; the non-vacuous deltas are the explicit
  DeadEnd+Assume reading, the isolation witness (+ negative control), and the
  forwarding pin. (2) **∀-params via the outer `∀ st`** — closure params are fresh
  ids, NOT frame FBind binders; `∀ st` ∀-binds them (matching AIR fresh
  constants); the ∀-params witness makes it concrete. (3) **Creation-time-context
  reliance is sound by the frozen-environment invariant** (Verus forbids mutable
  capture, `closures.rs::check_closure_well_formed`) — a spec-adequacy point
  (§8.5), not a Val-level obligation. (4) Val-level, partial correctness; adequacy
  spine to user `Prop`s is W5f (bootstrap-54). (5) Probe-first — authoring in
  tactus-core deferred; when the mirror grows a closure serializer path, the W2
  `decide` bridge validates its DeadEnd+Assume shape and this probe is the
  soundness half.
- **NEXT = W5f (bootstrap-54): the adequacy spine.** With the whole StmData
  vocabulary + prophecy + closures sound at the Val level, W5f lifts it to the
  user-facing `Prop`s.
