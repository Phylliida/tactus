---
title: "N3b — goal-side serialization via Wp provenance marks (the one production touch)"
status: todo
claimed_by:
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T19:38:00Z
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

## Writeup

_when done: findings, how the code works, assumptions made_
