---
title: "A6-short — assert-forall loud census rejection (skolem binders unmodeled at stage A)"
status: done
claimed_by: fable-endgame-A6
created: 2026-07-24T19:00:00Z
updated: 2026-07-24T19:00:00Z
---

## Description

Endgame A6 short form (`DESIGN-bootstrap-endgame.md` §3, required by
P2): the two tgt `lemma_runtime_word_view_*` fns assert
`forall |k: int| …` — production ∀-binds the referenced AssertByVar
skolems in the DeadEnd scope's goal telescope (`Wp::Scope.scope_vars`,
`collect_assert_by_vars`); stage A has no quantifier-binder arm, so
the serializer previously emitted NON-BRIDGING certs (the worst of
both worlds: not fixed, not tagged). Detection must use production's
own collection logic — never a heuristic.

The REAL fix (the stage-A `∀ (k : Int)` telescope binder arm) is
planned post-flip work, endgame table row 11b — this tag is b68
sequencing scaffolding only, never permanent (Q4 resolution).

## Progress

- (2026-07-24, fable-endgame-A6) Detection shared with production:
  `collect_assert_by_vars` split into `collect_assert_by_vars_in`
  (takes the `LocalDeclKind::AssertByVar` map; production wrapper
  keeps `WpCtx`); the serializer builds the SAME map from
  `check.local_decls` and its `StmX::DeadEnd` arm rejects
  (`assert-forall` tag) when the scope references any skolem —
  exactly when production would ∀-bind.

- (2026-07-24, fable-endgame-A6) **DONE.** Cold tgt regen: both lemmas
  census-reject `assert-forall` (2 in the tag table), NO certs emitted;
  **probe11 is now fully green — 3/3 CLOSE, zero honest-fails, ALL
  CLASSIFIED ✓** (stale classification entries removed; a reappearing
  cert without the binder arm lands UNCLASSIFIED and fails the runner).
  Battery: fixture 28/33 certified (no new rejects — no fixture
  assert-forall), probe9/13/38 green, units 406/0, gate 231/0 +
  discharge 150/0, e2e 551/0.
