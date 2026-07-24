---
title: "A2 — user-closer wrap-mode mirror (apply_hom class): shared closer gate + req-binder leaf reuse + call-leaves ledger"
status: done
claimed_by: fable-endgame-A2
created: 2026-07-24T18:00:00Z
updated: 2026-07-24T18:00:00Z
---

## Description

Endgame A2 (`DESIGN-bootstrap-endgame.md` §3): close the probe11
apply_hom_gen/apply_hom_inv honest-fails — the b74 sweep's "call-arg
temp lets + auto-ref arg coercion" class.

## Progress

- (2026-07-24, fable-endgame-A2) **DONE — both fns bridge-close;
  probe11 3/3 CLOSE, ALL CLASSIFIED ✓.**

  **The b74 diagnosis was wrong about the mechanism** (right about the
  fns): the wrap-forcer is not a typ-less `Wp::LetRaw` arg temp — the
  WP tree's lets are all typed. It is the **CLOSER GATE**:
  `emit_leaf_theorem` only calls `hoist_all` when the goal's closer is
  default (`tactus_auto` / the nonlin ladder); a fn-level user
  `tactus_tactic` (which both apply_hom fns carry) keeps every goal in
  legacy goal-position wrap — the user's tactic text is positional
  against that shape — and the Return keeps the legacy
  `Done(let ret := e; …)` leaf (same gate, `StmX::Return` arm). The
  serializer had been classifying those fns' lets by the hoist rules
  (AssignH/FLetH/RetLetH) — structure production never emits for them.

  **Three coordinated changes:**
  1. `sst_to_lean::closer_is_default(fn_sst, check)` — the gate
     extracted to a SINGLE SOURCE (attr + proof-block-prefix DFS),
     consumed by both `WpCtx::new` (via the call site) and the
     serializer. Serializer wrap-mode: every let classifies PLAIN
     (`Assign`/`FLet`/`RetLet` — Bool included: plain FLet both
     renders goal-position AND arms refWp's `has_plain_flet` wrap
     gate, which `FLetR` would not), `mark_flet_forced` from the
     start (freshening off — production's `rename_frame_vars` only
     runs inside `hoist_all`).
  2. `FnCtxData.reqs` leaf TEXT now comes from production's own
     `build_req_binders` (made pub(crate)) — the fn_map ctx +
     mut-ref rewrite + shadow prefix produce the view-arg auto-ref
     coercion (`Ref.mk h.deref.generator_images`) the old bare
     render missed; the seed req hyp leaf now byte-matches (the
     cert's old leaf-6-vs-goal-leaf-28 divergence).
  3. `cert_call_leaves` gains the serializer's `let_binder_typs`
     ledger (installed into the shell OblCtx + arg_rctx) — an
     earlier call-dest local (`tmp__1 : &Vec`, trusted ledger entry)
     now renders BARE at the next call's arg slot exactly as
     production's walk does; without it the instantiated ensures
     re-wrapped `Tactus.Ref.mk tmp__1` (leaf-24-vs-29 divergence).

  **P2 guards (loud, never a non-bridging cert):**
  `user-closer-hoistless` — a goal emitted in a wrap-mode fn before
  any plain FLet would HOIST reference-side (refWp's gate is
  per-goal; stage A has no fn-level force-wrap bit — vocabulary
  follow-up batched with the A3/A5 tactus-core churn);
  `user-closer-loop` — the mirror loop telescope is hoist-shaped,
  wrap-rendering it is unmodeled. (apply_hom_symbol_exec re-censuses
  as `assert-query-tactus` — A3's customer, as expected.)

  **Validation:** fresh cold certs (fixture 28/33 certified,
  runtime 24/0); hand `decide` bridges close for BOTH apply_hom certs
  (plain `Assign 12 11` / `FLet 14 15` / `RetLet 10 16` shapes);
  probe11 reclassified → **3/3 CLOSE + 2 documented assert-forall
  honest-fails, ALL CLASSIFIED ✓** (the runner's LAX-REGRESS tripwire
  fired during reclassification — the machinery works); probe9 18/20
  unchanged, probe13 + probe38 green (no fixture regression from the
  req-render/ledger changes); lean_verify units 406/0.

  **Ops note:** after an emitter rebuild, warm fixture out-trees
  false-red with "stmt olean build failed" (mixed-generation oleans —
  the known P3 staleness class, memory
  `reference_tactus_warm_tree_false_red`). Cold `rm -rf <out>` first.
