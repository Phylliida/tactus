import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 8000

-- ══════════════════════════════════════════════════════════════════════
-- W6e G4.2 PROBE (bootstrap-24) — the max_u64 If-fold, before wiring.
--
-- Goal (design "PROBE FIRST", W6d.0 discipline): hand-build the reference
-- recompute `RawExp` that the serializer's `lift_if_raw` MUST emit, render it
-- through the LANDED `render_exp`, and diff against the deep goal-side
-- `ExprData` that `lexpr_to_exprdata` MUST transcribe from production's leaf
-- 15/16 — BEFORE touching the serializer. If they agree, the G4.2 contract is
-- pinned: the two halves (recompute + transcription) have a single verified
-- target, and the frozen `ref_wp` will bridge once both are wired.
--
-- Unlike G4.1's kernel guard (isolated `render_exp`==shape, placeholder span
-- ids 9/12), this probe routes the WHOLE thing through the REAL emitted
-- `ref_wp`/`goals_eq` and uses production's REAL span-loc ids (11/13, read off
-- the live SST) — so it is the faithful model of the wired bridge, not just a
-- render spot-check.
--
-- max_u64 (bootstrap-fixture/lib.rs): `fn max_u64(x,y:u64)->r ensures r>=x, r>=y
-- { let m = if x<y {y} else {x}; m }`. The frontend lifts the fall-through `if`
-- INTO each ensures leaf, giving two branch-folded implications:
--   leaf 15:  x < y  → (let r := (let m := y; m); r≥x ∧ r≥y)
--   leaf 16: ¬(x < y) → (let r := (let m := x; m); r≥x ∧ r≥y)
-- ids: x=0 y=4 r=10 m=14; span locs 11 (@95:13, r≥x) / 13 (@95:21, r≥y);
-- opcodes Implies=13 Lt=2 And=11 Ge=5. (m-binder id 14 follows the G4.1 guard's
-- convention; the ABSOLUTE id is pinned at G4.3 re-emit — both sides intern the
-- SAME `sanitize(m)` text, so they agree by construction regardless of value.)
-- ══════════════════════════════════════════════════════════════════════

-- ── production fn context (VERBATIM from bootstrap-fixture/out/lib/cert/max_u64.cert.lean) ──
@[reducible] def ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 4 1 (Tactus.Box.mk lib.BinderList.Nil)))) (lib.ParamBoundList.Bound 3 2 (Tactus.Box.mk (lib.ParamBoundList.Bound 6 5 (Tactus.Box.mk lib.ParamBoundList.Nil)))) lib.BinderList.Nil (lib.LeafList.Cons 7 (Tactus.Box.mk (lib.LeafList.Cons 8 (Tactus.Box.mk lib.LeafList.Nil)))) 1)

-- ══ REFERENCE side: the recompute RawExps (what `lift_if_raw` must build) ══
-- shared ensures conjunction `r≥x ∧ r≥y`, each conjunct Span-wrapped at its
-- own source loc (11 = @95:13, 13 = @95:21). These reuse the exact Span locs
-- the live SST already carries for the two ensures (RawExp.Span 11 / 13).
@[reducible] def rx : lib.RawExp := lib.RawExp.BinOp 5 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 10 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 0 lib.TypData.TyInt))
@[reducible] def ry : lib.RawExp := lib.RawExp.BinOp 5 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 10 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 4 lib.TypData.TyInt))
@[reducible] def span_rx : lib.RawExp := lib.RawExp.Span 11 (Tactus.Box.mk rx)
@[reducible] def span_ry : lib.RawExp := lib.RawExp.Span 13 (Tactus.Box.mk ry)
@[reducible] def ens_and : lib.RawExp := lib.RawExp.BinOp 11 lib.TypData.TyBool (Tactus.Box.mk span_rx) (Tactus.Box.mk span_ry)
-- branch guard `x < y`
@[reducible] def lt_xy : lib.RawExp := lib.RawExp.BinOp 2 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 0 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 4 lib.TypData.TyInt))
-- the lifted branch returns: `let m := <y|x>; m`
@[reducible] def letm_y : lib.RawExp := lib.RawExp.Let 14 (Tactus.Box.mk (lib.RawExp.Var 4 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 14 lib.TypData.TyInt))
@[reducible] def letm_x : lib.RawExp := lib.RawExp.Let 14 (Tactus.Box.mk (lib.RawExp.Var 0 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 14 lib.TypData.TyInt))
-- `let r := <lifted return>; (ensures conjunction)`  — RetLet folded INTO the leaf
@[reducible] def body15 : lib.RawExp := lib.RawExp.Let 10 (Tactus.Box.mk letm_y) (Tactus.Box.mk ens_and)
@[reducible] def body16 : lib.RawExp := lib.RawExp.Let 10 (Tactus.Box.mk letm_x) (Tactus.Box.mk ens_and)
-- the two branch-folded implications
@[reducible] def impl15 : lib.RawExp := lib.RawExp.BinOp 13 lib.TypData.TyBool (Tactus.Box.mk lt_xy) (Tactus.Box.mk body15)
@[reducible] def impl16 : lib.RawExp := lib.RawExp.BinOp 13 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Not (Tactus.Box.mk lt_xy))) (Tactus.Box.mk body16)

-- the WIRED reference SST: `Ret([impl15, impl16], RetNone)`. RetNone is
-- load-bearing — the `let r` is ALREADY inside each obligation, so `ret_frame`
-- must NOT re-fold it (that is what makes the frame emit exactly 2 goals with
-- no outer Let, matching production's branch-split).
@[reducible] def sst_wired : lib.StmData :=
  lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk impl15) (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk impl16) (Tactus.Box.mk lib.RawExpList.Nil))))) lib.RetBind.RetNone

-- ══ GOAL side: the deep ExprData `lexpr_to_exprdata` must transcribe ══
-- (written INDEPENDENTLY as production's own output — NOT via render_exp — so
-- the bridge is a genuine cross-check, not a tautology.)
@[reducible] def ged_rx : lib.ExprData := lib.ExprData.BinOp 5 (Tactus.Box.mk (lib.ExprData.Atom 10)) (Tactus.Box.mk (lib.ExprData.Atom 0))
@[reducible] def ged_ry : lib.ExprData := lib.ExprData.BinOp 5 (Tactus.Box.mk (lib.ExprData.Atom 10)) (Tactus.Box.mk (lib.ExprData.Atom 4))
@[reducible] def gspan_rx : lib.ExprData := lib.ExprData.SpanMark 11 (Tactus.Box.mk ged_rx)
@[reducible] def gspan_ry : lib.ExprData := lib.ExprData.SpanMark 13 (Tactus.Box.mk ged_ry)
@[reducible] def gand : lib.ExprData := lib.ExprData.BinOp 11 (Tactus.Box.mk gspan_rx) (Tactus.Box.mk gspan_ry)
@[reducible] def glt : lib.ExprData := lib.ExprData.BinOp 2 (Tactus.Box.mk (lib.ExprData.Atom 0)) (Tactus.Box.mk (lib.ExprData.Atom 4))
@[reducible] def gletm_y : lib.ExprData := lib.ExprData.Let 14 (Tactus.Box.mk (lib.ExprData.Atom 4)) (Tactus.Box.mk (lib.ExprData.Atom 14))
@[reducible] def gletm_x : lib.ExprData := lib.ExprData.Let 14 (Tactus.Box.mk (lib.ExprData.Atom 0)) (Tactus.Box.mk (lib.ExprData.Atom 14))
@[reducible] def gbody15 : lib.ExprData := lib.ExprData.Let 10 (Tactus.Box.mk gletm_y) (Tactus.Box.mk gand)
@[reducible] def gbody16 : lib.ExprData := lib.ExprData.Let 10 (Tactus.Box.mk gletm_x) (Tactus.Box.mk gand)
@[reducible] def deep15 : lib.ExprData := lib.ExprData.BinOp 13 (Tactus.Box.mk glt) (Tactus.Box.mk gbody15)
@[reducible] def deep16 : lib.ExprData := lib.ExprData.BinOp 13 (Tactus.Box.mk (lib.ExprData.Not (Tactus.Box.mk glt))) (Tactus.Box.mk gbody16)

-- the binder telescope production wraps each leaf under (∀x,∀h_x,∀y,∀h_y).
@[reducible] def gtel (leaf : lib.ExprData) : lib.GoalData :=
  lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 4 1 (Tactus.Box.mk (lib.GoalData.All 6 5 (Tactus.Box.mk (lib.GoalData.LeafE leaf))))))))
@[reducible] def goals_wired : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (gtel deep15)) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (gtel deep16)) (Tactus.Box.mk lib.GoalList.Nil)))

-- ══════════════════════════════════════════════════════════════════════
-- (0) BEFORE — the current honest-fail is real. The LIVE cert's opaque SST
-- (`Ret([Span 11 (r≥x), Span 13 (r≥y)], RetLet 10 14)`, ensures-split) does
-- NOT bridge to the opaque `LeafE(Atom 15/16)` goals: refWp folds a `Let 10 14`
-- wrapper around a `r≥x`/`r≥y` leaf, split on the WRONG axis. This is exactly
-- probe9's `max_u64 hfail-ok`. (VERBATIM current cert sst/goals.)
-- ══════════════════════════════════════════════════════════════════════
@[reducible] def sst_current : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Span 11 (Tactus.Box.mk (lib.RawExp.BinOp 5 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 10 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 0 lib.TypData.TyInt)))))) (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Span 13 (Tactus.Box.mk (lib.RawExp.BinOp 5 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 10 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 4 lib.TypData.TyInt)))))) (Tactus.Box.mk lib.RawExpList.Nil))))) (lib.RetBind.RetLet 10 14))
@[reducible] def goals_current : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (gtel (lib.ExprData.Atom 15))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (gtel (lib.ExprData.Atom 16))) (Tactus.Box.mk lib.GoalList.Nil)))

-- the current opaque bridge does NOT close (documented honest-fail):
example : lib.goals_eq (lib.ref_wp ctx sst_current) goals_current = 0 := by decide

-- ══════════════════════════════════════════════════════════════════════
-- (A) AFTER — the WIRED deep bridge CLOSES. The recompute SST reproduces
-- production's two branch-folded goals, constructor-for-constructor.
-- ══════════════════════════════════════════════════════════════════════
example : lib.goals_eq (lib.ref_wp ctx sst_wired) goals_wired = 1 := by decide
-- the RetNone Ret path emits exactly 2 goals (no outer Let), matching prod:
example : lib.goal_count (lib.ref_wp ctx sst_wired) = 2 := by decide
example : lib.goal_count goals_wired = 2 := by decide

-- ══════════════════════════════════════════════════════════════════════
-- (B) render diff at the leaf — the direct probe ask: `render_exp` of each
-- recompute RawExp equals the independently-written deep goal leaf.
-- ══════════════════════════════════════════════════════════════════════
example : lib.expr_eq (lib.render_exp impl15) deep15 = 1 := by decide
example : lib.expr_eq (lib.render_exp impl16) deep16 = 1 := by decide

-- ══════════════════════════════════════════════════════════════════════
-- (C) mutation-kills — each single structural drop FLIPS the bridge 1→0,
-- proving the deep compare is load-bearing on BOTH halves of G4.2.
-- ══════════════════════════════════════════════════════════════════════

-- ── goal-side kills (buggy `lexpr_to_exprdata`; SST/refWp intact) ──
-- K1: goal leaf 15 drops the inner `let m` (Let value → bare `y`). refWp still
-- binds it from the recompute, so Let-tag vs Atom-tag diverge.
@[reducible] def deep15_k1 : lib.ExprData := lib.ExprData.BinOp 13 (Tactus.Box.mk glt) (Tactus.Box.mk (lib.ExprData.Let 10 (Tactus.Box.mk (lib.ExprData.Atom 4)) (Tactus.Box.mk gand)))
@[reducible] def goals_k1 : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (gtel deep15_k1)) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (gtel deep16)) (Tactus.Box.mk lib.GoalList.Nil)))
example : lib.goals_eq (lib.ref_wp ctx sst_wired) goals_k1 = 0 := by decide

-- K2: goal leaf 16 drops the `¬` guard (¬Lt → Lt). refWp emits Not from the
-- recompute, so Not-tag vs BinOp-tag diverge.
@[reducible] def deep16_k2 : lib.ExprData := lib.ExprData.BinOp 13 (Tactus.Box.mk glt) (Tactus.Box.mk gbody16)
@[reducible] def goals_k2 : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (gtel deep15)) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (gtel deep16_k2)) (Tactus.Box.mk lib.GoalList.Nil)))
example : lib.goals_eq (lib.ref_wp ctx sst_wired) goals_k2 = 0 := by decide

-- ── reference-side kills (buggy `lift_if_raw` recompute; goals intact) ──
-- these are the G4.2-SPECIFIC risk: the recompute is new code. A wrong RawExp
-- must be caught by refWp against production's REAL (correct) leaf 15/16.
-- K3: recompute drops the inner `let m` (value → bare `y`).
@[reducible] def sst_k3 : lib.StmData :=
  lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.BinOp 13 lib.TypData.TyBool (Tactus.Box.mk lt_xy) (Tactus.Box.mk (lib.RawExp.Let 10 (Tactus.Box.mk (lib.RawExp.Var 4 lib.TypData.TyInt)) (Tactus.Box.mk ens_and))))) (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk impl16) (Tactus.Box.mk lib.RawExpList.Nil))))) lib.RetBind.RetNone
example : lib.goals_eq (lib.ref_wp ctx sst_k3) goals_wired = 0 := by decide

-- K4: recompute takes the WRONG branch value (branch-true binds `x` not `y`).
@[reducible] def sst_k4 : lib.StmData :=
  lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.BinOp 13 lib.TypData.TyBool (Tactus.Box.mk lt_xy) (Tactus.Box.mk body16))) (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk impl16) (Tactus.Box.mk lib.RawExpList.Nil))))) lib.RetBind.RetNone
example : lib.goals_eq (lib.ref_wp ctx sst_k4) goals_wired = 0 := by decide

-- K5: recompute drops a span (Span 11 elided → bare `r≥x`). The silent-
-- divergence class the local model flagged: an ensures conjunct that loses its
-- `@rust:` loc. SpanMark-tag vs BinOp-tag diverge.
@[reducible] def ens_and_k5 : lib.RawExp := lib.RawExp.BinOp 11 lib.TypData.TyBool (Tactus.Box.mk rx) (Tactus.Box.mk span_ry)
@[reducible] def sst_k5 : lib.StmData :=
  lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.BinOp 13 lib.TypData.TyBool (Tactus.Box.mk lt_xy) (Tactus.Box.mk (lib.RawExp.Let 10 (Tactus.Box.mk letm_y) (Tactus.Box.mk ens_and_k5))))) (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk impl16) (Tactus.Box.mk lib.RawExpList.Nil))))) lib.RetBind.RetNone
example : lib.goals_eq (lib.ref_wp ctx sst_k5) goals_wired = 0 := by decide

-- K6: recompute uses the WRONG span loc (11 → 99). Same source expr, wrong
-- provenance — the exact byte-mismatch that a frozen refWp would silently
-- reject without diagnostic; the probe makes it LOUD.
@[reducible] def ens_and_k6 : lib.RawExp := lib.RawExp.BinOp 11 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Span 99 (Tactus.Box.mk rx))) (Tactus.Box.mk span_ry)
@[reducible] def sst_k6 : lib.StmData :=
  lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.BinOp 13 lib.TypData.TyBool (Tactus.Box.mk lt_xy) (Tactus.Box.mk (lib.RawExp.Let 10 (Tactus.Box.mk letm_y) (Tactus.Box.mk ens_and_k6))))) (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk impl16) (Tactus.Box.mk lib.RawExpList.Nil))))) lib.RetBind.RetNone
example : lib.goals_eq (lib.ref_wp ctx sst_k6) goals_wired = 0 := by decide
