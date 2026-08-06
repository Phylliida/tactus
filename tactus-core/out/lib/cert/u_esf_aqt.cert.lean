import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_esf_aqt`
-- tactus-core-vocab-hash: unvendored
-- Stage A certifies statement ASSEMBLY (binder telescopes, hypothesis
-- order, let-chains, obligation multiplicity/order). It does NOT certify
-- leaf rendering (stage B/W6), the serializer (it is the TCB), the
-- frontend, or SST-semantics adequacy (W5). Leaves below are opaque ids;
-- a stage-A pass coexisting with a leaf-renderer bug is possible.

-- ── leaf table ──────────────────────────────────────────────
-- leaf 0: ⟦pp⟧
-- leaf 1: ⟦lib.LeafList⟧
-- leaf 2: ⟦hp⟧
-- leaf 3: ⟦Int → (Int → Int) → Prop⟧
-- leaf 4: ⟦he⟧
-- leaf 5: ⟦lib.ExprData → (Int → Int) → Prop⟧
-- leaf 6: ⟦lv⟧
-- leaf 7: ⟦Int → (Int → Int) → Int⟧
-- leaf 8: ⟦f⟧
-- leaf 9: ⟦lib.FrameList⟧
-- leaf 10: ⟦o⟧
-- leaf 11: ⟦lib.RawExp⟧
-- leaf 12: ⟦hn⟧
-- leaf 13: ⟦Int⟧
-- leaf 14: ⟦0 ≤ hn ∧ hn < 18446744073709551616⟧
-- leaf 15: ⟦h_hn_bound⟧
-- leaf 16: ⟦h⟧
-- leaf 17: ⟦0 ≤ h ∧ h < 18446744073709551616⟧
-- leaf 18: ⟦h_h_bound⟧
-- leaf 19: ⟦∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.AssertQueryTactus o hn h) st = lib.close_sem_e pp hp he lv (lib.frame_append f (lib.FrameList.FUserCloser (Tactus.Box.mk lib.FrameList.FNil))) st o⟧
-- leaf 20: ⟦/- @rust:tactus-core/lib.rs:4954:13 -/ ∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.AssertQueryTactus o hn h) st = lib.close_sem_e pp hp he lv (lib.frame_append f (lib.FrameList.FUserCloser (Tactus.Box.mk lib.FrameList.FNil))) st o⟧

@[reducible] def cert_u_esf_aqt_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk (lib.BinderList.Cons 4 5 (Tactus.Box.mk (lib.BinderList.Cons 6 7 (Tactus.Box.mk (lib.BinderList.Cons 8 9 (Tactus.Box.mk (lib.BinderList.Cons 10 11 (Tactus.Box.mk (lib.BinderList.Cons 12 13 (Tactus.Box.mk (lib.BinderList.Cons 16 13 (Tactus.Box.mk lib.BinderList.Nil)))))))))))))))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.Bound 15 14 (Tactus.Box.mk (lib.ParamBoundList.Bound 18 17 (Tactus.Box.mk lib.ParamBoundList.Nil)))))))))))))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 19 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 0)

@[reducible] def cert_u_esf_aqt_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 20 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_esf_aqt_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_esf_aqt_at_lib_4954_13_1
@[reducible] def cert_u_esf_aqt_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.All 4 5 (Tactus.Box.mk (lib.GoalData.All 6 7 (Tactus.Box.mk (lib.GoalData.All 8 9 (Tactus.Box.mk (lib.GoalData.All 10 11 (Tactus.Box.mk (lib.GoalData.All 12 13 (Tactus.Box.mk (lib.GoalData.All 15 14 (Tactus.Box.mk (lib.GoalData.All 16 13 (Tactus.Box.mk (lib.GoalData.All 18 17 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 20))))))))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_esf_aqt_goals = 1 := by decide
