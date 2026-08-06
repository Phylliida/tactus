import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_csot_leth`
-- tactus-core-vocab-hash: unvendored
-- Stage A certifies statement ASSEMBLY (binder telescopes, hypothesis
-- order, let-chains, obligation multiplicity/order). It does NOT certify
-- leaf rendering (stage B/W6), the serializer (it is the TCB), the
-- frontend, or SST-semantics adequacy (W5). Leaves below are opaque ids;
-- a stage-A pass coexisting with a leaf-renderer bug is possible.

-- ── leaf table ──────────────────────────────────────────────
-- leaf 0: ⟦hp⟧
-- leaf 1: ⟦Int → (Int → Int) → Prop⟧
-- leaf 2: ⟦he⟧
-- leaf 3: ⟦lib.ExprData → (Int → Int) → Prop⟧
-- leaf 4: ⟦lv⟧
-- leaf 5: ⟦Int → (Int → Int) → Int⟧
-- leaf 6: ⟦x⟧
-- leaf 7: ⟦Int⟧
-- leaf 8: ⟦0 ≤ x ∧ x < 18446744073709551616⟧
-- leaf 9: ⟦h_x_bound⟧
-- leaf 10: ⟦ty⟧
-- leaf 11: ⟦0 ≤ ty ∧ ty < 18446744073709551616⟧
-- leaf 12: ⟦h_ty_bound⟧
-- leaf 13: ⟦v⟧
-- leaf 14: ⟦0 ≤ v ∧ v < 18446744073709551616⟧
-- leaf 15: ⟦h_v_bound⟧
-- leaf 16: ⟦en⟧
-- leaf 17: ⟦0 ≤ en ∧ en < 18446744073709551616⟧
-- leaf 18: ⟦h_en_bound⟧
-- leaf 19: ⟦ep⟧
-- leaf 20: ⟦0 ≤ ep ∧ ep < 18446744073709551616⟧
-- leaf 21: ⟦h_ep_bound⟧
-- leaf 22: ⟦t⟧
-- leaf 23: ⟦Tactus.Box lib.FrameList⟧
-- leaf 24: ⟦f0⟧
-- leaf 25: ⟦lib.FrameList⟧
-- leaf 26: ⟦l⟧
-- leaf 27: ⟦lib.RawExpList⟧
-- leaf 28: ⟦∀ (st : Int → Int), lib.close_sem_obligs_tel hp he lv (lib.FrameList.FLetH x ty v en ep t) f0 st l = (∀ (a : Int) (b : Int), lib.close_sem_obligs_tel hp he lv t f0 (lib.upd (lib.upd st x a) en b) l)⟧
-- leaf 29: ⟦/- @rust:tactus-core/lib.rs:4868:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs_tel hp he lv (lib.FrameList.FLetH x ty v en ep t) f0 st l = (∀ (a : Int) (b : Int), lib.close_sem_obligs_tel hp he lv t.deref f0 (lib.upd (lib.upd st x a) en b) l)⟧

@[reducible] def cert_u_csot_leth_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk (lib.BinderList.Cons 4 5 (Tactus.Box.mk (lib.BinderList.Cons 6 7 (Tactus.Box.mk (lib.BinderList.Cons 10 7 (Tactus.Box.mk (lib.BinderList.Cons 13 7 (Tactus.Box.mk (lib.BinderList.Cons 16 7 (Tactus.Box.mk (lib.BinderList.Cons 19 7 (Tactus.Box.mk (lib.BinderList.Cons 22 23 (Tactus.Box.mk (lib.BinderList.Cons 24 25 (Tactus.Box.mk (lib.BinderList.Cons 26 27 (Tactus.Box.mk lib.BinderList.Nil)))))))))))))))))))))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.Bound 9 8 (Tactus.Box.mk (lib.ParamBoundList.Bound 12 11 (Tactus.Box.mk (lib.ParamBoundList.Bound 15 14 (Tactus.Box.mk (lib.ParamBoundList.Bound 18 17 (Tactus.Box.mk (lib.ParamBoundList.Bound 21 20 (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))))))))))))))))))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 28 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 0)

@[reducible] def cert_u_csot_leth_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 29 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_csot_leth_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_csot_leth_at_lib_4868_13_1
@[reducible] def cert_u_csot_leth_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.All 4 5 (Tactus.Box.mk (lib.GoalData.All 6 7 (Tactus.Box.mk (lib.GoalData.All 9 8 (Tactus.Box.mk (lib.GoalData.All 10 7 (Tactus.Box.mk (lib.GoalData.All 12 11 (Tactus.Box.mk (lib.GoalData.All 13 7 (Tactus.Box.mk (lib.GoalData.All 15 14 (Tactus.Box.mk (lib.GoalData.All 16 7 (Tactus.Box.mk (lib.GoalData.All 18 17 (Tactus.Box.mk (lib.GoalData.All 19 7 (Tactus.Box.mk (lib.GoalData.All 21 20 (Tactus.Box.mk (lib.GoalData.All 22 23 (Tactus.Box.mk (lib.GoalData.All 24 25 (Tactus.Box.mk (lib.GoalData.All 26 27 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 29))))))))))))))))))))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_csot_leth_goals = 1 := by decide
