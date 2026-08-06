import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_esf_assignh`
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
-- leaf 10: ⟦x⟧
-- leaf 11: ⟦Int⟧
-- leaf 12: ⟦0 ≤ x ∧ x < 18446744073709551616⟧
-- leaf 13: ⟦h_x_bound⟧
-- leaf 14: ⟦ty⟧
-- leaf 15: ⟦0 ≤ ty ∧ ty < 18446744073709551616⟧
-- leaf 16: ⟦h_ty_bound⟧
-- leaf 17: ⟦v⟧
-- leaf 18: ⟦0 ≤ v ∧ v < 18446744073709551616⟧
-- leaf 19: ⟦h_v_bound⟧
-- leaf 20: ⟦en⟧
-- leaf 21: ⟦0 ≤ en ∧ en < 18446744073709551616⟧
-- leaf 22: ⟦h_en_bound⟧
-- leaf 23: ⟦ep⟧
-- leaf 24: ⟦0 ≤ ep ∧ ep < 18446744073709551616⟧
-- leaf 25: ⟦h_ep_bound⟧
-- leaf 26: ⟦∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.AssignH x ty v en ep) st = True⟧
-- leaf 27: ⟦/- @rust:tactus-core/lib.rs:4931:13 -/ ∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.AssignH x ty v en ep) st = True⟧

@[reducible] def cert_u_esf_assignh_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk (lib.BinderList.Cons 4 5 (Tactus.Box.mk (lib.BinderList.Cons 6 7 (Tactus.Box.mk (lib.BinderList.Cons 8 9 (Tactus.Box.mk (lib.BinderList.Cons 10 11 (Tactus.Box.mk (lib.BinderList.Cons 14 11 (Tactus.Box.mk (lib.BinderList.Cons 17 11 (Tactus.Box.mk (lib.BinderList.Cons 20 11 (Tactus.Box.mk (lib.BinderList.Cons 23 11 (Tactus.Box.mk lib.BinderList.Nil)))))))))))))))))))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.Bound 13 12 (Tactus.Box.mk (lib.ParamBoundList.Bound 16 15 (Tactus.Box.mk (lib.ParamBoundList.Bound 19 18 (Tactus.Box.mk (lib.ParamBoundList.Bound 22 21 (Tactus.Box.mk (lib.ParamBoundList.Bound 25 24 (Tactus.Box.mk lib.ParamBoundList.Nil)))))))))))))))))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 26 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 0)

@[reducible] def cert_u_esf_assignh_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 27 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_esf_assignh_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_esf_assignh_at_lib_4931_13_1
@[reducible] def cert_u_esf_assignh_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.All 4 5 (Tactus.Box.mk (lib.GoalData.All 6 7 (Tactus.Box.mk (lib.GoalData.All 8 9 (Tactus.Box.mk (lib.GoalData.All 10 11 (Tactus.Box.mk (lib.GoalData.All 13 12 (Tactus.Box.mk (lib.GoalData.All 14 11 (Tactus.Box.mk (lib.GoalData.All 16 15 (Tactus.Box.mk (lib.GoalData.All 17 11 (Tactus.Box.mk (lib.GoalData.All 19 18 (Tactus.Box.mk (lib.GoalData.All 20 11 (Tactus.Box.mk (lib.GoalData.All 22 21 (Tactus.Box.mk (lib.GoalData.All 23 11 (Tactus.Box.mk (lib.GoalData.All 25 24 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 27))))))))))))))))))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_esf_assignh_goals = 1 := by decide
