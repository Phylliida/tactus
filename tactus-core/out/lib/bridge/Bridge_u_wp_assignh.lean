import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_wp_assignh`
-- tactus-core-vocab-hash: unvendored
-- Stage A certifies statement ASSEMBLY (binder telescopes, hypothesis
-- order, let-chains, obligation multiplicity/order). It does NOT certify
-- leaf rendering (stage B/W6), the serializer (it is the TCB), the
-- frontend, or SST-semantics adequacy (W5). Leaves below are opaque ids;
-- a stage-A pass coexisting with a leaf-renderer bug is possible.

-- ── leaf table ──────────────────────────────────────────────
-- leaf 0: ⟦pp⟧
-- leaf 1: ⟦lib.LeafList⟧
-- leaf 2: ⟦f⟧
-- leaf 3: ⟦lib.FrameList⟧
-- leaf 4: ⟦x⟧
-- leaf 5: ⟦Int⟧
-- leaf 6: ⟦0 ≤ x ∧ x < 18446744073709551616⟧
-- leaf 7: ⟦h_x_bound⟧
-- leaf 8: ⟦ty⟧
-- leaf 9: ⟦0 ≤ ty ∧ ty < 18446744073709551616⟧
-- leaf 10: ⟦h_ty_bound⟧
-- leaf 11: ⟦v⟧
-- leaf 12: ⟦0 ≤ v ∧ v < 18446744073709551616⟧
-- leaf 13: ⟦h_v_bound⟧
-- leaf 14: ⟦en⟧
-- leaf 15: ⟦0 ≤ en ∧ en < 18446744073709551616⟧
-- leaf 16: ⟦h_en_bound⟧
-- leaf 17: ⟦ep⟧
-- leaf 18: ⟦0 ≤ ep ∧ ep < 18446744073709551616⟧
-- leaf 19: ⟦h_ep_bound⟧
-- leaf 20: ⟦lib.wp_stm pp f (lib.StmData.AssignH x ty v en ep) = lib.GoalList.Nil⟧
-- leaf 21: ⟦/- @rust:tactus-core/lib.rs:5241:13 -/ lib.wp_stm pp f (lib.StmData.AssignH x ty v en ep) = lib.GoalList.Nil⟧
-- leaf 22: ⟦lib.wp_stm⟧
-- leaf 23: ⟦lib.GoalList⟧
-- leaf 24: ⟦lib.StmData⟧

@[reducible] def cert_u_wp_assignh_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk (lib.BinderList.Cons 4 5 (Tactus.Box.mk (lib.BinderList.Cons 8 5 (Tactus.Box.mk (lib.BinderList.Cons 11 5 (Tactus.Box.mk (lib.BinderList.Cons 14 5 (Tactus.Box.mk (lib.BinderList.Cons 17 5 (Tactus.Box.mk lib.BinderList.Nil)))))))))))))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.Bound 7 6 (Tactus.Box.mk (lib.ParamBoundList.Bound 10 9 (Tactus.Box.mk (lib.ParamBoundList.Bound 13 12 (Tactus.Box.mk (lib.ParamBoundList.Bound 16 15 (Tactus.Box.mk (lib.ParamBoundList.Bound 19 18 (Tactus.Box.mk lib.ParamBoundList.Nil)))))))))))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 20 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 1)

@[reducible] def cert_u_wp_assignh_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 21 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_wp_assignh_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_wp_assignh_at_lib_5241_13_1
@[reducible] def cert_u_wp_assignh_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.All 4 5 (Tactus.Box.mk (lib.GoalData.All 7 6 (Tactus.Box.mk (lib.GoalData.All 8 5 (Tactus.Box.mk (lib.GoalData.All 10 9 (Tactus.Box.mk (lib.GoalData.All 11 5 (Tactus.Box.mk (lib.GoalData.All 13 12 (Tactus.Box.mk (lib.GoalData.All 14 5 (Tactus.Box.mk (lib.GoalData.All 16 15 (Tactus.Box.mk (lib.GoalData.All 17 5 (Tactus.Box.mk (lib.GoalData.All 19 18 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 21))))))))))))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_wp_assignh_goals = 1 := by decide

-- ── W4a in-gate bridge (bootstrap-38) ──
set_option maxRecDepth 8000
example : lib.goals_eq (lib.ref_wp cert_u_wp_assignh_ctx cert_u_wp_assignh_sst) cert_u_wp_assignh_goals = 1 := by decide
