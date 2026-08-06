import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_cser_bind`
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
-- leaf 13: ⟦t⟧
-- leaf 14: ⟦Tactus.Box lib.FrameList⟧
-- leaf 15: ⟦o⟧
-- leaf 16: ⟦lib.RawExp⟧
-- leaf 17: ⟦∀ (st : Int → Int), lib.close_sem_e_res hp he lv (lib.FrameList.FBind x ty t) st o = lib.close_sem_e_res hp he lv t st o⟧
-- leaf 18: ⟦/- @rust:tactus-core/lib.rs:4726:13 -/ ∀ (st : Int → Int), lib.close_sem_e_res hp he lv (lib.FrameList.FBind x ty t) st o = lib.close_sem_e_res hp he lv t.deref st o⟧

@[reducible] def cert_u_cser_bind_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk (lib.BinderList.Cons 4 5 (Tactus.Box.mk (lib.BinderList.Cons 6 7 (Tactus.Box.mk (lib.BinderList.Cons 10 7 (Tactus.Box.mk (lib.BinderList.Cons 13 14 (Tactus.Box.mk (lib.BinderList.Cons 15 16 (Tactus.Box.mk lib.BinderList.Nil)))))))))))))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.Bound 9 8 (Tactus.Box.mk (lib.ParamBoundList.Bound 12 11 (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))))))))))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 17 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 0)

@[reducible] def cert_u_cser_bind_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 18 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_cser_bind_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_cser_bind_at_lib_4726_13_1
@[reducible] def cert_u_cser_bind_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.All 4 5 (Tactus.Box.mk (lib.GoalData.All 6 7 (Tactus.Box.mk (lib.GoalData.All 9 8 (Tactus.Box.mk (lib.GoalData.All 10 7 (Tactus.Box.mk (lib.GoalData.All 12 11 (Tactus.Box.mk (lib.GoalData.All 13 14 (Tactus.Box.mk (lib.GoalData.All 15 16 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 18))))))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_cser_bind_goals = 1 := by decide
