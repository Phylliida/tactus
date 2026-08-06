import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_esf_ret`
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
-- leaf 10: ⟦es⟧
-- leaf 11: ⟦Tactus.Box lib.RawExpList⟧
-- leaf 12: ⟦rb⟧
-- leaf 13: ⟦lib.RetBind⟧
-- leaf 14: ⟦∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.Ret es rb) st = lib.close_sem_obligs pp hp he lv (lib.ret_frame pp f rb) st es⟧
-- leaf 15: ⟦/- @rust:tactus-core/lib.rs:4965:13 -/ ∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.Ret es rb) st = lib.close_sem_obligs pp hp he lv (lib.ret_frame pp f rb) st es.deref⟧

@[reducible] def cert_u_esf_ret_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk (lib.BinderList.Cons 4 5 (Tactus.Box.mk (lib.BinderList.Cons 6 7 (Tactus.Box.mk (lib.BinderList.Cons 8 9 (Tactus.Box.mk (lib.BinderList.Cons 10 11 (Tactus.Box.mk (lib.BinderList.Cons 12 13 (Tactus.Box.mk lib.BinderList.Nil)))))))))))))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))))))))))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 14 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 0)

@[reducible] def cert_u_esf_ret_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 15 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_esf_ret_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_esf_ret_at_lib_4965_13_1
@[reducible] def cert_u_esf_ret_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.All 4 5 (Tactus.Box.mk (lib.GoalData.All 6 7 (Tactus.Box.mk (lib.GoalData.All 8 9 (Tactus.Box.mk (lib.GoalData.All 10 11 (Tactus.Box.mk (lib.GoalData.All 12 13 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 15))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_esf_ret_goals = 1 := by decide

-- ── W4a in-gate bridge (bootstrap-38) ──
set_option maxRecDepth 8000
example : lib.goals_eq (lib.ref_wp cert_u_esf_ret_ctx cert_u_esf_ret_sst) cert_u_esf_ret_goals = 1 := by decide
