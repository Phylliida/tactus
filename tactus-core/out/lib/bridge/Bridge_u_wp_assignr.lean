import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_wp_assignr`
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
-- leaf 8: ⟦v⟧
-- leaf 9: ⟦0 ≤ v ∧ v < 18446744073709551616⟧
-- leaf 10: ⟦h_v_bound⟧
-- leaf 11: ⟦lib.wp_stm pp f (lib.StmData.AssignR x v) = lib.GoalList.Nil⟧
-- leaf 12: ⟦/- @rust:tactus-core/lib.rs:5244:13 -/ lib.wp_stm pp f (lib.StmData.AssignR x v) = lib.GoalList.Nil⟧
-- leaf 13: ⟦lib.wp_stm⟧
-- leaf 14: ⟦lib.GoalList⟧
-- leaf 15: ⟦lib.StmData⟧

@[reducible] def cert_u_wp_assignr_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk (lib.BinderList.Cons 4 5 (Tactus.Box.mk (lib.BinderList.Cons 8 5 (Tactus.Box.mk lib.BinderList.Nil)))))))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.Bound 7 6 (Tactus.Box.mk (lib.ParamBoundList.Bound 10 9 (Tactus.Box.mk lib.ParamBoundList.Nil)))))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 11 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 1)

@[reducible] def cert_u_wp_assignr_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 12 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_wp_assignr_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_wp_assignr_at_lib_5244_13_1
@[reducible] def cert_u_wp_assignr_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.All 4 5 (Tactus.Box.mk (lib.GoalData.All 7 6 (Tactus.Box.mk (lib.GoalData.All 8 5 (Tactus.Box.mk (lib.GoalData.All 10 9 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 12))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_wp_assignr_goals = 1 := by decide

-- ── W4a in-gate bridge (bootstrap-38) ──
set_option maxRecDepth 8000
example : lib.goals_eq (lib.ref_wp cert_u_wp_assignr_ctx cert_u_wp_assignr_sst) cert_u_wp_assignr_goals = 1 := by decide
