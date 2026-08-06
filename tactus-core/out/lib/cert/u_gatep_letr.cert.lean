import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_gatep_letr`
-- tactus-core-vocab-hash: unvendored
-- Stage A certifies statement ASSEMBLY (binder telescopes, hypothesis
-- order, let-chains, obligation multiplicity/order). It does NOT certify
-- leaf rendering (stage B/W6), the serializer (it is the TCB), the
-- frontend, or SST-semantics adequacy (W5). Leaves below are opaque ids;
-- a stage-A pass coexisting with a leaf-renderer bug is possible.

-- ── leaf table ──────────────────────────────────────────────
-- leaf 0: ⟦pp⟧
-- leaf 1: ⟦lib.LeafList⟧
-- leaf 2: ⟦x⟧
-- leaf 3: ⟦Int⟧
-- leaf 4: ⟦0 ≤ x ∧ x < 18446744073709551616⟧
-- leaf 5: ⟦h_x_bound⟧
-- leaf 6: ⟦v⟧
-- leaf 7: ⟦0 ≤ v ∧ v < 18446744073709551616⟧
-- leaf 8: ⟦h_v_bound⟧
-- leaf 9: ⟦t⟧
-- leaf 10: ⟦Tactus.Box lib.FrameList⟧
-- leaf 11: ⟦lib.has_poisoned_hyp pp (lib.FrameList.FLetR x v t) = lib.has_poisoned_hyp pp t⟧
-- leaf 12: ⟦/- @rust:tactus-core/lib.rs:5079:13 -/ lib.has_poisoned_hyp pp (lib.FrameList.FLetR x v t) = lib.has_poisoned_hyp pp t.deref⟧
-- leaf 13: ⟦lib.has_poisoned_hyp⟧
-- leaf 14: ⟦lib.FrameList⟧

@[reducible] def cert_u_gatep_letr_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk (lib.BinderList.Cons 6 3 (Tactus.Box.mk (lib.BinderList.Cons 9 10 (Tactus.Box.mk lib.BinderList.Nil)))))))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.Bound 5 4 (Tactus.Box.mk (lib.ParamBoundList.Bound 8 7 (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 11 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 1)

@[reducible] def cert_u_gatep_letr_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 12 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_gatep_letr_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_gatep_letr_at_lib_5079_13_1
@[reducible] def cert_u_gatep_letr_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.All 5 4 (Tactus.Box.mk (lib.GoalData.All 6 3 (Tactus.Box.mk (lib.GoalData.All 8 7 (Tactus.Box.mk (lib.GoalData.All 9 10 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 12))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_gatep_letr_goals = 1 := by decide
