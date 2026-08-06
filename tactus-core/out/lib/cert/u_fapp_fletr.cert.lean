import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_fapp_fletr`
-- tactus-core-vocab-hash: unvendored
-- Stage A certifies statement ASSEMBLY (binder telescopes, hypothesis
-- order, let-chains, obligation multiplicity/order). It does NOT certify
-- leaf rendering (stage B/W6), the serializer (it is the TCB), the
-- frontend, or SST-semantics adequacy (W5). Leaves below are opaque ids;
-- a stage-A pass coexisting with a leaf-renderer bug is possible.

-- ── leaf table ──────────────────────────────────────────────
-- leaf 0: ⟦x⟧
-- leaf 1: ⟦Int⟧
-- leaf 2: ⟦0 ≤ x ∧ x < 18446744073709551616⟧
-- leaf 3: ⟦h_x_bound⟧
-- leaf 4: ⟦v⟧
-- leaf 5: ⟦0 ≤ v ∧ v < 18446744073709551616⟧
-- leaf 6: ⟦h_v_bound⟧
-- leaf 7: ⟦t⟧
-- leaf 8: ⟦Tactus.Box lib.FrameList⟧
-- leaf 9: ⟦g⟧
-- leaf 10: ⟦lib.FrameList⟧
-- leaf 11: ⟦lib.frame_append (lib.FrameList.FLetR x v t) g = lib.FrameList.FLetR x v (Tactus.Box.mk (lib.frame_append t g))⟧
-- leaf 12: ⟦/- @rust:tactus-core/lib.rs:6484:13 -/ lib.frame_append (lib.FrameList.FLetR x v t) g = lib.FrameList.FLetR x v (Tactus.Box.mk (lib.frame_append t.deref g))⟧
-- leaf 13: ⟦lib.frame_append⟧

@[reducible] def cert_u_fapp_fletr_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 4 1 (Tactus.Box.mk (lib.BinderList.Cons 7 8 (Tactus.Box.mk (lib.BinderList.Cons 9 10 (Tactus.Box.mk lib.BinderList.Nil)))))))) (lib.ParamBoundList.Bound 3 2 (Tactus.Box.mk (lib.ParamBoundList.Bound 6 5 (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 11 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 1)

@[reducible] def cert_u_fapp_fletr_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 12 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_fapp_fletr_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_fapp_fletr_at_lib_6484_13_1
@[reducible] def cert_u_fapp_fletr_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 4 1 (Tactus.Box.mk (lib.GoalData.All 6 5 (Tactus.Box.mk (lib.GoalData.All 7 8 (Tactus.Box.mk (lib.GoalData.All 9 10 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 12))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_fapp_fletr_goals = 1 := by decide
