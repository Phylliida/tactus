import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_wp_ifctor`
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
-- leaf 4: ⟦pos_binders⟧
-- leaf 5: ⟦Tactus.Box lib.BinderList⟧
-- leaf 6: ⟦eq_name⟧
-- leaf 7: ⟦Int⟧
-- leaf 8: ⟦0 ≤ eq_name ∧ eq_name < 18446744073709551616⟧
-- leaf 9: ⟦h_eq_name_bound⟧
-- leaf 10: ⟦eq_prop⟧
-- leaf 11: ⟦0 ≤ eq_prop ∧ eq_prop < 18446744073709551616⟧
-- leaf 12: ⟦h_eq_prop_bound⟧
-- leaf 13: ⟦neg_name⟧
-- leaf 14: ⟦0 ≤ neg_name ∧ neg_name < 18446744073709551616⟧
-- leaf 15: ⟦h_neg_name_bound⟧
-- leaf 16: ⟦neg_prop⟧
-- leaf 17: ⟦0 ≤ neg_prop ∧ neg_prop < 18446744073709551616⟧
-- leaf 18: ⟦h_neg_prop_bound⟧
-- leaf 19: ⟦thn⟧
-- leaf 20: ⟦Tactus.Box lib.StmData⟧
-- leaf 21: ⟦els⟧
-- leaf 22: ⟦lib.wp_stm pp f (lib.StmData.IfCtor pos_binders eq_name eq_prop neg_name neg_prop thn els) = lib.goals_append (lib.wp_stm pp (lib.frame_append f (lib.ctor_pos_frame pos_binders eq_name eq_prop)) thn) (lib.wp_stm pp (lib.frame_append f (lib.FrameList.FHyp neg_name neg_prop (Tactus.Box.mk lib.FrameList.FNil))) els)⟧
-- leaf 23: ⟦/- @rust:tactus-core/lib.rs:5284:13 -/ lib.wp_stm pp f (lib.StmData.IfCtor pos_binders eq_name eq_prop neg_name neg_prop thn els) = lib.goals_append (lib.wp_stm pp (lib.frame_append f (lib.ctor_pos_frame pos_binders.deref eq_name eq_prop)) thn.deref) (lib.wp_stm pp (lib.frame_append f (lib.FrameList.FHyp neg_name neg_prop (Tactus.Box.mk lib.FrameList.FNil))) els.deref)⟧
-- leaf 24: ⟦lib.wp_stm⟧
-- leaf 25: ⟦lib.GoalList⟧
-- leaf 26: ⟦lib.StmData⟧

@[reducible] def cert_u_wp_ifctor_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk (lib.BinderList.Cons 4 5 (Tactus.Box.mk (lib.BinderList.Cons 6 7 (Tactus.Box.mk (lib.BinderList.Cons 10 7 (Tactus.Box.mk (lib.BinderList.Cons 13 7 (Tactus.Box.mk (lib.BinderList.Cons 16 7 (Tactus.Box.mk (lib.BinderList.Cons 19 20 (Tactus.Box.mk (lib.BinderList.Cons 21 20 (Tactus.Box.mk lib.BinderList.Nil)))))))))))))))))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.Bound 9 8 (Tactus.Box.mk (lib.ParamBoundList.Bound 12 11 (Tactus.Box.mk (lib.ParamBoundList.Bound 15 14 (Tactus.Box.mk (lib.ParamBoundList.Bound 18 17 (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))))))))))))))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 22 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 1)

@[reducible] def cert_u_wp_ifctor_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 23 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_wp_ifctor_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_wp_ifctor_at_lib_5284_13_1
@[reducible] def cert_u_wp_ifctor_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.All 4 5 (Tactus.Box.mk (lib.GoalData.All 6 7 (Tactus.Box.mk (lib.GoalData.All 9 8 (Tactus.Box.mk (lib.GoalData.All 10 7 (Tactus.Box.mk (lib.GoalData.All 12 11 (Tactus.Box.mk (lib.GoalData.All 13 7 (Tactus.Box.mk (lib.GoalData.All 15 14 (Tactus.Box.mk (lib.GoalData.All 16 7 (Tactus.Box.mk (lib.GoalData.All 18 17 (Tactus.Box.mk (lib.GoalData.All 19 20 (Tactus.Box.mk (lib.GoalData.All 21 20 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 23))))))))))))))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_wp_ifctor_goals = 1 := by decide

-- ── W4a in-gate bridge (bootstrap-38) ──
set_option maxRecDepth 8000
example : lib.goals_eq (lib.ref_wp cert_u_wp_ifctor_ctx cert_u_wp_ifctor_sst) cert_u_wp_ifctor_goals = 1 := by decide
