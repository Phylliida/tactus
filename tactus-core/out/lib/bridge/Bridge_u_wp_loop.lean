import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_wp_loop`
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
-- leaf 4: ⟦inv_hyps⟧
-- leaf 5: ⟦Tactus.Box lib.BinderList⟧
-- leaf 6: ⟦inv_obligs⟧
-- leaf 7: ⟦Tactus.Box lib.RawExpList⟧
-- leaf 8: ⟦inv_obligs_exit⟧
-- leaf 9: ⟦inv_obligs_break⟧
-- leaf 10: ⟦binders⟧
-- leaf 11: ⟦binder_bounds⟧
-- leaf 12: ⟦Tactus.Box lib.ParamBoundList⟧
-- leaf 13: ⟦cond_name⟧
-- leaf 14: ⟦Int⟧
-- leaf 15: ⟦0 ≤ cond_name ∧ cond_name < 18446744073709551616⟧
-- leaf 16: ⟦h_cond_name_bound⟧
-- leaf 17: ⟦cond_ann⟧
-- leaf 18: ⟦0 ≤ cond_ann ∧ cond_ann < 18446744073709551616⟧
-- leaf 19: ⟦h_cond_ann_bound⟧
-- leaf 20: ⟦neg_cond_ann⟧
-- leaf 21: ⟦0 ≤ neg_cond_ann ∧ neg_cond_ann < 18446744073709551616⟧
-- leaf 22: ⟦h_neg_cond_ann_bound⟧
-- leaf 23: ⟦neg_neg_cond_ann⟧
-- leaf 24: ⟦0 ≤ neg_neg_cond_ann ∧ neg_neg_cond_ann < 18446744073709551616⟧
-- leaf 25: ⟦h_neg_neg_cond_ann_bound⟧
-- leaf 26: ⟦break_guard_ann⟧
-- leaf 27: ⟦0 ≤ break_guard_ann ∧ break_guard_ann < 18446744073709551616⟧
-- leaf 28: ⟦h_break_guard_ann_bound⟧
-- leaf 29: ⟦break_use_ann⟧
-- leaf 30: ⟦0 ≤ break_use_ann ∧ break_use_ann < 18446744073709551616⟧
-- leaf 31: ⟦h_break_use_ann_bound⟧
-- leaf 32: ⟦d_old_name⟧
-- leaf 33: ⟦0 ≤ d_old_name ∧ d_old_name < 18446744073709551616⟧
-- leaf 34: ⟦h_d_old_name_bound⟧
-- leaf 35: ⟦d_old_ty⟧
-- leaf 36: ⟦0 ≤ d_old_ty ∧ d_old_ty < 18446744073709551616⟧
-- leaf 37: ⟦h_d_old_ty_bound⟧
-- leaf 38: ⟦d_old_val⟧
-- leaf 39: ⟦0 ≤ d_old_val ∧ d_old_val < 18446744073709551616⟧
-- leaf 40: ⟦h_d_old_val_bound⟧
-- leaf 41: ⟦d_old_eq_name⟧
-- leaf 42: ⟦0 ≤ d_old_eq_name ∧ d_old_eq_name < 18446744073709551616⟧
-- leaf 43: ⟦h_d_old_eq_name_bound⟧
-- leaf 44: ⟦d_old_eq_prop⟧
-- leaf 45: ⟦0 ≤ d_old_eq_prop ∧ d_old_eq_prop < 18446744073709551616⟧
-- leaf 46: ⟦h_d_old_eq_prop_bound⟧
-- leaf 47: ⟦decrease_oblig⟧
-- leaf 48: ⟦lib.RawExp⟧
-- leaf 49: ⟦setup⟧
-- leaf 50: ⟦Tactus.Box lib.StmData⟧
-- leaf 51: ⟦body⟧
-- leaf 52: ⟦lib.wp_stm pp f (lib.StmData.Loop inv_hyps inv_obligs inv_obligs_exit inv_obligs_break binders binder_bounds cond_name cond_ann neg_cond_ann neg_neg_cond_ann break_guard_ann break_use_ann d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop decrease_oblig setup body) = (if lib.is_skip setup = 1 then lib.goals_append (lib.close_each_e pp f inv_obligs) (lib.goals_append (lib.wp_stm pp (lib.loop_maintain_frame f inv_hyps binders binder_bounds cond_name cond_ann d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop) body) (lib.goals_append (lib.close_each_e pp (lib.frame_after pp (lib.loop_maintain_frame f inv_hyps binders binder_bounds cond_name cond_ann d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop) body) inv_obligs_exit) (lib.GoalList.Cons (Tactus.Box.mk (lib.close_e pp (lib.frame_after pp (lib.loop_maintain_frame f inv_hyps binders binder_bounds cond_name cond_ann d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop) body) decrease_oblig)) (Tactus.Box.mk lib.GoalList.Nil)))) else lib.goals_append (lib.close_each_e pp f inv_obligs) (lib.goals_append (lib.wp_stm pp (lib.frame_append (lib.loop_telescope_base f inv_hyps binders binder_bounds) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup) (lib.goals_append (lib.close_each_e pp (lib.frame_append (lib.frame_after pp (lib.frame_append (lib.loop_telescope_base f inv_hyps binders binder_bounds) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup) (lib.FrameList.FHyp cond_name break_guard_ann (Tactus.Box.mk lib.FrameList.FNil))) inv_obligs_break) (lib.goals_append (lib.wp_stm pp (lib.frame_append (lib.frame_after pp (lib.frame_append (lib.loop_telescope_base f inv_hyps binders binder_bounds) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup) (lib.FrameList.FHyp cond_name neg_neg_cond_ann (Tactus.Box.mk lib.FrameList.FNil))) body) (lib.goals_append (lib.close_each_e pp (lib.frame_after pp (lib.frame_append (lib.frame_after pp (lib.frame_append (lib.loop_telescope_base f inv_hyps binders binder_bounds) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup) (lib.FrameList.FHyp cond_name neg_neg_cond_ann (Tactus.Box.mk lib.FrameList.FNil))) body) inv_obligs_exit) (lib.goals_append (lib.GoalList.Cons (Tactus.Box.mk (lib.close_e pp (lib.frame_after pp (lib.frame_append (lib.frame_after pp (lib.frame_append (lib.loop_telescope_base f inv_hyps binders binder_bounds) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup) (lib.FrameList.FHyp cond_name neg_neg_cond_ann (Tactus.Box.mk lib.FrameList.FNil))) body) decrease_oblig)) (Tactus.Box.mk lib.GoalList.Nil)) (lib.wp_stm pp (lib.loop_telescope_base f inv_hyps binders binder_bounds) setup)))))))⟧
-- leaf 53: ⟦/- @rust:tactus-core/lib.rs:5304:13 -/ lib.wp_stm pp f (lib.StmData.Loop inv_hyps inv_obligs inv_obligs_exit inv_obligs_break binders binder_bounds cond_name cond_ann neg_cond_ann neg_neg_cond_ann break_guard_ann break_use_ann d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop decrease_oblig setup body) = (if lib.is_skip setup.deref = 1 then lib.goals_append (lib.close_each_e pp f inv_obligs.deref) (lib.goals_append (lib.wp_stm pp (lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop) body.deref) (lib.goals_append (lib.close_each_e pp (lib.frame_after pp (lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop) body.deref) inv_obligs_exit.deref) (lib.GoalList.Cons (Tactus.Box.mk (lib.close_e pp (lib.frame_after pp (lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop) body.deref) decrease_oblig)) (Tactus.Box.mk lib.GoalList.Nil)))) else lib.goals_append (lib.close_each_e pp f inv_obligs.deref) (lib.goals_append (lib.wp_stm pp (lib.frame_append (lib.loop_telescope_base f inv_hyps.deref binders.deref binder_bounds.deref) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup.deref) (lib.goals_append (lib.close_each_e pp (lib.frame_append (lib.frame_after pp (lib.frame_append (lib.loop_telescope_base f inv_hyps.deref binders.deref binder_bounds.deref) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup.deref) (lib.FrameList.FHyp cond_name break_guard_ann (Tactus.Box.mk lib.FrameList.FNil))) inv_obligs_break.deref) (lib.goals_append (lib.wp_stm pp (lib.frame_append (lib.frame_after pp (lib.frame_append (lib.loop_telescope_base f inv_hyps.deref binders.deref binder_bounds.deref) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup.deref) (lib.FrameList.FHyp cond_name neg_neg_cond_ann (Tactus.Box.mk lib.FrameList.FNil))) body.deref) (lib.goals_append (lib.close_each_e pp (lib.frame_after pp (lib.frame_append (lib.frame_after pp (lib.frame_append (lib.loop_telescope_base f inv_hyps.deref binders.deref binder_bounds.deref) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup.deref) (lib.FrameList.FHyp cond_name neg_neg_cond_ann (Tactus.Box.mk lib.FrameList.FNil))) body.deref) inv_obligs_exit.deref) (lib.goals_append (lib.GoalList.Cons (Tactus.Box.mk (lib.close_e pp (lib.frame_after pp (lib.frame_append (lib.frame_after pp (lib.frame_append (lib.loop_telescope_base f inv_hyps.deref binders.deref binder_bounds.deref) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup.deref) (lib.FrameList.FHyp cond_name neg_neg_cond_ann (Tactus.Box.mk lib.FrameList.FNil))) body.deref) decrease_oblig)) (Tactus.Box.mk lib.GoalList.Nil)) (lib.wp_stm pp (lib.loop_telescope_base f inv_hyps.deref binders.deref binder_bounds.deref) setup.deref)))))))⟧
-- leaf 54: ⟦lib.wp_stm⟧
-- leaf 55: ⟦lib.GoalList⟧
-- leaf 56: ⟦lib.StmData⟧

@[reducible] def cert_u_wp_loop_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk (lib.BinderList.Cons 4 5 (Tactus.Box.mk (lib.BinderList.Cons 6 7 (Tactus.Box.mk (lib.BinderList.Cons 8 7 (Tactus.Box.mk (lib.BinderList.Cons 9 7 (Tactus.Box.mk (lib.BinderList.Cons 10 5 (Tactus.Box.mk (lib.BinderList.Cons 11 12 (Tactus.Box.mk (lib.BinderList.Cons 13 14 (Tactus.Box.mk (lib.BinderList.Cons 17 14 (Tactus.Box.mk (lib.BinderList.Cons 20 14 (Tactus.Box.mk (lib.BinderList.Cons 23 14 (Tactus.Box.mk (lib.BinderList.Cons 26 14 (Tactus.Box.mk (lib.BinderList.Cons 29 14 (Tactus.Box.mk (lib.BinderList.Cons 32 14 (Tactus.Box.mk (lib.BinderList.Cons 35 14 (Tactus.Box.mk (lib.BinderList.Cons 38 14 (Tactus.Box.mk (lib.BinderList.Cons 41 14 (Tactus.Box.mk (lib.BinderList.Cons 44 14 (Tactus.Box.mk (lib.BinderList.Cons 47 48 (Tactus.Box.mk (lib.BinderList.Cons 49 50 (Tactus.Box.mk (lib.BinderList.Cons 51 50 (Tactus.Box.mk lib.BinderList.Nil)))))))))))))))))))))))))))))))))))))))))))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.Bound 16 15 (Tactus.Box.mk (lib.ParamBoundList.Bound 19 18 (Tactus.Box.mk (lib.ParamBoundList.Bound 22 21 (Tactus.Box.mk (lib.ParamBoundList.Bound 25 24 (Tactus.Box.mk (lib.ParamBoundList.Bound 28 27 (Tactus.Box.mk (lib.ParamBoundList.Bound 31 30 (Tactus.Box.mk (lib.ParamBoundList.Bound 34 33 (Tactus.Box.mk (lib.ParamBoundList.Bound 37 36 (Tactus.Box.mk (lib.ParamBoundList.Bound 40 39 (Tactus.Box.mk (lib.ParamBoundList.Bound 43 42 (Tactus.Box.mk (lib.ParamBoundList.Bound 46 45 (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))))))))))))))))))))))))))))))))))))))))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 52 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 1)

@[reducible] def cert_u_wp_loop_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 53 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_wp_loop_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_wp_loop_at_lib_5304_13_1
@[reducible] def cert_u_wp_loop_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.All 4 5 (Tactus.Box.mk (lib.GoalData.All 6 7 (Tactus.Box.mk (lib.GoalData.All 8 7 (Tactus.Box.mk (lib.GoalData.All 9 7 (Tactus.Box.mk (lib.GoalData.All 10 5 (Tactus.Box.mk (lib.GoalData.All 11 12 (Tactus.Box.mk (lib.GoalData.All 13 14 (Tactus.Box.mk (lib.GoalData.All 16 15 (Tactus.Box.mk (lib.GoalData.All 17 14 (Tactus.Box.mk (lib.GoalData.All 19 18 (Tactus.Box.mk (lib.GoalData.All 20 14 (Tactus.Box.mk (lib.GoalData.All 22 21 (Tactus.Box.mk (lib.GoalData.All 23 14 (Tactus.Box.mk (lib.GoalData.All 25 24 (Tactus.Box.mk (lib.GoalData.All 26 14 (Tactus.Box.mk (lib.GoalData.All 28 27 (Tactus.Box.mk (lib.GoalData.All 29 14 (Tactus.Box.mk (lib.GoalData.All 31 30 (Tactus.Box.mk (lib.GoalData.All 32 14 (Tactus.Box.mk (lib.GoalData.All 34 33 (Tactus.Box.mk (lib.GoalData.All 35 14 (Tactus.Box.mk (lib.GoalData.All 37 36 (Tactus.Box.mk (lib.GoalData.All 38 14 (Tactus.Box.mk (lib.GoalData.All 40 39 (Tactus.Box.mk (lib.GoalData.All 41 14 (Tactus.Box.mk (lib.GoalData.All 43 42 (Tactus.Box.mk (lib.GoalData.All 44 14 (Tactus.Box.mk (lib.GoalData.All 46 45 (Tactus.Box.mk (lib.GoalData.All 47 48 (Tactus.Box.mk (lib.GoalData.All 49 50 (Tactus.Box.mk (lib.GoalData.All 51 50 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 53))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_wp_loop_goals = 1 := by decide

-- ── W4a in-gate bridge (bootstrap-38) ──
set_option maxRecDepth 8000
example : lib.goals_eq (lib.ref_wp cert_u_wp_loop_ctx cert_u_wp_loop_sst) cert_u_wp_loop_goals = 1 := by decide
