import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_esf_loop`
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
-- leaf 10: ⟦inv_hyps⟧
-- leaf 11: ⟦Tactus.Box lib.BinderList⟧
-- leaf 12: ⟦inv_obligs⟧
-- leaf 13: ⟦Tactus.Box lib.RawExpList⟧
-- leaf 14: ⟦inv_obligs_exit⟧
-- leaf 15: ⟦inv_obligs_break⟧
-- leaf 16: ⟦binders⟧
-- leaf 17: ⟦binder_bounds⟧
-- leaf 18: ⟦Tactus.Box lib.ParamBoundList⟧
-- leaf 19: ⟦cond_name⟧
-- leaf 20: ⟦Int⟧
-- leaf 21: ⟦0 ≤ cond_name ∧ cond_name < 18446744073709551616⟧
-- leaf 22: ⟦h_cond_name_bound⟧
-- leaf 23: ⟦cond_ann⟧
-- leaf 24: ⟦0 ≤ cond_ann ∧ cond_ann < 18446744073709551616⟧
-- leaf 25: ⟦h_cond_ann_bound⟧
-- leaf 26: ⟦neg_cond_ann⟧
-- leaf 27: ⟦0 ≤ neg_cond_ann ∧ neg_cond_ann < 18446744073709551616⟧
-- leaf 28: ⟦h_neg_cond_ann_bound⟧
-- leaf 29: ⟦neg_neg_cond_ann⟧
-- leaf 30: ⟦0 ≤ neg_neg_cond_ann ∧ neg_neg_cond_ann < 18446744073709551616⟧
-- leaf 31: ⟦h_neg_neg_cond_ann_bound⟧
-- leaf 32: ⟦break_guard_ann⟧
-- leaf 33: ⟦0 ≤ break_guard_ann ∧ break_guard_ann < 18446744073709551616⟧
-- leaf 34: ⟦h_break_guard_ann_bound⟧
-- leaf 35: ⟦break_use_ann⟧
-- leaf 36: ⟦0 ≤ break_use_ann ∧ break_use_ann < 18446744073709551616⟧
-- leaf 37: ⟦h_break_use_ann_bound⟧
-- leaf 38: ⟦d_old_name⟧
-- leaf 39: ⟦0 ≤ d_old_name ∧ d_old_name < 18446744073709551616⟧
-- leaf 40: ⟦h_d_old_name_bound⟧
-- leaf 41: ⟦d_old_ty⟧
-- leaf 42: ⟦0 ≤ d_old_ty ∧ d_old_ty < 18446744073709551616⟧
-- leaf 43: ⟦h_d_old_ty_bound⟧
-- leaf 44: ⟦d_old_val⟧
-- leaf 45: ⟦0 ≤ d_old_val ∧ d_old_val < 18446744073709551616⟧
-- leaf 46: ⟦h_d_old_val_bound⟧
-- leaf 47: ⟦d_old_eq_name⟧
-- leaf 48: ⟦0 ≤ d_old_eq_name ∧ d_old_eq_name < 18446744073709551616⟧
-- leaf 49: ⟦h_d_old_eq_name_bound⟧
-- leaf 50: ⟦d_old_eq_prop⟧
-- leaf 51: ⟦0 ≤ d_old_eq_prop ∧ d_old_eq_prop < 18446744073709551616⟧
-- leaf 52: ⟦h_d_old_eq_prop_bound⟧
-- leaf 53: ⟦decrease_oblig⟧
-- leaf 54: ⟦lib.RawExp⟧
-- leaf 55: ⟦setup⟧
-- leaf 56: ⟦Tactus.Box lib.StmData⟧
-- leaf 57: ⟦body⟧
-- leaf 58: ⟦∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.Loop inv_hyps inv_obligs inv_obligs_exit inv_obligs_break binders binder_bounds cond_name cond_ann neg_cond_ann neg_neg_cond_ann break_guard_ann break_use_ann d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop decrease_oblig setup body) st = (if lib.is_skip setup = 1 then ((lib.close_sem_obligs pp hp he lv f st inv_obligs ∧ lib.exec_safe_f pp hp he lv (lib.loop_maintain_frame f inv_hyps binders binder_bounds cond_name cond_ann d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop) body st) ∧ lib.close_sem_obligs pp hp he lv (lib.frame_after pp (lib.loop_maintain_frame f inv_hyps binders binder_bounds cond_name cond_ann d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop) body) st inv_obligs_exit) ∧ lib.close_sem_e pp hp he lv (lib.frame_after pp (lib.loop_maintain_frame f inv_hyps binders binder_bounds cond_name cond_ann d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop) body) st decrease_oblig else (((((lib.close_sem_obligs pp hp he lv f st inv_obligs ∧ lib.exec_safe_f pp hp he lv (lib.frame_append (lib.loop_telescope_base f inv_hyps binders binder_bounds) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup st) ∧ lib.close_sem_obligs pp hp he lv (lib.frame_append (lib.frame_after pp (lib.frame_append (lib.loop_telescope_base f inv_hyps binders binder_bounds) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup) (lib.FrameList.FHyp cond_name break_guard_ann (Tactus.Box.mk lib.FrameList.FNil))) st inv_obligs_break) ∧ lib.exec_safe_f pp hp he lv (lib.frame_append (lib.frame_after pp (lib.frame_append (lib.loop_telescope_base f inv_hyps binders binder_bounds) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup) (lib.FrameList.FHyp cond_name neg_neg_cond_ann (Tactus.Box.mk lib.FrameList.FNil))) body st) ∧ lib.close_sem_obligs pp hp he lv (lib.frame_after pp (lib.frame_append (lib.frame_after pp (lib.frame_append (lib.loop_telescope_base f inv_hyps binders binder_bounds) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup) (lib.FrameList.FHyp cond_name neg_neg_cond_ann (Tactus.Box.mk lib.FrameList.FNil))) body) st inv_obligs_exit) ∧ lib.close_sem_e pp hp he lv (lib.frame_after pp (lib.frame_append (lib.frame_after pp (lib.frame_append (lib.loop_telescope_base f inv_hyps binders binder_bounds) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup) (lib.FrameList.FHyp cond_name neg_neg_cond_ann (Tactus.Box.mk lib.FrameList.FNil))) body) st decrease_oblig) ∧ lib.exec_safe_f pp hp he lv (lib.loop_telescope_base f inv_hyps binders binder_bounds) setup st)⟧
-- leaf 59: ⟦/- @rust:tactus-core/lib.rs:4981:13 -/ ∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.Loop inv_hyps inv_obligs inv_obligs_exit inv_obligs_break binders binder_bounds cond_name cond_ann neg_cond_ann neg_neg_cond_ann break_guard_ann break_use_ann d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop decrease_oblig setup body) st = (if lib.is_skip setup.deref = 1 then ((lib.close_sem_obligs pp hp he lv f st inv_obligs.deref ∧ lib.exec_safe_f pp hp he lv (lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop) body.deref st) ∧ lib.close_sem_obligs pp hp he lv (lib.frame_after pp (lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop) body.deref) st inv_obligs_exit.deref) ∧ lib.close_sem_e pp hp he lv (lib.frame_after pp (lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop) body.deref) st decrease_oblig else (((((lib.close_sem_obligs pp hp he lv f st inv_obligs.deref ∧ lib.exec_safe_f pp hp he lv (lib.frame_append (lib.loop_telescope_base f inv_hyps.deref binders.deref binder_bounds.deref) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup.deref st) ∧ lib.close_sem_obligs pp hp he lv (lib.frame_append (lib.frame_after pp (lib.frame_append (lib.loop_telescope_base f inv_hyps.deref binders.deref binder_bounds.deref) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup.deref) (lib.FrameList.FHyp cond_name break_guard_ann (Tactus.Box.mk lib.FrameList.FNil))) st inv_obligs_break.deref) ∧ lib.exec_safe_f pp hp he lv (lib.frame_append (lib.frame_after pp (lib.frame_append (lib.loop_telescope_base f inv_hyps.deref binders.deref binder_bounds.deref) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup.deref) (lib.FrameList.FHyp cond_name neg_neg_cond_ann (Tactus.Box.mk lib.FrameList.FNil))) body.deref st) ∧ lib.close_sem_obligs pp hp he lv (lib.frame_after pp (lib.frame_append (lib.frame_after pp (lib.frame_append (lib.loop_telescope_base f inv_hyps.deref binders.deref binder_bounds.deref) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup.deref) (lib.FrameList.FHyp cond_name neg_neg_cond_ann (Tactus.Box.mk lib.FrameList.FNil))) body.deref) st inv_obligs_exit.deref) ∧ lib.close_sem_e pp hp he lv (lib.frame_after pp (lib.frame_append (lib.frame_after pp (lib.frame_append (lib.loop_telescope_base f inv_hyps.deref binders.deref binder_bounds.deref) (lib.d_old_frame d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop)) setup.deref) (lib.FrameList.FHyp cond_name neg_neg_cond_ann (Tactus.Box.mk lib.FrameList.FNil))) body.deref) st decrease_oblig) ∧ lib.exec_safe_f pp hp he lv (lib.loop_telescope_base f inv_hyps.deref binders.deref binder_bounds.deref) setup.deref st)⟧

@[reducible] def cert_u_esf_loop_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk (lib.BinderList.Cons 4 5 (Tactus.Box.mk (lib.BinderList.Cons 6 7 (Tactus.Box.mk (lib.BinderList.Cons 8 9 (Tactus.Box.mk (lib.BinderList.Cons 10 11 (Tactus.Box.mk (lib.BinderList.Cons 12 13 (Tactus.Box.mk (lib.BinderList.Cons 14 13 (Tactus.Box.mk (lib.BinderList.Cons 15 13 (Tactus.Box.mk (lib.BinderList.Cons 16 11 (Tactus.Box.mk (lib.BinderList.Cons 17 18 (Tactus.Box.mk (lib.BinderList.Cons 19 20 (Tactus.Box.mk (lib.BinderList.Cons 23 20 (Tactus.Box.mk (lib.BinderList.Cons 26 20 (Tactus.Box.mk (lib.BinderList.Cons 29 20 (Tactus.Box.mk (lib.BinderList.Cons 32 20 (Tactus.Box.mk (lib.BinderList.Cons 35 20 (Tactus.Box.mk (lib.BinderList.Cons 38 20 (Tactus.Box.mk (lib.BinderList.Cons 41 20 (Tactus.Box.mk (lib.BinderList.Cons 44 20 (Tactus.Box.mk (lib.BinderList.Cons 47 20 (Tactus.Box.mk (lib.BinderList.Cons 50 20 (Tactus.Box.mk (lib.BinderList.Cons 53 54 (Tactus.Box.mk (lib.BinderList.Cons 55 56 (Tactus.Box.mk (lib.BinderList.Cons 57 56 (Tactus.Box.mk lib.BinderList.Nil)))))))))))))))))))))))))))))))))))))))))))))))))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.Bound 22 21 (Tactus.Box.mk (lib.ParamBoundList.Bound 25 24 (Tactus.Box.mk (lib.ParamBoundList.Bound 28 27 (Tactus.Box.mk (lib.ParamBoundList.Bound 31 30 (Tactus.Box.mk (lib.ParamBoundList.Bound 34 33 (Tactus.Box.mk (lib.ParamBoundList.Bound 37 36 (Tactus.Box.mk (lib.ParamBoundList.Bound 40 39 (Tactus.Box.mk (lib.ParamBoundList.Bound 43 42 (Tactus.Box.mk (lib.ParamBoundList.Bound 46 45 (Tactus.Box.mk (lib.ParamBoundList.Bound 49 48 (Tactus.Box.mk (lib.ParamBoundList.Bound 52 51 (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))))))))))))))))))))))))))))))))))))))))))))))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 58 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 0)

@[reducible] def cert_u_esf_loop_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 59 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_esf_loop_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_esf_loop_at_lib_4981_13_1
@[reducible] def cert_u_esf_loop_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.All 4 5 (Tactus.Box.mk (lib.GoalData.All 6 7 (Tactus.Box.mk (lib.GoalData.All 8 9 (Tactus.Box.mk (lib.GoalData.All 10 11 (Tactus.Box.mk (lib.GoalData.All 12 13 (Tactus.Box.mk (lib.GoalData.All 14 13 (Tactus.Box.mk (lib.GoalData.All 15 13 (Tactus.Box.mk (lib.GoalData.All 16 11 (Tactus.Box.mk (lib.GoalData.All 17 18 (Tactus.Box.mk (lib.GoalData.All 19 20 (Tactus.Box.mk (lib.GoalData.All 22 21 (Tactus.Box.mk (lib.GoalData.All 23 20 (Tactus.Box.mk (lib.GoalData.All 25 24 (Tactus.Box.mk (lib.GoalData.All 26 20 (Tactus.Box.mk (lib.GoalData.All 28 27 (Tactus.Box.mk (lib.GoalData.All 29 20 (Tactus.Box.mk (lib.GoalData.All 31 30 (Tactus.Box.mk (lib.GoalData.All 32 20 (Tactus.Box.mk (lib.GoalData.All 34 33 (Tactus.Box.mk (lib.GoalData.All 35 20 (Tactus.Box.mk (lib.GoalData.All 37 36 (Tactus.Box.mk (lib.GoalData.All 38 20 (Tactus.Box.mk (lib.GoalData.All 40 39 (Tactus.Box.mk (lib.GoalData.All 41 20 (Tactus.Box.mk (lib.GoalData.All 43 42 (Tactus.Box.mk (lib.GoalData.All 44 20 (Tactus.Box.mk (lib.GoalData.All 46 45 (Tactus.Box.mk (lib.GoalData.All 47 20 (Tactus.Box.mk (lib.GoalData.All 49 48 (Tactus.Box.mk (lib.GoalData.All 50 20 (Tactus.Box.mk (lib.GoalData.All 52 51 (Tactus.Box.mk (lib.GoalData.All 53 54 (Tactus.Box.mk (lib.GoalData.All 55 56 (Tactus.Box.mk (lib.GoalData.All 57 56 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 59))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_esf_loop_goals = 1 := by decide

-- ── W4a in-gate bridge (bootstrap-38) ──
set_option maxRecDepth 8000
example : lib.goals_eq (lib.ref_wp cert_u_esf_loop_ctx cert_u_esf_loop_sst) cert_u_esf_loop_goals = 1 := by decide
