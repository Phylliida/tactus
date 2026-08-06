import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_esf_ifctor`
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
-- leaf 10: ⟦pos_binders⟧
-- leaf 11: ⟦Tactus.Box lib.BinderList⟧
-- leaf 12: ⟦eq_name⟧
-- leaf 13: ⟦Int⟧
-- leaf 14: ⟦0 ≤ eq_name ∧ eq_name < 18446744073709551616⟧
-- leaf 15: ⟦h_eq_name_bound⟧
-- leaf 16: ⟦eq_prop⟧
-- leaf 17: ⟦0 ≤ eq_prop ∧ eq_prop < 18446744073709551616⟧
-- leaf 18: ⟦h_eq_prop_bound⟧
-- leaf 19: ⟦neg_name⟧
-- leaf 20: ⟦0 ≤ neg_name ∧ neg_name < 18446744073709551616⟧
-- leaf 21: ⟦h_neg_name_bound⟧
-- leaf 22: ⟦neg_prop⟧
-- leaf 23: ⟦0 ≤ neg_prop ∧ neg_prop < 18446744073709551616⟧
-- leaf 24: ⟦h_neg_prop_bound⟧
-- leaf 25: ⟦thn⟧
-- leaf 26: ⟦Tactus.Box lib.StmData⟧
-- leaf 27: ⟦els⟧
-- leaf 28: ⟦∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.IfCtor pos_binders eq_name eq_prop neg_name neg_prop thn els) st = (lib.exec_safe_f pp hp he lv (lib.frame_append f (lib.ctor_pos_frame pos_binders eq_name eq_prop)) thn st ∧ lib.exec_safe_f pp hp he lv (lib.frame_append f (lib.FrameList.FHyp neg_name neg_prop (Tactus.Box.mk lib.FrameList.FNil))) els st)⟧
-- leaf 29: ⟦/- @rust:tactus-core/lib.rs:4959:13 -/ ∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.IfCtor pos_binders eq_name eq_prop neg_name neg_prop thn els) st = (lib.exec_safe_f pp hp he lv (lib.frame_append f (lib.ctor_pos_frame pos_binders.deref eq_name eq_prop)) thn.deref st ∧ lib.exec_safe_f pp hp he lv (lib.frame_append f (lib.FrameList.FHyp neg_name neg_prop (Tactus.Box.mk lib.FrameList.FNil))) els.deref st)⟧

@[reducible] def cert_u_esf_ifctor_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk (lib.BinderList.Cons 4 5 (Tactus.Box.mk (lib.BinderList.Cons 6 7 (Tactus.Box.mk (lib.BinderList.Cons 8 9 (Tactus.Box.mk (lib.BinderList.Cons 10 11 (Tactus.Box.mk (lib.BinderList.Cons 12 13 (Tactus.Box.mk (lib.BinderList.Cons 16 13 (Tactus.Box.mk (lib.BinderList.Cons 19 13 (Tactus.Box.mk (lib.BinderList.Cons 22 13 (Tactus.Box.mk (lib.BinderList.Cons 25 26 (Tactus.Box.mk (lib.BinderList.Cons 27 26 (Tactus.Box.mk lib.BinderList.Nil)))))))))))))))))))))))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.Bound 15 14 (Tactus.Box.mk (lib.ParamBoundList.Bound 18 17 (Tactus.Box.mk (lib.ParamBoundList.Bound 21 20 (Tactus.Box.mk (lib.ParamBoundList.Bound 24 23 (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))))))))))))))))))))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 28 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 0)

@[reducible] def cert_u_esf_ifctor_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 29 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_esf_ifctor_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_esf_ifctor_at_lib_4959_13_1
@[reducible] def cert_u_esf_ifctor_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.All 4 5 (Tactus.Box.mk (lib.GoalData.All 6 7 (Tactus.Box.mk (lib.GoalData.All 8 9 (Tactus.Box.mk (lib.GoalData.All 10 11 (Tactus.Box.mk (lib.GoalData.All 12 13 (Tactus.Box.mk (lib.GoalData.All 15 14 (Tactus.Box.mk (lib.GoalData.All 16 13 (Tactus.Box.mk (lib.GoalData.All 18 17 (Tactus.Box.mk (lib.GoalData.All 19 13 (Tactus.Box.mk (lib.GoalData.All 21 20 (Tactus.Box.mk (lib.GoalData.All 22 13 (Tactus.Box.mk (lib.GoalData.All 24 23 (Tactus.Box.mk (lib.GoalData.All 25 26 (Tactus.Box.mk (lib.GoalData.All 27 26 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 29))))))))))))))))))))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_esf_ifctor_goals = 1 := by decide
