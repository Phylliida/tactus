import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_wp_aqnl`
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
-- leaf 4: ⟦b⟧
-- leaf 5: ⟦Tactus.Box lib.StmData⟧
-- leaf 6: ⟦tq⟧
-- leaf 7: ⟦lib.RawExp⟧
-- leaf 8: ⟦lib.wp_stm pp f (lib.StmData.AssertQueryNl b tq) = lib.goals_append (lib.wp_stm pp (lib.strip_hyps f) b) (lib.GoalList.Cons (Tactus.Box.mk (lib.close_e pp (lib.frame_after pp (lib.strip_hyps f) b) tq)) (Tactus.Box.mk lib.GoalList.Nil))⟧
-- leaf 9: ⟦/- @rust:tactus-core/lib.rs:5270:13 -/ lib.wp_stm pp f (lib.StmData.AssertQueryNl b tq) = lib.goals_append (lib.wp_stm pp (lib.strip_hyps f) b.deref) (lib.GoalList.Cons (Tactus.Box.mk (lib.close_e pp (lib.frame_after pp (lib.strip_hyps f) b.deref) tq)) (Tactus.Box.mk lib.GoalList.Nil))⟧
-- leaf 10: ⟦lib.wp_stm⟧
-- leaf 11: ⟦lib.GoalList⟧
-- leaf 12: ⟦lib.StmData⟧

@[reducible] def cert_u_wp_aqnl_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk (lib.BinderList.Cons 4 5 (Tactus.Box.mk (lib.BinderList.Cons 6 7 (Tactus.Box.mk lib.BinderList.Nil)))))))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 8 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 1)

@[reducible] def cert_u_wp_aqnl_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 9 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_wp_aqnl_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_wp_aqnl_at_lib_5270_13_1
@[reducible] def cert_u_wp_aqnl_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.All 4 5 (Tactus.Box.mk (lib.GoalData.All 6 7 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 9))))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_wp_aqnl_goals = 1 := by decide
