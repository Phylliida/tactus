import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_cewl_ucl`
-- tactus-core-vocab-hash: unvendored
-- Stage A certifies statement ASSEMBLY (binder telescopes, hypothesis
-- order, let-chains, obligation multiplicity/order). It does NOT certify
-- leaf rendering (stage B/W6), the serializer (it is the TCB), the
-- frontend, or SST-semantics adequacy (W5). Leaves below are opaque ids;
-- a stage-A pass coexisting with a leaf-renderer bug is possible.

-- ── leaf table ──────────────────────────────────────────────
-- leaf 0: ⟦t⟧
-- leaf 1: ⟦Tactus.Box lib.FrameList⟧
-- leaf 2: ⟦ob⟧
-- leaf 3: ⟦lib.RawExp⟧
-- leaf 4: ⟦lib.close_e_wrap_lead (lib.FrameList.FUserCloser t) ob = lib.close_e_wrap_lead t ob⟧
-- leaf 5: ⟦/- @rust:tactus-core/lib.rs:5163:13 -/ lib.close_e_wrap_lead (lib.FrameList.FUserCloser t) ob = lib.close_e_wrap_lead t.deref ob⟧
-- leaf 6: ⟦lib.close_e_wrap_lead⟧
-- leaf 7: ⟦lib.GoalData⟧
-- leaf 8: ⟦lib.FrameList⟧

@[reducible] def cert_u_cewl_ucl_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk lib.BinderList.Nil)))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 4 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 1)

@[reducible] def cert_u_cewl_ucl_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 5 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_cewl_ucl_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_cewl_ucl_at_lib_5163_13_1
@[reducible] def cert_u_cewl_ucl_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 5))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_cewl_ucl_goals = 1 := by decide

-- ── W4a in-gate bridge (bootstrap-38) ──
set_option maxRecDepth 8000
example : lib.goals_eq (lib.ref_wp cert_u_cewl_ucl_ctx cert_u_cewl_ucl_sst) cert_u_cewl_ucl_goals = 1 := by decide
