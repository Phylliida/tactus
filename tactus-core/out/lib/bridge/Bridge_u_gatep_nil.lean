import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_gatep_nil`
-- tactus-core-vocab-hash: unvendored
-- Stage A certifies statement ASSEMBLY (binder telescopes, hypothesis
-- order, let-chains, obligation multiplicity/order). It does NOT certify
-- leaf rendering (stage B/W6), the serializer (it is the TCB), the
-- frontend, or SST-semantics adequacy (W5). Leaves below are opaque ids;
-- a stage-A pass coexisting with a leaf-renderer bug is possible.

-- ── leaf table ──────────────────────────────────────────────
-- leaf 0: ⟦pp⟧
-- leaf 1: ⟦lib.LeafList⟧
-- leaf 2: ⟦lib.has_poisoned_hyp pp lib.FrameList.FNil = 0⟧
-- leaf 3: ⟦/- @rust:tactus-core/lib.rs:5064:13 -/ lib.has_poisoned_hyp pp lib.FrameList.FNil = 0⟧
-- leaf 4: ⟦lib.has_poisoned_hyp⟧
-- leaf 5: ⟦lib.FrameList⟧

@[reducible] def cert_u_gatep_nil_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 2 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 1)

@[reducible] def cert_u_gatep_nil_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 3 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_gatep_nil_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_gatep_nil_at_lib_5064_13_1
@[reducible] def cert_u_gatep_nil_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 3))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_gatep_nil_goals = 1 := by decide

-- ── W4a in-gate bridge (bootstrap-38) ──
set_option maxRecDepth 8000
example : lib.goals_eq (lib.ref_wp cert_u_gatep_nil_ctx cert_u_gatep_nil_sst) cert_u_gatep_nil_goals = 1 := by decide
