import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_mvf_nil_nil`
-- tactus-core-vocab-hash: unvendored
-- Stage A certifies statement ASSEMBLY (binder telescopes, hypothesis
-- order, let-chains, obligation multiplicity/order). It does NOT certify
-- leaf rendering (stage B/W6), the serializer (it is the TCB), the
-- frontend, or SST-semantics adequacy (W5). Leaves below are opaque ids;
-- a stage-A pass coexisting with a leaf-renderer bug is possible.

-- ── leaf table ──────────────────────────────────────────────
-- leaf 0: ⟦lib.mod_var_frames lib.BinderList.Nil lib.ParamBoundList.Nil = lib.FrameList.FNil⟧
-- leaf 1: ⟦/- @rust:tactus-core/lib.rs:6419:13 -/ lib.mod_var_frames lib.BinderList.Nil lib.ParamBoundList.Nil = lib.FrameList.FNil⟧
-- leaf 2: ⟦lib.mod_var_frames⟧
-- leaf 3: ⟦lib.FrameList⟧
-- leaf 4: ⟦lib.ParamBoundList⟧

@[reducible] def cert_u_mvf_nil_nil_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil lib.BinderList.Nil lib.ParamBoundList.Nil lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 0 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 1)

@[reducible] def cert_u_mvf_nil_nil_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_mvf_nil_nil_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_mvf_nil_nil_at_lib_6419_13_1
@[reducible] def cert_u_mvf_nil_nil_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 1))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_mvf_nil_nil_goals = 1 := by decide

-- ── W4a in-gate bridge (bootstrap-38) ──
set_option maxRecDepth 8000
example : lib.goals_eq (lib.ref_wp cert_u_mvf_nil_nil_ctx cert_u_mvf_nil_nil_sst) cert_u_mvf_nil_nil_goals = 1 := by decide
