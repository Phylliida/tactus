import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `deadend_scope_binder_pin`
-- tactus-core-vocab-hash: unvendored
-- Stage A certifies statement ASSEMBLY (binder telescopes, hypothesis
-- order, let-chains, obligation multiplicity/order). It does NOT certify
-- leaf rendering (stage B/W6), the serializer (it is the TCB), the
-- frontend, or SST-semantics adequacy (W5). Leaves below are opaque ids;
-- a stage-A pass coexisting with a leaf-renderer bug is possible.

-- ── leaf table ──────────────────────────────────────────────
-- leaf 0: ⟦lib.wp_stm lib.LeafList.Nil lib.FrameList.FNil (lib.StmData.DeadEnd (Tactus.Box.mk (lib.BinderList.Cons 15 16 (Tactus.Box.mk lib.BinderList.Nil))) (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil))) (Tactus.Box.mk (lib.StmData.Assert (lib.RawExp.Lit 7 lib.TypData.TyInt) 0 0))) = lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 15 16 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Lit 7))))) (Tactus.Box.mk lib.GoalList.Nil)⟧
-- leaf 1: ⟦/- @rust:tactus-core/lib.rs:5260:9 -/ lib.wp_stm lib.LeafList.Nil lib.FrameList.FNil (lib.StmData.DeadEnd (Tactus.Box.mk (lib.BinderList.Cons 15 16 (Tactus.Box.mk lib.BinderList.Nil))) (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil))) (Tactus.Box.mk (lib.StmData.Assert (lib.RawExp.Lit 7 lib.TypData.TyInt) 0 0))) = lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 15 16 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Lit 7))))) (Tactus.Box.mk lib.GoalList.Nil)⟧
-- leaf 2: ⟦lib.wp_stm⟧
-- leaf 3: ⟦lib.GoalList⟧
-- leaf 4: ⟦lib.StmData⟧

@[reducible] def cert_deadend_scope_binder_pin_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil lib.BinderList.Nil lib.ParamBoundList.Nil lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 0 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 1)

@[reducible] def cert_deadend_scope_binder_pin_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_deadend_scope_binder_pin_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_deadend_scope_binder_pin_at_lib_5260_9_1
@[reducible] def cert_deadend_scope_binder_pin_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 1))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_deadend_scope_binder_pin_goals = 1 := by decide
