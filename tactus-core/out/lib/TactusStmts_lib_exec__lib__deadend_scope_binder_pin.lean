import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_deadend_scope_binder_pin_at_lib_5260_9_1_stmt : Prop :=
  /- @rust:tactus-core/lib.rs:5260:9 -/ lib.wp_stm lib.LeafList.Nil lib.FrameList.FNil (lib.StmData.DeadEnd (Tactus.Box.mk (lib.BinderList.Cons 15 16 (Tactus.Box.mk lib.BinderList.Nil))) (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil))) (Tactus.Box.mk (lib.StmData.Assert (lib.RawExp.Lit 7 lib.TypData.TyInt) 0 0))) = lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 15 16 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Lit 7))))) (Tactus.Box.mk lib.GoalList.Nil)
