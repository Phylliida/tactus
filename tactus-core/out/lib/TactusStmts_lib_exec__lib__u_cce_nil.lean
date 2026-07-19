import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cce_nil_at_lib_3726_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList), /- @rust:lib.rs:3726:13 -/ lib.close_each_e f lib.RawExpList.Nil = lib.GoalList.Nil
