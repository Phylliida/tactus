import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_gapp_nil_at_lib_4430_13_1_stmt : Prop :=
  ∀ (b : lib.GoalList), /- @rust:tactus-core/lib.rs:4430:13 -/ lib.goals_append lib.GoalList.Nil b = b
