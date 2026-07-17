import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_assume_at_lib_3458_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList) (e : Int) (h_e_bound : 0 ≤ e ∧ e < 18446744073709551616), /- @rust:lib.rs:3458:13 -/ lib.wp_stm f (lib.StmData.Assume e) = lib.GoalList.Nil
