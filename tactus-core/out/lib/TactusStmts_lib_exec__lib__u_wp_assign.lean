import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_assign_at_lib_4444_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList) (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (rhs : Int) (h_rhs_bound : 0 ≤ rhs ∧ rhs < 18446744073709551616), /- @rust:tactus-core/lib.rs:4444:13 -/ lib.wp_stm f (lib.StmData.Assign x rhs) = lib.GoalList.Nil
