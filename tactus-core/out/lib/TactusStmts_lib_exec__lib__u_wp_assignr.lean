import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_assignr_at_lib_4549_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList) (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (v : Int) (h_v_bound : 0 ≤ v ∧ v < 18446744073709551616), /- @rust:tactus-core/lib.rs:4549:13 -/ lib.wp_stm f (lib.StmData.AssignR x v) = lib.GoalList.Nil
