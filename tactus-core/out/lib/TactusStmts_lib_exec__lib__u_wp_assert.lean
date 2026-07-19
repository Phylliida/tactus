import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_assert_at_lib_3740_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList) (o : lib.RawExp) (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616), /- @rust:lib.rs:3740:13 -/ lib.wp_stm f (lib.StmData.Assert o h) = lib.GoalList.Cons (Tactus.Box.mk (lib.close_e f o)) (Tactus.Box.mk lib.GoalList.Nil)
