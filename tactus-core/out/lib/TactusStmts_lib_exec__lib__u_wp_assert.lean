import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_assert_at_lib_5058_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList) (o : lib.RawExp) (hn : Int) (h_hn_bound : 0 ≤ hn ∧ hn < 18446744073709551616) (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616) (hpz : Int) (h_hpz_bound : 0 ≤ hpz ∧ hpz < 18446744073709551616), /- @rust:tactus-core/lib.rs:5058:13 -/ lib.wp_stm f (lib.StmData.Assert o hn h hpz) = lib.GoalList.Cons (Tactus.Box.mk (lib.close_e f o)) (Tactus.Box.mk lib.GoalList.Nil)
