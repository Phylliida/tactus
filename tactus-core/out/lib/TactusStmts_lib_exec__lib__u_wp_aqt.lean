import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_aqt_at_lib_5278_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (f : lib.FrameList) (o : lib.RawExp) (hn : Int) (h_hn_bound : 0 ≤ hn ∧ hn < 18446744073709551616) (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616), /- @rust:tactus-core/lib.rs:5278:13 -/ lib.wp_stm pp f (lib.StmData.AssertQueryTactus o hn h) = lib.GoalList.Cons (Tactus.Box.mk (lib.close_e pp (lib.frame_append f (lib.FrameList.FUserCloser (Tactus.Box.mk lib.FrameList.FNil))) o)) (Tactus.Box.mk lib.GoalList.Nil)
