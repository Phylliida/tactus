import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_if_at_lib_3476_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList) (c : Int) (h_c_bound : 0 ≤ c ∧ c < 18446744073709551616) (nc : Int) (h_nc_bound : 0 ≤ nc ∧ nc < 18446744073709551616) (t : Tactus.Box lib.StmData) (e : Tactus.Box lib.StmData), /- @rust:lib.rs:3476:13 -/ lib.wp_stm f (lib.StmData.If c nc t e) = lib.goals_append (lib.wp_stm (lib.frame_append f (lib.FrameList.FHyp c (Tactus.Box.mk lib.FrameList.FNil))) t.deref) (lib.wp_stm (lib.frame_append f (lib.FrameList.FHyp nc (Tactus.Box.mk lib.FrameList.FNil))) e.deref)
