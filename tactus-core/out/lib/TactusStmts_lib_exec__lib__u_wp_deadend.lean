import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_deadend_at_lib_5250_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (f : lib.FrameList) (bs : Tactus.Box lib.BinderList) (bds : Tactus.Box lib.ParamBoundList) (b : Tactus.Box lib.StmData), /- @rust:tactus-core/lib.rs:5250:13 -/ lib.wp_stm pp f (lib.StmData.DeadEnd bs bds b) = lib.wp_stm pp (lib.frame_append f (lib.mod_var_frames bs.deref bds.deref)) b.deref
