import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_fa_deadend_at_lib_6406_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (f : lib.FrameList) (bs : Tactus.Box lib.BinderList) (bds : Tactus.Box lib.ParamBoundList) (b : Tactus.Box lib.StmData), /- @rust:tactus-core/lib.rs:6406:13 -/ lib.frame_after pp f (lib.StmData.DeadEnd bs bds b) = f
