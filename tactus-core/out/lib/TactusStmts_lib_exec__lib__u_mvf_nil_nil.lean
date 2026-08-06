import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_mvf_nil_nil_at_lib_6419_13_1_stmt : Prop :=
  /- @rust:tactus-core/lib.rs:6419:13 -/ lib.mod_var_frames lib.BinderList.Nil lib.ParamBoundList.Nil = lib.FrameList.FNil
