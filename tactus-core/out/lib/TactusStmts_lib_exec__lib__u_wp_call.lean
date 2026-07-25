import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_call_at_lib_4552_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList) (reqs : Tactus.Box lib.RawExpList) (post : Tactus.Box lib.FrameList), /- @rust:tactus-core/lib.rs:4552:13 -/ lib.wp_stm f (lib.StmData.Call reqs post) = lib.close_each_e f reqs.deref
