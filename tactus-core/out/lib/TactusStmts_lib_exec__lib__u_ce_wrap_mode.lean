import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_ce_wrap_mode_at_lib_3686_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList) (ob : lib.RawExp) (h_req0 : lib.has_plain_flet f = 1), /- @rust:lib.rs:3686:13 -/ lib.close_e f ob = lib.close_e_wrap f ob
