import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_fa_assume_at_lib_5381_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList) (e : Int) (h_e_bound : 0 ≤ e ∧ e < 18446744073709551616), /- @rust:tactus-core/lib.rs:5381:13 -/ lib.frame_after f (lib.StmData.Assume 0 e 0) = lib.frame_append f (lib.FrameList.FHyp 0 e 0 (Tactus.Box.mk lib.FrameList.FNil))
