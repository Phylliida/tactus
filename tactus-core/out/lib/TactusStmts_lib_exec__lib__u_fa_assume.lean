import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_fa_assume_at_lib_6418_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (f : lib.FrameList) (e : Int) (h_e_bound : 0 ≤ e ∧ e < 18446744073709551616), /- @rust:tactus-core/lib.rs:6418:13 -/ lib.frame_after pp f (lib.StmData.Assume 0 e) = lib.frame_append f (lib.FrameList.FHyp 0 e (Tactus.Box.mk lib.FrameList.FNil))
