import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_gatep_letr_at_lib_5064_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (v : Int) (h_v_bound : 0 ≤ v ∧ v < 18446744073709551616) (t : Tactus.Box lib.FrameList), /- @rust:tactus-core/lib.rs:5064:13 -/ lib.has_poisoned_hyp pp (lib.FrameList.FLetR x v t) = lib.has_poisoned_hyp pp t.deref
