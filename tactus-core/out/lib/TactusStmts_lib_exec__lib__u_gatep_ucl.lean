import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_gatep_ucl_at_lib_5067_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (t : Tactus.Box lib.FrameList), /- @rust:tactus-core/lib.rs:5067:13 -/ lib.has_poisoned_hyp pp (lib.FrameList.FUserCloser t) = lib.has_poisoned_hyp pp t.deref
