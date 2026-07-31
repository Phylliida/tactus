import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def lib.probe_wp_stm_stmt : Prop :=
  lib.goal_count (lib.wp_stm lib.LeafList.Nil lib.FrameList.FNil (lib.StmData.Assert (lib.atom_ob 9) 0 9 0)) = 1 ∧ lib.goal_count (lib.wp_stm lib.LeafList.Nil lib.FrameList.FNil lib.StmData.Skip) = 0
