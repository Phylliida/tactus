import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def lib.probe_close_e_stmt : Prop :=
  lib.goal_size (lib.close_e lib.FrameList.FNil (lib.atom_ob 9)) = 1 ∧ lib.goal_size (lib.close_e (lib.FrameList.FBind 0 1 (Tactus.Box.mk lib.FrameList.FNil)) (lib.atom_ob 9)) = 2 ∧ lib.goal_eq (lib.close_e lib.FrameList.FNil (lib.atom_ob 9)) (lib.GoalData.LeafE (lib.ExprData.Atom 9)) = 1 ∧ lib.goal_eq (lib.close_e lib.FrameList.FNil (lib.atom_ob 9)) (lib.GoalData.Leaf 9) = 0
