import TactusStmts_lib_exec__lib__probe_close_e
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem lib.probe_close_e :
    lib.goal_size (lib.close_e lib.FrameList.FNil (lib.atom_ob 9)) = 1 ∧ lib.goal_size (lib.close_e (lib.FrameList.FBind 0 1 (Tactus.Box.mk lib.FrameList.FNil)) (lib.atom_ob 9)) = 2 ∧ lib.goal_eq (lib.close_e lib.FrameList.FNil (lib.atom_ob 9)) (lib.GoalData.LeafE (lib.ExprData.Atom 9)) = 1 ∧ lib.goal_eq (lib.close_e lib.FrameList.FNil (lib.atom_ob 9)) (lib.GoalData.Leaf 9) = 0 := by
  decide 
