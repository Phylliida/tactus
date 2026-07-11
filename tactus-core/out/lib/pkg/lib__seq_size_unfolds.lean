import TactusStmts_lib_exec__lib__seq_size_unfolds
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem lib.seq_size_unfolds :
    lib.stm_size (lib.StmData.Seq (Tactus.Box.mk lib.StmData.Skip) (Tactus.Box.mk lib.StmData.Skip)) = 1 + lib.stm_size lib.StmData.Skip + lib.stm_size lib.StmData.Skip ∧ lib.goal_count (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Leaf 0)) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Leaf 1)) (Tactus.Box.mk lib.GoalList.Nil)))) = 2 := by

  decide
