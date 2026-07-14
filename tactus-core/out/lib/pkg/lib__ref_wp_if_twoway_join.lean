import TactusStmts_lib_exec__lib__ref_wp_if_twoway_join
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem lib.ref_wp_if_twoway_join :
    lib.goals_eq (lib.ref_wp lib.cd19_ctx lib.cd19_sst) lib.cd19_goals = 1 ∧ lib.goal_count (lib.ref_wp lib.cd19_ctx lib.cd19_sst) = 4 ∧ lib.goal_eq (lib.gl_head (lib.ref_wp lib.cd19_ctx lib.cd19_sst)) (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.Let 7 0 (Tactus.Box.mk (lib.GoalData.Imp 8 (Tactus.Box.mk (lib.GoalData.Let 10 99 (Tactus.Box.mk (lib.GoalData.Let 6 10 (Tactus.Box.mk (lib.GoalData.Leaf 5))))))))))))) = 0 := by
  decide 
