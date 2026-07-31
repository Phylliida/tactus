import TactusStmts_lib_exec__lib__ref_wp_mut_preamble_wrap
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem lib.ref_wp_mut_preamble_wrap :
    lib.gate_wrap lib.LeafList.Nil (lib.seed_frame lib.s2_mut_ctx) = 1 ∧ lib.goals_eq (lib.ref_wp lib.s2_mut_ctx (lib.StmData.Assert (lib.atom_ob 9) 0 9 0)) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.Let 4 5 (Tactus.Box.mk (lib.GoalData.Let 0 5 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 9))))))))))) (Tactus.Box.mk lib.GoalList.Nil)) = 1 := by
  decide 
