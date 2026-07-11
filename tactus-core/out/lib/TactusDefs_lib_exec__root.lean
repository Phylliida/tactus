-- tactus defs part: root (base = machinery + instance closure; one part per source module, SCC-merged; umbrella = interface)
import TactusDefs_lib_exec__base
import TactusPrelude
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
noncomputable def lib.leaf_len (l : lib.LeafList) : Nat :=
  match l with | lib.LeafList.Nil => 0 | lib.LeafList.Cons _h t => 1 + lib.leaf_len t.deref
termination_by structural l
noncomputable def lib.stm_size (s : lib.StmData) : Nat :=
  match s with | lib.StmData.Assert _e => 1 | lib.StmData.Assume _e => 1 | lib.StmData.Assign _d _r => 1 | lib.StmData.Call reqs enss => 1 + lib.leaf_len reqs.deref + lib.leaf_len enss.deref | lib.StmData.DeadEnd b => 1 + lib.stm_size b.deref | lib.StmData.Ret _e => 1 | lib.StmData.If _c t e => 1 + lib.stm_size t.deref + lib.stm_size e.deref | lib.StmData.Loop invs _ body => 1 + lib.leaf_len invs.deref + lib.stm_size body.deref | lib.StmData.Skip => 1 | lib.StmData.Seq a b => 1 + lib.stm_size a.deref + lib.stm_size b.deref
termination_by structural s
noncomputable def lib.goal_size (g : lib.GoalData) : Nat :=
  match g with | lib.GoalData.Leaf _e => 1 | lib.GoalData.Imp _h b => 1 + lib.goal_size b.deref | lib.GoalData.All _x _t b => 1 + lib.goal_size b.deref | lib.GoalData.Let _x _v b => 1 + lib.goal_size b.deref
termination_by structural g
noncomputable def lib.goal_count (gs : lib.GoalList) : Nat :=
  match gs with | lib.GoalList.Nil => 0 | lib.GoalList.Cons _g t => 1 + lib.goal_count t.deref
termination_by structural gs
