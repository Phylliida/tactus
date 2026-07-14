import TactusPrelude
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
inductive lib.GoalData where
  | Leaf (val0 : Int)
  | Imp (val0 : Int) (val1 : Tactus.Box lib.GoalData)
  | All (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.GoalData)
  | Let (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.GoalData)
  deriving Inhabited
@[simp] noncomputable def lib.GoalData.height (s : lib.GoalData) : Nat :=
  match s with | lib.GoalData.Leaf _ => 1 | lib.GoalData.Imp _ val1 => 1 + lib.GoalData.height val1.deref | lib.GoalData.All _ _ val2 => 1 + lib.GoalData.height val2.deref | lib.GoalData.Let _ _ val2 => 1 + lib.GoalData.height val2.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
inductive lib.FrameList where
  | FNil
  | FBind (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.FrameList)
  | FHyp (val0 : Int) (val1 : Tactus.Box lib.FrameList)
  | FLet (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.FrameList)
  deriving Inhabited
@[simp] noncomputable def lib.FrameList.height (s : lib.FrameList) : Nat :=
  match s with | lib.FrameList.FNil => 1 | lib.FrameList.FBind _ _ val2 => 1 + lib.FrameList.height val2.deref | lib.FrameList.FHyp _ val1 => 1 + lib.FrameList.height val1.deref | lib.FrameList.FLet _ _ val2 => 1 + lib.FrameList.height val2.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
noncomputable def lib.goal_size (g : lib.GoalData) : Nat :=
  match g with | lib.GoalData.Leaf _e => 1 | lib.GoalData.Imp _h b => 1 + lib.goal_size b.deref | lib.GoalData.All _x _t b => 1 + lib.goal_size b.deref | lib.GoalData.Let _x _v b => 1 + lib.goal_size b.deref
termination_by structural g
noncomputable def lib.close (f : lib.FrameList) (obligation : Int) : lib.GoalData :=
  match f with | lib.FrameList.FNil => lib.GoalData.Leaf obligation | lib.FrameList.FBind id typ t => lib.GoalData.All id typ (Tactus.Box.mk (lib.close t.deref obligation)) | lib.FrameList.FHyp h t => lib.GoalData.Imp h (Tactus.Box.mk (lib.close t.deref obligation)) | lib.FrameList.FLet id v t => lib.GoalData.Let id v (Tactus.Box.mk (lib.close t.deref obligation))
termination_by structural f
theorem lib.probe_close :
    lib.goal_size (lib.close lib.FrameList.FNil 9) = 1 ∧ lib.goal_size (lib.close (lib.FrameList.FBind 0 1 (Tactus.Box.mk lib.FrameList.FNil)) 9) = 2 := by
  decide 
