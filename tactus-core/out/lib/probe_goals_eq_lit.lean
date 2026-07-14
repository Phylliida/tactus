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
inductive lib.GoalList where
  | Nil
  | Cons (val0 : Tactus.Box lib.GoalData) (val1 : Tactus.Box lib.GoalList)
  deriving Inhabited
@[simp] noncomputable def lib.GoalList.height (s : lib.GoalList) : Nat :=
  match s with | lib.GoalList.Nil => 1 | lib.GoalList.Cons _ val1 => 1 + lib.GoalList.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
noncomputable def lib.gd_tag (g : lib.GoalData) : Nat :=
  match g with | lib.GoalData.Leaf _ => 0 | lib.GoalData.Imp _ _ => 1 | lib.GoalData.All _ _ _ => 2 | lib.GoalData.Let _ _ _ => 3
noncomputable def lib.gd_leaf_id (g : lib.GoalData) : Int :=
  match g with | lib.GoalData.Leaf x => x | _ => 0
noncomputable def lib.gd_imp_hyp (g : lib.GoalData) : Int :=
  match g with | lib.GoalData.Imp h _ => h | _ => 0
noncomputable def lib.gd_all_name (g : lib.GoalData) : Int :=
  match g with | lib.GoalData.All x _ _ => x | _ => 0
noncomputable def lib.gd_all_typ (g : lib.GoalData) : Int :=
  match g with | lib.GoalData.All _ t _ => t | _ => 0
noncomputable def lib.gd_let_name (g : lib.GoalData) : Int :=
  match g with | lib.GoalData.Let x _ _ => x | _ => 0
noncomputable def lib.gd_let_val (g : lib.GoalData) : Int :=
  match g with | lib.GoalData.Let _ v _ => v | _ => 0
noncomputable def lib.gd_child (g : lib.GoalData) : lib.GoalData :=
  match g with | lib.GoalData.Imp _ t => t.deref | lib.GoalData.All _ _ t => t.deref | lib.GoalData.Let _ _ t => t.deref | lib.GoalData.Leaf x => lib.GoalData.Leaf x
noncomputable def lib.goal_eq (a : lib.GoalData) (b : lib.GoalData) : Nat :=
  match a with | lib.GoalData.Leaf x => if lib.gd_tag b = 0 then if x = lib.gd_leaf_id b then 1 else 0 else 0 | lib.GoalData.Imp h1 t1 => if lib.gd_tag b = 1 then if h1 = lib.gd_imp_hyp b then lib.goal_eq t1.deref (lib.gd_child b) else 0 else 0 | lib.GoalData.All x1 ty1 t1 => if lib.gd_tag b = 2 then if x1 = lib.gd_all_name b then if ty1 = lib.gd_all_typ b then lib.goal_eq t1.deref (lib.gd_child b) else 0 else 0 else 0 | lib.GoalData.Let x1 v1 t1 => if lib.gd_tag b = 3 then if x1 = lib.gd_let_name b then if v1 = lib.gd_let_val b then lib.goal_eq t1.deref (lib.gd_child b) else 0 else 0 else 0
termination_by structural a
noncomputable def lib.gl_tag (g : lib.GoalList) : Nat :=
  match g with | lib.GoalList.Nil => 0 | lib.GoalList.Cons _ _ => 1
noncomputable def lib.gl_head (g : lib.GoalList) : lib.GoalData :=
  match g with | lib.GoalList.Cons h _ => h.deref | lib.GoalList.Nil => lib.GoalData.Leaf 0
noncomputable def lib.gl_tail (g : lib.GoalList) : lib.GoalList :=
  match g with | lib.GoalList.Cons _ t => t.deref | lib.GoalList.Nil => lib.GoalList.Nil
noncomputable def lib.goals_eq (a : lib.GoalList) (b : lib.GoalList) : Nat :=
  match a with | lib.GoalList.Nil => if lib.gl_tag b = 0 then 1 else 0 | lib.GoalList.Cons h1 t1 => if lib.gl_tag b = 1 then if lib.goal_eq h1.deref (lib.gl_head b) = 1 then lib.goals_eq t1.deref (lib.gl_tail b) else 0 else 0
termination_by structural a
theorem lib.probe_goals_eq_lit :
    lib.goals_eq lib.GoalList.Nil lib.GoalList.Nil = 1 ∧ lib.goals_eq (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Leaf 9)) (Tactus.Box.mk lib.GoalList.Nil)) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Leaf 9)) (Tactus.Box.mk lib.GoalList.Nil)) = 1 := by
  decide 
