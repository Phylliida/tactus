import TactusPrelude
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
inductive lib.BinderList where
  | Nil
  | Cons (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.BinderList)
  deriving Inhabited
@[simp] noncomputable def lib.BinderList.height (s : lib.BinderList) : Nat :=
  match s with | lib.BinderList.Nil => 1 | lib.BinderList.Cons _ _ val2 => 1 + lib.BinderList.height val2.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
inductive lib.ParamBoundList where
  | Nil
  | NoBound (val0 : Tactus.Box lib.ParamBoundList)
  | Bound (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.ParamBoundList)
  deriving Inhabited
@[simp] noncomputable def lib.ParamBoundList.height (s : lib.ParamBoundList) : Nat :=
  match s with | lib.ParamBoundList.Nil => 1 | lib.ParamBoundList.NoBound val0 => 1 + lib.ParamBoundList.height val0.deref | lib.ParamBoundList.Bound _ _ val2 => 1 + lib.ParamBoundList.height val2.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
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
noncomputable def lib.frame_append (f : lib.FrameList) (g : lib.FrameList) : lib.FrameList :=
  match f with | lib.FrameList.FNil => g | lib.FrameList.FBind id typ t => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.frame_append t.deref g)) | lib.FrameList.FHyp h t => lib.FrameList.FHyp h (Tactus.Box.mk (lib.frame_append t.deref g)) | lib.FrameList.FLet id v t => lib.FrameList.FLet id v (Tactus.Box.mk (lib.frame_append t.deref g))
termination_by structural f
noncomputable def lib.binders_to_frame (b : lib.BinderList) : lib.FrameList :=
  match b with | lib.BinderList.Nil => lib.FrameList.FNil | lib.BinderList.Cons id typ t => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.binders_to_frame t.deref))
termination_by structural b
noncomputable def lib.close (f : lib.FrameList) (obligation : Int) : lib.GoalData :=
  match f with | lib.FrameList.FNil => lib.GoalData.Leaf obligation | lib.FrameList.FBind id typ t => lib.GoalData.All id typ (Tactus.Box.mk (lib.close t.deref obligation)) | lib.FrameList.FHyp h t => lib.GoalData.Imp h (Tactus.Box.mk (lib.close t.deref obligation)) | lib.FrameList.FLet id v t => lib.GoalData.Let id v (Tactus.Box.mk (lib.close t.deref obligation))
termination_by structural f
noncomputable def lib.binder_has_id (b : lib.BinderList) (x : Int) : Nat :=
  match b with | lib.BinderList.Nil => 0 | lib.BinderList.Cons id _typ t => if id = x then 1 else lib.binder_has_id t.deref x
termination_by structural b
noncomputable def lib.havoc_lets (f : lib.FrameList) (mods : lib.BinderList) : lib.FrameList :=
  match f with | lib.FrameList.FNil => lib.FrameList.FNil | lib.FrameList.FBind id typ t => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.havoc_lets t.deref mods)) | lib.FrameList.FHyp h t => lib.FrameList.FHyp h (Tactus.Box.mk (lib.havoc_lets t.deref mods)) | lib.FrameList.FLet id v t => if lib.binder_has_id mods id = 1 then lib.havoc_lets t.deref mods else lib.FrameList.FLet id v (Tactus.Box.mk (lib.havoc_lets t.deref mods))
termination_by structural f
noncomputable def lib.seed_params (params : lib.BinderList) (bounds : lib.ParamBoundList) : lib.FrameList :=
  match params with | lib.BinderList.Nil => lib.FrameList.FNil | lib.BinderList.Cons id typ t => match bounds with | lib.ParamBoundList.Bound hname prop bt => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.FrameList.FBind hname prop (Tactus.Box.mk (lib.seed_params t.deref bt.deref)))) | lib.ParamBoundList.NoBound bt => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.seed_params t.deref bt.deref)) | lib.ParamBoundList.Nil => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.seed_params t.deref lib.ParamBoundList.Nil))
termination_by structural params
noncomputable def lib.has_let (f : lib.FrameList) : Nat :=
  match f with | lib.FrameList.FNil => 0 | lib.FrameList.FBind _id _typ t => lib.has_let t.deref | lib.FrameList.FHyp _h t => lib.has_let t.deref | lib.FrameList.FLet _id _v _t => 1
termination_by structural f
noncomputable def lib.binderprops_to_hyps (b : lib.BinderList) : lib.FrameList :=
  match b with | lib.BinderList.Nil => lib.FrameList.FNil | lib.BinderList.Cons _name prop t => lib.FrameList.FHyp prop (Tactus.Box.mk (lib.binderprops_to_hyps t.deref))
termination_by structural b
noncomputable def lib.seed_binders_hyp_bounds (binders : lib.BinderList) (bounds : lib.ParamBoundList) : lib.FrameList :=
  match binders with | lib.BinderList.Nil => lib.FrameList.FNil | lib.BinderList.Cons id typ t => match bounds with | lib.ParamBoundList.Bound _hname prop bt => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.FrameList.FHyp prop (Tactus.Box.mk (lib.seed_binders_hyp_bounds t.deref bt.deref)))) | lib.ParamBoundList.NoBound bt => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.seed_binders_hyp_bounds t.deref bt.deref)) | lib.ParamBoundList.Nil => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.seed_binders_hyp_bounds t.deref lib.ParamBoundList.Nil))
termination_by structural binders
noncomputable def lib.loop_maintain_frame (f : lib.FrameList) (inv_hyps : lib.BinderList) (binders : lib.BinderList) (binder_bounds : lib.ParamBoundList) (cond_name : Int) (cond_ann : Int) (d_old_name : Int) (d_old_val : Int) : lib.FrameList :=
  let hv := lib.havoc_lets f binders;
  let d_old := lib.FrameList.FLet d_old_name d_old_val (Tactus.Box.mk lib.FrameList.FNil);
  if lib.has_let hv = 0 then lib.frame_append hv (lib.frame_append (lib.seed_params binders binder_bounds) (lib.frame_append (lib.binders_to_frame inv_hyps) (lib.frame_append (lib.FrameList.FBind cond_name cond_ann (Tactus.Box.mk lib.FrameList.FNil)) d_old))) else lib.frame_append hv (lib.frame_append (lib.seed_binders_hyp_bounds binders binder_bounds) (lib.frame_append (lib.binderprops_to_hyps inv_hyps) (lib.frame_append (lib.FrameList.FHyp cond_ann (Tactus.Box.mk lib.FrameList.FNil)) d_old)))
noncomputable def lib.loop_use_frame (f : lib.FrameList) (inv_hyps : lib.BinderList) (binders : lib.BinderList) (binder_bounds : lib.ParamBoundList) (cond_name : Int) (neg_cond_ann : Int) : lib.FrameList :=
  let hv := lib.havoc_lets f binders;
  if lib.has_let hv = 0 then lib.frame_append hv (lib.frame_append (lib.seed_params binders binder_bounds) (lib.frame_append (lib.binders_to_frame inv_hyps) (lib.FrameList.FBind cond_name neg_cond_ann (Tactus.Box.mk lib.FrameList.FNil)))) else lib.frame_append hv (lib.frame_append (lib.seed_binders_hyp_bounds binders binder_bounds) (lib.frame_append (lib.binderprops_to_hyps inv_hyps) (lib.FrameList.FHyp neg_cond_ann (Tactus.Box.mk lib.FrameList.FNil))))
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
theorem lib.ref_wp_nested_loop_nonleading :
    lib.goal_eq (lib.close (lib.loop_maintain_frame (lib.FrameList.FBind 0 1 (Tactus.Box.mk (lib.FrameList.FLet 20 21 (Tactus.Box.mk lib.FrameList.FNil)))) (lib.BinderList.Cons 13 25 (Tactus.Box.mk (lib.BinderList.Cons 15 26 (Tactus.Box.mk (lib.BinderList.Cons 17 27 (Tactus.Box.mk lib.BinderList.Nil)))))) (lib.BinderList.Cons 23 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.Bound 11 24 (Tactus.Box.mk lib.ParamBoundList.Nil)) 28 29 31 32) 35) (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.Let 20 21 (Tactus.Box.mk (lib.GoalData.All 23 1 (Tactus.Box.mk (lib.GoalData.Imp 24 (Tactus.Box.mk (lib.GoalData.Imp 25 (Tactus.Box.mk (lib.GoalData.Imp 26 (Tactus.Box.mk (lib.GoalData.Imp 27 (Tactus.Box.mk (lib.GoalData.Imp 29 (Tactus.Box.mk (lib.GoalData.Let 31 32 (Tactus.Box.mk (lib.GoalData.Leaf 35))))))))))))))))))) = 1 ∧ lib.goal_eq (lib.close (lib.loop_maintain_frame (lib.FrameList.FBind 0 1 (Tactus.Box.mk lib.FrameList.FNil)) (lib.BinderList.Cons 13 25 (Tactus.Box.mk (lib.BinderList.Cons 15 26 (Tactus.Box.mk (lib.BinderList.Cons 17 27 (Tactus.Box.mk lib.BinderList.Nil)))))) (lib.BinderList.Cons 23 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.Bound 11 24 (Tactus.Box.mk lib.ParamBoundList.Nil)) 28 29 31 32) 35) (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 23 1 (Tactus.Box.mk (lib.GoalData.All 11 24 (Tactus.Box.mk (lib.GoalData.All 13 25 (Tactus.Box.mk (lib.GoalData.All 15 26 (Tactus.Box.mk (lib.GoalData.All 17 27 (Tactus.Box.mk (lib.GoalData.All 28 29 (Tactus.Box.mk (lib.GoalData.Let 31 32 (Tactus.Box.mk (lib.GoalData.Leaf 35))))))))))))))))) = 1 ∧ lib.goal_eq (lib.close (lib.loop_use_frame (lib.FrameList.FBind 0 1 (Tactus.Box.mk (lib.FrameList.FLet 20 21 (Tactus.Box.mk lib.FrameList.FNil)))) (lib.BinderList.Cons 13 25 (Tactus.Box.mk (lib.BinderList.Cons 15 26 (Tactus.Box.mk (lib.BinderList.Cons 17 27 (Tactus.Box.mk lib.BinderList.Nil)))))) (lib.BinderList.Cons 23 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.Bound 11 24 (Tactus.Box.mk lib.ParamBoundList.Nil)) 28 30) 43) (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.Let 20 21 (Tactus.Box.mk (lib.GoalData.All 23 1 (Tactus.Box.mk (lib.GoalData.Imp 24 (Tactus.Box.mk (lib.GoalData.Imp 25 (Tactus.Box.mk (lib.GoalData.Imp 26 (Tactus.Box.mk (lib.GoalData.Imp 27 (Tactus.Box.mk (lib.GoalData.Imp 30 (Tactus.Box.mk (lib.GoalData.Leaf 43))))))))))))))))) = 1 := by
  decide 
