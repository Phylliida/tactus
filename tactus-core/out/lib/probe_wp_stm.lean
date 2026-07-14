import TactusPrelude
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
inductive lib.LeafList where
  | Nil
  | Cons (val0 : Int) (val1 : Tactus.Box lib.LeafList)
  deriving Inhabited
@[simp] noncomputable def lib.LeafList.height (s : lib.LeafList) : Nat :=
  match s with | lib.LeafList.Nil => 1 | lib.LeafList.Cons _ val1 => 1 + lib.LeafList.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
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
inductive lib.RetBind where
  | RetNone
  | RetLet (val0 : Int) (val1 : Int)
  deriving Inhabited
@[simp] noncomputable def lib.RetBind.height (_ : lib.RetBind) : Nat :=
  1
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
inductive lib.StmData where
  | Assert (val0 : Int) (val1 : Int)
  | Assume (val0 : Int)
  | Assign (val0 : Int) (val1 : Int)
  | Call (reqs : Tactus.Box lib.LeafList) (post : Tactus.Box lib.FrameList)
  | DeadEnd (val0 : Tactus.Box lib.StmData)
  | Ret (val0 : Tactus.Box lib.LeafList) (val1 : lib.RetBind)
  | If (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.StmData) (val3 : Tactus.Box lib.StmData)
  | Loop (inv_hyps : Tactus.Box lib.BinderList) (binders : Tactus.Box lib.BinderList) (binder_bounds : Tactus.Box lib.ParamBoundList) (cond_name : Int) (cond_ann : Int) (neg_cond_ann : Int) (d_old_name : Int) (d_old_val : Int) (decrease_oblig : Int) (body : Tactus.Box lib.StmData)
  | Skip
  | Seq (val0 : Tactus.Box lib.StmData) (val1 : Tactus.Box lib.StmData)
  deriving Inhabited
@[simp] noncomputable def lib.StmData.height (s : lib.StmData) : Nat :=
  match s with | lib.StmData.Assert _ _ => 1 | lib.StmData.Assume _ => 1 | lib.StmData.Assign _ _ => 1 | lib.StmData.Call _ _ => 1 | lib.StmData.DeadEnd val0 => 1 + lib.StmData.height val0.deref | lib.StmData.Ret _ _ => 1 | lib.StmData.If _ _ val2 val3 => 1 + lib.StmData.height val2.deref + lib.StmData.height val3.deref | lib.StmData.Loop _ _ _ _ _ _ _ _ _ body => 1 + lib.StmData.height body.deref | lib.StmData.Skip => 1 | lib.StmData.Seq val0 val1 => 1 + lib.StmData.height val0.deref + lib.StmData.height val1.deref
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
inductive lib.GoalList where
  | Nil
  | Cons (val0 : Tactus.Box lib.GoalData) (val1 : Tactus.Box lib.GoalList)
  deriving Inhabited
@[simp] noncomputable def lib.GoalList.height (s : lib.GoalList) : Nat :=
  match s with | lib.GoalList.Nil => 1 | lib.GoalList.Cons _ val1 => 1 + lib.GoalList.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
noncomputable def lib.goal_count (gs : lib.GoalList) : Nat :=
  match gs with | lib.GoalList.Nil => 0 | lib.GoalList.Cons _g t => 1 + lib.goal_count t.deref
termination_by structural gs
noncomputable def lib.frame_append (f : lib.FrameList) (g : lib.FrameList) : lib.FrameList :=
  match f with | lib.FrameList.FNil => g | lib.FrameList.FBind id typ t => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.frame_append t.deref g)) | lib.FrameList.FHyp h t => lib.FrameList.FHyp h (Tactus.Box.mk (lib.frame_append t.deref g)) | lib.FrameList.FLet id v t => lib.FrameList.FLet id v (Tactus.Box.mk (lib.frame_append t.deref g))
termination_by structural f
noncomputable def lib.binders_to_frame (b : lib.BinderList) : lib.FrameList :=
  match b with | lib.BinderList.Nil => lib.FrameList.FNil | lib.BinderList.Cons id typ t => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.binders_to_frame t.deref))
termination_by structural b
noncomputable def lib.close (f : lib.FrameList) (obligation : Int) : lib.GoalData :=
  match f with | lib.FrameList.FNil => lib.GoalData.Leaf obligation | lib.FrameList.FBind id typ t => lib.GoalData.All id typ (Tactus.Box.mk (lib.close t.deref obligation)) | lib.FrameList.FHyp h t => lib.GoalData.Imp h (Tactus.Box.mk (lib.close t.deref obligation)) | lib.FrameList.FLet id v t => lib.GoalData.Let id v (Tactus.Box.mk (lib.close t.deref obligation))
termination_by structural f
noncomputable def lib.close_each (f : lib.FrameList) (l : lib.LeafList) : lib.GoalList :=
  match l with | lib.LeafList.Nil => lib.GoalList.Nil | lib.LeafList.Cons h t => lib.GoalList.Cons (Tactus.Box.mk (lib.close f h)) (Tactus.Box.mk (lib.close_each f t.deref))
termination_by structural l
noncomputable def lib.goals_append (a : lib.GoalList) (b : lib.GoalList) : lib.GoalList :=
  match a with | lib.GoalList.Nil => b | lib.GoalList.Cons h t => lib.GoalList.Cons h (Tactus.Box.mk (lib.goals_append t.deref b))
termination_by structural a
noncomputable def lib.binder_has_id (b : lib.BinderList) (x : Int) : Nat :=
  match b with | lib.BinderList.Nil => 0 | lib.BinderList.Cons id _typ t => if id = x then 1 else lib.binder_has_id t.deref x
termination_by structural b
noncomputable def lib.havoc_lets (f : lib.FrameList) (mods : lib.BinderList) : lib.FrameList :=
  match f with | lib.FrameList.FNil => lib.FrameList.FNil | lib.FrameList.FBind id typ t => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.havoc_lets t.deref mods)) | lib.FrameList.FHyp h t => lib.FrameList.FHyp h (Tactus.Box.mk (lib.havoc_lets t.deref mods)) | lib.FrameList.FLet id v t => if lib.binder_has_id mods id = 1 then lib.havoc_lets t.deref mods else lib.FrameList.FLet id v (Tactus.Box.mk (lib.havoc_lets t.deref mods))
termination_by structural f
noncomputable def lib.close_each_binderprop (f : lib.FrameList) (b : lib.BinderList) : lib.GoalList :=
  match b with | lib.BinderList.Nil => lib.GoalList.Nil | lib.BinderList.Cons _name prop t => lib.GoalList.Cons (Tactus.Box.mk (lib.close f prop)) (Tactus.Box.mk (lib.close_each_binderprop f t.deref))
termination_by structural b
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
noncomputable def lib.is_skip (s : lib.StmData) : Nat :=
  match s with | lib.StmData.Skip => 1 | _ => 0
noncomputable def lib.diverges (s : lib.StmData) : Nat :=
  match s with | lib.StmData.Ret _es _rb => 1 | lib.StmData.DeadEnd _b => 1 | lib.StmData.Seq a b => if lib.diverges a.deref = 1 ∨ lib.diverges b.deref = 1 then 1 else 0 | lib.StmData.If _c _nc t e => if lib.diverges t.deref = 1 ∧ lib.diverges e.deref = 1 then 1 else 0 | _ => 0
termination_by structural s
noncomputable def lib.frame_after (f : lib.FrameList) (s : lib.StmData) : lib.FrameList :=
  match s with | lib.StmData.Assert _o h => lib.frame_append f (lib.FrameList.FHyp h (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.Assume e => lib.frame_append f (lib.FrameList.FHyp e (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.Assign x rhs => lib.frame_append f (lib.FrameList.FLet x rhs (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.Call _ post => lib.frame_append f post.deref | lib.StmData.DeadEnd _b => f | lib.StmData.Ret _es _rb => f | lib.StmData.If _c nc t e => if lib.diverges t.deref = 1 ∧ lib.is_skip e.deref = 1 then lib.frame_append f (lib.FrameList.FHyp nc (Tactus.Box.mk lib.FrameList.FNil)) else f | lib.StmData.Loop inv_hyps binders binder_bounds cond_name _ neg_cond_ann _ _ _ _ => lib.loop_use_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name neg_cond_ann | lib.StmData.Skip => f | lib.StmData.Seq a b => lib.frame_after (lib.frame_after f a.deref) b.deref
termination_by structural s
noncomputable def lib.ret_frame (f : lib.FrameList) (rb : lib.RetBind) : lib.FrameList :=
  match rb with | lib.RetBind.RetNone => f | lib.RetBind.RetLet name val => lib.frame_append f (lib.FrameList.FLet name val (Tactus.Box.mk lib.FrameList.FNil))
noncomputable def lib.wp_stm (f : lib.FrameList) (s : lib.StmData) : lib.GoalList :=
  match s with | lib.StmData.Assert o _h => lib.GoalList.Cons (Tactus.Box.mk (lib.close f o)) (Tactus.Box.mk lib.GoalList.Nil) | lib.StmData.Assume _e => lib.GoalList.Nil | lib.StmData.Assign _x _rhs => lib.GoalList.Nil | lib.StmData.Call reqs _ => lib.close_each f reqs.deref | lib.StmData.DeadEnd b => lib.wp_stm f b.deref | lib.StmData.Ret es rb => lib.close_each (lib.ret_frame f rb) es.deref | lib.StmData.If c nc t e => lib.goals_append (lib.wp_stm (lib.frame_append f (lib.FrameList.FHyp c (Tactus.Box.mk lib.FrameList.FNil))) t.deref) (lib.wp_stm (lib.frame_append f (lib.FrameList.FHyp nc (Tactus.Box.mk lib.FrameList.FNil))) e.deref) | lib.StmData.Loop inv_hyps binders binder_bounds cond_name cond_ann _ d_old_name d_old_val decrease_oblig body => let mframe := lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_val;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       let body_goals := lib.wp_stm mframe body.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       let endf := lib.frame_after mframe body.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       let maintain_reclose := lib.close_each_binderprop endf inv_hyps.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       let decrease_goal := lib.GoalList.Cons (Tactus.Box.mk (lib.close endf decrease_oblig)) (Tactus.Box.mk lib.GoalList.Nil);
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       let init := lib.close_each_binderprop f inv_hyps.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       lib.goals_append init (lib.goals_append body_goals (lib.goals_append maintain_reclose decrease_goal)) | lib.StmData.Skip => lib.GoalList.Nil | lib.StmData.Seq a b => match a.deref with | lib.StmData.If c nc t e => let tf := lib.frame_append f (lib.FrameList.FHyp c (Tactus.Box.mk lib.FrameList.FNil));
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             let ef := lib.frame_append f (lib.FrameList.FHyp nc (Tactus.Box.mk lib.FrameList.FNil));
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             let then_goals := if lib.diverges t.deref = 1 then lib.wp_stm tf t.deref else lib.goals_append (lib.wp_stm tf t.deref) (lib.wp_stm (lib.frame_after tf t.deref) b.deref);
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             let else_goals := if lib.diverges e.deref = 1 then lib.wp_stm ef e.deref else lib.goals_append (lib.wp_stm ef e.deref) (lib.wp_stm (lib.frame_after ef e.deref) b.deref);
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             lib.goals_append then_goals else_goals | _ => lib.goals_append (lib.wp_stm f a.deref) (lib.wp_stm (lib.frame_after f a.deref) b.deref)
termination_by structural s
theorem lib.probe_wp_stm :
    lib.goal_count (lib.wp_stm lib.FrameList.FNil (lib.StmData.Assert 9 9)) = 1 ∧ lib.goal_count (lib.wp_stm lib.FrameList.FNil lib.StmData.Skip) = 0 := by
  decide 
