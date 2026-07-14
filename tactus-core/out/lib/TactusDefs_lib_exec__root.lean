-- tactus defs part: root (base = machinery + instance closure; one part per source module, SCC-merged; umbrella = interface)
import TactusDefs_lib_exec__base
import TactusPrelude
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
noncomputable def lib.leaf_len (l : lib.LeafList) : Nat :=
  match l with | lib.LeafList.Nil => 0 | lib.LeafList.Cons _h t => 1 + lib.leaf_len t.deref
termination_by structural l
noncomputable def lib.binder_len (b : lib.BinderList) : Nat :=
  match b with | lib.BinderList.Nil => 0 | lib.BinderList.Cons _id _typ t => 1 + lib.binder_len t.deref
termination_by structural b
noncomputable def lib.param_bound_len (p : lib.ParamBoundList) : Nat :=
  match p with | lib.ParamBoundList.Nil => 0 | lib.ParamBoundList.NoBound t => 1 + lib.param_bound_len t.deref | lib.ParamBoundList.Bound _name _prop t => 1 + lib.param_bound_len t.deref
termination_by structural p
noncomputable def lib.frame_len (f : lib.FrameList) : Nat :=
  match f with | lib.FrameList.FNil => 0 | lib.FrameList.FBind _id _typ t => 1 + lib.frame_len t.deref | lib.FrameList.FHyp _h t => 1 + lib.frame_len t.deref | lib.FrameList.FLet _id _v t => 1 + lib.frame_len t.deref
termination_by structural f
noncomputable def lib.stm_size (s : lib.StmData) : Nat :=
  match s with | lib.StmData.Assert _o _h => 1 | lib.StmData.Assume _e => 1 | lib.StmData.Assign _d _r => 1 | lib.StmData.Call reqs enss _ _ => 1 + lib.leaf_len reqs.deref + lib.leaf_len enss.deref | lib.StmData.DeadEnd b => 1 + lib.stm_size b.deref | lib.StmData.Ret es _rb => 1 + lib.leaf_len es.deref | lib.StmData.If _c _nc t e => 1 + lib.stm_size t.deref + lib.stm_size e.deref | lib.StmData.Loop inv_hyps binders _ _ _ _ _ _ _ body => 1 + lib.binder_len inv_hyps.deref + lib.binder_len binders.deref + lib.stm_size body.deref | lib.StmData.Skip => 1 | lib.StmData.Seq a b => 1 + lib.stm_size a.deref + lib.stm_size b.deref
termination_by structural s
noncomputable def lib.goal_size (g : lib.GoalData) : Nat :=
  match g with | lib.GoalData.Leaf _e => 1 | lib.GoalData.Imp _h b => 1 + lib.goal_size b.deref | lib.GoalData.All _x _t b => 1 + lib.goal_size b.deref | lib.GoalData.Let _x _v b => 1 + lib.goal_size b.deref
termination_by structural g
noncomputable def lib.goal_count (gs : lib.GoalList) : Nat :=
  match gs with | lib.GoalList.Nil => 0 | lib.GoalList.Cons _g t => 1 + lib.goal_count t.deref
termination_by structural gs
noncomputable def lib.fnctx_arity (c : lib.FnCtxData) : Nat :=
  lib.binder_len c.params
noncomputable def lib.frame_append (f : lib.FrameList) (g : lib.FrameList) : lib.FrameList :=
  match f with | lib.FrameList.FNil => g | lib.FrameList.FBind id typ t => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.frame_append t.deref g)) | lib.FrameList.FHyp h t => lib.FrameList.FHyp h (Tactus.Box.mk (lib.frame_append t.deref g)) | lib.FrameList.FLet id v t => lib.FrameList.FLet id v (Tactus.Box.mk (lib.frame_append t.deref g))
termination_by structural f
noncomputable def lib.hyps_of_leaves (l : lib.LeafList) : lib.FrameList :=
  match l with | lib.LeafList.Nil => lib.FrameList.FNil | lib.LeafList.Cons h t => lib.FrameList.FHyp h (Tactus.Box.mk (lib.hyps_of_leaves t.deref))
termination_by structural l
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
noncomputable def lib.frame_after (f : lib.FrameList) (s : lib.StmData) : lib.FrameList :=
  match s with | lib.StmData.Assert _o h => lib.frame_append f (lib.FrameList.FHyp h (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.Assume e => lib.frame_append f (lib.FrameList.FHyp e (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.Assign x rhs => lib.frame_append f (lib.FrameList.FLet x rhs (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.Call _ enss dest dest_typ => lib.frame_append f (lib.FrameList.FBind dest dest_typ (Tactus.Box.mk (lib.hyps_of_leaves enss.deref))) | lib.StmData.DeadEnd _b => f | lib.StmData.Ret _es _rb => f | lib.StmData.If _c _nc _t _e => f | lib.StmData.Loop inv_hyps binders binder_bounds cond_name _ neg_cond_ann _ _ _ _ => lib.frame_append (lib.havoc_lets f binders.deref) (lib.frame_append (lib.seed_params binders.deref binder_bounds.deref) (lib.frame_append (lib.binders_to_frame inv_hyps.deref) (lib.FrameList.FBind cond_name neg_cond_ann (Tactus.Box.mk lib.FrameList.FNil)))) | lib.StmData.Skip => f | lib.StmData.Seq a b => lib.frame_after (lib.frame_after f a.deref) b.deref
termination_by structural s
noncomputable def lib.ret_frame (f : lib.FrameList) (rb : lib.RetBind) : lib.FrameList :=
  match rb with | lib.RetBind.RetNone => f | lib.RetBind.RetLet name val => lib.frame_append f (lib.FrameList.FLet name val (Tactus.Box.mk lib.FrameList.FNil))
noncomputable def lib.wp_stm (f : lib.FrameList) (s : lib.StmData) : lib.GoalList :=
  match s with | lib.StmData.Assert o _h => lib.GoalList.Cons (Tactus.Box.mk (lib.close f o)) (Tactus.Box.mk lib.GoalList.Nil) | lib.StmData.Assume _e => lib.GoalList.Nil | lib.StmData.Assign _x _rhs => lib.GoalList.Nil | lib.StmData.Call reqs _ _ _ => lib.close_each f reqs.deref | lib.StmData.DeadEnd b => lib.wp_stm f b.deref | lib.StmData.Ret es rb => lib.close_each (lib.ret_frame f rb) es.deref | lib.StmData.If c nc t e => lib.goals_append (lib.wp_stm (lib.frame_append f (lib.FrameList.FHyp c (Tactus.Box.mk lib.FrameList.FNil))) t.deref) (lib.wp_stm (lib.frame_append f (lib.FrameList.FHyp nc (Tactus.Box.mk lib.FrameList.FNil))) e.deref) | lib.StmData.Loop inv_hyps binders binder_bounds cond_name cond_ann _ d_old_name d_old_val decrease_oblig body => let mframe := lib.frame_append (lib.havoc_lets f binders.deref) (lib.frame_append (lib.seed_params binders.deref binder_bounds.deref) (lib.frame_append (lib.binders_to_frame inv_hyps.deref) (lib.frame_append (lib.FrameList.FBind cond_name cond_ann (Tactus.Box.mk lib.FrameList.FNil)) (lib.FrameList.FLet d_old_name d_old_val (Tactus.Box.mk lib.FrameList.FNil)))));
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           let body_goals := lib.wp_stm mframe body.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           let endf := lib.frame_after mframe body.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           let maintain_reclose := lib.close_each_binderprop endf inv_hyps.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           let decrease_goal := lib.GoalList.Cons (Tactus.Box.mk (lib.close endf decrease_oblig)) (Tactus.Box.mk lib.GoalList.Nil);
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           let init := lib.close_each_binderprop f inv_hyps.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           lib.goals_append init (lib.goals_append body_goals (lib.goals_append maintain_reclose decrease_goal)) | lib.StmData.Skip => lib.GoalList.Nil | lib.StmData.Seq a b => lib.goals_append (lib.wp_stm f a.deref) (lib.wp_stm (lib.frame_after f a.deref) b.deref)
termination_by structural s
noncomputable def lib.seed_frame (c : lib.FnCtxData) : lib.FrameList :=
  lib.frame_append (lib.binders_to_frame c.typ_params) (lib.frame_append (lib.seed_params c.params c.param_bounds) (lib.binders_to_frame c.reqs))
noncomputable def lib.ref_wp (c : lib.FnCtxData) (s : lib.StmData) : lib.GoalList :=
  lib.wp_stm (lib.seed_frame c) s
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
