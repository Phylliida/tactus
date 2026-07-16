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
inductive lib.CastKind where
  | IntToNat
  | NatToInt
  deriving Inhabited
@[simp] noncomputable def lib.CastKind.height (_ : lib.CastKind) : Nat :=
  1
inductive lib.ExprData where
  | Atom (val0 : Int)
  | Lit (val0 : Int)
  | Cast (val0 : lib.CastKind) (val1 : Tactus.Box lib.ExprData)
  | BinOp (val0 : Int) (val1 : Tactus.Box lib.ExprData) (val2 : Tactus.Box lib.ExprData)
  | App (val0 : Int) (val1 : Tactus.Box lib.ExprData)
  | FieldProj (val0 : Tactus.Box lib.ExprData) (val1 : Int)
  | SpanMark (val0 : Int) (val1 : Tactus.Box lib.ExprData)
  deriving Inhabited
@[simp] noncomputable def lib.ExprData.height (s : lib.ExprData) : Nat :=
  match s with | lib.ExprData.Atom _ => 1 | lib.ExprData.Lit _ => 1 | lib.ExprData.Cast _ val1 => 1 + lib.ExprData.height val1.deref | lib.ExprData.BinOp _ val1 val2 => 1 + lib.ExprData.height val1.deref + lib.ExprData.height val2.deref | lib.ExprData.App _ val1 => 1 + lib.ExprData.height val1.deref | lib.ExprData.FieldProj val0 _ => 1 + lib.ExprData.height val0.deref | lib.ExprData.SpanMark _ val1 => 1 + lib.ExprData.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
inductive lib.GoalData where
  | Leaf (val0 : Int)
  | Imp (val0 : Int) (val1 : Tactus.Box lib.GoalData)
  | All (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.GoalData)
  | Let (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.GoalData)
  | LeafE (val0 : lib.ExprData)
  deriving Inhabited
@[simp] noncomputable def lib.GoalData.height (s : lib.GoalData) : Nat :=
  match s with | lib.GoalData.Leaf _ => 1 | lib.GoalData.Imp _ val1 => 1 + lib.GoalData.height val1.deref | lib.GoalData.All _ _ val2 => 1 + lib.GoalData.height val2.deref | lib.GoalData.Let _ _ val2 => 1 + lib.GoalData.height val2.deref | lib.GoalData.LeafE _ => 1
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
noncomputable def lib.leaf_len (l : lib.LeafList) : Nat :=
  match l with | lib.LeafList.Nil => 0 | lib.LeafList.Cons _h t => 1 + lib.leaf_len t.deref
termination_by structural l
noncomputable def lib.binder_len (b : lib.BinderList) : Nat :=
  match b with | lib.BinderList.Nil => 0 | lib.BinderList.Cons _id _typ t => 1 + lib.binder_len t.deref
termination_by structural b
noncomputable def lib.frame_len (f : lib.FrameList) : Nat :=
  match f with | lib.FrameList.FNil => 0 | lib.FrameList.FBind _id _typ t => 1 + lib.frame_len t.deref | lib.FrameList.FHyp _h t => 1 + lib.frame_len t.deref | lib.FrameList.FLet _id _v t => 1 + lib.frame_len t.deref
termination_by structural f
noncomputable def lib.stm_size (s : lib.StmData) : Nat :=
  match s with | lib.StmData.Assert _o _h => 1 | lib.StmData.Assume _e => 1 | lib.StmData.Assign _d _r => 1 | lib.StmData.Call reqs post => 1 + lib.leaf_len reqs.deref + lib.frame_len post.deref | lib.StmData.DeadEnd b => 1 + lib.stm_size b.deref | lib.StmData.Ret es _rb => 1 + lib.leaf_len es.deref | lib.StmData.If _c _nc t e => 1 + lib.stm_size t.deref + lib.stm_size e.deref | lib.StmData.Loop inv_hyps binders _ _ _ _ _ _ _ body => 1 + lib.binder_len inv_hyps.deref + lib.binder_len binders.deref + lib.stm_size body.deref | lib.StmData.Skip => 1 | lib.StmData.Seq a b => 1 + lib.stm_size a.deref + lib.stm_size b.deref
termination_by structural s
noncomputable def lib.goal_size (g : lib.GoalData) : Nat :=
  match g with | lib.GoalData.Leaf _e => 1 | lib.GoalData.Imp _h b => 1 + lib.goal_size b.deref | lib.GoalData.All _x _t b => 1 + lib.goal_size b.deref | lib.GoalData.Let _x _v b => 1 + lib.goal_size b.deref | lib.GoalData.LeafE _e => 1
termination_by structural g
theorem lib.skeleton_kernel_computes :
    lib.stm_size (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert 0 0)) (Tactus.Box.mk (lib.StmData.If 1 2 (Tactus.Box.mk lib.StmData.Skip) (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk lib.LeafList.Nil) lib.RetBind.RetNone))))) = 5 ∧ lib.goal_size (lib.GoalData.Imp 7 (Tactus.Box.mk (lib.GoalData.All 8 9 (Tactus.Box.mk (lib.GoalData.Leaf 10))))) = 3 ∧ lib.leaf_len (lib.LeafList.Cons 1 (Tactus.Box.mk (lib.LeafList.Cons 2 (Tactus.Box.mk lib.LeafList.Nil)))) = 2 := by

  decide
