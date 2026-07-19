import TactusDefs
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
inductive lib.BinderIdList where
  | Nil
  | Cons (val0 : Int) (val1 : Tactus.Box lib.BinderIdList)
  deriving Inhabited
@[simp] noncomputable def lib.BinderIdList.height (s : lib.BinderIdList) : Nat :=
  match s with | lib.BinderIdList.Nil => 1 | lib.BinderIdList.Cons _ val1 => 1 + lib.BinderIdList.height val1.deref
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
inductive lib.TypData where
  | TyInt
  | TyNat
  | TyBool
  | TyNamed (val0 : Int)
  | TyRef (val0 : Int)
  | TyBox (val0 : Int)
  deriving Inhabited
@[simp] noncomputable def lib.TypData.height (_ : lib.TypData) : Nat :=
  1
mutual
inductive lib.RawExp where
  | Var (val0 : Int) (val1 : lib.TypData)
  | Lit (val0 : Int) (val1 : lib.TypData)
  | LitBool (val0 : Nat)
  | Clip (val0 : lib.TypData) (val1 : Tactus.Box lib.RawExp)
  | BinOp (val0 : Int) (val1 : lib.TypData) (val2 : Tactus.Box lib.RawExp) (val3 : Tactus.Box lib.RawExp)
  | Call (val0 : Int) (val1 : lib.TypData) (val2 : Tactus.Box lib.RawExp) (val3 : lib.TypData)
  | Field (val0 : Int) (val1 : lib.TypData) (val2 : Tactus.Box lib.RawExp)
  | HasType (val0 : Int) (val1 : Tactus.Box lib.RawExp)
  | Deref (val0 : Tactus.Box lib.RawExp)
  | Let (val0 : Int) (val1 : Tactus.Box lib.RawExp) (val2 : Tactus.Box lib.RawExp)
  | Not (val0 : Tactus.Box lib.RawExp)
  | Span (val0 : Int) (val1 : Tactus.Box lib.RawExp)
  | Ite (val0 : lib.TypData) (val1 : Tactus.Box lib.RawExp) (val2 : Tactus.Box lib.RawExp) (val3 : Tactus.Box lib.RawExp)
  | MatchR (val0 : Tactus.Box lib.RawExp) (val1 : Tactus.Box lib.RawArmList) (val2 : lib.TypData)
  | CallN (val0 : Int) (val1 : lib.TypData) (val2 : Tactus.Box lib.RawList)
  | ForallR (val0 : Int) (val1 : lib.TypData) (val2 : Tactus.Box lib.RawExp)
  | ExistsR (val0 : Int) (val1 : lib.TypData) (val2 : Tactus.Box lib.RawExp)
  deriving Inhabited
inductive lib.RawArmList where
  | Nil
  | Cons (val0 : Int) (val1 : lib.BinderIdList) (val2 : Tactus.Box lib.RawExp) (val3 : Tactus.Box lib.RawArmList)
  deriving Inhabited
inductive lib.RawList where
  | Nil
  | Cons (val0 : Tactus.Box lib.RawExp) (val1 : Tactus.Box lib.RawList)
  deriving Inhabited
end

mutual
@[simp] noncomputable def lib.RawExp.height (s : lib.RawExp) : Nat :=
  match s with | lib.RawExp.Var _ _ => 1 | lib.RawExp.Lit _ _ => 1 | lib.RawExp.LitBool _ => 1 | lib.RawExp.Clip _ val1 => 1 + lib.RawExp.height val1.deref | lib.RawExp.BinOp _ _ val2 val3 => 1 + lib.RawExp.height val2.deref + lib.RawExp.height val3.deref | lib.RawExp.Call _ _ val2 _ => 1 + lib.RawExp.height val2.deref | lib.RawExp.Field _ _ val2 => 1 + lib.RawExp.height val2.deref | lib.RawExp.HasType _ val1 => 1 + lib.RawExp.height val1.deref | lib.RawExp.Deref val0 => 1 + lib.RawExp.height val0.deref | lib.RawExp.Let _ val1 val2 => 1 + lib.RawExp.height val1.deref + lib.RawExp.height val2.deref | lib.RawExp.Not val0 => 1 + lib.RawExp.height val0.deref | lib.RawExp.Span _ val1 => 1 + lib.RawExp.height val1.deref | lib.RawExp.Ite _ val1 val2 val3 => 1 + lib.RawExp.height val1.deref + lib.RawExp.height val2.deref + lib.RawExp.height val3.deref | lib.RawExp.MatchR val0 val1 _ => 1 + lib.RawExp.height val0.deref + lib.RawArmList.height val1.deref | lib.RawExp.CallN _ _ val2 => 1 + lib.RawList.height val2.deref | lib.RawExp.ForallR _ _ val2 => 1 + lib.RawExp.height val2.deref | lib.RawExp.ExistsR _ _ val2 => 1 + lib.RawExp.height val2.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
@[simp] noncomputable def lib.RawArmList.height (s : lib.RawArmList) : Nat :=
  match s with | lib.RawArmList.Nil => 1 | lib.RawArmList.Cons _ _ val2 val3 => 1 + lib.RawExp.height val2.deref + lib.RawArmList.height val3.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
@[simp] noncomputable def lib.RawList.height (s : lib.RawList) : Nat :=
  match s with | lib.RawList.Nil => 1 | lib.RawList.Cons val0 val1 => 1 + lib.RawExp.height val0.deref + lib.RawList.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
end

inductive lib.RawExpList where
  | Nil
  | Cons (val0 : Tactus.Box lib.RawExp) (val1 : Tactus.Box lib.RawExpList)
  deriving Inhabited
@[simp] noncomputable def lib.RawExpList.height (s : lib.RawExpList) : Nat :=
  match s with | lib.RawExpList.Nil => 1 | lib.RawExpList.Cons _ val1 => 1 + lib.RawExpList.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
inductive lib.FrameList where
  | FNil
  | FBind (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.FrameList)
  | FHyp (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.FrameList)
  | FLet (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.FrameList)
  | FLetH (val0 : Int) (val1 : Int) (val2 : Int) (val3 : Int) (val4 : Int) (val5 : Tactus.Box lib.FrameList)
  deriving Inhabited
@[simp] noncomputable def lib.FrameList.height (s : lib.FrameList) : Nat :=
  match s with | lib.FrameList.FNil => 1 | lib.FrameList.FBind _ _ val2 => 1 + lib.FrameList.height val2.deref | lib.FrameList.FHyp _ _ val2 => 1 + lib.FrameList.height val2.deref | lib.FrameList.FLet _ _ val2 => 1 + lib.FrameList.height val2.deref | lib.FrameList.FLetH _ _ _ _ _ val5 => 1 + lib.FrameList.height val5.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
inductive lib.StmData where
  | Assert (val0 : lib.RawExp) (val1 : Int)
  | Assume (val0 : Int)
  | Assign (val0 : Int) (val1 : Int)
  | Call (reqs : Tactus.Box lib.RawExpList) (post : Tactus.Box lib.FrameList)
  | DeadEnd (val0 : Tactus.Box lib.StmData)
  | Ret (val0 : Tactus.Box lib.RawExpList) (val1 : lib.RetBind)
  | If (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.StmData) (val3 : Tactus.Box lib.StmData)
  | Loop (inv_hyps : Tactus.Box lib.BinderList) (inv_obligs : Tactus.Box lib.RawExpList) (binders : Tactus.Box lib.BinderList) (binder_bounds : Tactus.Box lib.ParamBoundList) (cond_name : Int) (cond_ann : Int) (neg_cond_ann : Int) (d_old_name : Int) (d_old_val : Int) (decrease_oblig : lib.RawExp) (body : Tactus.Box lib.StmData)
  | AssertQueryNl (val0 : Tactus.Box lib.StmData)
  | Skip
  | Seq (val0 : Tactus.Box lib.StmData) (val1 : Tactus.Box lib.StmData)
  deriving Inhabited
@[simp] noncomputable def lib.StmData.height (s : lib.StmData) : Nat :=
  match s with | lib.StmData.Assert _ _ => 1 | lib.StmData.Assume _ => 1 | lib.StmData.Assign _ _ => 1 | lib.StmData.Call _ _ => 1 | lib.StmData.DeadEnd val0 => 1 + lib.StmData.height val0.deref | lib.StmData.Ret _ _ => 1 | lib.StmData.If _ _ val2 val3 => 1 + lib.StmData.height val2.deref + lib.StmData.height val3.deref | lib.StmData.Loop _ _ _ _ _ _ _ _ _ _ body => 1 + lib.StmData.height body.deref | lib.StmData.AssertQueryNl val0 => 1 + lib.StmData.height val0.deref | lib.StmData.Skip => 1 | lib.StmData.Seq val0 val1 => 1 + lib.StmData.height val0.deref + lib.StmData.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
structure lib.FnCtxData where
  typ_params : lib.BinderList
  params : lib.BinderList
  param_bounds : lib.ParamBoundList
  reqs : lib.BinderList
  enss : lib.LeafList
  deriving Inhabited
@[simp] noncomputable def lib.FnCtxData.height (_ : lib.FnCtxData) : Nat :=
  1
noncomputable def lib.raw_exp_list_len (l : lib.RawExpList) : Nat :=
  match l with | lib.RawExpList.Nil => 0 | lib.RawExpList.Cons _h t => 1 + lib.raw_exp_list_len t.deref
termination_by structural l
noncomputable def lib.binder_len (b : lib.BinderList) : Nat :=
  match b with | lib.BinderList.Nil => 0 | lib.BinderList.Cons _id _typ t => 1 + lib.binder_len t.deref
termination_by structural b
noncomputable def lib.param_bound_len (p : lib.ParamBoundList) : Nat :=
  match p with | lib.ParamBoundList.Nil => 0 | lib.ParamBoundList.NoBound t => 1 + lib.param_bound_len t.deref | lib.ParamBoundList.Bound _name _prop t => 1 + lib.param_bound_len t.deref
termination_by structural p
noncomputable def lib.frame_len (f : lib.FrameList) : Nat :=
  match f with | lib.FrameList.FNil => 0 | lib.FrameList.FBind _id _typ t => 1 + lib.frame_len t.deref | lib.FrameList.FHyp _hn _h t => 1 + lib.frame_len t.deref | lib.FrameList.FLetH _x _ty _v _en _ep t => 1 + lib.frame_len t.deref | lib.FrameList.FLet _id _v t => 1 + lib.frame_len t.deref
termination_by structural f
noncomputable def lib.stm_size (s : lib.StmData) : Nat :=
  match s with | lib.StmData.Assert _o _h => 1 | lib.StmData.Assume _e => 1 | lib.StmData.Assign _d _r => 1 | lib.StmData.Call reqs post => 1 + lib.raw_exp_list_len reqs.deref + lib.frame_len post.deref | lib.StmData.DeadEnd b => 1 + lib.stm_size b.deref | lib.StmData.AssertQueryNl b => 1 + lib.stm_size b.deref | lib.StmData.Ret es _rb => 1 + lib.raw_exp_list_len es.deref | lib.StmData.If _c _nc t e => 1 + lib.stm_size t.deref + lib.stm_size e.deref | lib.StmData.Loop inv_hyps inv_obligs binders _ _ _ _ _ _ _ body => 1 + lib.binder_len inv_hyps.deref + lib.raw_exp_list_len inv_obligs.deref + lib.binder_len binders.deref + lib.stm_size body.deref | lib.StmData.Skip => 1 | lib.StmData.Seq a b => 1 + lib.stm_size a.deref + lib.stm_size b.deref
termination_by structural s
noncomputable def lib.fnctx_arity (c : lib.FnCtxData) : Nat :=
  lib.binder_len c.params
noncomputable def lib.atom_ob (id : Int) : lib.RawExp :=
  lib.RawExp.Var id lib.TypData.TyBool
theorem lib.amended_shapes_kernel_compute :
    lib.stm_size (lib.StmData.Loop (Tactus.Box.mk (lib.BinderList.Cons 0 10 (Tactus.Box.mk lib.BinderList.Nil))) (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 10)) (Tactus.Box.mk lib.RawExpList.Nil))) (Tactus.Box.mk (lib.BinderList.Cons 3 4 (Tactus.Box.mk lib.BinderList.Nil))) (Tactus.Box.mk (lib.ParamBoundList.Bound 20 21 (Tactus.Box.mk lib.ParamBoundList.Nil))) 5 1 2 6 7 (lib.atom_ob 8) (Tactus.Box.mk lib.StmData.Skip)) = 5 ∧ lib.stm_size (lib.StmData.Call (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 0)) (Tactus.Box.mk lib.RawExpList.Nil))) (Tactus.Box.mk (lib.FrameList.FBind 5 6 (Tactus.Box.mk lib.FrameList.FNil)))) = 3 ∧ lib.stm_size (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 0)) (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 1)) (Tactus.Box.mk lib.RawExpList.Nil))))) lib.RetBind.RetNone) = 3 ∧ lib.stm_size (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 0)) (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 1)) (Tactus.Box.mk lib.RawExpList.Nil))))) (lib.RetBind.RetLet 23 9)) = 3 ∧ lib.binder_len (lib.BinderList.Cons 1 2 (Tactus.Box.mk lib.BinderList.Nil)) = 1 ∧ lib.param_bound_len (lib.ParamBoundList.Bound 4 5 (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))) = 2 ∧ lib.frame_len (lib.FrameList.FBind 1 2 (Tactus.Box.mk (lib.FrameList.FHyp 0 3 (Tactus.Box.mk (lib.FrameList.FLet 4 5 (Tactus.Box.mk lib.FrameList.FNil)))))) = 3 ∧ lib.fnctx_arity (lib.FnCtxData.mk (lib.BinderList.Cons 0 100 (Tactus.Box.mk lib.BinderList.Nil)) (lib.BinderList.Cons 1 101 (Tactus.Box.mk (lib.BinderList.Cons 2 102 (Tactus.Box.mk lib.BinderList.Nil)))) (lib.ParamBoundList.Bound 199 200 (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))) lib.BinderList.Nil (lib.LeafList.Cons 300 (Tactus.Box.mk lib.LeafList.Nil))) = 2 := by

  decide
