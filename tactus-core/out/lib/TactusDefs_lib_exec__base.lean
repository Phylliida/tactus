-- tactus defs part: base (base = machinery + instance closure; one part per source module, SCC-merged; umbrella = interface)
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
inductive lib.TypData where
  | TyInt
  | TyNat
  | TyBool
  | TyNamed (val0 : Int)
  | TyRef (val0 : Int)
  deriving Inhabited
@[simp] noncomputable def lib.TypData.height (_ : lib.TypData) : Nat :=
  1
inductive lib.CastKind where
  | IntToNat
  | NatToInt
  deriving Inhabited
@[simp] noncomputable def lib.CastKind.height (_ : lib.CastKind) : Nat :=
  1
inductive lib.ExprData where
  | Atom (val0 : Int)
  | Lit (val0 : Int)
  | LitBool (val0 : Nat)
  | Cast (val0 : lib.CastKind) (val1 : Tactus.Box lib.ExprData)
  | BinOp (val0 : Int) (val1 : Tactus.Box lib.ExprData) (val2 : Tactus.Box lib.ExprData)
  | App (val0 : Int) (val1 : Tactus.Box lib.ExprData)
  | FieldProj (val0 : Tactus.Box lib.ExprData) (val1 : Int)
  | SpanMark (val0 : Int) (val1 : Tactus.Box lib.ExprData)
  deriving Inhabited
@[simp] noncomputable def lib.ExprData.height (s : lib.ExprData) : Nat :=
  match s with | lib.ExprData.Atom _ => 1 | lib.ExprData.Lit _ => 1 | lib.ExprData.LitBool _ => 1 | lib.ExprData.Cast _ val1 => 1 + lib.ExprData.height val1.deref | lib.ExprData.BinOp _ val1 val2 => 1 + lib.ExprData.height val1.deref + lib.ExprData.height val2.deref | lib.ExprData.App _ val1 => 1 + lib.ExprData.height val1.deref | lib.ExprData.FieldProj val0 _ => 1 + lib.ExprData.height val0.deref | lib.ExprData.SpanMark _ val1 => 1 + lib.ExprData.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
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
  | Span (val0 : Int) (val1 : Tactus.Box lib.RawExp)
  deriving Inhabited
@[simp] noncomputable def lib.RawExp.height (s : lib.RawExp) : Nat :=
  match s with | lib.RawExp.Var _ _ => 1 | lib.RawExp.Lit _ _ => 1 | lib.RawExp.LitBool _ => 1 | lib.RawExp.Clip _ val1 => 1 + lib.RawExp.height val1.deref | lib.RawExp.BinOp _ _ val2 val3 => 1 + lib.RawExp.height val2.deref + lib.RawExp.height val3.deref | lib.RawExp.Call _ _ val2 _ => 1 + lib.RawExp.height val2.deref | lib.RawExp.Field _ _ val2 => 1 + lib.RawExp.height val2.deref | lib.RawExp.HasType _ val1 => 1 + lib.RawExp.height val1.deref | lib.RawExp.Deref val0 => 1 + lib.RawExp.height val0.deref | lib.RawExp.Span _ val1 => 1 + lib.RawExp.height val1.deref
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
inductive lib.GoalList where
  | Nil
  | Cons (val0 : Tactus.Box lib.GoalData) (val1 : Tactus.Box lib.GoalList)
  deriving Inhabited
@[simp] noncomputable def lib.GoalList.height (s : lib.GoalList) : Nat :=
  match s with | lib.GoalList.Nil => 1 | lib.GoalList.Cons _ val1 => 1 + lib.GoalList.height val1.deref
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
