import TactusDefs
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
import TactusSearch
set_option autoImplicit false
inductive lib.LeafList where
  | Nil
  | Cons (val0 : Int) (val1 : Tactus.Box lib.LeafList)
  deriving Inhabited
@[simp] noncomputable def lib.LeafList.isNil (x : lib.LeafList) : Prop :=
  match x with | lib.LeafList.Nil => True | _ => False
@[simp] noncomputable def lib.LeafList.isCons (x : lib.LeafList) : Prop :=
  match x with | lib.LeafList.Cons _ _ => True | _ => False
@[simp] noncomputable def lib.LeafList.Cons_val0 (x : lib.LeafList) : Int :=
  match x with | lib.LeafList.Cons val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.LeafList.Cons_val1 (x : lib.LeafList) : Tactus.Box lib.LeafList :=
  match x with | lib.LeafList.Cons _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.LeafList.height (s : lib.LeafList) : Nat :=
  match s with | lib.LeafList.Nil => 1 | lib.LeafList.Cons _ val1 => 1 + lib.LeafList.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
inductive lib.BinderIdList where
  | Nil
  | Cons (val0 : Int) (val1 : Tactus.Box lib.BinderIdList)
  deriving Inhabited
@[simp] noncomputable def lib.BinderIdList.isNil (x : lib.BinderIdList) : Prop :=
  match x with | lib.BinderIdList.Nil => True | _ => False
@[simp] noncomputable def lib.BinderIdList.isCons (x : lib.BinderIdList) : Prop :=
  match x with | lib.BinderIdList.Cons _ _ => True | _ => False
@[simp] noncomputable def lib.BinderIdList.Cons_val0 (x : lib.BinderIdList) : Int :=
  match x with | lib.BinderIdList.Cons val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.BinderIdList.Cons_val1 (x : lib.BinderIdList) : Tactus.Box lib.BinderIdList :=
  match x with | lib.BinderIdList.Cons _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.BinderIdList.height (s : lib.BinderIdList) : Nat :=
  match s with | lib.BinderIdList.Nil => 1 | lib.BinderIdList.Cons _ val1 => 1 + lib.BinderIdList.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
inductive lib.BinderList where
  | Nil
  | Cons (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.BinderList)
  deriving Inhabited
@[simp] noncomputable def lib.BinderList.isNil (x : lib.BinderList) : Prop :=
  match x with | lib.BinderList.Nil => True | _ => False
@[simp] noncomputable def lib.BinderList.isCons (x : lib.BinderList) : Prop :=
  match x with | lib.BinderList.Cons _ _ _ => True | _ => False
@[simp] noncomputable def lib.BinderList.Cons_val0 (x : lib.BinderList) : Int :=
  match x with | lib.BinderList.Cons val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.BinderList.Cons_val1 (x : lib.BinderList) : Int :=
  match x with | lib.BinderList.Cons _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.BinderList.Cons_val2 (x : lib.BinderList) : Tactus.Box lib.BinderList :=
  match x with | lib.BinderList.Cons _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.BinderList.height (s : lib.BinderList) : Nat :=
  match s with | lib.BinderList.Nil => 1 | lib.BinderList.Cons _ _ val2 => 1 + lib.BinderList.height val2.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
inductive lib.ParamBoundList where
  | Nil
  | NoBound (val0 : Tactus.Box lib.ParamBoundList)
  | Bound (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.ParamBoundList)
  deriving Inhabited
@[simp] noncomputable def lib.ParamBoundList.isNil (x : lib.ParamBoundList) : Prop :=
  match x with | lib.ParamBoundList.Nil => True | _ => False
@[simp] noncomputable def lib.ParamBoundList.isNoBound (x : lib.ParamBoundList) : Prop :=
  match x with | lib.ParamBoundList.NoBound _ => True | _ => False
@[simp] noncomputable def lib.ParamBoundList.isBound (x : lib.ParamBoundList) : Prop :=
  match x with | lib.ParamBoundList.Bound _ _ _ => True | _ => False
@[simp] noncomputable def lib.ParamBoundList.NoBound_val0 (x : lib.ParamBoundList) : Tactus.Box lib.ParamBoundList :=
  match x with | lib.ParamBoundList.NoBound val0 => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ParamBoundList.Bound_val0 (x : lib.ParamBoundList) : Int :=
  match x with | lib.ParamBoundList.Bound val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ParamBoundList.Bound_val1 (x : lib.ParamBoundList) : Int :=
  match x with | lib.ParamBoundList.Bound _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ParamBoundList.Bound_val2 (x : lib.ParamBoundList) : Tactus.Box lib.ParamBoundList :=
  match x with | lib.ParamBoundList.Bound _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ParamBoundList.height (s : lib.ParamBoundList) : Nat :=
  match s with | lib.ParamBoundList.Nil => 1 | lib.ParamBoundList.NoBound val0 => 1 + lib.ParamBoundList.height val0.deref | lib.ParamBoundList.Bound _ _ val2 => 1 + lib.ParamBoundList.height val2.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
inductive lib.RetBind where
  | RetNone
  | RetLet (val0 : Int) (val1 : Int)
  deriving Inhabited
@[simp] noncomputable def lib.RetBind.isRetNone (x : lib.RetBind) : Prop :=
  match x with | lib.RetBind.RetNone => True | _ => False
@[simp] noncomputable def lib.RetBind.isRetLet (x : lib.RetBind) : Prop :=
  match x with | lib.RetBind.RetLet _ _ => True | _ => False
@[simp] noncomputable def lib.RetBind.RetLet_val0 (x : lib.RetBind) : Int :=
  match x with | lib.RetBind.RetLet val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RetBind.RetLet_val1 (x : lib.RetBind) : Int :=
  match x with | lib.RetBind.RetLet _ val1 => val1 | _ => Classical.ofNonempty
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
@[simp] noncomputable def lib.TypData.isTyInt (x : lib.TypData) : Prop :=
  match x with | lib.TypData.TyInt => True | _ => False
@[simp] noncomputable def lib.TypData.isTyNat (x : lib.TypData) : Prop :=
  match x with | lib.TypData.TyNat => True | _ => False
@[simp] noncomputable def lib.TypData.isTyBool (x : lib.TypData) : Prop :=
  match x with | lib.TypData.TyBool => True | _ => False
@[simp] noncomputable def lib.TypData.isTyNamed (x : lib.TypData) : Prop :=
  match x with | lib.TypData.TyNamed _ => True | _ => False
@[simp] noncomputable def lib.TypData.isTyRef (x : lib.TypData) : Prop :=
  match x with | lib.TypData.TyRef _ => True | _ => False
@[simp] noncomputable def lib.TypData.isTyBox (x : lib.TypData) : Prop :=
  match x with | lib.TypData.TyBox _ => True | _ => False
@[simp] noncomputable def lib.TypData.TyNamed_val0 (x : lib.TypData) : Int :=
  match x with | lib.TypData.TyNamed val0 => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.TypData.TyRef_val0 (x : lib.TypData) : Int :=
  match x with | lib.TypData.TyRef val0 => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.TypData.TyBox_val0 (x : lib.TypData) : Int :=
  match x with | lib.TypData.TyBox val0 => val0 | _ => Classical.ofNonempty
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
inductive lib.RawList where
  | Nil
  | Cons (val0 : Tactus.Box lib.RawExp) (val1 : Tactus.Box lib.RawList)
  deriving Inhabited
inductive lib.RawArmList where
  | Nil
  | Cons (val0 : Int) (val1 : lib.BinderIdList) (val2 : Tactus.Box lib.RawExp) (val3 : Tactus.Box lib.RawArmList)
  deriving Inhabited
end

@[simp] noncomputable def lib.RawExp.isVar (x : lib.RawExp) : Prop :=
  match x with | lib.RawExp.Var _ _ => True | _ => False
@[simp] noncomputable def lib.RawExp.isLit (x : lib.RawExp) : Prop :=
  match x with | lib.RawExp.Lit _ _ => True | _ => False
@[simp] noncomputable def lib.RawExp.isLitBool (x : lib.RawExp) : Prop :=
  match x with | lib.RawExp.LitBool _ => True | _ => False
@[simp] noncomputable def lib.RawExp.isClip (x : lib.RawExp) : Prop :=
  match x with | lib.RawExp.Clip _ _ => True | _ => False
@[simp] noncomputable def lib.RawExp.isBinOp (x : lib.RawExp) : Prop :=
  match x with | lib.RawExp.BinOp _ _ _ _ => True | _ => False
@[simp] noncomputable def lib.RawExp.isCall (x : lib.RawExp) : Prop :=
  match x with | lib.RawExp.Call _ _ _ _ => True | _ => False
@[simp] noncomputable def lib.RawExp.isField (x : lib.RawExp) : Prop :=
  match x with | lib.RawExp.Field _ _ _ => True | _ => False
@[simp] noncomputable def lib.RawExp.isHasType (x : lib.RawExp) : Prop :=
  match x with | lib.RawExp.HasType _ _ => True | _ => False
@[simp] noncomputable def lib.RawExp.isDeref (x : lib.RawExp) : Prop :=
  match x with | lib.RawExp.Deref _ => True | _ => False
@[simp] noncomputable def lib.RawExp.isLet (x : lib.RawExp) : Prop :=
  match x with | lib.RawExp.Let _ _ _ => True | _ => False
@[simp] noncomputable def lib.RawExp.isNot (x : lib.RawExp) : Prop :=
  match x with | lib.RawExp.Not _ => True | _ => False
@[simp] noncomputable def lib.RawExp.isSpan (x : lib.RawExp) : Prop :=
  match x with | lib.RawExp.Span _ _ => True | _ => False
@[simp] noncomputable def lib.RawExp.isIte (x : lib.RawExp) : Prop :=
  match x with | lib.RawExp.Ite _ _ _ _ => True | _ => False
@[simp] noncomputable def lib.RawExp.isMatchR (x : lib.RawExp) : Prop :=
  match x with | lib.RawExp.MatchR _ _ _ => True | _ => False
@[simp] noncomputable def lib.RawExp.isCallN (x : lib.RawExp) : Prop :=
  match x with | lib.RawExp.CallN _ _ _ => True | _ => False
@[simp] noncomputable def lib.RawExp.isForallR (x : lib.RawExp) : Prop :=
  match x with | lib.RawExp.ForallR _ _ _ => True | _ => False
@[simp] noncomputable def lib.RawExp.isExistsR (x : lib.RawExp) : Prop :=
  match x with | lib.RawExp.ExistsR _ _ _ => True | _ => False
@[simp] noncomputable def lib.RawExp.Var_val0 (x : lib.RawExp) : Int :=
  match x with | lib.RawExp.Var val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Var_val1 (x : lib.RawExp) : lib.TypData :=
  match x with | lib.RawExp.Var _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Lit_val0 (x : lib.RawExp) : Int :=
  match x with | lib.RawExp.Lit val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Lit_val1 (x : lib.RawExp) : lib.TypData :=
  match x with | lib.RawExp.Lit _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.LitBool_val0 (x : lib.RawExp) : Nat :=
  match x with | lib.RawExp.LitBool val0 => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Clip_val0 (x : lib.RawExp) : lib.TypData :=
  match x with | lib.RawExp.Clip val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Clip_val1 (x : lib.RawExp) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExp.Clip _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.BinOp_val0 (x : lib.RawExp) : Int :=
  match x with | lib.RawExp.BinOp val0 _ _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.BinOp_val1 (x : lib.RawExp) : lib.TypData :=
  match x with | lib.RawExp.BinOp _ val1 _ _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.BinOp_val2 (x : lib.RawExp) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExp.BinOp _ _ val2 _ => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.BinOp_val3 (x : lib.RawExp) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExp.BinOp _ _ _ val3 => val3 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Call_val0 (x : lib.RawExp) : Int :=
  match x with | lib.RawExp.Call val0 _ _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Call_val1 (x : lib.RawExp) : lib.TypData :=
  match x with | lib.RawExp.Call _ val1 _ _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Call_val2 (x : lib.RawExp) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExp.Call _ _ val2 _ => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Call_val3 (x : lib.RawExp) : lib.TypData :=
  match x with | lib.RawExp.Call _ _ _ val3 => val3 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Field_val0 (x : lib.RawExp) : Int :=
  match x with | lib.RawExp.Field val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Field_val1 (x : lib.RawExp) : lib.TypData :=
  match x with | lib.RawExp.Field _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Field_val2 (x : lib.RawExp) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExp.Field _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.HasType_val0 (x : lib.RawExp) : Int :=
  match x with | lib.RawExp.HasType val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.HasType_val1 (x : lib.RawExp) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExp.HasType _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Deref_val0 (x : lib.RawExp) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExp.Deref val0 => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Let_val0 (x : lib.RawExp) : Int :=
  match x with | lib.RawExp.Let val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Let_val1 (x : lib.RawExp) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExp.Let _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Let_val2 (x : lib.RawExp) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExp.Let _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Not_val0 (x : lib.RawExp) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExp.Not val0 => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Span_val0 (x : lib.RawExp) : Int :=
  match x with | lib.RawExp.Span val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Span_val1 (x : lib.RawExp) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExp.Span _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Ite_val0 (x : lib.RawExp) : lib.TypData :=
  match x with | lib.RawExp.Ite val0 _ _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Ite_val1 (x : lib.RawExp) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExp.Ite _ val1 _ _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Ite_val2 (x : lib.RawExp) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExp.Ite _ _ val2 _ => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.Ite_val3 (x : lib.RawExp) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExp.Ite _ _ _ val3 => val3 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.MatchR_val0 (x : lib.RawExp) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExp.MatchR val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.MatchR_val1 (x : lib.RawExp) : Tactus.Box lib.RawArmList :=
  match x with | lib.RawExp.MatchR _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.MatchR_val2 (x : lib.RawExp) : lib.TypData :=
  match x with | lib.RawExp.MatchR _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.CallN_val0 (x : lib.RawExp) : Int :=
  match x with | lib.RawExp.CallN val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.CallN_val1 (x : lib.RawExp) : lib.TypData :=
  match x with | lib.RawExp.CallN _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.CallN_val2 (x : lib.RawExp) : Tactus.Box lib.RawList :=
  match x with | lib.RawExp.CallN _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.ForallR_val0 (x : lib.RawExp) : Int :=
  match x with | lib.RawExp.ForallR val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.ForallR_val1 (x : lib.RawExp) : lib.TypData :=
  match x with | lib.RawExp.ForallR _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.ForallR_val2 (x : lib.RawExp) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExp.ForallR _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.ExistsR_val0 (x : lib.RawExp) : Int :=
  match x with | lib.RawExp.ExistsR val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.ExistsR_val1 (x : lib.RawExp) : lib.TypData :=
  match x with | lib.RawExp.ExistsR _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExp.ExistsR_val2 (x : lib.RawExp) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExp.ExistsR _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawList.isNil (x : lib.RawList) : Prop :=
  match x with | lib.RawList.Nil => True | _ => False
@[simp] noncomputable def lib.RawList.isCons (x : lib.RawList) : Prop :=
  match x with | lib.RawList.Cons _ _ => True | _ => False
@[simp] noncomputable def lib.RawList.Cons_val0 (x : lib.RawList) : Tactus.Box lib.RawExp :=
  match x with | lib.RawList.Cons val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawList.Cons_val1 (x : lib.RawList) : Tactus.Box lib.RawList :=
  match x with | lib.RawList.Cons _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawArmList.isNil (x : lib.RawArmList) : Prop :=
  match x with | lib.RawArmList.Nil => True | _ => False
@[simp] noncomputable def lib.RawArmList.isCons (x : lib.RawArmList) : Prop :=
  match x with | lib.RawArmList.Cons _ _ _ _ => True | _ => False
@[simp] noncomputable def lib.RawArmList.Cons_val0 (x : lib.RawArmList) : Int :=
  match x with | lib.RawArmList.Cons val0 _ _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawArmList.Cons_val1 (x : lib.RawArmList) : lib.BinderIdList :=
  match x with | lib.RawArmList.Cons _ val1 _ _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawArmList.Cons_val2 (x : lib.RawArmList) : Tactus.Box lib.RawExp :=
  match x with | lib.RawArmList.Cons _ _ val2 _ => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawArmList.Cons_val3 (x : lib.RawArmList) : Tactus.Box lib.RawArmList :=
  match x with | lib.RawArmList.Cons _ _ _ val3 => val3 | _ => Classical.ofNonempty
mutual
@[simp] noncomputable def lib.RawExp.height (s : lib.RawExp) : Nat :=
  match s with | lib.RawExp.Var _ _ => 1 | lib.RawExp.Lit _ _ => 1 | lib.RawExp.LitBool _ => 1 | lib.RawExp.Clip _ val1 => 1 + lib.RawExp.height val1.deref | lib.RawExp.BinOp _ _ val2 val3 => 1 + lib.RawExp.height val2.deref + lib.RawExp.height val3.deref | lib.RawExp.Call _ _ val2 _ => 1 + lib.RawExp.height val2.deref | lib.RawExp.Field _ _ val2 => 1 + lib.RawExp.height val2.deref | lib.RawExp.HasType _ val1 => 1 + lib.RawExp.height val1.deref | lib.RawExp.Deref val0 => 1 + lib.RawExp.height val0.deref | lib.RawExp.Let _ val1 val2 => 1 + lib.RawExp.height val1.deref + lib.RawExp.height val2.deref | lib.RawExp.Not val0 => 1 + lib.RawExp.height val0.deref | lib.RawExp.Span _ val1 => 1 + lib.RawExp.height val1.deref | lib.RawExp.Ite _ val1 val2 val3 => 1 + lib.RawExp.height val1.deref + lib.RawExp.height val2.deref + lib.RawExp.height val3.deref | lib.RawExp.MatchR val0 val1 _ => 1 + lib.RawExp.height val0.deref + lib.RawArmList.height val1.deref | lib.RawExp.CallN _ _ val2 => 1 + lib.RawList.height val2.deref | lib.RawExp.ForallR _ _ val2 => 1 + lib.RawExp.height val2.deref | lib.RawExp.ExistsR _ _ val2 => 1 + lib.RawExp.height val2.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
@[simp] noncomputable def lib.RawList.height (s : lib.RawList) : Nat :=
  match s with | lib.RawList.Nil => 1 | lib.RawList.Cons val0 val1 => 1 + lib.RawExp.height val0.deref + lib.RawList.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
@[simp] noncomputable def lib.RawArmList.height (s : lib.RawArmList) : Nat :=
  match s with | lib.RawArmList.Nil => 1 | lib.RawArmList.Cons _ _ val2 val3 => 1 + lib.RawExp.height val2.deref + lib.RawArmList.height val3.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
end

inductive lib.RawExpList where
  | Nil
  | Cons (val0 : Tactus.Box lib.RawExp) (val1 : Tactus.Box lib.RawExpList)
  deriving Inhabited
@[simp] noncomputable def lib.RawExpList.isNil (x : lib.RawExpList) : Prop :=
  match x with | lib.RawExpList.Nil => True | _ => False
@[simp] noncomputable def lib.RawExpList.isCons (x : lib.RawExpList) : Prop :=
  match x with | lib.RawExpList.Cons _ _ => True | _ => False
@[simp] noncomputable def lib.RawExpList.Cons_val0 (x : lib.RawExpList) : Tactus.Box lib.RawExp :=
  match x with | lib.RawExpList.Cons val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.RawExpList.Cons_val1 (x : lib.RawExpList) : Tactus.Box lib.RawExpList :=
  match x with | lib.RawExpList.Cons _ val1 => val1 | _ => Classical.ofNonempty
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
@[simp] noncomputable def lib.FrameList.isFNil (x : lib.FrameList) : Prop :=
  match x with | lib.FrameList.FNil => True | _ => False
@[simp] noncomputable def lib.FrameList.isFBind (x : lib.FrameList) : Prop :=
  match x with | lib.FrameList.FBind _ _ _ => True | _ => False
@[simp] noncomputable def lib.FrameList.isFHyp (x : lib.FrameList) : Prop :=
  match x with | lib.FrameList.FHyp _ _ _ => True | _ => False
@[simp] noncomputable def lib.FrameList.isFLet (x : lib.FrameList) : Prop :=
  match x with | lib.FrameList.FLet _ _ _ => True | _ => False
@[simp] noncomputable def lib.FrameList.isFLetH (x : lib.FrameList) : Prop :=
  match x with | lib.FrameList.FLetH _ _ _ _ _ _ => True | _ => False
@[simp] noncomputable def lib.FrameList.FBind_val0 (x : lib.FrameList) : Int :=
  match x with | lib.FrameList.FBind val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FBind_val1 (x : lib.FrameList) : Int :=
  match x with | lib.FrameList.FBind _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FBind_val2 (x : lib.FrameList) : Tactus.Box lib.FrameList :=
  match x with | lib.FrameList.FBind _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FHyp_val0 (x : lib.FrameList) : Int :=
  match x with | lib.FrameList.FHyp val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FHyp_val1 (x : lib.FrameList) : Int :=
  match x with | lib.FrameList.FHyp _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FHyp_val2 (x : lib.FrameList) : Tactus.Box lib.FrameList :=
  match x with | lib.FrameList.FHyp _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FLet_val0 (x : lib.FrameList) : Int :=
  match x with | lib.FrameList.FLet val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FLet_val1 (x : lib.FrameList) : Int :=
  match x with | lib.FrameList.FLet _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FLet_val2 (x : lib.FrameList) : Tactus.Box lib.FrameList :=
  match x with | lib.FrameList.FLet _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FLetH_val0 (x : lib.FrameList) : Int :=
  match x with | lib.FrameList.FLetH val0 _ _ _ _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FLetH_val1 (x : lib.FrameList) : Int :=
  match x with | lib.FrameList.FLetH _ val1 _ _ _ _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FLetH_val2 (x : lib.FrameList) : Int :=
  match x with | lib.FrameList.FLetH _ _ val2 _ _ _ => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FLetH_val3 (x : lib.FrameList) : Int :=
  match x with | lib.FrameList.FLetH _ _ _ val3 _ _ => val3 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FLetH_val4 (x : lib.FrameList) : Int :=
  match x with | lib.FrameList.FLetH _ _ _ _ val4 _ => val4 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FLetH_val5 (x : lib.FrameList) : Tactus.Box lib.FrameList :=
  match x with | lib.FrameList.FLetH _ _ _ _ _ val5 => val5 | _ => Classical.ofNonempty
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
@[simp] noncomputable def lib.StmData.isAssert (x : lib.StmData) : Prop :=
  match x with | lib.StmData.Assert _ _ => True | _ => False
@[simp] noncomputable def lib.StmData.isAssume (x : lib.StmData) : Prop :=
  match x with | lib.StmData.Assume _ => True | _ => False
@[simp] noncomputable def lib.StmData.isAssign (x : lib.StmData) : Prop :=
  match x with | lib.StmData.Assign _ _ => True | _ => False
@[simp] noncomputable def lib.StmData.isCall (x : lib.StmData) : Prop :=
  match x with | lib.StmData.Call _ _ => True | _ => False
@[simp] noncomputable def lib.StmData.isDeadEnd (x : lib.StmData) : Prop :=
  match x with | lib.StmData.DeadEnd _ => True | _ => False
@[simp] noncomputable def lib.StmData.isRet (x : lib.StmData) : Prop :=
  match x with | lib.StmData.Ret _ _ => True | _ => False
@[simp] noncomputable def lib.StmData.isIf (x : lib.StmData) : Prop :=
  match x with | lib.StmData.If _ _ _ _ => True | _ => False
@[simp] noncomputable def lib.StmData.isLoop (x : lib.StmData) : Prop :=
  match x with | lib.StmData.Loop _ _ _ _ _ _ _ _ _ _ _ => True | _ => False
@[simp] noncomputable def lib.StmData.isAssertQueryNl (x : lib.StmData) : Prop :=
  match x with | lib.StmData.AssertQueryNl _ => True | _ => False
@[simp] noncomputable def lib.StmData.isSkip (x : lib.StmData) : Prop :=
  match x with | lib.StmData.Skip => True | _ => False
@[simp] noncomputable def lib.StmData.isSeq (x : lib.StmData) : Prop :=
  match x with | lib.StmData.Seq _ _ => True | _ => False
@[simp] noncomputable def lib.StmData.Assert_val0 (x : lib.StmData) : lib.RawExp :=
  match x with | lib.StmData.Assert val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Assert_val1 (x : lib.StmData) : Int :=
  match x with | lib.StmData.Assert _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Assume_val0 (x : lib.StmData) : Int :=
  match x with | lib.StmData.Assume val0 => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Assign_val0 (x : lib.StmData) : Int :=
  match x with | lib.StmData.Assign val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Assign_val1 (x : lib.StmData) : Int :=
  match x with | lib.StmData.Assign _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Call_reqs (x : lib.StmData) : Tactus.Box lib.RawExpList :=
  match x with | lib.StmData.Call reqs _ => reqs | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Call_post (x : lib.StmData) : Tactus.Box lib.FrameList :=
  match x with | lib.StmData.Call _ post => post | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.DeadEnd_val0 (x : lib.StmData) : Tactus.Box lib.StmData :=
  match x with | lib.StmData.DeadEnd val0 => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Ret_val0 (x : lib.StmData) : Tactus.Box lib.RawExpList :=
  match x with | lib.StmData.Ret val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Ret_val1 (x : lib.StmData) : lib.RetBind :=
  match x with | lib.StmData.Ret _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.If_val0 (x : lib.StmData) : Int :=
  match x with | lib.StmData.If val0 _ _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.If_val1 (x : lib.StmData) : Int :=
  match x with | lib.StmData.If _ val1 _ _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.If_val2 (x : lib.StmData) : Tactus.Box lib.StmData :=
  match x with | lib.StmData.If _ _ val2 _ => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.If_val3 (x : lib.StmData) : Tactus.Box lib.StmData :=
  match x with | lib.StmData.If _ _ _ val3 => val3 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Loop_inv_hyps (x : lib.StmData) : Tactus.Box lib.BinderList :=
  match x with | lib.StmData.Loop inv_hyps _ _ _ _ _ _ _ _ _ _ => inv_hyps | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Loop_inv_obligs (x : lib.StmData) : Tactus.Box lib.RawExpList :=
  match x with | lib.StmData.Loop _ inv_obligs _ _ _ _ _ _ _ _ _ => inv_obligs | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Loop_binders (x : lib.StmData) : Tactus.Box lib.BinderList :=
  match x with | lib.StmData.Loop _ _ binders _ _ _ _ _ _ _ _ => binders | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Loop_binder_bounds (x : lib.StmData) : Tactus.Box lib.ParamBoundList :=
  match x with | lib.StmData.Loop _ _ _ binder_bounds _ _ _ _ _ _ _ => binder_bounds | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Loop_cond_name (x : lib.StmData) : Int :=
  match x with | lib.StmData.Loop _ _ _ _ cond_name _ _ _ _ _ _ => cond_name | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Loop_cond_ann (x : lib.StmData) : Int :=
  match x with | lib.StmData.Loop _ _ _ _ _ cond_ann _ _ _ _ _ => cond_ann | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Loop_neg_cond_ann (x : lib.StmData) : Int :=
  match x with | lib.StmData.Loop _ _ _ _ _ _ neg_cond_ann _ _ _ _ => neg_cond_ann | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Loop_d_old_name (x : lib.StmData) : Int :=
  match x with | lib.StmData.Loop _ _ _ _ _ _ _ d_old_name _ _ _ => d_old_name | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Loop_d_old_val (x : lib.StmData) : Int :=
  match x with | lib.StmData.Loop _ _ _ _ _ _ _ _ d_old_val _ _ => d_old_val | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Loop_decrease_oblig (x : lib.StmData) : lib.RawExp :=
  match x with | lib.StmData.Loop _ _ _ _ _ _ _ _ _ decrease_oblig _ => decrease_oblig | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Loop_body (x : lib.StmData) : Tactus.Box lib.StmData :=
  match x with | lib.StmData.Loop _ _ _ _ _ _ _ _ _ _ body => body | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.AssertQueryNl_val0 (x : lib.StmData) : Tactus.Box lib.StmData :=
  match x with | lib.StmData.AssertQueryNl val0 => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Seq_val0 (x : lib.StmData) : Tactus.Box lib.StmData :=
  match x with | lib.StmData.Seq val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Seq_val1 (x : lib.StmData) : Tactus.Box lib.StmData :=
  match x with | lib.StmData.Seq _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.height (s : lib.StmData) : Nat :=
  match s with | lib.StmData.Assert _ _ => 1 | lib.StmData.Assume _ => 1 | lib.StmData.Assign _ _ => 1 | lib.StmData.Call _ _ => 1 | lib.StmData.DeadEnd val0 => 1 + lib.StmData.height val0.deref | lib.StmData.Ret _ _ => 1 | lib.StmData.If _ _ val2 val3 => 1 + lib.StmData.height val2.deref + lib.StmData.height val3.deref | lib.StmData.Loop _ _ _ _ _ _ _ _ _ _ body => 1 + lib.StmData.height body.deref | lib.StmData.AssertQueryNl val0 => 1 + lib.StmData.height val0.deref | lib.StmData.Skip => 1 | lib.StmData.Seq val0 val1 => 1 + lib.StmData.height val0.deref + lib.StmData.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
inductive lib.CastKind where
  | IntToNat
  | NatToInt
  deriving Inhabited
@[simp] noncomputable def lib.CastKind.isIntToNat (x : lib.CastKind) : Prop :=
  match x with | lib.CastKind.IntToNat => True | _ => False
@[simp] noncomputable def lib.CastKind.isNatToInt (x : lib.CastKind) : Prop :=
  match x with | lib.CastKind.NatToInt => True | _ => False
@[simp] noncomputable def lib.CastKind.height (_ : lib.CastKind) : Nat :=
  1
mutual
inductive lib.ExprData where
  | Atom (val0 : Int)
  | Lit (val0 : Int)
  | LitBool (val0 : Nat)
  | Cast (val0 : lib.CastKind) (val1 : Tactus.Box lib.ExprData)
  | BinOp (val0 : Int) (val1 : Tactus.Box lib.ExprData) (val2 : Tactus.Box lib.ExprData)
  | App (val0 : Int) (val1 : Tactus.Box lib.ExprData)
  | FieldProj (val0 : Tactus.Box lib.ExprData) (val1 : Int)
  | SpanMark (val0 : Int) (val1 : Tactus.Box lib.ExprData)
  | Let (val0 : Int) (val1 : Tactus.Box lib.ExprData) (val2 : Tactus.Box lib.ExprData)
  | Not (val0 : Tactus.Box lib.ExprData)
  | Ite (val0 : Tactus.Box lib.ExprData) (val1 : Tactus.Box lib.ExprData) (val2 : Tactus.Box lib.ExprData)
  | Match (val0 : Tactus.Box lib.ExprData) (val1 : Tactus.Box lib.ArmList)
  | AppN (val0 : Int) (val1 : Tactus.Box lib.ExprList)
  | Forall (val0 : Int) (val1 : lib.TypData) (val2 : Tactus.Box lib.ExprData)
  | Exists (val0 : Int) (val1 : lib.TypData) (val2 : Tactus.Box lib.ExprData)
  deriving Inhabited
inductive lib.ExprList where
  | Nil
  | Cons (val0 : Tactus.Box lib.ExprData) (val1 : Tactus.Box lib.ExprList)
  deriving Inhabited
inductive lib.ArmList where
  | Nil
  | Cons (val0 : Int) (val1 : lib.BinderIdList) (val2 : Tactus.Box lib.ExprData) (val3 : Tactus.Box lib.ArmList)
  deriving Inhabited
end

@[simp] noncomputable def lib.ExprData.isAtom (x : lib.ExprData) : Prop :=
  match x with | lib.ExprData.Atom _ => True | _ => False
@[simp] noncomputable def lib.ExprData.isLit (x : lib.ExprData) : Prop :=
  match x with | lib.ExprData.Lit _ => True | _ => False
@[simp] noncomputable def lib.ExprData.isLitBool (x : lib.ExprData) : Prop :=
  match x with | lib.ExprData.LitBool _ => True | _ => False
@[simp] noncomputable def lib.ExprData.isCast (x : lib.ExprData) : Prop :=
  match x with | lib.ExprData.Cast _ _ => True | _ => False
@[simp] noncomputable def lib.ExprData.isBinOp (x : lib.ExprData) : Prop :=
  match x with | lib.ExprData.BinOp _ _ _ => True | _ => False
@[simp] noncomputable def lib.ExprData.isApp (x : lib.ExprData) : Prop :=
  match x with | lib.ExprData.App _ _ => True | _ => False
@[simp] noncomputable def lib.ExprData.isFieldProj (x : lib.ExprData) : Prop :=
  match x with | lib.ExprData.FieldProj _ _ => True | _ => False
@[simp] noncomputable def lib.ExprData.isSpanMark (x : lib.ExprData) : Prop :=
  match x with | lib.ExprData.SpanMark _ _ => True | _ => False
@[simp] noncomputable def lib.ExprData.isLet (x : lib.ExprData) : Prop :=
  match x with | lib.ExprData.Let _ _ _ => True | _ => False
@[simp] noncomputable def lib.ExprData.isNot (x : lib.ExprData) : Prop :=
  match x with | lib.ExprData.Not _ => True | _ => False
@[simp] noncomputable def lib.ExprData.isIte (x : lib.ExprData) : Prop :=
  match x with | lib.ExprData.Ite _ _ _ => True | _ => False
@[simp] noncomputable def lib.ExprData.isMatch (x : lib.ExprData) : Prop :=
  match x with | lib.ExprData.Match _ _ => True | _ => False
@[simp] noncomputable def lib.ExprData.isAppN (x : lib.ExprData) : Prop :=
  match x with | lib.ExprData.AppN _ _ => True | _ => False
@[simp] noncomputable def lib.ExprData.isForall (x : lib.ExprData) : Prop :=
  match x with | lib.ExprData.Forall _ _ _ => True | _ => False
@[simp] noncomputable def lib.ExprData.isExists (x : lib.ExprData) : Prop :=
  match x with | lib.ExprData.Exists _ _ _ => True | _ => False
@[simp] noncomputable def lib.ExprData.Atom_val0 (x : lib.ExprData) : Int :=
  match x with | lib.ExprData.Atom val0 => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Lit_val0 (x : lib.ExprData) : Int :=
  match x with | lib.ExprData.Lit val0 => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.LitBool_val0 (x : lib.ExprData) : Nat :=
  match x with | lib.ExprData.LitBool val0 => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Cast_val0 (x : lib.ExprData) : lib.CastKind :=
  match x with | lib.ExprData.Cast val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Cast_val1 (x : lib.ExprData) : Tactus.Box lib.ExprData :=
  match x with | lib.ExprData.Cast _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.BinOp_val0 (x : lib.ExprData) : Int :=
  match x with | lib.ExprData.BinOp val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.BinOp_val1 (x : lib.ExprData) : Tactus.Box lib.ExprData :=
  match x with | lib.ExprData.BinOp _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.BinOp_val2 (x : lib.ExprData) : Tactus.Box lib.ExprData :=
  match x with | lib.ExprData.BinOp _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.App_val0 (x : lib.ExprData) : Int :=
  match x with | lib.ExprData.App val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.App_val1 (x : lib.ExprData) : Tactus.Box lib.ExprData :=
  match x with | lib.ExprData.App _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.FieldProj_val0 (x : lib.ExprData) : Tactus.Box lib.ExprData :=
  match x with | lib.ExprData.FieldProj val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.FieldProj_val1 (x : lib.ExprData) : Int :=
  match x with | lib.ExprData.FieldProj _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.SpanMark_val0 (x : lib.ExprData) : Int :=
  match x with | lib.ExprData.SpanMark val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.SpanMark_val1 (x : lib.ExprData) : Tactus.Box lib.ExprData :=
  match x with | lib.ExprData.SpanMark _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Let_val0 (x : lib.ExprData) : Int :=
  match x with | lib.ExprData.Let val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Let_val1 (x : lib.ExprData) : Tactus.Box lib.ExprData :=
  match x with | lib.ExprData.Let _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Let_val2 (x : lib.ExprData) : Tactus.Box lib.ExprData :=
  match x with | lib.ExprData.Let _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Not_val0 (x : lib.ExprData) : Tactus.Box lib.ExprData :=
  match x with | lib.ExprData.Not val0 => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Ite_val0 (x : lib.ExprData) : Tactus.Box lib.ExprData :=
  match x with | lib.ExprData.Ite val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Ite_val1 (x : lib.ExprData) : Tactus.Box lib.ExprData :=
  match x with | lib.ExprData.Ite _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Ite_val2 (x : lib.ExprData) : Tactus.Box lib.ExprData :=
  match x with | lib.ExprData.Ite _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Match_val0 (x : lib.ExprData) : Tactus.Box lib.ExprData :=
  match x with | lib.ExprData.Match val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Match_val1 (x : lib.ExprData) : Tactus.Box lib.ArmList :=
  match x with | lib.ExprData.Match _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.AppN_val0 (x : lib.ExprData) : Int :=
  match x with | lib.ExprData.AppN val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.AppN_val1 (x : lib.ExprData) : Tactus.Box lib.ExprList :=
  match x with | lib.ExprData.AppN _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Forall_val0 (x : lib.ExprData) : Int :=
  match x with | lib.ExprData.Forall val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Forall_val1 (x : lib.ExprData) : lib.TypData :=
  match x with | lib.ExprData.Forall _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Forall_val2 (x : lib.ExprData) : Tactus.Box lib.ExprData :=
  match x with | lib.ExprData.Forall _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Exists_val0 (x : lib.ExprData) : Int :=
  match x with | lib.ExprData.Exists val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Exists_val1 (x : lib.ExprData) : lib.TypData :=
  match x with | lib.ExprData.Exists _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprData.Exists_val2 (x : lib.ExprData) : Tactus.Box lib.ExprData :=
  match x with | lib.ExprData.Exists _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprList.isNil (x : lib.ExprList) : Prop :=
  match x with | lib.ExprList.Nil => True | _ => False
@[simp] noncomputable def lib.ExprList.isCons (x : lib.ExprList) : Prop :=
  match x with | lib.ExprList.Cons _ _ => True | _ => False
@[simp] noncomputable def lib.ExprList.Cons_val0 (x : lib.ExprList) : Tactus.Box lib.ExprData :=
  match x with | lib.ExprList.Cons val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ExprList.Cons_val1 (x : lib.ExprList) : Tactus.Box lib.ExprList :=
  match x with | lib.ExprList.Cons _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ArmList.isNil (x : lib.ArmList) : Prop :=
  match x with | lib.ArmList.Nil => True | _ => False
@[simp] noncomputable def lib.ArmList.isCons (x : lib.ArmList) : Prop :=
  match x with | lib.ArmList.Cons _ _ _ _ => True | _ => False
@[simp] noncomputable def lib.ArmList.Cons_val0 (x : lib.ArmList) : Int :=
  match x with | lib.ArmList.Cons val0 _ _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ArmList.Cons_val1 (x : lib.ArmList) : lib.BinderIdList :=
  match x with | lib.ArmList.Cons _ val1 _ _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ArmList.Cons_val2 (x : lib.ArmList) : Tactus.Box lib.ExprData :=
  match x with | lib.ArmList.Cons _ _ val2 _ => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ArmList.Cons_val3 (x : lib.ArmList) : Tactus.Box lib.ArmList :=
  match x with | lib.ArmList.Cons _ _ _ val3 => val3 | _ => Classical.ofNonempty
mutual
@[simp] noncomputable def lib.ExprData.height (s : lib.ExprData) : Nat :=
  match s with | lib.ExprData.Atom _ => 1 | lib.ExprData.Lit _ => 1 | lib.ExprData.LitBool _ => 1 | lib.ExprData.Cast _ val1 => 1 + lib.ExprData.height val1.deref | lib.ExprData.BinOp _ val1 val2 => 1 + lib.ExprData.height val1.deref + lib.ExprData.height val2.deref | lib.ExprData.App _ val1 => 1 + lib.ExprData.height val1.deref | lib.ExprData.FieldProj val0 _ => 1 + lib.ExprData.height val0.deref | lib.ExprData.SpanMark _ val1 => 1 + lib.ExprData.height val1.deref | lib.ExprData.Let _ val1 val2 => 1 + lib.ExprData.height val1.deref + lib.ExprData.height val2.deref | lib.ExprData.Not val0 => 1 + lib.ExprData.height val0.deref | lib.ExprData.Ite val0 val1 val2 => 1 + lib.ExprData.height val0.deref + lib.ExprData.height val1.deref + lib.ExprData.height val2.deref | lib.ExprData.Match val0 val1 => 1 + lib.ExprData.height val0.deref + lib.ArmList.height val1.deref | lib.ExprData.AppN _ val1 => 1 + lib.ExprList.height val1.deref | lib.ExprData.Forall _ _ val2 => 1 + lib.ExprData.height val2.deref | lib.ExprData.Exists _ _ val2 => 1 + lib.ExprData.height val2.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
@[simp] noncomputable def lib.ExprList.height (s : lib.ExprList) : Nat :=
  match s with | lib.ExprList.Nil => 1 | lib.ExprList.Cons val0 val1 => 1 + lib.ExprData.height val0.deref + lib.ExprList.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
@[simp] noncomputable def lib.ArmList.height (s : lib.ArmList) : Nat :=
  match s with | lib.ArmList.Nil => 1 | lib.ArmList.Cons _ _ val2 val3 => 1 + lib.ExprData.height val2.deref + lib.ArmList.height val3.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
end

inductive lib.ParamList where
  | Nil
  | Cons (val0 : Int) (val1 : lib.TypData) (val2 : Tactus.Box lib.ParamList)
  deriving Inhabited
@[simp] noncomputable def lib.ParamList.isNil (x : lib.ParamList) : Prop :=
  match x with | lib.ParamList.Nil => True | _ => False
@[simp] noncomputable def lib.ParamList.isCons (x : lib.ParamList) : Prop :=
  match x with | lib.ParamList.Cons _ _ _ => True | _ => False
@[simp] noncomputable def lib.ParamList.Cons_val0 (x : lib.ParamList) : Int :=
  match x with | lib.ParamList.Cons val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ParamList.Cons_val1 (x : lib.ParamList) : lib.TypData :=
  match x with | lib.ParamList.Cons _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ParamList.Cons_val2 (x : lib.ParamList) : Tactus.Box lib.ParamList :=
  match x with | lib.ParamList.Cons _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.ParamList.height (s : lib.ParamList) : Nat :=
  match s with | lib.ParamList.Nil => 1 | lib.ParamList.Cons _ _ val2 => 1 + lib.ParamList.height val2.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
inductive lib.TypList where
  | Nil
  | Cons (val0 : lib.TypData) (val1 : Tactus.Box lib.TypList)
  deriving Inhabited
@[simp] noncomputable def lib.TypList.isNil (x : lib.TypList) : Prop :=
  match x with | lib.TypList.Nil => True | _ => False
@[simp] noncomputable def lib.TypList.isCons (x : lib.TypList) : Prop :=
  match x with | lib.TypList.Cons _ _ => True | _ => False
@[simp] noncomputable def lib.TypList.Cons_val0 (x : lib.TypList) : lib.TypData :=
  match x with | lib.TypList.Cons val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.TypList.Cons_val1 (x : lib.TypList) : Tactus.Box lib.TypList :=
  match x with | lib.TypList.Cons _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.TypList.height (s : lib.TypList) : Nat :=
  match s with | lib.TypList.Nil => 1 | lib.TypList.Cons _ val1 => 1 + lib.TypList.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
inductive lib.CtorList where
  | Nil
  | Cons (val0 : Int) (val1 : lib.TypList) (val2 : Tactus.Box lib.CtorList)
  deriving Inhabited
@[simp] noncomputable def lib.CtorList.isNil (x : lib.CtorList) : Prop :=
  match x with | lib.CtorList.Nil => True | _ => False
@[simp] noncomputable def lib.CtorList.isCons (x : lib.CtorList) : Prop :=
  match x with | lib.CtorList.Cons _ _ _ => True | _ => False
@[simp] noncomputable def lib.CtorList.Cons_val0 (x : lib.CtorList) : Int :=
  match x with | lib.CtorList.Cons val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.CtorList.Cons_val1 (x : lib.CtorList) : lib.TypList :=
  match x with | lib.CtorList.Cons _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.CtorList.Cons_val2 (x : lib.CtorList) : Tactus.Box lib.CtorList :=
  match x with | lib.CtorList.Cons _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.CtorList.height (s : lib.CtorList) : Nat :=
  match s with | lib.CtorList.Nil => 1 | lib.CtorList.Cons _ _ val2 => 1 + lib.CtorList.height val2.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
structure lib.DefData where
  name : Int
  params : lib.ParamList
  ret : lib.TypData
  body : lib.ExprData
  deriving Inhabited
@[simp] noncomputable def lib.DefData.height (_ : lib.DefData) : Nat :=
  1
structure lib.RawDef where
  name : Int
  params : lib.ParamList
  ret : lib.TypData
  body : lib.RawExp
  deriving Inhabited
@[simp] noncomputable def lib.RawDef.height (_ : lib.RawDef) : Nat :=
  1
structure lib.DtData where
  name : Int
  ctors : lib.CtorList
  deriving Inhabited
@[simp] noncomputable def lib.DtData.height (_ : lib.DtData) : Nat :=
  1
structure lib.RawDt where
  name : Int
  ctors : lib.CtorList
  deriving Inhabited
@[simp] noncomputable def lib.RawDt.height (_ : lib.RawDt) : Nat :=
  1
inductive lib.GoalData where
  | Leaf (val0 : Int)
  | Imp (val0 : Int) (val1 : Tactus.Box lib.GoalData)
  | All (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.GoalData)
  | Let (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.GoalData)
  | LeafE (val0 : lib.ExprData)
  deriving Inhabited
@[simp] noncomputable def lib.GoalData.isLeaf (x : lib.GoalData) : Prop :=
  match x with | lib.GoalData.Leaf _ => True | _ => False
@[simp] noncomputable def lib.GoalData.isImp (x : lib.GoalData) : Prop :=
  match x with | lib.GoalData.Imp _ _ => True | _ => False
@[simp] noncomputable def lib.GoalData.isAll (x : lib.GoalData) : Prop :=
  match x with | lib.GoalData.All _ _ _ => True | _ => False
@[simp] noncomputable def lib.GoalData.isLet (x : lib.GoalData) : Prop :=
  match x with | lib.GoalData.Let _ _ _ => True | _ => False
@[simp] noncomputable def lib.GoalData.isLeafE (x : lib.GoalData) : Prop :=
  match x with | lib.GoalData.LeafE _ => True | _ => False
@[simp] noncomputable def lib.GoalData.Leaf_val0 (x : lib.GoalData) : Int :=
  match x with | lib.GoalData.Leaf val0 => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.GoalData.Imp_val0 (x : lib.GoalData) : Int :=
  match x with | lib.GoalData.Imp val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.GoalData.Imp_val1 (x : lib.GoalData) : Tactus.Box lib.GoalData :=
  match x with | lib.GoalData.Imp _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.GoalData.All_val0 (x : lib.GoalData) : Int :=
  match x with | lib.GoalData.All val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.GoalData.All_val1 (x : lib.GoalData) : Int :=
  match x with | lib.GoalData.All _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.GoalData.All_val2 (x : lib.GoalData) : Tactus.Box lib.GoalData :=
  match x with | lib.GoalData.All _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.GoalData.Let_val0 (x : lib.GoalData) : Int :=
  match x with | lib.GoalData.Let val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.GoalData.Let_val1 (x : lib.GoalData) : Int :=
  match x with | lib.GoalData.Let _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.GoalData.Let_val2 (x : lib.GoalData) : Tactus.Box lib.GoalData :=
  match x with | lib.GoalData.Let _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.GoalData.LeafE_val0 (x : lib.GoalData) : lib.ExprData :=
  match x with | lib.GoalData.LeafE val0 => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.GoalData.height (s : lib.GoalData) : Nat :=
  match s with | lib.GoalData.Leaf _ => 1 | lib.GoalData.Imp _ val1 => 1 + lib.GoalData.height val1.deref | lib.GoalData.All _ _ val2 => 1 + lib.GoalData.height val2.deref | lib.GoalData.Let _ _ val2 => 1 + lib.GoalData.height val2.deref | lib.GoalData.LeafE _ => 1
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
inductive lib.GoalList where
  | Nil
  | Cons (val0 : Tactus.Box lib.GoalData) (val1 : Tactus.Box lib.GoalList)
  deriving Inhabited
@[simp] noncomputable def lib.GoalList.isNil (x : lib.GoalList) : Prop :=
  match x with | lib.GoalList.Nil => True | _ => False
@[simp] noncomputable def lib.GoalList.isCons (x : lib.GoalList) : Prop :=
  match x with | lib.GoalList.Cons _ _ => True | _ => False
@[simp] noncomputable def lib.GoalList.Cons_val0 (x : lib.GoalList) : Tactus.Box lib.GoalData :=
  match x with | lib.GoalList.Cons val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.GoalList.Cons_val1 (x : lib.GoalList) : Tactus.Box lib.GoalList :=
  match x with | lib.GoalList.Cons _ val1 => val1 | _ => Classical.ofNonempty
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
noncomputable def lib.leaf_len (l : lib.LeafList) : Nat :=
  match l with | lib.LeafList.Nil => 0 | lib.LeafList.Cons _h t => 1 + lib.leaf_len t.deref
termination_by structural l
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
noncomputable def lib.goal_size (g : lib.GoalData) : Nat :=
  match g with | lib.GoalData.Leaf _e => 1 | lib.GoalData.Imp _h b => 1 + lib.goal_size b.deref | lib.GoalData.All _x _t b => 1 + lib.goal_size b.deref | lib.GoalData.Let _x _v b => 1 + lib.goal_size b.deref | lib.GoalData.LeafE _e => 1
termination_by structural g
noncomputable def lib.goal_count (gs : lib.GoalList) : Nat :=
  match gs with | lib.GoalList.Nil => 0 | lib.GoalList.Cons _g t => 1 + lib.goal_count t.deref
termination_by structural gs
noncomputable def lib.fnctx_arity (c : lib.FnCtxData) : Nat :=
  lib.binder_len c.params
mutual
noncomputable def lib.expr_size (e : lib.ExprData) : Nat :=
  match e with | lib.ExprData.Atom _ => 1 | lib.ExprData.Lit _ => 1 | lib.ExprData.LitBool _ => 1 | lib.ExprData.Cast _k t => 1 + lib.expr_size t.deref | lib.ExprData.BinOp _op l r => 1 + lib.expr_size l.deref + lib.expr_size r.deref | lib.ExprData.App _fn a => 1 + lib.expr_size a.deref | lib.ExprData.FieldProj t _f => 1 + lib.expr_size t.deref | lib.ExprData.SpanMark _loc t => 1 + lib.expr_size t.deref | lib.ExprData.Let _n v bd => 1 + lib.expr_size v.deref + lib.expr_size bd.deref | lib.ExprData.Not t => 1 + lib.expr_size t.deref | lib.ExprData.Ite c t e => 1 + lib.expr_size c.deref + lib.expr_size t.deref + lib.expr_size e.deref | lib.ExprData.Match s arms => 1 + lib.expr_size s.deref + lib.arms_size arms.deref | lib.ExprData.AppN _fn args => 1 + lib.exprlist_size args.deref | lib.ExprData.Forall _bid _bty body => 1 + lib.expr_size body.deref | lib.ExprData.Exists _bid _bty body => 1 + lib.expr_size body.deref
termination_by structural e
noncomputable def lib.arms_size (a : lib.ArmList) : Nat :=
  match a with | lib.ArmList.Nil => 0 | lib.ArmList.Cons _c _bs body tl => 1 + lib.expr_size body.deref + lib.arms_size tl.deref
termination_by structural a
noncomputable def lib.exprlist_size (l : lib.ExprList) : Nat :=
  match l with | lib.ExprList.Nil => 0 | lib.ExprList.Cons h t => 1 + lib.expr_size h.deref + lib.exprlist_size t.deref
termination_by structural l
end

noncomputable def lib.typ_size (t : lib.TypData) : Nat :=
  match t with | lib.TypData.TyInt => 1 | lib.TypData.TyNat => 1 | lib.TypData.TyBool => 1 | lib.TypData.TyNamed _ => 1 | lib.TypData.TyRef _ => 1 | lib.TypData.TyBox _ => 1
noncomputable def lib.td_tag (t : lib.TypData) : Nat :=
  match t with | lib.TypData.TyInt => 0 | lib.TypData.TyNat => 1 | lib.TypData.TyBool => 2 | lib.TypData.TyNamed _ => 3 | lib.TypData.TyRef _ => 4 | lib.TypData.TyBox _ => 5
noncomputable def lib.deref_type (t : lib.TypData) : lib.TypData :=
  match t with | lib.TypData.TyRef inner => lib.TypData.TyNamed inner | lib.TypData.TyBox inner => lib.TypData.TyNamed inner | lib.TypData.TyInt => lib.TypData.TyInt | lib.TypData.TyNat => lib.TypData.TyNat | lib.TypData.TyBool => lib.TypData.TyBool | lib.TypData.TyNamed n => lib.TypData.TyNamed n
noncomputable def lib.td_id (t : lib.TypData) : Int :=
  match t with | lib.TypData.TyNamed n => n | lib.TypData.TyRef n => n | lib.TypData.TyBox n => n | _ => 0
noncomputable def lib.typ_eq (a : lib.TypData) (b : lib.TypData) : Nat :=
  if lib.td_tag a = lib.td_tag b then if lib.td_id a = lib.td_id b then 1 else 0 else 0
noncomputable def lib.type_of (re : lib.RawExp) : lib.TypData :=
  match re with | lib.RawExp.Var _id ty => ty | lib.RawExp.Lit _v ty => ty | lib.RawExp.LitBool _b => lib.TypData.TyBool | lib.RawExp.Clip target _e => target | lib.RawExp.BinOp _op ty _l _r => ty | lib.RawExp.Call _fn ret _arg _argty => ret | lib.RawExp.Field _fid fty _base => fty | lib.RawExp.HasType _n _inner => lib.TypData.TyBool | lib.RawExp.Deref e => lib.deref_type (lib.type_of e.deref) | lib.RawExp.Let _name _val body => lib.type_of body.deref | lib.RawExp.Not _e => lib.TypData.TyBool | lib.RawExp.Span _loc e => lib.type_of e.deref | lib.RawExp.Ite ty _c _t _e => ty | lib.RawExp.MatchR _scrut _arms ty => ty | lib.RawExp.CallN _fn ret _args => ret | lib.RawExp.ForallR _bid _bty _body => lib.TypData.TyBool | lib.RawExp.ExistsR _bid _bty _body => lib.TypData.TyBool
termination_by structural re
noncomputable def lib.needs_nat_coercion (operand : lib.TypData) (op_result : lib.TypData) : Nat :=
  if lib.td_tag operand = 0 ∧ lib.td_tag op_result = 1 then 1 else 0
noncomputable def lib.coerce_if (b : Nat) (e : lib.ExprData) : lib.ExprData :=
  if b = 1 then lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk e) else e
noncomputable def lib.deref_field : Int :=
  0
noncomputable def lib.needs_ref_deref (operand : lib.TypData) : Nat :=
  if lib.td_tag operand = 4 then 1 else 0
noncomputable def lib.deref_if (b : Nat) (e : lib.ExprData) : lib.ExprData :=
  if b = 1 then lib.ExprData.FieldProj (Tactus.Box.mk e) lib.deref_field else e
noncomputable def lib.pow2 (n : Nat) : Int :=
  if n = 8 then 256 else if n = 16 then 65536 else if n = 32 then 4294967296 else if n = 64 then 18446744073709551616 else if n = 128 then 18446744073709551616 * 18446744073709551616 else 0
mutual
noncomputable def lib.render_exp (re : lib.RawExp) : lib.ExprData :=
  match re with | lib.RawExp.Var id _ty => lib.ExprData.Atom id | lib.RawExp.Lit v _ty => lib.ExprData.Lit v | lib.RawExp.LitBool b => lib.ExprData.LitBool b | lib.RawExp.Clip target e => lib.coerce_if (lib.needs_nat_coercion (lib.type_of e.deref) target) (lib.render_exp e.deref) | lib.RawExp.BinOp op ty l r => let dl := lib.needs_ref_deref (lib.type_of l.deref);
                                                                                                                                                                                                                                                                                                                         let dr := lib.needs_ref_deref (lib.type_of r.deref);
                                                                                                                                                                                                                                                                                                                         let l1 := lib.deref_if (if dl > dr then 1 else 0) (lib.render_exp l.deref);
                                                                                                                                                                                                                                                                                                                         let r1 := lib.deref_if (if dr > dl then 1 else 0) (lib.render_exp r.deref);
                                                                                                                                                                                                                                                                                                                         let l2 := lib.coerce_if (lib.needs_nat_coercion (lib.type_of l.deref) ty) l1;
                                                                                                                                                                                                                                                                                                                         let r2 := lib.coerce_if (lib.needs_nat_coercion (lib.type_of r.deref) ty) r1;
                                                                                                                                                                                                                                                                                                                         lib.ExprData.BinOp op (Tactus.Box.mk l2) (Tactus.Box.mk r2) | lib.RawExp.Call fnid _ret arg argty => let a1 := lib.render_exp arg.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                              let a2 := lib.coerce_if (lib.needs_nat_coercion (lib.type_of arg.deref) argty) a1;
                                                                                                                                                                                                                                                                                                                                                                                                                              let a3 := lib.deref_if (lib.needs_ref_deref (lib.type_of arg.deref)) a2;
                                                                                                                                                                                                                                                                                                                                                                                                                              lib.ExprData.App fnid (Tactus.Box.mk a3) | lib.RawExp.Field fid _fty base => lib.ExprData.FieldProj (Tactus.Box.mk (lib.render_exp base.deref)) fid | lib.RawExp.HasType n inner => let e2 := lib.render_exp inner.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  lib.ExprData.BinOp 11 (Tactus.Box.mk (lib.ExprData.BinOp 3 (Tactus.Box.mk (lib.ExprData.Lit 0)) (Tactus.Box.mk e2))) (Tactus.Box.mk (lib.ExprData.BinOp 2 (Tactus.Box.mk e2) (Tactus.Box.mk (lib.ExprData.Lit (lib.pow2 (Int.toNat n)))))) | lib.RawExp.Deref e => lib.ExprData.FieldProj (Tactus.Box.mk (lib.render_exp e.deref)) lib.deref_field | lib.RawExp.Let name val body => lib.ExprData.Let name (Tactus.Box.mk (lib.render_exp val.deref)) (Tactus.Box.mk (lib.render_exp body.deref)) | lib.RawExp.Not e => lib.ExprData.Not (Tactus.Box.mk (lib.render_exp e.deref)) | lib.RawExp.Span loc e => lib.ExprData.SpanMark loc (Tactus.Box.mk (lib.render_exp e.deref)) | lib.RawExp.Ite ty c t e => let t2 := lib.coerce_if (lib.needs_nat_coercion (lib.type_of t.deref) ty) (lib.render_exp t.deref);
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               let e2 := lib.coerce_if (lib.needs_nat_coercion (lib.type_of e.deref) ty) (lib.render_exp e.deref);
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               lib.ExprData.Ite (Tactus.Box.mk (lib.render_exp c.deref)) (Tactus.Box.mk t2) (Tactus.Box.mk e2) | lib.RawExp.MatchR scrut arms ty => lib.ExprData.Match (Tactus.Box.mk (lib.render_exp scrut.deref)) (Tactus.Box.mk (lib.render_arms arms.deref ty)) | lib.RawExp.CallN fnid _ret args => lib.ExprData.AppN fnid (Tactus.Box.mk (lib.render_list args.deref)) | lib.RawExp.ForallR bid bty body => lib.ExprData.Forall bid bty (Tactus.Box.mk (lib.render_exp body.deref)) | lib.RawExp.ExistsR bid bty body => lib.ExprData.Exists bid bty (Tactus.Box.mk (lib.render_exp body.deref))
termination_by structural re
noncomputable def lib.render_list (l : lib.RawList) : lib.ExprList :=
  match l with | lib.RawList.Nil => lib.ExprList.Nil | lib.RawList.Cons h t => lib.ExprList.Cons (Tactus.Box.mk (lib.render_exp h.deref)) (Tactus.Box.mk (lib.render_list t.deref))
termination_by structural l
noncomputable def lib.render_arms (a : lib.RawArmList) (ty : lib.TypData) : lib.ArmList :=
  match a with | lib.RawArmList.Nil => lib.ArmList.Nil | lib.RawArmList.Cons c bs body tl => lib.ArmList.Cons c bs (Tactus.Box.mk (lib.coerce_if (lib.needs_nat_coercion (lib.type_of body.deref) ty) (lib.render_exp body.deref))) (Tactus.Box.mk (lib.render_arms tl.deref ty))
termination_by structural a
end

noncomputable def lib.render_def (d : lib.RawDef) : lib.DefData :=
  lib.DefData.mk d.name d.params d.ret (lib.render_exp d.body)
noncomputable def lib.render_dt (d : lib.RawDt) : lib.DtData :=
  lib.DtData.mk d.name d.ctors
noncomputable def lib.ck_tag (k : lib.CastKind) : Nat :=
  match k with | lib.CastKind.IntToNat => 0 | lib.CastKind.NatToInt => 1
noncomputable def lib.castkind_eq (a : lib.CastKind) (b : lib.CastKind) : Nat :=
  if lib.ck_tag a = lib.ck_tag b then 1 else 0
noncomputable def lib.ed_tag (e : lib.ExprData) : Nat :=
  match e with | lib.ExprData.Atom _ => 0 | lib.ExprData.Lit _ => 1 | lib.ExprData.Cast _ _ => 2 | lib.ExprData.BinOp _ _ _ => 3 | lib.ExprData.App _ _ => 4 | lib.ExprData.FieldProj _ _ => 5 | lib.ExprData.SpanMark _ _ => 6 | lib.ExprData.LitBool _ => 7 | lib.ExprData.Let _ _ _ => 8 | lib.ExprData.Not _ => 9 | lib.ExprData.Ite _ _ _ => 10 | lib.ExprData.Match _ _ => 11 | lib.ExprData.AppN _ _ => 12 | lib.ExprData.Forall _ _ _ => 13 | lib.ExprData.Exists _ _ _ => 14
noncomputable def lib.ed_atom_id (e : lib.ExprData) : Int :=
  match e with | lib.ExprData.Atom x => x | _ => 0
noncomputable def lib.ed_lit_val (e : lib.ExprData) : Int :=
  match e with | lib.ExprData.Lit v => v | _ => 0
noncomputable def lib.ed_litbool_val (e : lib.ExprData) : Nat :=
  match e with | lib.ExprData.LitBool x => x | _ => 0
noncomputable def lib.ed_cast_k (e : lib.ExprData) : lib.CastKind :=
  match e with | lib.ExprData.Cast k _ => k | _ => lib.CastKind.IntToNat
noncomputable def lib.ed_cast_e (e : lib.ExprData) : lib.ExprData :=
  match e with | lib.ExprData.Cast _ t => t.deref | _ => lib.ExprData.Atom 0
noncomputable def lib.ed_binop_op (e : lib.ExprData) : Int :=
  match e with | lib.ExprData.BinOp op _ _ => op | _ => 0
noncomputable def lib.ed_binop_l (e : lib.ExprData) : lib.ExprData :=
  match e with | lib.ExprData.BinOp _ l _ => l.deref | _ => lib.ExprData.Atom 0
noncomputable def lib.ed_binop_r (e : lib.ExprData) : lib.ExprData :=
  match e with | lib.ExprData.BinOp _ _ r => r.deref | _ => lib.ExprData.Atom 0
noncomputable def lib.ed_app_fn (e : lib.ExprData) : Int :=
  match e with | lib.ExprData.App f _ => f | _ => 0
noncomputable def lib.ed_app_arg (e : lib.ExprData) : lib.ExprData :=
  match e with | lib.ExprData.App _ a => a.deref | _ => lib.ExprData.Atom 0
noncomputable def lib.ed_fp_e (e : lib.ExprData) : lib.ExprData :=
  match e with | lib.ExprData.FieldProj t _ => t.deref | _ => lib.ExprData.Atom 0
noncomputable def lib.ed_fp_field (e : lib.ExprData) : Int :=
  match e with | lib.ExprData.FieldProj _ f => f | _ => 0
noncomputable def lib.ed_span_loc (e : lib.ExprData) : Int :=
  match e with | lib.ExprData.SpanMark loc _ => loc | _ => 0
noncomputable def lib.ed_span_e (e : lib.ExprData) : lib.ExprData :=
  match e with | lib.ExprData.SpanMark _ t => t.deref | _ => lib.ExprData.Atom 0
noncomputable def lib.ed_let_name (e : lib.ExprData) : Int :=
  match e with | lib.ExprData.Let n _ _ => n | _ => 0
noncomputable def lib.ed_let_val (e : lib.ExprData) : lib.ExprData :=
  match e with | lib.ExprData.Let _ v _ => v.deref | _ => lib.ExprData.Atom 0
noncomputable def lib.ed_let_body (e : lib.ExprData) : lib.ExprData :=
  match e with | lib.ExprData.Let _ _ b => b.deref | _ => lib.ExprData.Atom 0
noncomputable def lib.ed_not_e (e : lib.ExprData) : lib.ExprData :=
  match e with | lib.ExprData.Not t => t.deref | _ => lib.ExprData.Atom 0
noncomputable def lib.ed_ite_c (e : lib.ExprData) : lib.ExprData :=
  match e with | lib.ExprData.Ite c _ _ => c.deref | _ => lib.ExprData.Atom 0
noncomputable def lib.ed_ite_t (e : lib.ExprData) : lib.ExprData :=
  match e with | lib.ExprData.Ite _ t _ => t.deref | _ => lib.ExprData.Atom 0
noncomputable def lib.ed_ite_e (e : lib.ExprData) : lib.ExprData :=
  match e with | lib.ExprData.Ite _ _ el => el.deref | _ => lib.ExprData.Atom 0
noncomputable def lib.ed_match_scrut (e : lib.ExprData) : lib.ExprData :=
  match e with | lib.ExprData.Match s _ => s.deref | _ => lib.ExprData.Atom 0
noncomputable def lib.ed_match_arms (e : lib.ExprData) : lib.ArmList :=
  match e with | lib.ExprData.Match _ a => a.deref | _ => lib.ArmList.Nil
noncomputable def lib.ed_appn_fn (e : lib.ExprData) : Int :=
  match e with | lib.ExprData.AppN f _ => f | _ => 0
noncomputable def lib.ed_appn_args (e : lib.ExprData) : lib.ExprList :=
  match e with | lib.ExprData.AppN _ a => a.deref | _ => lib.ExprList.Nil
noncomputable def lib.ed_forall_bid (e : lib.ExprData) : Int :=
  match e with | lib.ExprData.Forall x _ _ => x | _ => 0
noncomputable def lib.ed_forall_bty (e : lib.ExprData) : lib.TypData :=
  match e with | lib.ExprData.Forall _ t _ => t | _ => lib.TypData.TyInt
noncomputable def lib.ed_forall_body (e : lib.ExprData) : lib.ExprData :=
  match e with | lib.ExprData.Forall _ _ b => b.deref | _ => lib.ExprData.Atom 0
noncomputable def lib.ed_exists_bid (e : lib.ExprData) : Int :=
  match e with | lib.ExprData.Exists x _ _ => x | _ => 0
noncomputable def lib.ed_exists_bty (e : lib.ExprData) : lib.TypData :=
  match e with | lib.ExprData.Exists _ t _ => t | _ => lib.TypData.TyInt
noncomputable def lib.ed_exists_body (e : lib.ExprData) : lib.ExprData :=
  match e with | lib.ExprData.Exists _ _ b => b.deref | _ => lib.ExprData.Atom 0
noncomputable def lib.al_is_nil (a : lib.ArmList) : Nat :=
  match a with | lib.ArmList.Nil => 1 | _ => 0
noncomputable def lib.al_hd_ctor (a : lib.ArmList) : Int :=
  match a with | lib.ArmList.Cons c _ _ _ => c | _ => 0
noncomputable def lib.al_hd_binds (a : lib.ArmList) : lib.BinderIdList :=
  match a with | lib.ArmList.Cons _ bs _ _ => bs | _ => lib.BinderIdList.Nil
noncomputable def lib.al_hd_body (a : lib.ArmList) : lib.ExprData :=
  match a with | lib.ArmList.Cons _ _ b _ => b.deref | _ => lib.ExprData.Atom 0
noncomputable def lib.al_tl (a : lib.ArmList) : lib.ArmList :=
  match a with | lib.ArmList.Cons _ _ _ t => t.deref | _ => lib.ArmList.Nil
noncomputable def lib.el_is_nil (l : lib.ExprList) : Nat :=
  match l with | lib.ExprList.Nil => 1 | _ => 0
noncomputable def lib.el_hd (l : lib.ExprList) : lib.ExprData :=
  match l with | lib.ExprList.Cons h _ => h.deref | _ => lib.ExprData.Atom 0
noncomputable def lib.el_tl (l : lib.ExprList) : lib.ExprList :=
  match l with | lib.ExprList.Cons _ t => t.deref | _ => lib.ExprList.Nil
noncomputable def lib.bil_is_nil (b : lib.BinderIdList) : Nat :=
  match b with | lib.BinderIdList.Nil => 1 | _ => 0
noncomputable def lib.bil_hd (b : lib.BinderIdList) : Int :=
  match b with | lib.BinderIdList.Cons x _ => x | _ => 0
noncomputable def lib.bil_tl (b : lib.BinderIdList) : lib.BinderIdList :=
  match b with | lib.BinderIdList.Cons _ t => t.deref | _ => lib.BinderIdList.Nil
noncomputable def lib.bidl_eq (a : lib.BinderIdList) (b : lib.BinderIdList) : Nat :=
  match a with | lib.BinderIdList.Nil => lib.bil_is_nil b | lib.BinderIdList.Cons x t => if lib.bil_is_nil b = 1 then 0 else if x = lib.bil_hd b then lib.bidl_eq t.deref (lib.bil_tl b) else 0
termination_by structural a
mutual
noncomputable def lib.expr_eq (a : lib.ExprData) (b : lib.ExprData) : Nat :=
  match a with | lib.ExprData.Atom x => if lib.ed_tag b = 0 then if x = lib.ed_atom_id b then 1 else 0 else 0 | lib.ExprData.Lit v => if lib.ed_tag b = 1 then if v = lib.ed_lit_val b then 1 else 0 else 0 | lib.ExprData.LitBool x => if lib.ed_tag b = 7 then if x = lib.ed_litbool_val b then 1 else 0 else 0 | lib.ExprData.Cast k t => if lib.ed_tag b = 2 then if lib.castkind_eq k (lib.ed_cast_k b) = 1 then lib.expr_eq t.deref (lib.ed_cast_e b) else 0 else 0 | lib.ExprData.BinOp op l r => if lib.ed_tag b = 3 then if op = lib.ed_binop_op b then if lib.expr_eq l.deref (lib.ed_binop_l b) = 1 then lib.expr_eq r.deref (lib.ed_binop_r b) else 0 else 0 else 0 | lib.ExprData.App f a2 => if lib.ed_tag b = 4 then if f = lib.ed_app_fn b then lib.expr_eq a2.deref (lib.ed_app_arg b) else 0 else 0 | lib.ExprData.FieldProj t fld => if lib.ed_tag b = 5 then if fld = lib.ed_fp_field b then lib.expr_eq t.deref (lib.ed_fp_e b) else 0 else 0 | lib.ExprData.SpanMark loc t => if lib.ed_tag b = 6 then if loc = lib.ed_span_loc b then lib.expr_eq t.deref (lib.ed_span_e b) else 0 else 0 | lib.ExprData.Let n v bd => if lib.ed_tag b = 8 then if n = lib.ed_let_name b then if lib.expr_eq v.deref (lib.ed_let_val b) = 1 then lib.expr_eq bd.deref (lib.ed_let_body b) else 0 else 0 else 0 | lib.ExprData.Not t => if lib.ed_tag b = 9 then lib.expr_eq t.deref (lib.ed_not_e b) else 0 | lib.ExprData.Ite c t e => if lib.ed_tag b = 10 then if lib.expr_eq c.deref (lib.ed_ite_c b) = 1 then if lib.expr_eq t.deref (lib.ed_ite_t b) = 1 then lib.expr_eq e.deref (lib.ed_ite_e b) else 0 else 0 else 0 | lib.ExprData.Match s arms => if lib.ed_tag b = 11 then if lib.expr_eq s.deref (lib.ed_match_scrut b) = 1 then lib.arms_eq arms.deref (lib.ed_match_arms b) else 0 else 0 | lib.ExprData.AppN f args => if lib.ed_tag b = 12 then if f = lib.ed_appn_fn b then lib.exprlist_eq args.deref (lib.ed_appn_args b) else 0 else 0 | lib.ExprData.Forall bid bty body => if lib.ed_tag b = 13 then if bid = lib.ed_forall_bid b then if lib.typ_eq bty (lib.ed_forall_bty b) = 1 then lib.expr_eq body.deref (lib.ed_forall_body b) else 0 else 0 else 0 | lib.ExprData.Exists bid bty body => if lib.ed_tag b = 14 then if bid = lib.ed_exists_bid b then if lib.typ_eq bty (lib.ed_exists_bty b) = 1 then lib.expr_eq body.deref (lib.ed_exists_body b) else 0 else 0 else 0
termination_by structural a
noncomputable def lib.exprlist_eq (a : lib.ExprList) (b : lib.ExprList) : Nat :=
  match a with | lib.ExprList.Nil => lib.el_is_nil b | lib.ExprList.Cons h t => if lib.el_is_nil b = 1 then 0 else if lib.expr_eq h.deref (lib.el_hd b) = 1 then lib.exprlist_eq t.deref (lib.el_tl b) else 0
termination_by structural a
noncomputable def lib.arms_eq (a : lib.ArmList) (b : lib.ArmList) : Nat :=
  match a with | lib.ArmList.Nil => lib.al_is_nil b | lib.ArmList.Cons c bs body tl => if lib.al_is_nil b = 1 then 0 else if c = lib.al_hd_ctor b then if lib.bidl_eq bs (lib.al_hd_binds b) = 1 then if lib.expr_eq body.deref (lib.al_hd_body b) = 1 then lib.arms_eq tl.deref (lib.al_tl b) else 0 else 0 else 0
termination_by structural a
end

noncomputable def lib.pl_is_nil (p : lib.ParamList) : Nat :=
  match p with | lib.ParamList.Nil => 1 | _ => 0
noncomputable def lib.pl_hd_id (p : lib.ParamList) : Int :=
  match p with | lib.ParamList.Cons id _ _ => id | _ => 0
noncomputable def lib.pl_hd_ty (p : lib.ParamList) : lib.TypData :=
  match p with | lib.ParamList.Cons _ ty _ => ty | _ => lib.TypData.TyInt
noncomputable def lib.pl_tl (p : lib.ParamList) : lib.ParamList :=
  match p with | lib.ParamList.Cons _ _ t => t.deref | _ => lib.ParamList.Nil
noncomputable def lib.param_list_eq (a : lib.ParamList) (b : lib.ParamList) : Nat :=
  match a with | lib.ParamList.Nil => lib.pl_is_nil b | lib.ParamList.Cons id ty t => if lib.pl_is_nil b = 1 then 0 else if id = lib.pl_hd_id b then if lib.typ_eq ty (lib.pl_hd_ty b) = 1 then lib.param_list_eq t.deref (lib.pl_tl b) else 0 else 0
termination_by structural a
noncomputable def lib.tyl_is_nil (l : lib.TypList) : Nat :=
  match l with | lib.TypList.Nil => 1 | _ => 0
noncomputable def lib.tyl_hd (l : lib.TypList) : lib.TypData :=
  match l with | lib.TypList.Cons ty _ => ty | _ => lib.TypData.TyInt
noncomputable def lib.tyl_tl (l : lib.TypList) : lib.TypList :=
  match l with | lib.TypList.Cons _ t => t.deref | _ => lib.TypList.Nil
noncomputable def lib.typ_list_eq (a : lib.TypList) (b : lib.TypList) : Nat :=
  match a with | lib.TypList.Nil => lib.tyl_is_nil b | lib.TypList.Cons ty t => if lib.tyl_is_nil b = 1 then 0 else if lib.typ_eq ty (lib.tyl_hd b) = 1 then lib.typ_list_eq t.deref (lib.tyl_tl b) else 0
termination_by structural a
noncomputable def lib.cl_is_nil (c : lib.CtorList) : Nat :=
  match c with | lib.CtorList.Nil => 1 | _ => 0
noncomputable def lib.cl_hd_name (c : lib.CtorList) : Int :=
  match c with | lib.CtorList.Cons nm _ _ => nm | _ => 0
noncomputable def lib.cl_hd_fields (c : lib.CtorList) : lib.TypList :=
  match c with | lib.CtorList.Cons _ f _ => f | _ => lib.TypList.Nil
noncomputable def lib.cl_tl (c : lib.CtorList) : lib.CtorList :=
  match c with | lib.CtorList.Cons _ _ t => t.deref | _ => lib.CtorList.Nil
noncomputable def lib.ctor_list_eq (a : lib.CtorList) (b : lib.CtorList) : Nat :=
  match a with | lib.CtorList.Nil => lib.cl_is_nil b | lib.CtorList.Cons nm flds t => if lib.cl_is_nil b = 1 then 0 else if nm = lib.cl_hd_name b then if lib.typ_list_eq flds (lib.cl_hd_fields b) = 1 then lib.ctor_list_eq t.deref (lib.cl_tl b) else 0 else 0
termination_by structural a
noncomputable def lib.def_eq (a : lib.DefData) (b : lib.DefData) : Nat :=
  if a.name = b.name then if lib.param_list_eq a.params b.params = 1 then if lib.typ_eq a.ret b.ret = 1 then lib.expr_eq a.body b.body else 0 else 0 else 0
noncomputable def lib.dt_eq (a : lib.DtData) (b : lib.DtData) : Nat :=
  if a.name = b.name then lib.ctor_list_eq a.ctors b.ctors else 0
noncomputable def lib.frame_append (f : lib.FrameList) (g : lib.FrameList) : lib.FrameList :=
  match f with | lib.FrameList.FNil => g | lib.FrameList.FBind id typ t => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.frame_append t.deref g)) | lib.FrameList.FHyp hn h t => lib.FrameList.FHyp hn h (Tactus.Box.mk (lib.frame_append t.deref g)) | lib.FrameList.FLetH x ty v en ep t => lib.FrameList.FLetH x ty v en ep (Tactus.Box.mk (lib.frame_append t.deref g)) | lib.FrameList.FLet id v t => lib.FrameList.FLet id v (Tactus.Box.mk (lib.frame_append t.deref g))
termination_by structural f
noncomputable def lib.binders_to_frame (b : lib.BinderList) : lib.FrameList :=
  match b with | lib.BinderList.Nil => lib.FrameList.FNil | lib.BinderList.Cons id typ t => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.binders_to_frame t.deref))
termination_by structural b
noncomputable def lib.close (f : lib.FrameList) (obligation : Int) : lib.GoalData :=
  match f with | lib.FrameList.FNil => lib.GoalData.Leaf obligation | lib.FrameList.FBind id typ t => lib.GoalData.All id typ (Tactus.Box.mk (lib.close t.deref obligation)) | lib.FrameList.FHyp _hn h t => lib.GoalData.Imp h (Tactus.Box.mk (lib.close t.deref obligation)) | lib.FrameList.FLetH id _ty v _en _ep t => lib.GoalData.Let id v (Tactus.Box.mk (lib.close t.deref obligation)) | lib.FrameList.FLet id v t => lib.GoalData.Let id v (Tactus.Box.mk (lib.close t.deref obligation))
termination_by structural f
noncomputable def lib.has_plain_flet (f : lib.FrameList) : Nat :=
  match f with | lib.FrameList.FNil => 0 | lib.FrameList.FBind _x _ty t => lib.has_plain_flet t.deref | lib.FrameList.FHyp _n _h t => lib.has_plain_flet t.deref | lib.FrameList.FLet _x _v _t => 1 | lib.FrameList.FLetH _x _ty _v _en _ep t => lib.has_plain_flet t.deref
termination_by structural f
noncomputable def lib.close_e_wrap (f : lib.FrameList) (ob : lib.RawExp) : lib.GoalData :=
  match f with | lib.FrameList.FNil => lib.GoalData.LeafE (lib.render_exp ob) | lib.FrameList.FBind id typ t => lib.GoalData.All id typ (Tactus.Box.mk (lib.close_e_wrap t.deref ob)) | lib.FrameList.FHyp _hn h t => lib.GoalData.Imp h (Tactus.Box.mk (lib.close_e_wrap t.deref ob)) | lib.FrameList.FLet id v t => lib.GoalData.Let id v (Tactus.Box.mk (lib.close_e_wrap t.deref ob)) | lib.FrameList.FLetH id _ty v _en _ep t => lib.GoalData.Let id v (Tactus.Box.mk (lib.close_e_wrap t.deref ob))
termination_by structural f
noncomputable def lib.close_e_hoist (f : lib.FrameList) (ob : lib.RawExp) : lib.GoalData :=
  match f with | lib.FrameList.FNil => lib.GoalData.LeafE (lib.render_exp ob) | lib.FrameList.FBind id typ t => lib.GoalData.All id typ (Tactus.Box.mk (lib.close_e_hoist t.deref ob)) | lib.FrameList.FHyp hn h t => lib.GoalData.All hn h (Tactus.Box.mk (lib.close_e_hoist t.deref ob)) | lib.FrameList.FLet id v t => lib.GoalData.Let id v (Tactus.Box.mk (lib.close_e_hoist t.deref ob)) | lib.FrameList.FLetH id ty _v en ep t => lib.GoalData.All id ty (Tactus.Box.mk (lib.GoalData.All en ep (Tactus.Box.mk (lib.close_e_hoist t.deref ob))))
termination_by structural f
noncomputable def lib.close_e (f : lib.FrameList) (ob : lib.RawExp) : lib.GoalData :=
  if lib.has_plain_flet f = 1 then lib.close_e_wrap f ob else lib.close_e_hoist f ob
noncomputable def lib.atom_ob (id : Int) : lib.RawExp :=
  lib.RawExp.Var id lib.TypData.TyBool
noncomputable def lib.close_each_e (f : lib.FrameList) (l : lib.RawExpList) : lib.GoalList :=
  match l with | lib.RawExpList.Nil => lib.GoalList.Nil | lib.RawExpList.Cons h t => lib.GoalList.Cons (Tactus.Box.mk (lib.close_e f h.deref)) (Tactus.Box.mk (lib.close_each_e f t.deref))
termination_by structural l
noncomputable def lib.goals_append (a : lib.GoalList) (b : lib.GoalList) : lib.GoalList :=
  match a with | lib.GoalList.Nil => b | lib.GoalList.Cons h t => lib.GoalList.Cons h (Tactus.Box.mk (lib.goals_append t.deref b))
termination_by structural a
noncomputable def lib.binder_has_id (b : lib.BinderList) (x : Int) : Nat :=
  match b with | lib.BinderList.Nil => 0 | lib.BinderList.Cons id _typ t => if id = x then 1 else lib.binder_has_id t.deref x
termination_by structural b
noncomputable def lib.havoc_lets (f : lib.FrameList) (mods : lib.BinderList) : lib.FrameList :=
  match f with | lib.FrameList.FNil => lib.FrameList.FNil | lib.FrameList.FBind id typ t => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.havoc_lets t.deref mods)) | lib.FrameList.FHyp hn h t => lib.FrameList.FHyp hn h (Tactus.Box.mk (lib.havoc_lets t.deref mods)) | lib.FrameList.FLet id v t => if lib.binder_has_id mods id = 1 then lib.havoc_lets t.deref mods else lib.FrameList.FLet id v (Tactus.Box.mk (lib.havoc_lets t.deref mods)) | lib.FrameList.FLetH id ty v en ep t => if lib.binder_has_id mods id = 1 then lib.havoc_lets t.deref mods else lib.FrameList.FLetH id ty v en ep (Tactus.Box.mk (lib.havoc_lets t.deref mods))
termination_by structural f
noncomputable def lib.seed_params (params : lib.BinderList) (bounds : lib.ParamBoundList) : lib.FrameList :=
  match params with | lib.BinderList.Nil => lib.FrameList.FNil | lib.BinderList.Cons id typ t => match bounds with | lib.ParamBoundList.Bound hname prop bt => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.FrameList.FBind hname prop (Tactus.Box.mk (lib.seed_params t.deref bt.deref)))) | lib.ParamBoundList.NoBound bt => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.seed_params t.deref bt.deref)) | lib.ParamBoundList.Nil => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.seed_params t.deref lib.ParamBoundList.Nil))
termination_by structural params
noncomputable def lib.has_let (f : lib.FrameList) : Nat :=
  match f with | lib.FrameList.FNil => 0 | lib.FrameList.FBind _id _typ t => lib.has_let t.deref | lib.FrameList.FHyp _hn _h t => lib.has_let t.deref | lib.FrameList.FLet _id _v _t => 1 | lib.FrameList.FLetH _id _ty _v _en _ep _t => 1
termination_by structural f
noncomputable def lib.binderprops_to_hyps (b : lib.BinderList) : lib.FrameList :=
  match b with | lib.BinderList.Nil => lib.FrameList.FNil | lib.BinderList.Cons name prop t => lib.FrameList.FHyp name prop (Tactus.Box.mk (lib.binderprops_to_hyps t.deref))
termination_by structural b
noncomputable def lib.seed_binders_hyp_bounds (binders : lib.BinderList) (bounds : lib.ParamBoundList) : lib.FrameList :=
  match binders with | lib.BinderList.Nil => lib.FrameList.FNil | lib.BinderList.Cons id typ t => match bounds with | lib.ParamBoundList.Bound _hname prop bt => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.FrameList.FHyp 0 prop (Tactus.Box.mk (lib.seed_binders_hyp_bounds t.deref bt.deref)))) | lib.ParamBoundList.NoBound bt => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.seed_binders_hyp_bounds t.deref bt.deref)) | lib.ParamBoundList.Nil => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.seed_binders_hyp_bounds t.deref lib.ParamBoundList.Nil))
termination_by structural binders
noncomputable def lib.loop_maintain_frame (f : lib.FrameList) (inv_hyps : lib.BinderList) (binders : lib.BinderList) (binder_bounds : lib.ParamBoundList) (cond_name : Int) (cond_ann : Int) (d_old_name : Int) (d_old_val : Int) : lib.FrameList :=
  let hv := lib.havoc_lets f binders;
  let d_old := lib.FrameList.FLet d_old_name d_old_val (Tactus.Box.mk lib.FrameList.FNil);
  if lib.has_let hv = 0 then lib.frame_append hv (lib.frame_append (lib.seed_params binders binder_bounds) (lib.frame_append (lib.binders_to_frame inv_hyps) (lib.frame_append (lib.FrameList.FBind cond_name cond_ann (Tactus.Box.mk lib.FrameList.FNil)) d_old))) else lib.frame_append hv (lib.frame_append (lib.seed_binders_hyp_bounds binders binder_bounds) (lib.frame_append (lib.binderprops_to_hyps inv_hyps) (lib.frame_append (lib.FrameList.FHyp 0 cond_ann (Tactus.Box.mk lib.FrameList.FNil)) d_old)))
noncomputable def lib.loop_use_frame (f : lib.FrameList) (inv_hyps : lib.BinderList) (binders : lib.BinderList) (binder_bounds : lib.ParamBoundList) (cond_name : Int) (neg_cond_ann : Int) : lib.FrameList :=
  let hv := lib.havoc_lets f binders;
  if lib.has_let hv = 0 then lib.frame_append hv (lib.frame_append (lib.seed_params binders binder_bounds) (lib.frame_append (lib.binders_to_frame inv_hyps) (lib.FrameList.FBind cond_name neg_cond_ann (Tactus.Box.mk lib.FrameList.FNil)))) else lib.frame_append hv (lib.frame_append (lib.seed_binders_hyp_bounds binders binder_bounds) (lib.frame_append (lib.binderprops_to_hyps inv_hyps) (lib.FrameList.FHyp 0 neg_cond_ann (Tactus.Box.mk lib.FrameList.FNil))))
noncomputable def lib.is_skip (s : lib.StmData) : Nat :=
  match s with | lib.StmData.Skip => 1 | _ => 0
noncomputable def lib.diverges (s : lib.StmData) : Nat :=
  match s with | lib.StmData.Ret _es _rb => 1 | lib.StmData.DeadEnd _b => 1 | lib.StmData.Seq a b => if lib.diverges a.deref = 1 ∨ lib.diverges b.deref = 1 then 1 else 0 | lib.StmData.If _c _nc t e => if lib.diverges t.deref = 1 ∧ lib.diverges e.deref = 1 then 1 else 0 | _ => 0
termination_by structural s
noncomputable def lib.strip_hyps (f : lib.FrameList) : lib.FrameList :=
  match f with | lib.FrameList.FNil => lib.FrameList.FNil | lib.FrameList.FBind x ty t => lib.FrameList.FBind x ty (Tactus.Box.mk (lib.strip_hyps t.deref)) | lib.FrameList.FHyp _hn _h t => lib.strip_hyps t.deref | lib.FrameList.FLet x v t => lib.FrameList.FLet x v (Tactus.Box.mk (lib.strip_hyps t.deref)) | lib.FrameList.FLetH x ty v en ep t => lib.FrameList.FLetH x ty v en ep (Tactus.Box.mk (lib.strip_hyps t.deref))
termination_by structural f
noncomputable def lib.frame_after (f : lib.FrameList) (s : lib.StmData) : lib.FrameList :=
  match s with | lib.StmData.Assert _o h => lib.frame_append f (lib.FrameList.FHyp 0 h (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.Assume e => lib.frame_append f (lib.FrameList.FHyp 0 e (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.Assign x rhs => lib.frame_append f (lib.FrameList.FLet x rhs (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.Call _ post => lib.frame_append f post.deref | lib.StmData.DeadEnd _b => f | lib.StmData.AssertQueryNl _b => f | lib.StmData.Ret _es _rb => f | lib.StmData.If _c nc t e => if lib.diverges t.deref = 1 ∧ lib.is_skip e.deref = 1 then lib.frame_append f (lib.FrameList.FHyp 0 nc (Tactus.Box.mk lib.FrameList.FNil)) else f | lib.StmData.Loop inv_hyps _ binders binder_bounds cond_name _ neg_cond_ann _ _ _ _ => lib.loop_use_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name neg_cond_ann | lib.StmData.Skip => f | lib.StmData.Seq a b => lib.frame_after (lib.frame_after f a.deref) b.deref
termination_by structural s
noncomputable def lib.ret_frame (f : lib.FrameList) (rb : lib.RetBind) : lib.FrameList :=
  match rb with | lib.RetBind.RetNone => f | lib.RetBind.RetLet name val => lib.frame_append f (lib.FrameList.FLet name val (Tactus.Box.mk lib.FrameList.FNil))
noncomputable def lib.wp_stm (f : lib.FrameList) (s : lib.StmData) : lib.GoalList :=
  match s with | lib.StmData.Assert o _h => lib.GoalList.Cons (Tactus.Box.mk (lib.close_e f o)) (Tactus.Box.mk lib.GoalList.Nil) | lib.StmData.Assume _e => lib.GoalList.Nil | lib.StmData.Assign _x _rhs => lib.GoalList.Nil | lib.StmData.Call reqs _ => lib.close_each_e f reqs.deref | lib.StmData.DeadEnd b => lib.wp_stm f b.deref | lib.StmData.AssertQueryNl b => lib.wp_stm (lib.strip_hyps f) b.deref | lib.StmData.Ret es rb => lib.close_each_e (lib.ret_frame f rb) es.deref | lib.StmData.If c nc t e => lib.goals_append (lib.wp_stm (lib.frame_append f (lib.FrameList.FHyp 0 c (Tactus.Box.mk lib.FrameList.FNil))) t.deref) (lib.wp_stm (lib.frame_append f (lib.FrameList.FHyp 0 nc (Tactus.Box.mk lib.FrameList.FNil))) e.deref) | lib.StmData.Loop inv_hyps inv_obligs binders binder_bounds cond_name cond_ann _ d_old_name d_old_val decrease_oblig body => let mframe := lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_val;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   let body_goals := lib.wp_stm mframe body.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   let endf := lib.frame_after mframe body.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   let maintain_reclose := lib.close_each_e endf inv_obligs.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   let decrease_goal := lib.GoalList.Cons (Tactus.Box.mk (lib.close_e endf decrease_oblig)) (Tactus.Box.mk lib.GoalList.Nil);
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   let init := lib.close_each_e f inv_obligs.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   lib.goals_append init (lib.goals_append body_goals (lib.goals_append maintain_reclose decrease_goal)) | lib.StmData.Skip => lib.GoalList.Nil | lib.StmData.Seq a b => lib.goals_append (lib.wp_stm f a.deref) (lib.wp_stm (lib.frame_after f a.deref) b.deref)
termination_by structural s
noncomputable def lib.seed_frame (c : lib.FnCtxData) : lib.FrameList :=
  lib.frame_append (lib.binders_to_frame c.typ_params) (lib.frame_append (lib.seed_params c.params c.param_bounds) (lib.binders_to_frame c.reqs))
noncomputable def lib.ref_wp (c : lib.FnCtxData) (s : lib.StmData) : lib.GoalList :=
  lib.wp_stm (lib.seed_frame c) s
noncomputable def lib.gd_tag (g : lib.GoalData) : Nat :=
  match g with | lib.GoalData.Leaf _ => 0 | lib.GoalData.Imp _ _ => 1 | lib.GoalData.All _ _ _ => 2 | lib.GoalData.Let _ _ _ => 3 | lib.GoalData.LeafE _ => 4
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
noncomputable def lib.gd_leafe_expr (g : lib.GoalData) : lib.ExprData :=
  match g with | lib.GoalData.LeafE e => e | _ => lib.ExprData.Atom 0
noncomputable def lib.gd_child (g : lib.GoalData) : lib.GoalData :=
  match g with | lib.GoalData.Imp _ t => t.deref | lib.GoalData.All _ _ t => t.deref | lib.GoalData.Let _ _ t => t.deref | lib.GoalData.Leaf x => lib.GoalData.Leaf x | lib.GoalData.LeafE e => lib.GoalData.LeafE e
noncomputable def lib.goal_eq (a : lib.GoalData) (b : lib.GoalData) : Nat :=
  match a with | lib.GoalData.Leaf x => if lib.gd_tag b = 0 then if x = lib.gd_leaf_id b then 1 else 0 else 0 | lib.GoalData.Imp h1 t1 => if lib.gd_tag b = 1 then if h1 = lib.gd_imp_hyp b then lib.goal_eq t1.deref (lib.gd_child b) else 0 else 0 | lib.GoalData.All x1 ty1 t1 => if lib.gd_tag b = 2 then if x1 = lib.gd_all_name b then if ty1 = lib.gd_all_typ b then lib.goal_eq t1.deref (lib.gd_child b) else 0 else 0 else 0 | lib.GoalData.Let x1 v1 t1 => if lib.gd_tag b = 3 then if x1 = lib.gd_let_name b then if v1 = lib.gd_let_val b then lib.goal_eq t1.deref (lib.gd_child b) else 0 else 0 else 0 | lib.GoalData.LeafE e1 => if lib.gd_tag b = 4 then lib.expr_eq e1 (lib.gd_leafe_expr b) else 0
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
noncomputable def lib.cd19_ctx : lib.FnCtxData :=
  lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.Bound 3 2 (Tactus.Box.mk lib.ParamBoundList.Nil)) lib.BinderList.Nil (lib.LeafList.Cons 4 (Tactus.Box.mk lib.LeafList.Nil))
noncomputable def lib.cd19_sst : lib.StmData :=
  lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 7 0)) (Tactus.Box.mk (lib.StmData.If 8 9 (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 10 11)) (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 5)) (Tactus.Box.mk lib.RawExpList.Nil))) (lib.RetBind.RetLet 6 10))))) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 13) 12)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assume 12)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 14 15)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 17) 16)) (Tactus.Box.mk (lib.StmData.Call (Tactus.Box.mk lib.RawExpList.Nil) (Tactus.Box.mk (lib.FrameList.FHyp 0 20 (Tactus.Box.mk (lib.FrameList.FLet 18 19 (Tactus.Box.mk lib.FrameList.FNil))))))))))))))) (Tactus.Box.mk (lib.StmData.Assign 10 18)))) (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 5)) (Tactus.Box.mk lib.RawExpList.Nil))) (lib.RetBind.RetLet 6 10)))))))
noncomputable def lib.cd19_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.Let 7 0 (Tactus.Box.mk (lib.GoalData.Imp 8 (Tactus.Box.mk (lib.GoalData.Let 10 11 (Tactus.Box.mk (lib.GoalData.Let 6 10 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 5))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.Let 7 0 (Tactus.Box.mk (lib.GoalData.Imp 9 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 13))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.Let 7 0 (Tactus.Box.mk (lib.GoalData.Imp 9 (Tactus.Box.mk (lib.GoalData.Imp 12 (Tactus.Box.mk (lib.GoalData.Imp 12 (Tactus.Box.mk (lib.GoalData.Let 14 15 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 17))))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.Let 7 0 (Tactus.Box.mk (lib.GoalData.Imp 9 (Tactus.Box.mk (lib.GoalData.Imp 12 (Tactus.Box.mk (lib.GoalData.Imp 12 (Tactus.Box.mk (lib.GoalData.Let 14 15 (Tactus.Box.mk (lib.GoalData.Imp 16 (Tactus.Box.mk (lib.GoalData.Imp 20 (Tactus.Box.mk (lib.GoalData.Let 18 19 (Tactus.Box.mk (lib.GoalData.Let 10 18 (Tactus.Box.mk (lib.GoalData.Let 6 10 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 5))))))))))))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)))))))
noncomputable def lib.upd (st : Int → Int) (x : Int) (n : Int) : Int → Int :=
  fun (k : Int) => if k = x then n else (Tactus.Ref.mk st).deref k
noncomputable def lib.close_sem_e_wrap (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (st : Int → Int) (o : lib.RawExp) : Prop :=
  match f with | lib.FrameList.FNil => (Tactus.Ref.mk he).deref (lib.render_exp o) st | lib.FrameList.FBind x _ty t => ∀ (n : Int), lib.close_sem_e_wrap hp he lv t.deref (lib.upd st x n) o | lib.FrameList.FHyp _hn h t => (Tactus.Ref.mk hp).deref h st → lib.close_sem_e_wrap hp he lv t.deref st o | lib.FrameList.FLet x v t => lib.close_sem_e_wrap hp he lv t.deref (lib.upd st x ((Tactus.Ref.mk lv).deref v st)) o | lib.FrameList.FLetH x _ty v _en _ep t => lib.close_sem_e_wrap hp he lv t.deref (lib.upd st x ((Tactus.Ref.mk lv).deref v st)) o
termination_by structural f
noncomputable def lib.close_sem_e_hoist (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (st : Int → Int) (o : lib.RawExp) : Prop :=
  match f with | lib.FrameList.FNil => (Tactus.Ref.mk he).deref (lib.render_exp o) st | lib.FrameList.FBind x _ty t => ∀ (n : Int), lib.close_sem_e_hoist hp he lv t.deref (lib.upd st x n) o | lib.FrameList.FHyp hn _h t => ∀ (n : Int), lib.close_sem_e_hoist hp he lv t.deref (lib.upd st hn n) o | lib.FrameList.FLet x v t => lib.close_sem_e_hoist hp he lv t.deref (lib.upd st x ((Tactus.Ref.mk lv).deref v st)) o | lib.FrameList.FLetH x _ty _v en _ep t => ∀ (a : Int) (b : Int), lib.close_sem_e_hoist hp he lv t.deref (lib.upd (lib.upd st x a) en b) o
termination_by structural f
noncomputable def lib.close_sem_e (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (st : Int → Int) (o : lib.RawExp) : Prop :=
  if lib.has_plain_flet f = 1 then lib.close_sem_e_wrap hp he lv f st o else lib.close_sem_e_hoist hp he lv f st o
theorem lib.expr_mirror_kernel_computes :
    lib.expr_eq (lib.render_exp (lib.RawExp.BinOp 0 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Clip lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyInt)))) (Tactus.Box.mk (lib.RawExp.Call 10 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Clip lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Var 2 lib.TypData.TyInt)))) lib.TypData.TyNat)))) (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 1)))) (Tactus.Box.mk (lib.ExprData.App 10 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 2))))))) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.BinOp 0 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Clip lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyInt)))) (Tactus.Box.mk (lib.RawExp.Call 10 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Clip lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Var 2 lib.TypData.TyInt)))) lib.TypData.TyNat)))) (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ExprData.App 10 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 2))))))) = 0 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.BinOp 1 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Var 3 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 3 lib.TypData.TyInt)))) (lib.ExprData.BinOp 1 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))) (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3))))) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.BinOp 1 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Var 3 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 3 lib.TypData.TyInt)))) (lib.ExprData.BinOp 1 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))) (Tactus.Box.mk (lib.ExprData.Atom 3))) = 0 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.Call 11 (lib.TypData.TyNamed 100) (Tactus.Box.mk (lib.RawExp.Deref (Tactus.Box.mk (lib.RawExp.Var 4 (lib.TypData.TyRef 100))))) (lib.TypData.TyNamed 100))) (lib.ExprData.App 11 (Tactus.Box.mk (lib.ExprData.FieldProj (Tactus.Box.mk (lib.ExprData.Atom 4)) 0))) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.Call 11 (lib.TypData.TyNamed 100) (Tactus.Box.mk (lib.RawExp.Deref (Tactus.Box.mk (lib.RawExp.Var 4 (lib.TypData.TyRef 100))))) (lib.TypData.TyNamed 100))) (lib.ExprData.App 11 (Tactus.Box.mk (lib.ExprData.Atom 4))) = 0 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.BinOp 0 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 3 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Clip lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Var 3 lib.TypData.TyInt)))))) (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.Atom 3)) (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3))))) = 1 ∧ lib.expr_eq (lib.ExprData.Lit 5) (lib.ExprData.Lit 5) = 1 ∧ lib.expr_eq (lib.ExprData.Lit 5) (lib.ExprData.Lit 6) = 0 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.LitBool 1)) (lib.ExprData.LitBool 1) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.LitBool 1)) (lib.ExprData.LitBool 0) = 0 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.HasType 64 (Tactus.Box.mk (lib.RawExp.BinOp 6 lib.TypData.TyInt (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 2 lib.TypData.TyInt)))))) (lib.ExprData.BinOp 11 (Tactus.Box.mk (lib.ExprData.BinOp 3 (Tactus.Box.mk (lib.ExprData.Lit 0)) (Tactus.Box.mk (lib.ExprData.BinOp 6 (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ExprData.Atom 2)))))) (Tactus.Box.mk (lib.ExprData.BinOp 2 (Tactus.Box.mk (lib.ExprData.BinOp 6 (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ExprData.Atom 2)))) (Tactus.Box.mk (lib.ExprData.Lit 18446744073709551616))))) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.HasType 64 (Tactus.Box.mk (lib.RawExp.BinOp 6 lib.TypData.TyInt (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 2 lib.TypData.TyInt)))))) (lib.ExprData.BinOp 11 (Tactus.Box.mk (lib.ExprData.BinOp 3 (Tactus.Box.mk (lib.ExprData.Lit 0)) (Tactus.Box.mk (lib.ExprData.BinOp 6 (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ExprData.Atom 2)))))) (Tactus.Box.mk (lib.ExprData.BinOp 2 (Tactus.Box.mk (lib.ExprData.BinOp 6 (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ExprData.Atom 2)))) (Tactus.Box.mk (lib.ExprData.Lit 4294967296))))) = 0 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.Field 5 lib.TypData.TyInt (Tactus.Box.mk (lib.RawExp.Var 9 (lib.TypData.TyNamed 50))))) (lib.ExprData.FieldProj (Tactus.Box.mk (lib.ExprData.Atom 9)) 5) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.Field 5 lib.TypData.TyInt (Tactus.Box.mk (lib.RawExp.Var 9 (lib.TypData.TyNamed 50))))) (lib.ExprData.Atom 9) = 0 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.Call 11 (lib.TypData.TyNamed 100) (Tactus.Box.mk (lib.RawExp.Var 4 (lib.TypData.TyRef 100))) (lib.TypData.TyNamed 100))) (lib.ExprData.App 11 (Tactus.Box.mk (lib.ExprData.FieldProj (Tactus.Box.mk (lib.ExprData.Atom 4)) 0))) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.Call 11 (lib.TypData.TyNamed 100) (Tactus.Box.mk (lib.RawExp.Var 4 (lib.TypData.TyRef 100))) (lib.TypData.TyNamed 100))) (lib.ExprData.App 11 (Tactus.Box.mk (lib.ExprData.Atom 4))) = 0 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.BinOp 0 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 6 (lib.TypData.TyNamed 5))) (Tactus.Box.mk (lib.RawExp.Var 0 (lib.TypData.TyRef 5))))) (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.Atom 6)) (Tactus.Box.mk (lib.ExprData.FieldProj (Tactus.Box.mk (lib.ExprData.Atom 0)) 0))) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.BinOp 0 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 6 (lib.TypData.TyNamed 5))) (Tactus.Box.mk (lib.RawExp.Var 0 (lib.TypData.TyRef 5))))) (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.Atom 6)) (Tactus.Box.mk (lib.ExprData.Atom 0))) = 0 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.BinOp 0 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 6 (lib.TypData.TyRef 5))) (Tactus.Box.mk (lib.RawExp.Var 0 (lib.TypData.TyRef 5))))) (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.Atom 6)) (Tactus.Box.mk (lib.ExprData.Atom 0))) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.BinOp 0 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 6 (lib.TypData.TyRef 5))) (Tactus.Box.mk (lib.RawExp.Var 0 (lib.TypData.TyRef 5))))) (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.FieldProj (Tactus.Box.mk (lib.ExprData.Atom 6)) 0)) (Tactus.Box.mk (lib.ExprData.Atom 0))) = 0 ∧ lib.expr_size (lib.ExprData.BinOp 1 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))) (Tactus.Box.mk (lib.ExprData.Atom 3))) = 4 ∧ lib.typ_size (lib.TypData.TyRef 7) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.BinOp 13 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.BinOp 2 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 0 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 4 lib.TypData.TyInt)))) (Tactus.Box.mk (lib.RawExp.Let 10 (Tactus.Box.mk (lib.RawExp.Let 14 (Tactus.Box.mk (lib.RawExp.Var 4 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 14 lib.TypData.TyInt)))) (Tactus.Box.mk (lib.RawExp.BinOp 11 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Span 9 (Tactus.Box.mk (lib.RawExp.BinOp 5 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 10 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 0 lib.TypData.TyInt)))))) (Tactus.Box.mk (lib.RawExp.Span 12 (Tactus.Box.mk (lib.RawExp.BinOp 5 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 10 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 4 lib.TypData.TyInt)))))))))))) (lib.ExprData.BinOp 13 (Tactus.Box.mk (lib.ExprData.BinOp 2 (Tactus.Box.mk (lib.ExprData.Atom 0)) (Tactus.Box.mk (lib.ExprData.Atom 4)))) (Tactus.Box.mk (lib.ExprData.Let 10 (Tactus.Box.mk (lib.ExprData.Let 14 (Tactus.Box.mk (lib.ExprData.Atom 4)) (Tactus.Box.mk (lib.ExprData.Atom 14)))) (Tactus.Box.mk (lib.ExprData.BinOp 11 (Tactus.Box.mk (lib.ExprData.SpanMark 9 (Tactus.Box.mk (lib.ExprData.BinOp 5 (Tactus.Box.mk (lib.ExprData.Atom 10)) (Tactus.Box.mk (lib.ExprData.Atom 0)))))) (Tactus.Box.mk (lib.ExprData.SpanMark 12 (Tactus.Box.mk (lib.ExprData.BinOp 5 (Tactus.Box.mk (lib.ExprData.Atom 10)) (Tactus.Box.mk (lib.ExprData.Atom 4))))))))))) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.Let 10 (Tactus.Box.mk (lib.RawExp.Let 14 (Tactus.Box.mk (lib.RawExp.Var 4 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 14 lib.TypData.TyInt)))) (Tactus.Box.mk (lib.RawExp.Var 10 lib.TypData.TyInt)))) (lib.ExprData.Let 10 (Tactus.Box.mk (lib.ExprData.Atom 4)) (Tactus.Box.mk (lib.ExprData.Atom 10))) = 0 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.Not (Tactus.Box.mk (lib.RawExp.BinOp 2 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 0 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 4 lib.TypData.TyInt)))))) (lib.ExprData.Not (Tactus.Box.mk (lib.ExprData.BinOp 2 (Tactus.Box.mk (lib.ExprData.Atom 0)) (Tactus.Box.mk (lib.ExprData.Atom 4))))) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.Not (Tactus.Box.mk (lib.RawExp.BinOp 2 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 0 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 4 lib.TypData.TyInt)))))) (lib.ExprData.BinOp 2 (Tactus.Box.mk (lib.ExprData.Atom 0)) (Tactus.Box.mk (lib.ExprData.Atom 4))) = 0 ∧ lib.expr_size (lib.ExprData.Let 10 (Tactus.Box.mk (lib.ExprData.Atom 4)) (Tactus.Box.mk (lib.ExprData.Not (Tactus.Box.mk (lib.ExprData.Atom 0))))) = 4 := by
  decide 
theorem lib.defs_expr_vocab_kernel_computes :
    lib.expr_eq (lib.render_exp (lib.RawExp.Ite lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.BinOp 0 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawExp.Lit 0 lib.TypData.TyNat)))) (Tactus.Box.mk (lib.RawExp.Lit 0 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawExp.BinOp 6 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawExp.Call 20 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Clip lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.BinOp 7 lib.TypData.TyInt (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Lit 1 lib.TypData.TyInt)))))) lib.TypData.TyNat)))))) (lib.ExprData.Ite (Tactus.Box.mk (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ExprData.Lit 0)))) (Tactus.Box.mk (lib.ExprData.Lit 0)) (Tactus.Box.mk (lib.ExprData.BinOp 6 (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ExprData.App 20 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.BinOp 7 (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ExprData.Lit 1))))))))))) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.Ite lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.BinOp 0 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawExp.Lit 0 lib.TypData.TyNat)))) (Tactus.Box.mk (lib.RawExp.Lit 0 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyNat)))) (lib.ExprData.Ite (Tactus.Box.mk (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ExprData.Lit 0)))) (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ExprData.Lit 0))) = 0 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.MatchR (Tactus.Box.mk (lib.RawExp.Var 3 (lib.TypData.TyNamed 100))) (Tactus.Box.mk (lib.RawArmList.Cons 30 (lib.BinderIdList.Cons 2 (Tactus.Box.mk lib.BinderIdList.Nil)) (Tactus.Box.mk (lib.RawExp.Var 2 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawArmList.Cons 31 (lib.BinderIdList.Cons 5 (Tactus.Box.mk (lib.BinderIdList.Cons 6 (Tactus.Box.mk lib.BinderIdList.Nil)))) (Tactus.Box.mk (lib.RawExp.Lit 0 lib.TypData.TyInt)) (Tactus.Box.mk lib.RawArmList.Nil))))) lib.TypData.TyInt)) (lib.ExprData.Match (Tactus.Box.mk (lib.ExprData.Atom 3)) (Tactus.Box.mk (lib.ArmList.Cons 30 (lib.BinderIdList.Cons 2 (Tactus.Box.mk lib.BinderIdList.Nil)) (Tactus.Box.mk (lib.ExprData.Atom 2)) (Tactus.Box.mk (lib.ArmList.Cons 31 (lib.BinderIdList.Cons 5 (Tactus.Box.mk (lib.BinderIdList.Cons 6 (Tactus.Box.mk lib.BinderIdList.Nil)))) (Tactus.Box.mk (lib.ExprData.Lit 0)) (Tactus.Box.mk lib.ArmList.Nil)))))) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.MatchR (Tactus.Box.mk (lib.RawExp.Var 3 (lib.TypData.TyNamed 100))) (Tactus.Box.mk (lib.RawArmList.Cons 30 (lib.BinderIdList.Cons 2 (Tactus.Box.mk lib.BinderIdList.Nil)) (Tactus.Box.mk (lib.RawExp.Var 2 lib.TypData.TyInt)) (Tactus.Box.mk lib.RawArmList.Nil))) lib.TypData.TyInt)) (lib.ExprData.Match (Tactus.Box.mk (lib.ExprData.Atom 3)) (Tactus.Box.mk (lib.ArmList.Cons 30 (lib.BinderIdList.Cons 99 (Tactus.Box.mk lib.BinderIdList.Nil)) (Tactus.Box.mk (lib.ExprData.Atom 2)) (Tactus.Box.mk lib.ArmList.Nil)))) = 0 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.MatchR (Tactus.Box.mk (lib.RawExp.Var 4 (lib.TypData.TyNamed 100))) (Tactus.Box.mk (lib.RawArmList.Cons 30 (lib.BinderIdList.Cons 99 (Tactus.Box.mk lib.BinderIdList.Nil)) (Tactus.Box.mk (lib.RawExp.Lit 1 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawArmList.Cons 31 (lib.BinderIdList.Cons 7 (Tactus.Box.mk (lib.BinderIdList.Cons 8 (Tactus.Box.mk lib.BinderIdList.Nil)))) (Tactus.Box.mk (lib.RawExp.BinOp 6 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.BinOp 6 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Lit 1 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawExp.Call 23 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Deref (Tactus.Box.mk (lib.RawExp.Var 7 (lib.TypData.TyBox 100))))) (lib.TypData.TyNamed 100))))) (Tactus.Box.mk (lib.RawExp.Call 23 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Deref (Tactus.Box.mk (lib.RawExp.Var 8 (lib.TypData.TyBox 100))))) (lib.TypData.TyNamed 100))))) (Tactus.Box.mk lib.RawArmList.Nil))))) lib.TypData.TyNat)) (lib.ExprData.Match (Tactus.Box.mk (lib.ExprData.Atom 4)) (Tactus.Box.mk (lib.ArmList.Cons 30 (lib.BinderIdList.Cons 99 (Tactus.Box.mk lib.BinderIdList.Nil)) (Tactus.Box.mk (lib.ExprData.Lit 1)) (Tactus.Box.mk (lib.ArmList.Cons 31 (lib.BinderIdList.Cons 7 (Tactus.Box.mk (lib.BinderIdList.Cons 8 (Tactus.Box.mk lib.BinderIdList.Nil)))) (Tactus.Box.mk (lib.ExprData.BinOp 6 (Tactus.Box.mk (lib.ExprData.BinOp 6 (Tactus.Box.mk (lib.ExprData.Lit 1)) (Tactus.Box.mk (lib.ExprData.App 23 (Tactus.Box.mk (lib.ExprData.FieldProj (Tactus.Box.mk (lib.ExprData.Atom 7)) 0)))))) (Tactus.Box.mk (lib.ExprData.App 23 (Tactus.Box.mk (lib.ExprData.FieldProj (Tactus.Box.mk (lib.ExprData.Atom 8)) 0)))))) (Tactus.Box.mk lib.ArmList.Nil)))))) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.MatchR (Tactus.Box.mk (lib.RawExp.Var 4 (lib.TypData.TyNamed 100))) (Tactus.Box.mk (lib.RawArmList.Cons 30 (lib.BinderIdList.Cons 99 (Tactus.Box.mk lib.BinderIdList.Nil)) (Tactus.Box.mk (lib.RawExp.Lit 1 lib.TypData.TyNat)) (Tactus.Box.mk lib.RawArmList.Nil))) lib.TypData.TyNat)) (lib.ExprData.Match (Tactus.Box.mk (lib.ExprData.Atom 4)) (Tactus.Box.mk (lib.ArmList.Cons 30 (lib.BinderIdList.Cons 99 (Tactus.Box.mk lib.BinderIdList.Nil)) (Tactus.Box.mk (lib.ExprData.Lit 0)) (Tactus.Box.mk lib.ArmList.Nil)))) = 0 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.CallN 24 lib.TypData.TyNat (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 9 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 10 lib.TypData.TyNat)) (Tactus.Box.mk lib.RawList.Nil))))))) (lib.ExprData.AppN 24 (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom 9)) (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom 10)) (Tactus.Box.mk lib.ExprList.Nil)))))) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.CallN 24 lib.TypData.TyNat (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 9 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 10 lib.TypData.TyNat)) (Tactus.Box.mk lib.RawList.Nil))))))) (lib.ExprData.AppN 24 (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom 10)) (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom 9)) (Tactus.Box.mk lib.ExprList.Nil)))))) = 0 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.ForallR 15 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.BinOp 0 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 15 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawExp.Var 15 lib.TypData.TyNat)))))) (lib.ExprData.Forall 15 lib.TypData.TyNat (Tactus.Box.mk (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.Atom 15)) (Tactus.Box.mk (lib.ExprData.Atom 15))))) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.ForallR 15 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.BinOp 0 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 15 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawExp.Var 15 lib.TypData.TyNat)))))) (lib.ExprData.Forall 15 lib.TypData.TyInt (Tactus.Box.mk (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.Atom 15)) (Tactus.Box.mk (lib.ExprData.Atom 15))))) = 0 := by
  decide 
theorem lib.defs_mirror_kernel_computes :
    lib.def_eq (lib.render_def (lib.RawDef.mk 20 (lib.ParamList.Cons 1 lib.TypData.TyNat (Tactus.Box.mk lib.ParamList.Nil)) lib.TypData.TyNat (lib.RawExp.BinOp 6 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawExp.Call 20 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyNat)) lib.TypData.TyNat))))) (lib.DefData.mk 20 (lib.ParamList.Cons 1 lib.TypData.TyNat (Tactus.Box.mk lib.ParamList.Nil)) lib.TypData.TyNat (lib.ExprData.BinOp 6 (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ExprData.App 20 (Tactus.Box.mk (lib.ExprData.Atom 1)))))) = 1 ∧ lib.def_eq (lib.render_def (lib.RawDef.mk 20 (lib.ParamList.Cons 1 lib.TypData.TyNat (Tactus.Box.mk lib.ParamList.Nil)) lib.TypData.TyNat (lib.RawExp.Var 1 lib.TypData.TyNat))) (lib.DefData.mk 20 (lib.ParamList.Cons 1 lib.TypData.TyInt (Tactus.Box.mk lib.ParamList.Nil)) lib.TypData.TyNat (lib.ExprData.Atom 1)) = 0 ∧ lib.def_eq (lib.render_def (lib.RawDef.mk 20 (lib.ParamList.Cons 1 lib.TypData.TyNat (Tactus.Box.mk lib.ParamList.Nil)) lib.TypData.TyNat (lib.RawExp.BinOp 6 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawExp.Call 20 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyNat)) lib.TypData.TyNat))))) (lib.DefData.mk 20 (lib.ParamList.Cons 1 lib.TypData.TyNat (Tactus.Box.mk lib.ParamList.Nil)) lib.TypData.TyNat (lib.ExprData.BinOp 6 (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ExprData.Atom 1)))) = 0 ∧ lib.dt_eq (lib.render_dt (lib.RawDt.mk 100 (lib.CtorList.Cons 30 (lib.TypList.Cons lib.TypData.TyInt (Tactus.Box.mk lib.TypList.Nil)) (Tactus.Box.mk (lib.CtorList.Cons 31 (lib.TypList.Cons (lib.TypData.TyBox 100) (Tactus.Box.mk (lib.TypList.Cons (lib.TypData.TyBox 100) (Tactus.Box.mk lib.TypList.Nil)))) (Tactus.Box.mk lib.CtorList.Nil)))))) (lib.DtData.mk 100 (lib.CtorList.Cons 30 (lib.TypList.Cons lib.TypData.TyInt (Tactus.Box.mk lib.TypList.Nil)) (Tactus.Box.mk (lib.CtorList.Cons 31 (lib.TypList.Cons (lib.TypData.TyBox 100) (Tactus.Box.mk (lib.TypList.Cons (lib.TypData.TyBox 100) (Tactus.Box.mk lib.TypList.Nil)))) (Tactus.Box.mk lib.CtorList.Nil))))) = 1 ∧ lib.dt_eq (lib.render_dt (lib.RawDt.mk 100 (lib.CtorList.Cons 30 (lib.TypList.Cons lib.TypData.TyInt (Tactus.Box.mk lib.TypList.Nil)) (Tactus.Box.mk lib.CtorList.Nil)))) (lib.DtData.mk 100 (lib.CtorList.Cons 30 (lib.TypList.Cons (lib.TypData.TyBox 100) (Tactus.Box.mk lib.TypList.Nil)) (Tactus.Box.mk lib.CtorList.Nil))) = 0 := by
  decide 
theorem lib.skeleton_kernel_computes :
    lib.stm_size (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 0) 0)) (Tactus.Box.mk (lib.StmData.If 1 2 (Tactus.Box.mk lib.StmData.Skip) (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk lib.RawExpList.Nil) lib.RetBind.RetNone))))) = 5 ∧ lib.goal_size (lib.GoalData.Imp 7 (Tactus.Box.mk (lib.GoalData.All 8 9 (Tactus.Box.mk (lib.GoalData.Leaf 10))))) = 3 ∧ lib.leaf_len (lib.LeafList.Cons 1 (Tactus.Box.mk (lib.LeafList.Cons 2 (Tactus.Box.mk lib.LeafList.Nil)))) = 2 := by

  decide
theorem lib.seq_size_unfolds :
    lib.stm_size (lib.StmData.Seq (Tactus.Box.mk lib.StmData.Skip) (Tactus.Box.mk lib.StmData.Skip)) = 1 + lib.stm_size lib.StmData.Skip + lib.stm_size lib.StmData.Skip ∧ lib.goal_count (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Leaf 0)) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Leaf 1)) (Tactus.Box.mk lib.GoalList.Nil)))) = 2 := by

  decide
theorem lib.probe_goal_eq_leaf :
    lib.goal_eq (lib.GoalData.Leaf 5) (lib.GoalData.Leaf 5) = 1 ∧ lib.goal_eq (lib.GoalData.Leaf 5) (lib.GoalData.Leaf 6) = 0 := by
  decide 
theorem lib.probe_goal_eq_nested :
    lib.goal_eq (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.Leaf 9))) (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.Leaf 9))) = 1 ∧ lib.goal_eq (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.Leaf 9))) (lib.GoalData.All 7 1 (Tactus.Box.mk (lib.GoalData.Leaf 9))) = 0 := by
  decide 
theorem lib.probe_goals_eq_lit :
    lib.goals_eq lib.GoalList.Nil lib.GoalList.Nil = 1 ∧ lib.goals_eq (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Leaf 9)) (Tactus.Box.mk lib.GoalList.Nil)) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Leaf 9)) (Tactus.Box.mk lib.GoalList.Nil)) = 1 := by
  decide 
theorem lib.probe_close :
    lib.goal_size (lib.close lib.FrameList.FNil 9) = 1 ∧ lib.goal_size (lib.close (lib.FrameList.FBind 0 1 (Tactus.Box.mk lib.FrameList.FNil)) 9) = 2 := by
  decide 
theorem lib.probe_close_e :
    lib.goal_size (lib.close_e lib.FrameList.FNil (lib.atom_ob 9)) = 1 ∧ lib.goal_size (lib.close_e (lib.FrameList.FBind 0 1 (Tactus.Box.mk lib.FrameList.FNil)) (lib.atom_ob 9)) = 2 ∧ lib.goal_eq (lib.close_e lib.FrameList.FNil (lib.atom_ob 9)) (lib.GoalData.LeafE (lib.ExprData.Atom 9)) = 1 ∧ lib.goal_eq (lib.close_e lib.FrameList.FNil (lib.atom_ob 9)) (lib.GoalData.Leaf 9) = 0 := by
  decide 
theorem lib.probe_wp_stm :
    lib.goal_count (lib.wp_stm lib.FrameList.FNil (lib.StmData.Assert (lib.atom_ob 9) 9)) = 1 ∧ lib.goal_count (lib.wp_stm lib.FrameList.FNil lib.StmData.Skip) = 0 := by
  decide 
theorem lib.probe_ref_wp :
    lib.goal_count (lib.ref_wp (lib.FnCtxData.mk lib.BinderList.Nil lib.BinderList.Nil lib.ParamBoundList.Nil lib.BinderList.Nil lib.LeafList.Nil) (lib.StmData.Assert (lib.atom_ob 9) 9)) = 1 := by
  decide 
theorem lib.ref_wp_seed_and_assert :
    lib.goals_eq (lib.ref_wp (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.Bound 19 2 (Tactus.Box.mk lib.ParamBoundList.Nil)) lib.BinderList.Nil lib.LeafList.Nil) (lib.StmData.Assert (lib.atom_ob 9) 9)) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 19 2 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 9))))))) (Tactus.Box.mk lib.GoalList.Nil)) = 1 ∧ lib.goal_count (lib.ref_wp (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.Bound 19 2 (Tactus.Box.mk lib.ParamBoundList.Nil)) lib.BinderList.Nil (lib.LeafList.Cons 5 (Tactus.Box.mk (lib.LeafList.Cons 6 (Tactus.Box.mk lib.LeafList.Nil))))) (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 5)) (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 6)) (Tactus.Box.mk lib.RawExpList.Nil))))) lib.RetBind.RetNone)) = 2 := by
  decide 
theorem lib.ref_wp_seq_threads_frame :
    lib.goals_eq (lib.ref_wp (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.Bound 19 2 (Tactus.Box.mk lib.ParamBoundList.Nil)) lib.BinderList.Nil lib.LeafList.Nil) (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 9) 9)) (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 10) 10)))) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 19 2 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 9))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 19 2 (Tactus.Box.mk (lib.GoalData.All 0 9 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 10))))))))) (Tactus.Box.mk lib.GoalList.Nil)))) = 1 := by
  decide 
theorem lib.ref_wp_add_capped_seed_spine :
    lib.goals_eq (lib.ref_wp (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 4 1 (Tactus.Box.mk lib.BinderList.Nil)))) (lib.ParamBoundList.Bound 3 2 (Tactus.Box.mk (lib.ParamBoundList.Bound 6 5 (Tactus.Box.mk lib.ParamBoundList.Nil)))) (lib.BinderList.Cons 8 7 (Tactus.Box.mk (lib.BinderList.Cons 10 9 (Tactus.Box.mk lib.BinderList.Nil)))) (lib.LeafList.Cons 11 (Tactus.Box.mk lib.LeafList.Nil))) (lib.StmData.Assert (lib.atom_ob 15) 14)) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 4 1 (Tactus.Box.mk (lib.GoalData.All 6 5 (Tactus.Box.mk (lib.GoalData.All 8 7 (Tactus.Box.mk (lib.GoalData.All 10 9 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 15))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)) = 1 := by
  decide 
theorem lib.ref_wp_ret_return_binding :
    lib.goals_eq (lib.wp_stm (lib.FrameList.FLet 16 23 (Tactus.Box.mk lib.FrameList.FNil)) (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 12)) (Tactus.Box.mk lib.RawExpList.Nil))) (lib.RetBind.RetLet 13 16))) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Let 16 23 (Tactus.Box.mk (lib.GoalData.Let 13 16 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 12))))))) (Tactus.Box.mk lib.GoalList.Nil)) = 1 ∧ lib.goals_eq (lib.wp_stm (lib.FrameList.FLet 16 23 (Tactus.Box.mk lib.FrameList.FNil)) (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 12)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Let 16 23 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 12))))) (Tactus.Box.mk lib.GoalList.Nil)) = 1 := by
  decide 
theorem lib.ref_wp_sum_to_loop :
    lib.goals_eq (lib.ref_wp (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.Bound 3 2 (Tactus.Box.mk lib.ParamBoundList.Nil)) (lib.BinderList.Cons 5 4 (Tactus.Box.mk lib.BinderList.Nil)) (lib.LeafList.Cons 6 (Tactus.Box.mk lib.LeafList.Nil))) (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 9 10)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 11 10)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Loop (Tactus.Box.mk (lib.BinderList.Cons 34 23 (Tactus.Box.mk (lib.BinderList.Cons 33 24 (Tactus.Box.mk (lib.BinderList.Cons 32 25 (Tactus.Box.mk (lib.BinderList.Cons 31 26 (Tactus.Box.mk lib.BinderList.Nil))))))))) (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 23)) (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 24)) (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 25)) (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 26)) (Tactus.Box.mk lib.RawExpList.Nil))))))))) (Tactus.Box.mk (lib.BinderList.Cons 9 1 (Tactus.Box.mk (lib.BinderList.Cons 11 1 (Tactus.Box.mk lib.BinderList.Nil))))) (Tactus.Box.mk (lib.ParamBoundList.Bound 37 38 (Tactus.Box.mk (lib.ParamBoundList.Bound 35 36 (Tactus.Box.mk lib.ParamBoundList.Nil))))) 29 30 40 27 28 (lib.atom_ob 39) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 18) 17)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assume 17)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 9 19)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 21) 20)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assume 20)) (Tactus.Box.mk (lib.StmData.Assign 11 22)))))))))))))) (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 7)) (Tactus.Box.mk lib.RawExpList.Nil))) (lib.RetBind.RetLet 8 11))))))))) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 5 4 (Tactus.Box.mk (lib.GoalData.Let 9 10 (Tactus.Box.mk (lib.GoalData.Let 11 10 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 23))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 5 4 (Tactus.Box.mk (lib.GoalData.Let 9 10 (Tactus.Box.mk (lib.GoalData.Let 11 10 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 24))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 5 4 (Tactus.Box.mk (lib.GoalData.Let 9 10 (Tactus.Box.mk (lib.GoalData.Let 11 10 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 25))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 5 4 (Tactus.Box.mk (lib.GoalData.Let 9 10 (Tactus.Box.mk (lib.GoalData.Let 11 10 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 26))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 5 4 (Tactus.Box.mk (lib.GoalData.All 9 1 (Tactus.Box.mk (lib.GoalData.All 37 38 (Tactus.Box.mk (lib.GoalData.All 11 1 (Tactus.Box.mk (lib.GoalData.All 35 36 (Tactus.Box.mk (lib.GoalData.All 34 23 (Tactus.Box.mk (lib.GoalData.All 33 24 (Tactus.Box.mk (lib.GoalData.All 32 25 (Tactus.Box.mk (lib.GoalData.All 31 26 (Tactus.Box.mk (lib.GoalData.All 29 30 (Tactus.Box.mk (lib.GoalData.Let 27 28 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 18))))))))))))))))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 5 4 (Tactus.Box.mk (lib.GoalData.All 9 1 (Tactus.Box.mk (lib.GoalData.All 37 38 (Tactus.Box.mk (lib.GoalData.All 11 1 (Tactus.Box.mk (lib.GoalData.All 35 36 (Tactus.Box.mk (lib.GoalData.All 34 23 (Tactus.Box.mk (lib.GoalData.All 33 24 (Tactus.Box.mk (lib.GoalData.All 32 25 (Tactus.Box.mk (lib.GoalData.All 31 26 (Tactus.Box.mk (lib.GoalData.All 29 30 (Tactus.Box.mk (lib.GoalData.Let 27 28 (Tactus.Box.mk (lib.GoalData.Imp 17 (Tactus.Box.mk (lib.GoalData.Imp 17 (Tactus.Box.mk (lib.GoalData.Let 9 19 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 21))))))))))))))))))))))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 5 4 (Tactus.Box.mk (lib.GoalData.All 9 1 (Tactus.Box.mk (lib.GoalData.All 37 38 (Tactus.Box.mk (lib.GoalData.All 11 1 (Tactus.Box.mk (lib.GoalData.All 35 36 (Tactus.Box.mk (lib.GoalData.All 34 23 (Tactus.Box.mk (lib.GoalData.All 33 24 (Tactus.Box.mk (lib.GoalData.All 32 25 (Tactus.Box.mk (lib.GoalData.All 31 26 (Tactus.Box.mk (lib.GoalData.All 29 30 (Tactus.Box.mk (lib.GoalData.Let 27 28 (Tactus.Box.mk (lib.GoalData.Imp 17 (Tactus.Box.mk (lib.GoalData.Imp 17 (Tactus.Box.mk (lib.GoalData.Let 9 19 (Tactus.Box.mk (lib.GoalData.Imp 20 (Tactus.Box.mk (lib.GoalData.Imp 20 (Tactus.Box.mk (lib.GoalData.Let 11 22 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 23))))))))))))))))))))))))))))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 5 4 (Tactus.Box.mk (lib.GoalData.All 9 1 (Tactus.Box.mk (lib.GoalData.All 37 38 (Tactus.Box.mk (lib.GoalData.All 11 1 (Tactus.Box.mk (lib.GoalData.All 35 36 (Tactus.Box.mk (lib.GoalData.All 34 23 (Tactus.Box.mk (lib.GoalData.All 33 24 (Tactus.Box.mk (lib.GoalData.All 32 25 (Tactus.Box.mk (lib.GoalData.All 31 26 (Tactus.Box.mk (lib.GoalData.All 29 30 (Tactus.Box.mk (lib.GoalData.Let 27 28 (Tactus.Box.mk (lib.GoalData.Imp 17 (Tactus.Box.mk (lib.GoalData.Imp 17 (Tactus.Box.mk (lib.GoalData.Let 9 19 (Tactus.Box.mk (lib.GoalData.Imp 20 (Tactus.Box.mk (lib.GoalData.Imp 20 (Tactus.Box.mk (lib.GoalData.Let 11 22 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 24))))))))))))))))))))))))))))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 5 4 (Tactus.Box.mk (lib.GoalData.All 9 1 (Tactus.Box.mk (lib.GoalData.All 37 38 (Tactus.Box.mk (lib.GoalData.All 11 1 (Tactus.Box.mk (lib.GoalData.All 35 36 (Tactus.Box.mk (lib.GoalData.All 34 23 (Tactus.Box.mk (lib.GoalData.All 33 24 (Tactus.Box.mk (lib.GoalData.All 32 25 (Tactus.Box.mk (lib.GoalData.All 31 26 (Tactus.Box.mk (lib.GoalData.All 29 30 (Tactus.Box.mk (lib.GoalData.Let 27 28 (Tactus.Box.mk (lib.GoalData.Imp 17 (Tactus.Box.mk (lib.GoalData.Imp 17 (Tactus.Box.mk (lib.GoalData.Let 9 19 (Tactus.Box.mk (lib.GoalData.Imp 20 (Tactus.Box.mk (lib.GoalData.Imp 20 (Tactus.Box.mk (lib.GoalData.Let 11 22 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 25))))))))))))))))))))))))))))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 5 4 (Tactus.Box.mk (lib.GoalData.All 9 1 (Tactus.Box.mk (lib.GoalData.All 37 38 (Tactus.Box.mk (lib.GoalData.All 11 1 (Tactus.Box.mk (lib.GoalData.All 35 36 (Tactus.Box.mk (lib.GoalData.All 34 23 (Tactus.Box.mk (lib.GoalData.All 33 24 (Tactus.Box.mk (lib.GoalData.All 32 25 (Tactus.Box.mk (lib.GoalData.All 31 26 (Tactus.Box.mk (lib.GoalData.All 29 30 (Tactus.Box.mk (lib.GoalData.Let 27 28 (Tactus.Box.mk (lib.GoalData.Imp 17 (Tactus.Box.mk (lib.GoalData.Imp 17 (Tactus.Box.mk (lib.GoalData.Let 9 19 (Tactus.Box.mk (lib.GoalData.Imp 20 (Tactus.Box.mk (lib.GoalData.Imp 20 (Tactus.Box.mk (lib.GoalData.Let 11 22 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 26))))))))))))))))))))))))))))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 5 4 (Tactus.Box.mk (lib.GoalData.All 9 1 (Tactus.Box.mk (lib.GoalData.All 37 38 (Tactus.Box.mk (lib.GoalData.All 11 1 (Tactus.Box.mk (lib.GoalData.All 35 36 (Tactus.Box.mk (lib.GoalData.All 34 23 (Tactus.Box.mk (lib.GoalData.All 33 24 (Tactus.Box.mk (lib.GoalData.All 32 25 (Tactus.Box.mk (lib.GoalData.All 31 26 (Tactus.Box.mk (lib.GoalData.All 29 30 (Tactus.Box.mk (lib.GoalData.Let 27 28 (Tactus.Box.mk (lib.GoalData.Imp 17 (Tactus.Box.mk (lib.GoalData.Imp 17 (Tactus.Box.mk (lib.GoalData.Let 9 19 (Tactus.Box.mk (lib.GoalData.Imp 20 (Tactus.Box.mk (lib.GoalData.Imp 20 (Tactus.Box.mk (lib.GoalData.Let 11 22 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 39))))))))))))))))))))))))))))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 5 4 (Tactus.Box.mk (lib.GoalData.All 9 1 (Tactus.Box.mk (lib.GoalData.All 37 38 (Tactus.Box.mk (lib.GoalData.All 11 1 (Tactus.Box.mk (lib.GoalData.All 35 36 (Tactus.Box.mk (lib.GoalData.All 34 23 (Tactus.Box.mk (lib.GoalData.All 33 24 (Tactus.Box.mk (lib.GoalData.All 32 25 (Tactus.Box.mk (lib.GoalData.All 31 26 (Tactus.Box.mk (lib.GoalData.All 29 40 (Tactus.Box.mk (lib.GoalData.Let 8 11 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 7))))))))))))))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)))))))))))))))))))))))) = 1 := by
  decide 
theorem lib.ref_wp_nested_loop_nonleading :
    lib.goal_eq (lib.close_e (lib.loop_maintain_frame (lib.FrameList.FBind 0 1 (Tactus.Box.mk (lib.FrameList.FLet 20 21 (Tactus.Box.mk lib.FrameList.FNil)))) (lib.BinderList.Cons 13 25 (Tactus.Box.mk (lib.BinderList.Cons 15 26 (Tactus.Box.mk (lib.BinderList.Cons 17 27 (Tactus.Box.mk lib.BinderList.Nil)))))) (lib.BinderList.Cons 23 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.Bound 11 24 (Tactus.Box.mk lib.ParamBoundList.Nil)) 28 29 31 32) (lib.atom_ob 35)) (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.Let 20 21 (Tactus.Box.mk (lib.GoalData.All 23 1 (Tactus.Box.mk (lib.GoalData.Imp 24 (Tactus.Box.mk (lib.GoalData.Imp 25 (Tactus.Box.mk (lib.GoalData.Imp 26 (Tactus.Box.mk (lib.GoalData.Imp 27 (Tactus.Box.mk (lib.GoalData.Imp 29 (Tactus.Box.mk (lib.GoalData.Let 31 32 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 35)))))))))))))))))))) = 1 ∧ lib.goal_eq (lib.close_e (lib.loop_maintain_frame (lib.FrameList.FBind 0 1 (Tactus.Box.mk lib.FrameList.FNil)) (lib.BinderList.Cons 13 25 (Tactus.Box.mk (lib.BinderList.Cons 15 26 (Tactus.Box.mk (lib.BinderList.Cons 17 27 (Tactus.Box.mk lib.BinderList.Nil)))))) (lib.BinderList.Cons 23 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.Bound 11 24 (Tactus.Box.mk lib.ParamBoundList.Nil)) 28 29 31 32) (lib.atom_ob 35)) (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 23 1 (Tactus.Box.mk (lib.GoalData.All 11 24 (Tactus.Box.mk (lib.GoalData.All 13 25 (Tactus.Box.mk (lib.GoalData.All 15 26 (Tactus.Box.mk (lib.GoalData.All 17 27 (Tactus.Box.mk (lib.GoalData.All 28 29 (Tactus.Box.mk (lib.GoalData.Let 31 32 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 35)))))))))))))))))) = 1 ∧ lib.goal_eq (lib.close_e (lib.loop_use_frame (lib.FrameList.FBind 0 1 (Tactus.Box.mk (lib.FrameList.FLet 20 21 (Tactus.Box.mk lib.FrameList.FNil)))) (lib.BinderList.Cons 13 25 (Tactus.Box.mk (lib.BinderList.Cons 15 26 (Tactus.Box.mk (lib.BinderList.Cons 17 27 (Tactus.Box.mk lib.BinderList.Nil)))))) (lib.BinderList.Cons 23 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.Bound 11 24 (Tactus.Box.mk lib.ParamBoundList.Nil)) 28 30) (lib.atom_ob 43)) (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.Let 20 21 (Tactus.Box.mk (lib.GoalData.All 23 1 (Tactus.Box.mk (lib.GoalData.Imp 24 (Tactus.Box.mk (lib.GoalData.Imp 25 (Tactus.Box.mk (lib.GoalData.Imp 26 (Tactus.Box.mk (lib.GoalData.Imp 27 (Tactus.Box.mk (lib.GoalData.Imp 30 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 43)))))))))))))))))) = 1 := by
  decide 
theorem lib.ref_wp_if_fallthrough_divergence :
    lib.goals_eq (lib.wp_stm (lib.FrameList.FHyp 0 34 (Tactus.Box.mk lib.FrameList.FNil)) (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.If 36 37 (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 7)) (Tactus.Box.mk lib.RawExpList.Nil))) (lib.RetBind.RetLet 8 9))) (Tactus.Box.mk lib.StmData.Skip))) (Tactus.Box.mk lib.StmData.Skip))) (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 40) 39)))) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Imp 34 (Tactus.Box.mk (lib.GoalData.Imp 36 (Tactus.Box.mk (lib.GoalData.Let 8 9 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 7))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 34 (Tactus.Box.mk (lib.GoalData.All 0 37 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 40))))))) (Tactus.Box.mk lib.GoalList.Nil)))) = 1 ∧ lib.goals_eq (lib.wp_stm (lib.FrameList.FHyp 0 34 (Tactus.Box.mk lib.FrameList.FNil)) (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.If 36 37 (Tactus.Box.mk lib.StmData.Skip) (Tactus.Box.mk lib.StmData.Skip))) (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 40) 39)))) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 34 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 40))))) (Tactus.Box.mk lib.GoalList.Nil)) = 1 := by
  decide 
theorem lib.ref_wp_if_twoway_join :
    lib.goals_eq (lib.ref_wp lib.cd19_ctx lib.cd19_sst) lib.cd19_goals = 1 ∧ lib.goal_count (lib.ref_wp lib.cd19_ctx lib.cd19_sst) = 4 ∧ lib.goal_eq (lib.gl_head (lib.ref_wp lib.cd19_ctx lib.cd19_sst)) (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.Let 7 0 (Tactus.Box.mk (lib.GoalData.Imp 8 (Tactus.Box.mk (lib.GoalData.Let 10 99 (Tactus.Box.mk (lib.GoalData.Let 6 10 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 5)))))))))))))) = 0 := by
  decide 
theorem lib.ref_wp_call_pass_through :
    lib.goals_eq (lib.wp_stm (lib.FrameList.FHyp 0 100 (Tactus.Box.mk lib.FrameList.FNil)) (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Call (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 7)) (Tactus.Box.mk lib.RawExpList.Nil))) (Tactus.Box.mk (lib.FrameList.FHyp 0 9 (Tactus.Box.mk (lib.FrameList.FLet 8 10 (Tactus.Box.mk lib.FrameList.FNil))))))) (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 11) 12)))) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 100 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 7))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Imp 100 (Tactus.Box.mk (lib.GoalData.Imp 9 (Tactus.Box.mk (lib.GoalData.Let 8 10 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 11))))))))) (Tactus.Box.mk lib.GoalList.Nil)))) = 1 ∧ lib.goals_eq (lib.wp_stm (lib.FrameList.FHyp 0 100 (Tactus.Box.mk lib.FrameList.FNil)) (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Call (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 7)) (Tactus.Box.mk lib.RawExpList.Nil))) (Tactus.Box.mk (lib.FrameList.FBind 8 1 (Tactus.Box.mk (lib.FrameList.FHyp 0 9 (Tactus.Box.mk (lib.FrameList.FHyp 0 13 (Tactus.Box.mk lib.FrameList.FNil))))))))) (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 11) 12)))) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 100 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 7))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 100 (Tactus.Box.mk (lib.GoalData.All 8 1 (Tactus.Box.mk (lib.GoalData.All 0 9 (Tactus.Box.mk (lib.GoalData.All 0 13 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 11))))))))))) (Tactus.Box.mk lib.GoalList.Nil)))) = 1 ∧ lib.goals_eq (lib.wp_stm (lib.FrameList.FHyp 0 100 (Tactus.Box.mk lib.FrameList.FNil)) (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Call (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 7)) (Tactus.Box.mk lib.RawExpList.Nil))) (Tactus.Box.mk (lib.FrameList.FHyp 0 9 (Tactus.Box.mk (lib.FrameList.FLet 8 10 (Tactus.Box.mk lib.FrameList.FNil))))))) (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 11) 12)))) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 100 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 7))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Imp 100 (Tactus.Box.mk (lib.GoalData.Imp 9 (Tactus.Box.mk (lib.GoalData.Let 8 99 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 11))))))))) (Tactus.Box.mk lib.GoalList.Nil)))) = 0 := by
  decide 
theorem lib.goal_eq_strictness :
    lib.goal_eq (lib.GoalData.Leaf 5) (lib.GoalData.Leaf 6) = 0 ∧ lib.goal_eq (lib.GoalData.Leaf 5) (lib.GoalData.Leaf 5) = 1 ∧ lib.goal_eq (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.Leaf 9))) (lib.GoalData.All 7 1 (Tactus.Box.mk (lib.GoalData.Leaf 9))) = 0 ∧ lib.goal_eq (lib.GoalData.Imp 2 (Tactus.Box.mk (lib.GoalData.Leaf 9))) (lib.GoalData.Imp 3 (Tactus.Box.mk (lib.GoalData.Leaf 9))) = 0 ∧ lib.goal_eq (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.Leaf 9))) (lib.GoalData.Imp 1 (Tactus.Box.mk (lib.GoalData.Leaf 9))) = 0 ∧ lib.goals_eq (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Leaf 9)) (Tactus.Box.mk lib.GoalList.Nil)) lib.GoalList.Nil = 0 := by
  decide 
theorem lib.leafe_goal_bridge_kernel_computes :
    lib.goal_eq (lib.GoalData.LeafE (lib.ExprData.BinOp 1 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))) (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))))) (lib.GoalData.LeafE (lib.ExprData.BinOp 1 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))) (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))))) = 1 ∧ lib.goal_eq (lib.GoalData.LeafE (lib.ExprData.BinOp 1 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))) (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))))) (lib.GoalData.LeafE (lib.ExprData.BinOp 1 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))) (Tactus.Box.mk (lib.ExprData.Atom 3)))) = 0 ∧ lib.goal_eq (lib.GoalData.LeafE (lib.ExprData.Atom 5)) (lib.GoalData.Leaf 5) = 0 ∧ lib.goal_eq (lib.GoalData.Leaf 5) (lib.GoalData.LeafE (lib.ExprData.Atom 5)) = 0 ∧ lib.goals_eq (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 9))) (Tactus.Box.mk lib.GoalList.Nil)) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 9))) (Tactus.Box.mk lib.GoalList.Nil)) = 1 ∧ lib.goal_size (lib.GoalData.Imp 7 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 9)))) = 2 := by
  decide 
theorem lib.amended_shapes_kernel_compute :
    lib.stm_size (lib.StmData.Loop (Tactus.Box.mk (lib.BinderList.Cons 0 10 (Tactus.Box.mk lib.BinderList.Nil))) (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 10)) (Tactus.Box.mk lib.RawExpList.Nil))) (Tactus.Box.mk (lib.BinderList.Cons 3 4 (Tactus.Box.mk lib.BinderList.Nil))) (Tactus.Box.mk (lib.ParamBoundList.Bound 20 21 (Tactus.Box.mk lib.ParamBoundList.Nil))) 5 1 2 6 7 (lib.atom_ob 8) (Tactus.Box.mk lib.StmData.Skip)) = 5 ∧ lib.stm_size (lib.StmData.Call (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 0)) (Tactus.Box.mk lib.RawExpList.Nil))) (Tactus.Box.mk (lib.FrameList.FBind 5 6 (Tactus.Box.mk lib.FrameList.FNil)))) = 3 ∧ lib.stm_size (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 0)) (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 1)) (Tactus.Box.mk lib.RawExpList.Nil))))) lib.RetBind.RetNone) = 3 ∧ lib.stm_size (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 0)) (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 1)) (Tactus.Box.mk lib.RawExpList.Nil))))) (lib.RetBind.RetLet 23 9)) = 3 ∧ lib.binder_len (lib.BinderList.Cons 1 2 (Tactus.Box.mk lib.BinderList.Nil)) = 1 ∧ lib.param_bound_len (lib.ParamBoundList.Bound 4 5 (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))) = 2 ∧ lib.frame_len (lib.FrameList.FBind 1 2 (Tactus.Box.mk (lib.FrameList.FHyp 0 3 (Tactus.Box.mk (lib.FrameList.FLet 4 5 (Tactus.Box.mk lib.FrameList.FNil)))))) = 3 ∧ lib.fnctx_arity (lib.FnCtxData.mk (lib.BinderList.Cons 0 100 (Tactus.Box.mk lib.BinderList.Nil)) (lib.BinderList.Cons 1 101 (Tactus.Box.mk (lib.BinderList.Cons 2 102 (Tactus.Box.mk lib.BinderList.Nil)))) (lib.ParamBoundList.Bound 199 200 (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))) lib.BinderList.Nil (lib.LeafList.Cons 300 (Tactus.Box.mk lib.LeafList.Nil))) = 2 := by

  decide
theorem _tactus_postcondition_u_cse_wrap_mode_at_lib_3455_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp) (h_req0 : lib.has_plain_flet f = 1) :
    /- @rust:lib.rs:3455:13 -/ ∀ (st : Int → Int), lib.close_sem_e hp he lv f st o = lib.close_sem_e_wrap hp he lv f st o := by
  first | tactus_auto | (intros <;> simp_all [close_sem_e])
