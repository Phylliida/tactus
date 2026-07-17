-- tactus defs part: base (base = machinery + instance closure; one part per source module, SCC-merged; umbrella = interface)
import TactusPrelude
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
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
  | FHyp (val0 : Int) (val1 : Tactus.Box lib.FrameList)
  | FLet (val0 : Int) (val1 : Int) (val2 : Tactus.Box lib.FrameList)
  deriving Inhabited
@[simp] noncomputable def lib.FrameList.isFNil (x : lib.FrameList) : Prop :=
  match x with | lib.FrameList.FNil => True | _ => False
@[simp] noncomputable def lib.FrameList.isFBind (x : lib.FrameList) : Prop :=
  match x with | lib.FrameList.FBind _ _ _ => True | _ => False
@[simp] noncomputable def lib.FrameList.isFHyp (x : lib.FrameList) : Prop :=
  match x with | lib.FrameList.FHyp _ _ => True | _ => False
@[simp] noncomputable def lib.FrameList.isFLet (x : lib.FrameList) : Prop :=
  match x with | lib.FrameList.FLet _ _ _ => True | _ => False
@[simp] noncomputable def lib.FrameList.FBind_val0 (x : lib.FrameList) : Int :=
  match x with | lib.FrameList.FBind val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FBind_val1 (x : lib.FrameList) : Int :=
  match x with | lib.FrameList.FBind _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FBind_val2 (x : lib.FrameList) : Tactus.Box lib.FrameList :=
  match x with | lib.FrameList.FBind _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FHyp_val0 (x : lib.FrameList) : Int :=
  match x with | lib.FrameList.FHyp val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FHyp_val1 (x : lib.FrameList) : Tactus.Box lib.FrameList :=
  match x with | lib.FrameList.FHyp _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FLet_val0 (x : lib.FrameList) : Int :=
  match x with | lib.FrameList.FLet val0 _ _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FLet_val1 (x : lib.FrameList) : Int :=
  match x with | lib.FrameList.FLet _ val1 _ => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.FLet_val2 (x : lib.FrameList) : Tactus.Box lib.FrameList :=
  match x with | lib.FrameList.FLet _ _ val2 => val2 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.FrameList.height (s : lib.FrameList) : Nat :=
  match s with | lib.FrameList.FNil => 1 | lib.FrameList.FBind _ _ val2 => 1 + lib.FrameList.height val2.deref | lib.FrameList.FHyp _ val1 => 1 + lib.FrameList.height val1.deref | lib.FrameList.FLet _ _ val2 => 1 + lib.FrameList.height val2.deref
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
@[simp] noncomputable def lib.StmData.Seq_val0 (x : lib.StmData) : Tactus.Box lib.StmData :=
  match x with | lib.StmData.Seq val0 _ => val0 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.Seq_val1 (x : lib.StmData) : Tactus.Box lib.StmData :=
  match x with | lib.StmData.Seq _ val1 => val1 | _ => Classical.ofNonempty
@[simp] noncomputable def lib.StmData.height (s : lib.StmData) : Nat :=
  match s with | lib.StmData.Assert _ _ => 1 | lib.StmData.Assume _ => 1 | lib.StmData.Assign _ _ => 1 | lib.StmData.Call _ _ => 1 | lib.StmData.DeadEnd val0 => 1 + lib.StmData.height val0.deref | lib.StmData.Ret _ _ => 1 | lib.StmData.If _ _ val2 val3 => 1 + lib.StmData.height val2.deref + lib.StmData.height val3.deref | lib.StmData.Loop _ _ _ _ _ _ _ _ _ _ body => 1 + lib.StmData.height body.deref | lib.StmData.Skip => 1 | lib.StmData.Seq val0 val1 => 1 + lib.StmData.height val0.deref + lib.StmData.height val1.deref
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
