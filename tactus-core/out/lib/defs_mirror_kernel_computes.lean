import TactusDefs
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
inductive lib.BinderIdList where
  | Nil
  | Cons (val0 : Int) (val1 : Tactus.Box lib.BinderIdList)
  deriving Inhabited
@[simp] noncomputable def lib.BinderIdList.height (s : lib.BinderIdList) : Nat :=
  match s with | lib.BinderIdList.Nil => 1 | lib.BinderIdList.Cons _ val1 => 1 + lib.BinderIdList.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
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
inductive lib.CastKind where
  | IntToNat
  | NatToInt
  deriving Inhabited
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

inductive lib.ParamList where
  | Nil
  | Cons (val0 : Int) (val1 : lib.TypData) (val2 : Tactus.Box lib.ParamList)
  deriving Inhabited
@[simp] noncomputable def lib.ParamList.height (s : lib.ParamList) : Nat :=
  match s with | lib.ParamList.Nil => 1 | lib.ParamList.Cons _ _ val2 => 1 + lib.ParamList.height val2.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
inductive lib.TypList where
  | Nil
  | Cons (val0 : lib.TypData) (val1 : Tactus.Box lib.TypList)
  deriving Inhabited
@[simp] noncomputable def lib.TypList.height (s : lib.TypList) : Nat :=
  match s with | lib.TypList.Nil => 1 | lib.TypList.Cons _ val1 => 1 + lib.TypList.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
inductive lib.CtorList where
  | Nil
  | Cons (val0 : Int) (val1 : lib.TypList) (val2 : Tactus.Box lib.CtorList)
  deriving Inhabited
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
noncomputable def lib.render_arms (a : lib.RawArmList) (ty : lib.TypData) : lib.ArmList :=
  match a with | lib.RawArmList.Nil => lib.ArmList.Nil | lib.RawArmList.Cons c bs body tl => lib.ArmList.Cons c bs (Tactus.Box.mk (lib.coerce_if (lib.needs_nat_coercion (lib.type_of body.deref) ty) (lib.render_exp body.deref))) (Tactus.Box.mk (lib.render_arms tl.deref ty))
termination_by structural a
noncomputable def lib.render_list (l : lib.RawList) : lib.ExprList :=
  match l with | lib.RawList.Nil => lib.ExprList.Nil | lib.RawList.Cons h t => lib.ExprList.Cons (Tactus.Box.mk (lib.render_exp h.deref)) (Tactus.Box.mk (lib.render_list t.deref))
termination_by structural l
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
noncomputable def lib.arms_eq (a : lib.ArmList) (b : lib.ArmList) : Nat :=
  match a with | lib.ArmList.Nil => lib.al_is_nil b | lib.ArmList.Cons c bs body tl => if lib.al_is_nil b = 1 then 0 else if c = lib.al_hd_ctor b then if lib.bidl_eq bs (lib.al_hd_binds b) = 1 then if lib.expr_eq body.deref (lib.al_hd_body b) = 1 then lib.arms_eq tl.deref (lib.al_tl b) else 0 else 0 else 0
termination_by structural a
noncomputable def lib.exprlist_eq (a : lib.ExprList) (b : lib.ExprList) : Nat :=
  match a with | lib.ExprList.Nil => lib.el_is_nil b | lib.ExprList.Cons h t => if lib.el_is_nil b = 1 then 0 else if lib.expr_eq h.deref (lib.el_hd b) = 1 then lib.exprlist_eq t.deref (lib.el_tl b) else 0
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
theorem lib.defs_mirror_kernel_computes :
    lib.def_eq (lib.render_def (lib.RawDef.mk 20 (lib.ParamList.Cons 1 lib.TypData.TyNat (Tactus.Box.mk lib.ParamList.Nil)) lib.TypData.TyNat (lib.RawExp.BinOp 6 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawExp.Call 20 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyNat)) lib.TypData.TyNat))))) (lib.DefData.mk 20 (lib.ParamList.Cons 1 lib.TypData.TyNat (Tactus.Box.mk lib.ParamList.Nil)) lib.TypData.TyNat (lib.ExprData.BinOp 6 (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ExprData.App 20 (Tactus.Box.mk (lib.ExprData.Atom 1)))))) = 1 ∧ lib.def_eq (lib.render_def (lib.RawDef.mk 20 (lib.ParamList.Cons 1 lib.TypData.TyNat (Tactus.Box.mk lib.ParamList.Nil)) lib.TypData.TyNat (lib.RawExp.Var 1 lib.TypData.TyNat))) (lib.DefData.mk 20 (lib.ParamList.Cons 1 lib.TypData.TyInt (Tactus.Box.mk lib.ParamList.Nil)) lib.TypData.TyNat (lib.ExprData.Atom 1)) = 0 ∧ lib.def_eq (lib.render_def (lib.RawDef.mk 20 (lib.ParamList.Cons 1 lib.TypData.TyNat (Tactus.Box.mk lib.ParamList.Nil)) lib.TypData.TyNat (lib.RawExp.BinOp 6 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawExp.Call 20 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyNat)) lib.TypData.TyNat))))) (lib.DefData.mk 20 (lib.ParamList.Cons 1 lib.TypData.TyNat (Tactus.Box.mk lib.ParamList.Nil)) lib.TypData.TyNat (lib.ExprData.BinOp 6 (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ExprData.Atom 1)))) = 0 ∧ lib.dt_eq (lib.render_dt (lib.RawDt.mk 100 (lib.CtorList.Cons 30 (lib.TypList.Cons lib.TypData.TyInt (Tactus.Box.mk lib.TypList.Nil)) (Tactus.Box.mk (lib.CtorList.Cons 31 (lib.TypList.Cons (lib.TypData.TyBox 100) (Tactus.Box.mk (lib.TypList.Cons (lib.TypData.TyBox 100) (Tactus.Box.mk lib.TypList.Nil)))) (Tactus.Box.mk lib.CtorList.Nil)))))) (lib.DtData.mk 100 (lib.CtorList.Cons 30 (lib.TypList.Cons lib.TypData.TyInt (Tactus.Box.mk lib.TypList.Nil)) (Tactus.Box.mk (lib.CtorList.Cons 31 (lib.TypList.Cons (lib.TypData.TyBox 100) (Tactus.Box.mk (lib.TypList.Cons (lib.TypData.TyBox 100) (Tactus.Box.mk lib.TypList.Nil)))) (Tactus.Box.mk lib.CtorList.Nil))))) = 1 ∧ lib.dt_eq (lib.render_dt (lib.RawDt.mk 100 (lib.CtorList.Cons 30 (lib.TypList.Cons lib.TypData.TyInt (Tactus.Box.mk lib.TypList.Nil)) (Tactus.Box.mk lib.CtorList.Nil)))) (lib.DtData.mk 100 (lib.CtorList.Cons 30 (lib.TypList.Cons (lib.TypData.TyBox 100) (Tactus.Box.mk lib.TypList.Nil)) (Tactus.Box.mk lib.CtorList.Nil))) = 0 := by
  decide 
