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
noncomputable def lib.td_tag (t : lib.TypData) : Nat :=
  match t with | lib.TypData.TyInt => 0 | lib.TypData.TyNat => 1 | lib.TypData.TyBool => 2 | lib.TypData.TyNamed _ => 3 | lib.TypData.TyRef _ => 4 | lib.TypData.TyBox _ => 5
noncomputable def lib.td_id (t : lib.TypData) : Int :=
  match t with | lib.TypData.TyNamed n => n | lib.TypData.TyRef n => n | lib.TypData.TyBox n => n | _ => 0
noncomputable def lib.typ_eq (a : lib.TypData) (b : lib.TypData) : Nat :=
  if lib.td_tag a = lib.td_tag b then if lib.td_id a = lib.td_id b then 1 else 0 else 0
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
theorem lib.probe_goals_eq_lit :
    lib.goals_eq lib.GoalList.Nil lib.GoalList.Nil = 1 ∧ lib.goals_eq (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Leaf 9)) (Tactus.Box.mk lib.GoalList.Nil)) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Leaf 9)) (Tactus.Box.mk lib.GoalList.Nil)) = 1 := by
  decide 
