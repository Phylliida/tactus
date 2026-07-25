-- tactus defs part: root (base = machinery + instance closure; one part per source module, SCC-merged; umbrella = interface)
import TactusDefs_lib_exec__base
import TactusDefs
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
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
  match f with | lib.FrameList.FNil => 0 | lib.FrameList.FBind _id _typ t => 1 + lib.frame_len t.deref | lib.FrameList.FHyp _hn _h _p t => 1 + lib.frame_len t.deref | lib.FrameList.FLetH _x _ty _v _en _ep t => 1 + lib.frame_len t.deref | lib.FrameList.FLet _id _v t => 1 + lib.frame_len t.deref | lib.FrameList.FLetR _id _v t => 1 + lib.frame_len t.deref | lib.FrameList.FUserCloser t => 1 + lib.frame_len t.deref
termination_by structural f
noncomputable def lib.stm_size (s : lib.StmData) : Nat :=
  match s with | lib.StmData.Assert _o _hn _h _hp => 1 | lib.StmData.Assume _hn _e _hp => 1 | lib.StmData.Assign _d _r => 1 | lib.StmData.AssignH _x _ty _v _en _ep => 1 | lib.StmData.AssignR _x _v => 1 | lib.StmData.Call reqs post => 1 + lib.raw_exp_list_len reqs.deref + lib.frame_len post.deref | lib.StmData.DeadEnd b => 1 + lib.stm_size b.deref | lib.StmData.AssertQueryNl b _tq => 1 + lib.stm_size b.deref | lib.StmData.AssertQueryTactus _o _hn _h _hp => 1 | lib.StmData.Ret es _rb => 1 + lib.raw_exp_list_len es.deref | lib.StmData.If _c _cn _nc _ncn _cp t e => 1 + lib.stm_size t.deref + lib.stm_size e.deref | lib.StmData.IfCtor pos_binders _ _ _ _ _ _ thn els => 1 + lib.binder_len pos_binders.deref + lib.stm_size thn.deref + lib.stm_size els.deref | lib.StmData.Loop inv_hyps inv_obligs inv_obligs_exit binders _ _ _ _ _ _ _ _ _ _ _ body => 1 + lib.binder_len inv_hyps.deref + lib.raw_exp_list_len inv_obligs.deref + lib.raw_exp_list_len inv_obligs_exit.deref + lib.binder_len binders.deref + lib.stm_size body.deref | lib.StmData.Skip => 1 | lib.StmData.Seq a b => 1 + lib.stm_size a.deref + lib.stm_size b.deref
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
noncomputable def lib.frame_append (f : lib.FrameList) (g : lib.FrameList) : lib.FrameList :=
  match f with | lib.FrameList.FNil => g | lib.FrameList.FBind id typ t => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.frame_append t.deref g)) | lib.FrameList.FHyp hn h p t => lib.FrameList.FHyp hn h p (Tactus.Box.mk (lib.frame_append t.deref g)) | lib.FrameList.FLetH x ty v en ep t => lib.FrameList.FLetH x ty v en ep (Tactus.Box.mk (lib.frame_append t.deref g)) | lib.FrameList.FLet id v t => lib.FrameList.FLet id v (Tactus.Box.mk (lib.frame_append t.deref g)) | lib.FrameList.FLetR id v t => lib.FrameList.FLetR id v (Tactus.Box.mk (lib.frame_append t.deref g)) | lib.FrameList.FUserCloser t => lib.FrameList.FUserCloser (Tactus.Box.mk (lib.frame_append t.deref g))
termination_by structural f
noncomputable def lib.binders_to_frame (b : lib.BinderList) : lib.FrameList :=
  match b with | lib.BinderList.Nil => lib.FrameList.FNil | lib.BinderList.Cons id typ t => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.binders_to_frame t.deref))
termination_by structural b
noncomputable def lib.close (f : lib.FrameList) (obligation : Int) : lib.GoalData :=
  match f with | lib.FrameList.FNil => lib.GoalData.Leaf obligation | lib.FrameList.FBind id typ t => lib.GoalData.All id typ (Tactus.Box.mk (lib.close t.deref obligation)) | lib.FrameList.FHyp _hn h _p t => lib.GoalData.Imp h (Tactus.Box.mk (lib.close t.deref obligation)) | lib.FrameList.FLetH id _ty v _en _ep t => lib.GoalData.Let id v (Tactus.Box.mk (lib.close t.deref obligation)) | lib.FrameList.FLet id v t => lib.GoalData.Let id v (Tactus.Box.mk (lib.close t.deref obligation)) | lib.FrameList.FLetR id v t => lib.GoalData.Let id v (Tactus.Box.mk (lib.close t.deref obligation)) | lib.FrameList.FUserCloser t => lib.close t.deref obligation
termination_by structural f
noncomputable def lib.has_plain_flet (f : lib.FrameList) : Nat :=
  match f with | lib.FrameList.FNil => 0 | lib.FrameList.FBind _x _ty t => lib.has_plain_flet t.deref | lib.FrameList.FHyp _n _h _p t => lib.has_plain_flet t.deref | lib.FrameList.FLet _x _v _t => 1 | lib.FrameList.FLetH _x _ty _v _en _ep t => lib.has_plain_flet t.deref | lib.FrameList.FLetR _x _v t => lib.has_plain_flet t.deref | lib.FrameList.FUserCloser t => lib.has_plain_flet t.deref
termination_by structural f
noncomputable def lib.has_poisoned_hyp (f : lib.FrameList) : Nat :=
  match f with | lib.FrameList.FNil => 0 | lib.FrameList.FBind _x _ty t => lib.has_poisoned_hyp t.deref | lib.FrameList.FHyp _n _h p t => if p = 1 then 1 else lib.has_poisoned_hyp t.deref | lib.FrameList.FLet _x _v t => lib.has_poisoned_hyp t.deref | lib.FrameList.FLetH _x _ty _v _en _ep t => lib.has_poisoned_hyp t.deref | lib.FrameList.FLetR _x _v t => lib.has_poisoned_hyp t.deref | lib.FrameList.FUserCloser t => lib.has_poisoned_hyp t.deref
termination_by structural f
noncomputable def lib.has_user_closer (f : lib.FrameList) : Nat :=
  match f with | lib.FrameList.FNil => 0 | lib.FrameList.FBind _x _ty t => lib.has_user_closer t.deref | lib.FrameList.FHyp _n _h _p t => lib.has_user_closer t.deref | lib.FrameList.FLet _x _v t => lib.has_user_closer t.deref | lib.FrameList.FLetH _x _ty _v _en _ep t => lib.has_user_closer t.deref | lib.FrameList.FLetR _x _v t => lib.has_user_closer t.deref | lib.FrameList.FUserCloser _t => 1
termination_by structural f
noncomputable def lib.gate_wrap (f : lib.FrameList) : Nat :=
  if (lib.has_plain_flet f = 1 ∨ lib.has_poisoned_hyp f = 1) ∨ lib.has_user_closer f = 1 then 1 else 0
noncomputable def lib.close_e_wrap (f : lib.FrameList) (ob : lib.RawExp) : lib.GoalData :=
  match f with | lib.FrameList.FNil => lib.GoalData.LeafE (lib.render_exp ob) | lib.FrameList.FBind id typ t => lib.GoalData.All id typ (Tactus.Box.mk (lib.close_e_wrap t.deref ob)) | lib.FrameList.FHyp _hn h _p t => lib.GoalData.Imp h (Tactus.Box.mk (lib.close_e_wrap t.deref ob)) | lib.FrameList.FLet id v t => lib.GoalData.Let id v (Tactus.Box.mk (lib.close_e_wrap t.deref ob)) | lib.FrameList.FLetH id _ty v _en _ep t => lib.GoalData.Let id v (Tactus.Box.mk (lib.close_e_wrap t.deref ob)) | lib.FrameList.FLetR id v t => lib.GoalData.Let id v (Tactus.Box.mk (lib.close_e_wrap t.deref ob)) | lib.FrameList.FUserCloser t => lib.close_e_wrap t.deref ob
termination_by structural f
noncomputable def lib.close_e_tel (f : lib.FrameList) (g : lib.GoalData) : lib.GoalData :=
  match f with | lib.FrameList.FNil => g | lib.FrameList.FBind id typ t => lib.GoalData.All id typ (Tactus.Box.mk (lib.close_e_tel t.deref g)) | lib.FrameList.FHyp hn h _p t => lib.GoalData.All hn h (Tactus.Box.mk (lib.close_e_tel t.deref g)) | lib.FrameList.FLet id v t => lib.GoalData.Let id v (Tactus.Box.mk (lib.close_e_tel t.deref g)) | lib.FrameList.FLetH id ty _v en ep t => lib.GoalData.All id ty (Tactus.Box.mk (lib.GoalData.All en ep (Tactus.Box.mk (lib.close_e_tel t.deref g)))) | lib.FrameList.FLetR _id _v t => lib.close_e_tel t.deref g | lib.FrameList.FUserCloser t => lib.close_e_tel t.deref g
termination_by structural f
noncomputable def lib.residue_fold_e (f : lib.FrameList) (g : lib.GoalData) : lib.GoalData :=
  match f with | lib.FrameList.FNil => g | lib.FrameList.FLetR id v t => lib.GoalData.Let id v (Tactus.Box.mk (lib.residue_fold_e t.deref g)) | lib.FrameList.FBind _id _typ t => lib.residue_fold_e t.deref g | lib.FrameList.FHyp _hn _h _p t => lib.residue_fold_e t.deref g | lib.FrameList.FLet _id _v t => lib.residue_fold_e t.deref g | lib.FrameList.FLetH _id _ty _v _en _ep t => lib.residue_fold_e t.deref g | lib.FrameList.FUserCloser t => lib.residue_fold_e t.deref g
termination_by structural f
noncomputable def lib.close_e_hoist (f : lib.FrameList) (ob : lib.RawExp) : lib.GoalData :=
  lib.close_e_tel f (lib.residue_fold_e f (lib.GoalData.LeafE (lib.render_exp ob)))
noncomputable def lib.close_e (f : lib.FrameList) (ob : lib.RawExp) : lib.GoalData :=
  if lib.gate_wrap f = 1 then lib.close_e_wrap f ob else lib.close_e_hoist f ob
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
  match f with | lib.FrameList.FNil => lib.FrameList.FNil | lib.FrameList.FBind id typ t => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.havoc_lets t.deref mods)) | lib.FrameList.FHyp hn h p t => lib.FrameList.FHyp hn h p (Tactus.Box.mk (lib.havoc_lets t.deref mods)) | lib.FrameList.FLet id v t => if lib.binder_has_id mods id = 1 then lib.havoc_lets t.deref mods else lib.FrameList.FLet id v (Tactus.Box.mk (lib.havoc_lets t.deref mods)) | lib.FrameList.FLetH id ty v en ep t => if lib.binder_has_id mods id = 1 then lib.havoc_lets t.deref mods else lib.FrameList.FLetH id ty v en ep (Tactus.Box.mk (lib.havoc_lets t.deref mods)) | lib.FrameList.FLetR id v t => if lib.binder_has_id mods id = 1 then lib.havoc_lets t.deref mods else lib.FrameList.FLetR id v (Tactus.Box.mk (lib.havoc_lets t.deref mods)) | lib.FrameList.FUserCloser t => lib.FrameList.FUserCloser (Tactus.Box.mk (lib.havoc_lets t.deref mods))
termination_by structural f
noncomputable def lib.seed_params (params : lib.BinderList) (bounds : lib.ParamBoundList) : lib.FrameList :=
  match params with | lib.BinderList.Nil => lib.FrameList.FNil | lib.BinderList.Cons id typ t => match bounds with | lib.ParamBoundList.Bound hname prop bt => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.FrameList.FBind hname prop (Tactus.Box.mk (lib.seed_params t.deref bt.deref)))) | lib.ParamBoundList.NoBound bt => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.seed_params t.deref bt.deref)) | lib.ParamBoundList.Nil => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.seed_params t.deref lib.ParamBoundList.Nil))
termination_by structural params
noncomputable def lib.binderprops_to_hyps (b : lib.BinderList) : lib.FrameList :=
  match b with | lib.BinderList.Nil => lib.FrameList.FNil | lib.BinderList.Cons name prop t => lib.FrameList.FHyp name prop 0 (Tactus.Box.mk (lib.binderprops_to_hyps t.deref))
termination_by structural b
noncomputable def lib.mod_var_frames (binders : lib.BinderList) (bounds : lib.ParamBoundList) : lib.FrameList :=
  match binders with | lib.BinderList.Nil => lib.FrameList.FNil | lib.BinderList.Cons id typ t => match bounds with | lib.ParamBoundList.Bound hname prop bt => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.FrameList.FHyp hname prop 0 (Tactus.Box.mk (lib.mod_var_frames t.deref bt.deref)))) | lib.ParamBoundList.NoBound bt => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.mod_var_frames t.deref bt.deref)) | lib.ParamBoundList.Nil => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.mod_var_frames t.deref lib.ParamBoundList.Nil))
termination_by structural binders
noncomputable def lib.loop_maintain_frame (f : lib.FrameList) (inv_hyps : lib.BinderList) (binders : lib.BinderList) (binder_bounds : lib.ParamBoundList) (cond_name : Int) (cond_ann : Int) (cond_poison : Int) (d_old_name : Int) (d_old_ty : Int) (d_old_val : Int) (d_old_eq_name : Int) (d_old_eq_prop : Int) : lib.FrameList :=
  let hv := lib.havoc_lets f binders;
  let d_old := lib.FrameList.FLetH d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop (Tactus.Box.mk lib.FrameList.FNil);
  lib.frame_append hv (lib.frame_append (lib.mod_var_frames binders binder_bounds) (lib.frame_append (lib.binderprops_to_hyps inv_hyps) (lib.frame_append (lib.FrameList.FHyp cond_name cond_ann cond_poison (Tactus.Box.mk lib.FrameList.FNil)) d_old)))
noncomputable def lib.loop_use_frame (f : lib.FrameList) (inv_hyps : lib.BinderList) (binders : lib.BinderList) (binder_bounds : lib.ParamBoundList) (cond_name : Int) (neg_cond_ann : Int) (cond_poison : Int) : lib.FrameList :=
  let hv := lib.havoc_lets f binders;
  lib.frame_append hv (lib.frame_append (lib.mod_var_frames binders binder_bounds) (lib.frame_append (lib.binderprops_to_hyps inv_hyps) (lib.FrameList.FHyp cond_name neg_cond_ann cond_poison (Tactus.Box.mk lib.FrameList.FNil))))
noncomputable def lib.is_skip (s : lib.StmData) : Nat :=
  match s with | lib.StmData.Skip => 1 | _ => 0
noncomputable def lib.diverges (s : lib.StmData) : Nat :=
  match s with | lib.StmData.Ret _es _rb => 1 | lib.StmData.DeadEnd _b => 1 | lib.StmData.Seq a b => if lib.diverges a.deref = 1 ∨ lib.diverges b.deref = 1 then 1 else 0 | lib.StmData.If _c _cn _nc _ncn _cp t e => if lib.diverges t.deref = 1 ∧ lib.diverges e.deref = 1 then 1 else 0 | lib.StmData.IfCtor _ _ _ _ _ _ _ thn els => if lib.diverges thn.deref = 1 ∧ lib.diverges els.deref = 1 then 1 else 0 | _ => 0
termination_by structural s
noncomputable def lib.strip_hyps (f : lib.FrameList) : lib.FrameList :=
  match f with | lib.FrameList.FNil => lib.FrameList.FNil | lib.FrameList.FBind x ty t => lib.FrameList.FBind x ty (Tactus.Box.mk (lib.strip_hyps t.deref)) | lib.FrameList.FHyp _hn _h _p t => lib.strip_hyps t.deref | lib.FrameList.FLet x v t => lib.FrameList.FLet x v (Tactus.Box.mk (lib.strip_hyps t.deref)) | lib.FrameList.FLetH x ty v en ep t => lib.FrameList.FLetH x ty v en ep (Tactus.Box.mk (lib.strip_hyps t.deref)) | lib.FrameList.FLetR x v t => lib.FrameList.FLetR x v (Tactus.Box.mk (lib.strip_hyps t.deref)) | lib.FrameList.FUserCloser t => lib.strip_hyps t.deref
termination_by structural f
noncomputable def lib.ctor_pos_frame (b : lib.BinderList) (en : Int) (ep : Int) (epo : Int) : lib.FrameList :=
  lib.frame_append (lib.binders_to_frame b) (lib.FrameList.FHyp en ep epo (Tactus.Box.mk lib.FrameList.FNil))
noncomputable def lib.frame_after (f : lib.FrameList) (s : lib.StmData) : lib.FrameList :=
  match s with | lib.StmData.Assert _o hn h hp => lib.frame_append f (lib.FrameList.FHyp hn h hp (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.Assume hn e hp => lib.frame_append f (lib.FrameList.FHyp hn e hp (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.Assign x rhs => lib.frame_append f (lib.FrameList.FLet x rhs (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.AssignH x ty v en ep => lib.frame_append f (lib.FrameList.FLetH x ty v en ep (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.AssignR x v => lib.frame_append f (lib.FrameList.FLetR x v (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.Call _ post => lib.frame_append f post.deref | lib.StmData.DeadEnd _b => f | lib.StmData.AssertQueryNl _b _tq => f | lib.StmData.AssertQueryTactus _o hn h hp => lib.frame_append f (lib.FrameList.FHyp hn h hp (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.Ret _es _rb => f | lib.StmData.If _c _cn nc ncn cp t e => if lib.diverges t.deref = 1 ∧ lib.is_skip e.deref = 1 then lib.frame_append f (lib.FrameList.FHyp ncn nc cp (Tactus.Box.mk lib.FrameList.FNil)) else f | lib.StmData.IfCtor _ _ _ _ neg_name neg_prop neg_poison thn els => if lib.diverges thn.deref = 1 ∧ lib.is_skip els.deref = 1 then lib.frame_append f (lib.FrameList.FHyp neg_name neg_prop neg_poison (Tactus.Box.mk lib.FrameList.FNil)) else f | lib.StmData.Loop inv_hyps _ _ binders binder_bounds cond_name _ neg_cond_ann cond_poison _ _ _ _ _ _ _ => lib.loop_use_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name neg_cond_ann cond_poison | lib.StmData.Skip => f | lib.StmData.Seq a b => lib.frame_after (lib.frame_after f a.deref) b.deref
termination_by structural s
noncomputable def lib.ret_frame (f : lib.FrameList) (rb : lib.RetBind) : lib.FrameList :=
  match rb with | lib.RetBind.RetNone => f | lib.RetBind.RetLet name val => lib.frame_append f (lib.FrameList.FLet name val (Tactus.Box.mk lib.FrameList.FNil)) | lib.RetBind.RetLetH name ty val en ep => lib.frame_append f (lib.FrameList.FLetH name ty val en ep (Tactus.Box.mk lib.FrameList.FNil))
noncomputable def lib.wp_stm (f : lib.FrameList) (s : lib.StmData) : lib.GoalList :=
  match s with | lib.StmData.Assert o _hn _h _hp => lib.GoalList.Cons (Tactus.Box.mk (lib.close_e f o)) (Tactus.Box.mk lib.GoalList.Nil) | lib.StmData.Assume _hn _e _hp => lib.GoalList.Nil | lib.StmData.Assign _x _rhs => lib.GoalList.Nil | lib.StmData.AssignH _x _ty _v _en _ep => lib.GoalList.Nil | lib.StmData.AssignR _x _v => lib.GoalList.Nil | lib.StmData.Call reqs _ => lib.close_each_e f reqs.deref | lib.StmData.DeadEnd b => lib.wp_stm f b.deref | lib.StmData.AssertQueryNl b tq => lib.goals_append (lib.wp_stm (lib.strip_hyps f) b.deref) (lib.GoalList.Cons (Tactus.Box.mk (lib.close_e (lib.frame_after (lib.strip_hyps f) b.deref) tq)) (Tactus.Box.mk lib.GoalList.Nil)) | lib.StmData.AssertQueryTactus o _hn _h _hp => lib.GoalList.Cons (Tactus.Box.mk (lib.close_e (lib.frame_append f (lib.FrameList.FUserCloser (Tactus.Box.mk lib.FrameList.FNil))) o)) (Tactus.Box.mk lib.GoalList.Nil) | lib.StmData.Ret es rb => lib.close_each_e (lib.ret_frame f rb) es.deref | lib.StmData.If c cn nc ncn cp t e => lib.goals_append (lib.wp_stm (lib.frame_append f (lib.FrameList.FHyp cn c cp (Tactus.Box.mk lib.FrameList.FNil))) t.deref) (lib.wp_stm (lib.frame_append f (lib.FrameList.FHyp ncn nc cp (Tactus.Box.mk lib.FrameList.FNil))) e.deref) | lib.StmData.IfCtor pos_binders eq_name eq_prop eq_poison neg_name neg_prop neg_poison thn els => lib.goals_append (lib.wp_stm (lib.frame_append f (lib.ctor_pos_frame pos_binders.deref eq_name eq_prop eq_poison)) thn.deref) (lib.wp_stm (lib.frame_append f (lib.FrameList.FHyp neg_name neg_prop neg_poison (Tactus.Box.mk lib.FrameList.FNil))) els.deref) | lib.StmData.Loop inv_hyps inv_obligs inv_obligs_exit binders binder_bounds cond_name cond_ann _ cond_poison d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop decrease_oblig body => let mframe := lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann cond_poison d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     let body_goals := lib.wp_stm mframe body.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     let endf := lib.frame_after mframe body.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     let maintain_reclose := lib.close_each_e endf inv_obligs_exit.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     let decrease_goal := lib.GoalList.Cons (Tactus.Box.mk (lib.close_e endf decrease_oblig)) (Tactus.Box.mk lib.GoalList.Nil);
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     let init := lib.close_each_e f inv_obligs.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     lib.goals_append init (lib.goals_append body_goals (lib.goals_append maintain_reclose decrease_goal)) | lib.StmData.Skip => lib.GoalList.Nil | lib.StmData.Seq a b => lib.goals_append (lib.wp_stm f a.deref) (lib.wp_stm (lib.frame_after f a.deref) b.deref)
termination_by structural s
noncomputable def lib.mut_preamble_frame (m : lib.MutParamList) : lib.FrameList :=
  match m with | lib.MutParamList.Nil => lib.FrameList.FNil | lib.MutParamList.Cons p at_pre deref_val t => lib.FrameList.FLet at_pre deref_val (Tactus.Box.mk (lib.FrameList.FLet p deref_val (Tactus.Box.mk (lib.mut_preamble_frame t.deref))))
termination_by structural m
noncomputable def lib.seed_frame (c : lib.FnCtxData) : lib.FrameList :=
  lib.frame_append (lib.binders_to_frame c.typ_params) (lib.frame_append (lib.seed_params c.params c.param_bounds) (lib.frame_append (lib.binders_to_frame c.reqs) (lib.frame_append (lib.mut_preamble_frame c.mut_params) (if c.closer_default = 1 then lib.FrameList.FNil else lib.FrameList.FUserCloser (Tactus.Box.mk lib.FrameList.FNil)))))
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
noncomputable def lib.s2_mut_ctx : lib.FnCtxData :=
  lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)) (lib.BinderList.Cons 3 2 (Tactus.Box.mk lib.BinderList.Nil)) (lib.MutParamList.Cons 0 4 5 (Tactus.Box.mk lib.MutParamList.Nil)) lib.LeafList.Nil 1
noncomputable def lib.cd19_ctx : lib.FnCtxData :=
  lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.Bound 3 2 (Tactus.Box.mk lib.ParamBoundList.Nil)) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 4 (Tactus.Box.mk lib.LeafList.Nil)) 1
noncomputable def lib.cd19_sst : lib.StmData :=
  lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 7 0)) (Tactus.Box.mk (lib.StmData.If 8 0 9 0 0 (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 10 11)) (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 5)) (Tactus.Box.mk lib.RawExpList.Nil))) (lib.RetBind.RetLet 6 10))))) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 13) 0 12 0)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assume 0 12 0)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 14 15)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 17) 0 16 0)) (Tactus.Box.mk (lib.StmData.Call (Tactus.Box.mk lib.RawExpList.Nil) (Tactus.Box.mk (lib.FrameList.FHyp 0 20 0 (Tactus.Box.mk (lib.FrameList.FLet 18 19 (Tactus.Box.mk lib.FrameList.FNil))))))))))))))) (Tactus.Box.mk (lib.StmData.Assign 10 18)))) (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 5)) (Tactus.Box.mk lib.RawExpList.Nil))) (lib.RetBind.RetLet 6 10)))))))
noncomputable def lib.cd19_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.Let 7 0 (Tactus.Box.mk (lib.GoalData.Imp 8 (Tactus.Box.mk (lib.GoalData.Let 10 11 (Tactus.Box.mk (lib.GoalData.Let 6 10 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 5))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.Let 7 0 (Tactus.Box.mk (lib.GoalData.Imp 9 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 13))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.Let 7 0 (Tactus.Box.mk (lib.GoalData.Imp 9 (Tactus.Box.mk (lib.GoalData.Imp 12 (Tactus.Box.mk (lib.GoalData.Imp 12 (Tactus.Box.mk (lib.GoalData.Let 14 15 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 17))))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.Let 7 0 (Tactus.Box.mk (lib.GoalData.Imp 9 (Tactus.Box.mk (lib.GoalData.Imp 12 (Tactus.Box.mk (lib.GoalData.Imp 12 (Tactus.Box.mk (lib.GoalData.Let 14 15 (Tactus.Box.mk (lib.GoalData.Imp 16 (Tactus.Box.mk (lib.GoalData.Imp 20 (Tactus.Box.mk (lib.GoalData.Let 18 19 (Tactus.Box.mk (lib.GoalData.Let 10 18 (Tactus.Box.mk (lib.GoalData.Let 6 10 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 5))))))))))))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)))))))
noncomputable def lib.upd (st : Int → Int) (x : Int) (n : Int) : Int → Int :=
  fun (k : Int) => if k = x then n else (Tactus.Ref.mk st).deref k
noncomputable def lib.holds (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (g : lib.GoalData) (st : Int → Int) : Prop :=
  match g with | lib.GoalData.Leaf id => (Tactus.Ref.mk hp).deref id st | lib.GoalData.Imp h t => (Tactus.Ref.mk hp).deref h st → lib.holds hp he lv t.deref st | lib.GoalData.All x _ty t => ∀ (n : Int), lib.holds hp he lv t.deref (lib.upd st x n) | lib.GoalData.Let x v t => lib.holds hp he lv t.deref (lib.upd st x ((Tactus.Ref.mk lv).deref v st)) | lib.GoalData.LeafE e => (Tactus.Ref.mk he).deref e st
termination_by structural g
noncomputable def lib.holds_all (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (gs : lib.GoalList) (st : Int → Int) : Prop :=
  match gs with | lib.GoalList.Nil => True | lib.GoalList.Cons g t => lib.holds hp he lv g.deref st ∧ lib.holds_all hp he lv t.deref st
termination_by structural gs
noncomputable def lib.obligs_safe (he : lib.ExprData → (Int → Int) → Prop) (l : lib.RawExpList) (st : Int → Int) : Prop :=
  match l with | lib.RawExpList.Nil => True | lib.RawExpList.Cons h t => (Tactus.Ref.mk he).deref (lib.render_exp h.deref) st ∧ lib.obligs_safe he t.deref st
termination_by structural l
noncomputable def lib.close_sem_e_wrap (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (st : Int → Int) (o : lib.RawExp) : Prop :=
  match f with | lib.FrameList.FNil => (Tactus.Ref.mk he).deref (lib.render_exp o) st | lib.FrameList.FBind x _ty t => ∀ (n : Int), lib.close_sem_e_wrap hp he lv t.deref (lib.upd st x n) o | lib.FrameList.FHyp _hn h _p t => (Tactus.Ref.mk hp).deref h st → lib.close_sem_e_wrap hp he lv t.deref st o | lib.FrameList.FLet x v t => lib.close_sem_e_wrap hp he lv t.deref (lib.upd st x ((Tactus.Ref.mk lv).deref v st)) o | lib.FrameList.FLetH x _ty v _en _ep t => lib.close_sem_e_wrap hp he lv t.deref (lib.upd st x ((Tactus.Ref.mk lv).deref v st)) o | lib.FrameList.FLetR x v t => lib.close_sem_e_wrap hp he lv t.deref (lib.upd st x ((Tactus.Ref.mk lv).deref v st)) o | lib.FrameList.FUserCloser t => lib.close_sem_e_wrap hp he lv t.deref st o
termination_by structural f
noncomputable def lib.close_sem_e_res (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (st : Int → Int) (o : lib.RawExp) : Prop :=
  match f with | lib.FrameList.FNil => (Tactus.Ref.mk he).deref (lib.render_exp o) st | lib.FrameList.FLetR x v t => lib.close_sem_e_res hp he lv t.deref (lib.upd st x ((Tactus.Ref.mk lv).deref v st)) o | lib.FrameList.FBind _x _ty t => lib.close_sem_e_res hp he lv t.deref st o | lib.FrameList.FHyp _hn _h _p t => lib.close_sem_e_res hp he lv t.deref st o | lib.FrameList.FLet _x _v t => lib.close_sem_e_res hp he lv t.deref st o | lib.FrameList.FLetH _x _ty _v _en _ep t => lib.close_sem_e_res hp he lv t.deref st o | lib.FrameList.FUserCloser t => lib.close_sem_e_res hp he lv t.deref st o
termination_by structural f
noncomputable def lib.close_sem_e_tel (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (f0 : lib.FrameList) (st : Int → Int) (o : lib.RawExp) : Prop :=
  match f with | lib.FrameList.FNil => lib.close_sem_e_res hp he lv f0 st o | lib.FrameList.FBind x _ty t => ∀ (n : Int), lib.close_sem_e_tel hp he lv t.deref f0 (lib.upd st x n) o | lib.FrameList.FHyp hn _h _p t => ∀ (n : Int), lib.close_sem_e_tel hp he lv t.deref f0 (lib.upd st hn n) o | lib.FrameList.FLet x v t => lib.close_sem_e_tel hp he lv t.deref f0 (lib.upd st x ((Tactus.Ref.mk lv).deref v st)) o | lib.FrameList.FLetH x _ty _v en _ep t => ∀ (a : Int) (b : Int), lib.close_sem_e_tel hp he lv t.deref f0 (lib.upd (lib.upd st x a) en b) o | lib.FrameList.FLetR _x _v t => lib.close_sem_e_tel hp he lv t.deref f0 st o | lib.FrameList.FUserCloser t => lib.close_sem_e_tel hp he lv t.deref f0 st o
termination_by structural f
noncomputable def lib.close_sem_e_hoist (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (st : Int → Int) (o : lib.RawExp) : Prop :=
  lib.close_sem_e_tel hp he lv f f st o
noncomputable def lib.close_sem_e (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (st : Int → Int) (o : lib.RawExp) : Prop :=
  if lib.gate_wrap f = 1 then lib.close_sem_e_wrap hp he lv f st o else lib.close_sem_e_hoist hp he lv f st o
noncomputable def lib.close_sem_obligs_wrap (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (st : Int → Int) (l : lib.RawExpList) : Prop :=
  match f with | lib.FrameList.FNil => lib.obligs_safe he l st | lib.FrameList.FBind x _ty t => ∀ (n : Int), lib.close_sem_obligs_wrap hp he lv t.deref (lib.upd st x n) l | lib.FrameList.FHyp _hn h _p t => (Tactus.Ref.mk hp).deref h st → lib.close_sem_obligs_wrap hp he lv t.deref st l | lib.FrameList.FLet x v t => lib.close_sem_obligs_wrap hp he lv t.deref (lib.upd st x ((Tactus.Ref.mk lv).deref v st)) l | lib.FrameList.FLetH x _ty v _en _ep t => lib.close_sem_obligs_wrap hp he lv t.deref (lib.upd st x ((Tactus.Ref.mk lv).deref v st)) l | lib.FrameList.FLetR x v t => lib.close_sem_obligs_wrap hp he lv t.deref (lib.upd st x ((Tactus.Ref.mk lv).deref v st)) l | lib.FrameList.FUserCloser t => lib.close_sem_obligs_wrap hp he lv t.deref st l
termination_by structural f
noncomputable def lib.close_sem_obligs_res (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (st : Int → Int) (l : lib.RawExpList) : Prop :=
  match f with | lib.FrameList.FNil => lib.obligs_safe he l st | lib.FrameList.FLetR x v t => lib.close_sem_obligs_res hp he lv t.deref (lib.upd st x ((Tactus.Ref.mk lv).deref v st)) l | lib.FrameList.FBind _x _ty t => lib.close_sem_obligs_res hp he lv t.deref st l | lib.FrameList.FHyp _hn _h _p t => lib.close_sem_obligs_res hp he lv t.deref st l | lib.FrameList.FLet _x _v t => lib.close_sem_obligs_res hp he lv t.deref st l | lib.FrameList.FLetH _x _ty _v _en _ep t => lib.close_sem_obligs_res hp he lv t.deref st l | lib.FrameList.FUserCloser t => lib.close_sem_obligs_res hp he lv t.deref st l
termination_by structural f
noncomputable def lib.close_sem_obligs_tel (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (f0 : lib.FrameList) (st : Int → Int) (l : lib.RawExpList) : Prop :=
  match f with | lib.FrameList.FNil => lib.close_sem_obligs_res hp he lv f0 st l | lib.FrameList.FBind x _ty t => ∀ (n : Int), lib.close_sem_obligs_tel hp he lv t.deref f0 (lib.upd st x n) l | lib.FrameList.FHyp hn _h _p t => ∀ (n : Int), lib.close_sem_obligs_tel hp he lv t.deref f0 (lib.upd st hn n) l | lib.FrameList.FLet x v t => lib.close_sem_obligs_tel hp he lv t.deref f0 (lib.upd st x ((Tactus.Ref.mk lv).deref v st)) l | lib.FrameList.FLetH x _ty _v en _ep t => ∀ (a : Int) (b : Int), lib.close_sem_obligs_tel hp he lv t.deref f0 (lib.upd (lib.upd st x a) en b) l | lib.FrameList.FLetR _x _v t => lib.close_sem_obligs_tel hp he lv t.deref f0 st l | lib.FrameList.FUserCloser t => lib.close_sem_obligs_tel hp he lv t.deref f0 st l
termination_by structural f
noncomputable def lib.close_sem_obligs_hoist (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (st : Int → Int) (l : lib.RawExpList) : Prop :=
  lib.close_sem_obligs_tel hp he lv f f st l
noncomputable def lib.close_sem_obligs (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (st : Int → Int) (l : lib.RawExpList) : Prop :=
  if lib.gate_wrap f = 1 then lib.close_sem_obligs_wrap hp he lv f st l else lib.close_sem_obligs_hoist hp he lv f st l
noncomputable def lib.exec_safe_f (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (s : lib.StmData) (st : Int → Int) : Prop :=
  match s with | lib.StmData.Assert o _hn _h _hp => lib.close_sem_e hp he lv f st o | lib.StmData.Assume _hn _e _hp => True | lib.StmData.Assign _x _rhs => True | lib.StmData.AssignH _x _ty _v _en _ep => True | lib.StmData.AssignR _x _v => True | lib.StmData.Call reqs _ => lib.close_sem_obligs hp he lv f st reqs.deref | lib.StmData.DeadEnd b => lib.exec_safe_f hp he lv f b.deref st | lib.StmData.AssertQueryNl b tq => lib.exec_safe_f hp he lv (lib.strip_hyps f) b.deref st ∧ lib.close_sem_e hp he lv (lib.frame_after (lib.strip_hyps f) b.deref) st tq | lib.StmData.AssertQueryTactus o _hn _h _hp => lib.close_sem_e hp he lv (lib.frame_append f (lib.FrameList.FUserCloser (Tactus.Box.mk lib.FrameList.FNil))) st o | lib.StmData.Ret es rb => lib.close_sem_obligs hp he lv (lib.ret_frame f rb) st es.deref | lib.StmData.If c cn nc ncn cp t e => lib.exec_safe_f hp he lv (lib.frame_append f (lib.FrameList.FHyp cn c cp (Tactus.Box.mk lib.FrameList.FNil))) t.deref st ∧ lib.exec_safe_f hp he lv (lib.frame_append f (lib.FrameList.FHyp ncn nc cp (Tactus.Box.mk lib.FrameList.FNil))) e.deref st | lib.StmData.IfCtor pos_binders eq_name eq_prop eq_poison neg_name neg_prop neg_poison thn els => lib.exec_safe_f hp he lv (lib.frame_append f (lib.ctor_pos_frame pos_binders.deref eq_name eq_prop eq_poison)) thn.deref st ∧ lib.exec_safe_f hp he lv (lib.frame_append f (lib.FrameList.FHyp neg_name neg_prop neg_poison (Tactus.Box.mk lib.FrameList.FNil))) els.deref st | lib.StmData.Loop inv_hyps inv_obligs inv_obligs_exit binders binder_bounds cond_name cond_ann _ cond_poison d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop decrease_oblig body => let mframe := lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann cond_poison d_old_name d_old_ty d_old_val d_old_eq_name d_old_eq_prop;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   let endf := lib.frame_after mframe body.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   ((lib.close_sem_obligs hp he lv f st inv_obligs.deref ∧ lib.exec_safe_f hp he lv mframe body.deref st) ∧ lib.close_sem_obligs hp he lv endf st inv_obligs_exit.deref) ∧ lib.close_sem_e hp he lv endf st decrease_oblig | lib.StmData.Skip => True | lib.StmData.Seq a b => lib.exec_safe_f hp he lv f a.deref st ∧ lib.exec_safe_f hp he lv (lib.frame_after f a.deref) b.deref st
termination_by structural s
