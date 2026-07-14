-- tactus defs part: root (base = machinery + instance closure; one part per source module, SCC-merged; umbrella = interface)
import TactusDefs_lib_exec__base
import TactusPrelude
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
  match f with | lib.FrameList.FNil => 0 | lib.FrameList.FBind _id _typ t => 1 + lib.frame_len t.deref | lib.FrameList.FHyp _h t => 1 + lib.frame_len t.deref | lib.FrameList.FLet _id _v t => 1 + lib.frame_len t.deref
termination_by structural f
noncomputable def lib.stm_size (s : lib.StmData) : Nat :=
  match s with | lib.StmData.Assert _o _h => 1 | lib.StmData.Assume _e => 1 | lib.StmData.Assign _d _r => 1 | lib.StmData.Call reqs post => 1 + lib.raw_exp_list_len reqs.deref + lib.frame_len post.deref | lib.StmData.DeadEnd b => 1 + lib.stm_size b.deref | lib.StmData.Ret es _rb => 1 + lib.raw_exp_list_len es.deref | lib.StmData.If _c _nc t e => 1 + lib.stm_size t.deref + lib.stm_size e.deref | lib.StmData.Loop inv_hyps inv_obligs binders _ _ _ _ _ _ _ body => 1 + lib.binder_len inv_hyps.deref + lib.raw_exp_list_len inv_obligs.deref + lib.binder_len binders.deref + lib.stm_size body.deref | lib.StmData.Skip => 1 | lib.StmData.Seq a b => 1 + lib.stm_size a.deref + lib.stm_size b.deref
termination_by structural s
noncomputable def lib.goal_size (g : lib.GoalData) : Nat :=
  match g with | lib.GoalData.Leaf _e => 1 | lib.GoalData.Imp _h b => 1 + lib.goal_size b.deref | lib.GoalData.All _x _t b => 1 + lib.goal_size b.deref | lib.GoalData.Let _x _v b => 1 + lib.goal_size b.deref | lib.GoalData.LeafE _e => 1
termination_by structural g
noncomputable def lib.goal_count (gs : lib.GoalList) : Nat :=
  match gs with | lib.GoalList.Nil => 0 | lib.GoalList.Cons _g t => 1 + lib.goal_count t.deref
termination_by structural gs
noncomputable def lib.fnctx_arity (c : lib.FnCtxData) : Nat :=
  lib.binder_len c.params
noncomputable def lib.expr_size (e : lib.ExprData) : Nat :=
  match e with | lib.ExprData.Atom _ => 1 | lib.ExprData.Lit _ => 1 | lib.ExprData.LitBool _ => 1 | lib.ExprData.Cast _k t => 1 + lib.expr_size t.deref | lib.ExprData.BinOp _op l r => 1 + lib.expr_size l.deref + lib.expr_size r.deref | lib.ExprData.App _fn a => 1 + lib.expr_size a.deref | lib.ExprData.FieldProj t _f => 1 + lib.expr_size t.deref | lib.ExprData.SpanMark _loc t => 1 + lib.expr_size t.deref
termination_by structural e
noncomputable def lib.typ_size (t : lib.TypData) : Nat :=
  match t with | lib.TypData.TyInt => 1 | lib.TypData.TyNat => 1 | lib.TypData.TyBool => 1 | lib.TypData.TyNamed _ => 1 | lib.TypData.TyRef _ => 1
noncomputable def lib.td_tag (t : lib.TypData) : Nat :=
  match t with | lib.TypData.TyInt => 0 | lib.TypData.TyNat => 1 | lib.TypData.TyBool => 2 | lib.TypData.TyNamed _ => 3 | lib.TypData.TyRef _ => 4
noncomputable def lib.deref_type (t : lib.TypData) : lib.TypData :=
  match t with | lib.TypData.TyRef inner => lib.TypData.TyNamed inner | lib.TypData.TyInt => lib.TypData.TyInt | lib.TypData.TyNat => lib.TypData.TyNat | lib.TypData.TyBool => lib.TypData.TyBool | lib.TypData.TyNamed n => lib.TypData.TyNamed n
noncomputable def lib.type_of (re : lib.RawExp) : lib.TypData :=
  match re with | lib.RawExp.Var _id ty => ty | lib.RawExp.Lit _v ty => ty | lib.RawExp.LitBool _b => lib.TypData.TyBool | lib.RawExp.Clip target _e => target | lib.RawExp.BinOp _op ty _l _r => ty | lib.RawExp.Call _fn ret _arg _argty => ret | lib.RawExp.Field _fid fty _base => fty | lib.RawExp.HasType _n _inner => lib.TypData.TyBool | lib.RawExp.Deref e => lib.deref_type (lib.type_of e.deref) | lib.RawExp.Span _loc e => lib.type_of e.deref
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
noncomputable def lib.render_exp (re : lib.RawExp) : lib.ExprData :=
  match re with | lib.RawExp.Var id _ty => lib.ExprData.Atom id | lib.RawExp.Lit v _ty => lib.ExprData.Lit v | lib.RawExp.LitBool b => lib.ExprData.LitBool b | lib.RawExp.Clip target e => lib.coerce_if (lib.needs_nat_coercion (lib.type_of e.deref) target) (lib.render_exp e.deref) | lib.RawExp.BinOp op ty l r => let l2 := lib.coerce_if (lib.needs_nat_coercion (lib.type_of l.deref) ty) (lib.render_exp l.deref);
                                                                                                                                                                                                                                                                                                                         let r2 := lib.coerce_if (lib.needs_nat_coercion (lib.type_of r.deref) ty) (lib.render_exp r.deref);
                                                                                                                                                                                                                                                                                                                         lib.ExprData.BinOp op (Tactus.Box.mk l2) (Tactus.Box.mk r2) | lib.RawExp.Call fnid _ret arg argty => let a1 := lib.render_exp arg.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                              let a2 := lib.coerce_if (lib.needs_nat_coercion (lib.type_of arg.deref) argty) a1;
                                                                                                                                                                                                                                                                                                                                                                                                                              let a3 := lib.deref_if (lib.needs_ref_deref (lib.type_of arg.deref)) a2;
                                                                                                                                                                                                                                                                                                                                                                                                                              lib.ExprData.App fnid (Tactus.Box.mk a3) | lib.RawExp.Field fid _fty base => lib.ExprData.FieldProj (Tactus.Box.mk (lib.render_exp base.deref)) fid | lib.RawExp.HasType n inner => let e2 := lib.render_exp inner.deref;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  lib.ExprData.BinOp 11 (Tactus.Box.mk (lib.ExprData.BinOp 3 (Tactus.Box.mk (lib.ExprData.Lit 0)) (Tactus.Box.mk e2))) (Tactus.Box.mk (lib.ExprData.BinOp 2 (Tactus.Box.mk e2) (Tactus.Box.mk (lib.ExprData.Lit (lib.pow2 (Int.toNat n)))))) | lib.RawExp.Deref e => lib.ExprData.FieldProj (Tactus.Box.mk (lib.render_exp e.deref)) lib.deref_field | lib.RawExp.Span loc e => lib.ExprData.SpanMark loc (Tactus.Box.mk (lib.render_exp e.deref))
termination_by structural re
noncomputable def lib.ck_tag (k : lib.CastKind) : Nat :=
  match k with | lib.CastKind.IntToNat => 0 | lib.CastKind.NatToInt => 1
noncomputable def lib.castkind_eq (a : lib.CastKind) (b : lib.CastKind) : Nat :=
  if lib.ck_tag a = lib.ck_tag b then 1 else 0
noncomputable def lib.ed_tag (e : lib.ExprData) : Nat :=
  match e with | lib.ExprData.Atom _ => 0 | lib.ExprData.Lit _ => 1 | lib.ExprData.Cast _ _ => 2 | lib.ExprData.BinOp _ _ _ => 3 | lib.ExprData.App _ _ => 4 | lib.ExprData.FieldProj _ _ => 5 | lib.ExprData.SpanMark _ _ => 6 | lib.ExprData.LitBool _ => 7
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
noncomputable def lib.expr_eq (a : lib.ExprData) (b : lib.ExprData) : Nat :=
  match a with | lib.ExprData.Atom x => if lib.ed_tag b = 0 then if x = lib.ed_atom_id b then 1 else 0 else 0 | lib.ExprData.Lit v => if lib.ed_tag b = 1 then if v = lib.ed_lit_val b then 1 else 0 else 0 | lib.ExprData.LitBool x => if lib.ed_tag b = 7 then if x = lib.ed_litbool_val b then 1 else 0 else 0 | lib.ExprData.Cast k t => if lib.ed_tag b = 2 then if lib.castkind_eq k (lib.ed_cast_k b) = 1 then lib.expr_eq t.deref (lib.ed_cast_e b) else 0 else 0 | lib.ExprData.BinOp op l r => if lib.ed_tag b = 3 then if op = lib.ed_binop_op b then if lib.expr_eq l.deref (lib.ed_binop_l b) = 1 then lib.expr_eq r.deref (lib.ed_binop_r b) else 0 else 0 else 0 | lib.ExprData.App f a2 => if lib.ed_tag b = 4 then if f = lib.ed_app_fn b then lib.expr_eq a2.deref (lib.ed_app_arg b) else 0 else 0 | lib.ExprData.FieldProj t fld => if lib.ed_tag b = 5 then if fld = lib.ed_fp_field b then lib.expr_eq t.deref (lib.ed_fp_e b) else 0 else 0 | lib.ExprData.SpanMark loc t => if lib.ed_tag b = 6 then if loc = lib.ed_span_loc b then lib.expr_eq t.deref (lib.ed_span_e b) else 0 else 0
termination_by structural a
noncomputable def lib.frame_append (f : lib.FrameList) (g : lib.FrameList) : lib.FrameList :=
  match f with | lib.FrameList.FNil => g | lib.FrameList.FBind id typ t => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.frame_append t.deref g)) | lib.FrameList.FHyp h t => lib.FrameList.FHyp h (Tactus.Box.mk (lib.frame_append t.deref g)) | lib.FrameList.FLet id v t => lib.FrameList.FLet id v (Tactus.Box.mk (lib.frame_append t.deref g))
termination_by structural f
noncomputable def lib.binders_to_frame (b : lib.BinderList) : lib.FrameList :=
  match b with | lib.BinderList.Nil => lib.FrameList.FNil | lib.BinderList.Cons id typ t => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.binders_to_frame t.deref))
termination_by structural b
noncomputable def lib.close (f : lib.FrameList) (obligation : Int) : lib.GoalData :=
  match f with | lib.FrameList.FNil => lib.GoalData.Leaf obligation | lib.FrameList.FBind id typ t => lib.GoalData.All id typ (Tactus.Box.mk (lib.close t.deref obligation)) | lib.FrameList.FHyp h t => lib.GoalData.Imp h (Tactus.Box.mk (lib.close t.deref obligation)) | lib.FrameList.FLet id v t => lib.GoalData.Let id v (Tactus.Box.mk (lib.close t.deref obligation))
termination_by structural f
noncomputable def lib.close_e (f : lib.FrameList) (ob : lib.RawExp) : lib.GoalData :=
  match f with | lib.FrameList.FNil => lib.GoalData.LeafE (lib.render_exp ob) | lib.FrameList.FBind id typ t => lib.GoalData.All id typ (Tactus.Box.mk (lib.close_e t.deref ob)) | lib.FrameList.FHyp h t => lib.GoalData.Imp h (Tactus.Box.mk (lib.close_e t.deref ob)) | lib.FrameList.FLet id v t => lib.GoalData.Let id v (Tactus.Box.mk (lib.close_e t.deref ob))
termination_by structural f
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
  match f with | lib.FrameList.FNil => lib.FrameList.FNil | lib.FrameList.FBind id typ t => lib.FrameList.FBind id typ (Tactus.Box.mk (lib.havoc_lets t.deref mods)) | lib.FrameList.FHyp h t => lib.FrameList.FHyp h (Tactus.Box.mk (lib.havoc_lets t.deref mods)) | lib.FrameList.FLet id v t => if lib.binder_has_id mods id = 1 then lib.havoc_lets t.deref mods else lib.FrameList.FLet id v (Tactus.Box.mk (lib.havoc_lets t.deref mods))
termination_by structural f
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
  match s with | lib.StmData.Assert _o h => lib.frame_append f (lib.FrameList.FHyp h (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.Assume e => lib.frame_append f (lib.FrameList.FHyp e (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.Assign x rhs => lib.frame_append f (lib.FrameList.FLet x rhs (Tactus.Box.mk lib.FrameList.FNil)) | lib.StmData.Call _ post => lib.frame_append f post.deref | lib.StmData.DeadEnd _b => f | lib.StmData.Ret _es _rb => f | lib.StmData.If _c nc t e => if lib.diverges t.deref = 1 ∧ lib.is_skip e.deref = 1 then lib.frame_append f (lib.FrameList.FHyp nc (Tactus.Box.mk lib.FrameList.FNil)) else f | lib.StmData.Loop inv_hyps _ binders binder_bounds cond_name _ neg_cond_ann _ _ _ _ => lib.loop_use_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name neg_cond_ann | lib.StmData.Skip => f | lib.StmData.Seq a b => lib.frame_after (lib.frame_after f a.deref) b.deref
termination_by structural s
noncomputable def lib.ret_frame (f : lib.FrameList) (rb : lib.RetBind) : lib.FrameList :=
  match rb with | lib.RetBind.RetNone => f | lib.RetBind.RetLet name val => lib.frame_append f (lib.FrameList.FLet name val (Tactus.Box.mk lib.FrameList.FNil))
noncomputable def lib.wp_stm (f : lib.FrameList) (s : lib.StmData) : lib.GoalList :=
  match s with | lib.StmData.Assert o _h => lib.GoalList.Cons (Tactus.Box.mk (lib.close_e f o)) (Tactus.Box.mk lib.GoalList.Nil) | lib.StmData.Assume _e => lib.GoalList.Nil | lib.StmData.Assign _x _rhs => lib.GoalList.Nil | lib.StmData.Call reqs _ => lib.close_each_e f reqs.deref | lib.StmData.DeadEnd b => lib.wp_stm f b.deref | lib.StmData.Ret es rb => lib.close_each_e (lib.ret_frame f rb) es.deref | lib.StmData.If c nc t e => lib.goals_append (lib.wp_stm (lib.frame_append f (lib.FrameList.FHyp c (Tactus.Box.mk lib.FrameList.FNil))) t.deref) (lib.wp_stm (lib.frame_append f (lib.FrameList.FHyp nc (Tactus.Box.mk lib.FrameList.FNil))) e.deref) | lib.StmData.Loop inv_hyps inv_obligs binders binder_bounds cond_name cond_ann _ d_old_name d_old_val decrease_oblig body => let mframe := lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_val;
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
  lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 7 0)) (Tactus.Box.mk (lib.StmData.If 8 9 (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 10 11)) (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 5)) (Tactus.Box.mk lib.RawExpList.Nil))) (lib.RetBind.RetLet 6 10))))) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 13) 12)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assume 12)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 14 15)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 17) 16)) (Tactus.Box.mk (lib.StmData.Call (Tactus.Box.mk lib.RawExpList.Nil) (Tactus.Box.mk (lib.FrameList.FHyp 20 (Tactus.Box.mk (lib.FrameList.FLet 18 19 (Tactus.Box.mk lib.FrameList.FNil))))))))))))))) (Tactus.Box.mk (lib.StmData.Assign 10 18)))) (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 5)) (Tactus.Box.mk lib.RawExpList.Nil))) (lib.RetBind.RetLet 6 10)))))))
noncomputable def lib.cd19_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.Let 7 0 (Tactus.Box.mk (lib.GoalData.Imp 8 (Tactus.Box.mk (lib.GoalData.Let 10 11 (Tactus.Box.mk (lib.GoalData.Let 6 10 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 5))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.Let 7 0 (Tactus.Box.mk (lib.GoalData.Imp 9 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 13))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.Let 7 0 (Tactus.Box.mk (lib.GoalData.Imp 9 (Tactus.Box.mk (lib.GoalData.Imp 12 (Tactus.Box.mk (lib.GoalData.Imp 12 (Tactus.Box.mk (lib.GoalData.Let 14 15 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 17))))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.Let 7 0 (Tactus.Box.mk (lib.GoalData.Imp 9 (Tactus.Box.mk (lib.GoalData.Imp 12 (Tactus.Box.mk (lib.GoalData.Imp 12 (Tactus.Box.mk (lib.GoalData.Let 14 15 (Tactus.Box.mk (lib.GoalData.Imp 16 (Tactus.Box.mk (lib.GoalData.Imp 20 (Tactus.Box.mk (lib.GoalData.Let 18 19 (Tactus.Box.mk (lib.GoalData.Let 10 18 (Tactus.Box.mk (lib.GoalData.Let 6 10 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 5))))))))))))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)))))))
