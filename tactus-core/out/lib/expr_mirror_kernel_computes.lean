import TactusPrelude
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
inductive lib.TypData where
  | Int
  | Nat
  | Bool
  | Named (val0 : Int)
  | Ref (val0 : Int)
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
inductive lib.RawExp where
  | Var (val0 : Int) (val1 : lib.TypData)
  | Lit (val0 : Int) (val1 : lib.TypData)
  | Clip (val0 : lib.TypData) (val1 : Tactus.Box lib.RawExp)
  | BinOp (val0 : Int) (val1 : lib.TypData) (val2 : Tactus.Box lib.RawExp) (val3 : Tactus.Box lib.RawExp)
  | Call (val0 : Int) (val1 : lib.TypData) (val2 : Tactus.Box lib.RawExp) (val3 : lib.TypData)
  | Deref (val0 : Tactus.Box lib.RawExp)
  | Span (val0 : Int) (val1 : Tactus.Box lib.RawExp)
  deriving Inhabited
@[simp] noncomputable def lib.RawExp.height (s : lib.RawExp) : Nat :=
  match s with | lib.RawExp.Var _ _ => 1 | lib.RawExp.Lit _ _ => 1 | lib.RawExp.Clip _ val1 => 1 + lib.RawExp.height val1.deref | lib.RawExp.BinOp _ _ val2 val3 => 1 + lib.RawExp.height val2.deref + lib.RawExp.height val3.deref | lib.RawExp.Call _ _ val2 _ => 1 + lib.RawExp.height val2.deref | lib.RawExp.Deref val0 => 1 + lib.RawExp.height val0.deref | lib.RawExp.Span _ val1 => 1 + lib.RawExp.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
noncomputable def lib.expr_size (e : lib.ExprData) : Nat :=
  match e with | lib.ExprData.Atom _ => 1 | lib.ExprData.Lit _ => 1 | lib.ExprData.Cast _k t => 1 + lib.expr_size t.deref | lib.ExprData.BinOp _op l r => 1 + lib.expr_size l.deref + lib.expr_size r.deref | lib.ExprData.App _fn a => 1 + lib.expr_size a.deref | lib.ExprData.FieldProj t _f => 1 + lib.expr_size t.deref | lib.ExprData.SpanMark _loc t => 1 + lib.expr_size t.deref
termination_by structural e
noncomputable def lib.typ_size (t : lib.TypData) : Nat :=
  match t with | lib.TypData.Int => 1 | lib.TypData.Nat => 1 | lib.TypData.Bool => 1 | lib.TypData.Named _ => 1 | lib.TypData.Ref _ => 1
noncomputable def lib.td_tag (t : lib.TypData) : Nat :=
  match t with | lib.TypData.Int => 0 | lib.TypData.Nat => 1 | lib.TypData.Bool => 2 | lib.TypData.Named _ => 3 | lib.TypData.Ref _ => 4
noncomputable def lib.deref_type (t : lib.TypData) : lib.TypData :=
  match t with | lib.TypData.Ref inner => lib.TypData.Named inner | lib.TypData.Int => lib.TypData.Int | lib.TypData.Nat => lib.TypData.Nat | lib.TypData.Bool => lib.TypData.Bool | lib.TypData.Named n => lib.TypData.Named n
noncomputable def lib.type_of (re : lib.RawExp) : lib.TypData :=
  match re with | lib.RawExp.Var _id ty => ty | lib.RawExp.Lit _v ty => ty | lib.RawExp.Clip target _e => target | lib.RawExp.BinOp _op ty _l _r => ty | lib.RawExp.Call _fn ret _arg _argty => ret | lib.RawExp.Deref e => lib.deref_type (lib.type_of e.deref) | lib.RawExp.Span _loc e => lib.type_of e.deref
termination_by structural re
noncomputable def lib.needs_nat_coercion (operand : lib.TypData) (op_result : lib.TypData) : Nat :=
  if lib.td_tag operand = 0 ∧ lib.td_tag op_result = 1 then 1 else 0
noncomputable def lib.coerce_if (b : Nat) (e : lib.ExprData) : lib.ExprData :=
  if b = 1 then lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk e) else e
noncomputable def lib.deref_field : Int :=
  0
noncomputable def lib.render_exp (re : lib.RawExp) : lib.ExprData :=
  match re with | lib.RawExp.Var id _ty => lib.ExprData.Atom id | lib.RawExp.Lit v _ty => lib.ExprData.Lit v | lib.RawExp.Clip target e => lib.coerce_if (lib.needs_nat_coercion (lib.type_of e.deref) target) (lib.render_exp e.deref) | lib.RawExp.BinOp op ty l r => let l2 := lib.coerce_if (lib.needs_nat_coercion (lib.type_of l.deref) ty) (lib.render_exp l.deref);
                                                                                                                                                                                                                                                                        let r2 := lib.coerce_if (lib.needs_nat_coercion (lib.type_of r.deref) ty) (lib.render_exp r.deref);
                                                                                                                                                                                                                                                                        lib.ExprData.BinOp op (Tactus.Box.mk l2) (Tactus.Box.mk r2) | lib.RawExp.Call fnid _ret arg argty => lib.ExprData.App fnid (Tactus.Box.mk (lib.coerce_if (lib.needs_nat_coercion (lib.type_of arg.deref) argty) (lib.render_exp arg.deref))) | lib.RawExp.Deref e => lib.ExprData.FieldProj (Tactus.Box.mk (lib.render_exp e.deref)) lib.deref_field | lib.RawExp.Span loc e => lib.ExprData.SpanMark loc (Tactus.Box.mk (lib.render_exp e.deref))
termination_by structural re
noncomputable def lib.ck_tag (k : lib.CastKind) : Nat :=
  match k with | lib.CastKind.IntToNat => 0 | lib.CastKind.NatToInt => 1
noncomputable def lib.castkind_eq (a : lib.CastKind) (b : lib.CastKind) : Nat :=
  if lib.ck_tag a = lib.ck_tag b then 1 else 0
noncomputable def lib.ed_tag (e : lib.ExprData) : Nat :=
  match e with | lib.ExprData.Atom _ => 0 | lib.ExprData.Lit _ => 1 | lib.ExprData.Cast _ _ => 2 | lib.ExprData.BinOp _ _ _ => 3 | lib.ExprData.App _ _ => 4 | lib.ExprData.FieldProj _ _ => 5 | lib.ExprData.SpanMark _ _ => 6
noncomputable def lib.ed_atom_id (e : lib.ExprData) : Int :=
  match e with | lib.ExprData.Atom x => x | _ => 0
noncomputable def lib.ed_lit_val (e : lib.ExprData) : Int :=
  match e with | lib.ExprData.Lit v => v | _ => 0
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
  match a with | lib.ExprData.Atom x => if lib.ed_tag b = 0 then if x = lib.ed_atom_id b then 1 else 0 else 0 | lib.ExprData.Lit v => if lib.ed_tag b = 1 then if v = lib.ed_lit_val b then 1 else 0 else 0 | lib.ExprData.Cast k t => if lib.ed_tag b = 2 then if lib.castkind_eq k (lib.ed_cast_k b) = 1 then lib.expr_eq t.deref (lib.ed_cast_e b) else 0 else 0 | lib.ExprData.BinOp op l r => if lib.ed_tag b = 3 then if op = lib.ed_binop_op b then if lib.expr_eq l.deref (lib.ed_binop_l b) = 1 then lib.expr_eq r.deref (lib.ed_binop_r b) else 0 else 0 else 0 | lib.ExprData.App f a2 => if lib.ed_tag b = 4 then if f = lib.ed_app_fn b then lib.expr_eq a2.deref (lib.ed_app_arg b) else 0 else 0 | lib.ExprData.FieldProj t fld => if lib.ed_tag b = 5 then if fld = lib.ed_fp_field b then lib.expr_eq t.deref (lib.ed_fp_e b) else 0 else 0 | lib.ExprData.SpanMark loc t => if lib.ed_tag b = 6 then if loc = lib.ed_span_loc b then lib.expr_eq t.deref (lib.ed_span_e b) else 0 else 0
termination_by structural a
theorem lib.expr_mirror_kernel_computes :
    lib.expr_eq (lib.render_exp (lib.RawExp.BinOp 0 lib.TypData.Bool (Tactus.Box.mk (lib.RawExp.Clip lib.TypData.Nat (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.Int)))) (Tactus.Box.mk (lib.RawExp.Call 10 lib.TypData.Nat (Tactus.Box.mk (lib.RawExp.Clip lib.TypData.Nat (Tactus.Box.mk (lib.RawExp.Var 2 lib.TypData.Int)))) lib.TypData.Nat)))) (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 1)))) (Tactus.Box.mk (lib.ExprData.App 10 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 2))))))) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.BinOp 0 lib.TypData.Bool (Tactus.Box.mk (lib.RawExp.Clip lib.TypData.Nat (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.Int)))) (Tactus.Box.mk (lib.RawExp.Call 10 lib.TypData.Nat (Tactus.Box.mk (lib.RawExp.Clip lib.TypData.Nat (Tactus.Box.mk (lib.RawExp.Var 2 lib.TypData.Int)))) lib.TypData.Nat)))) (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ExprData.App 10 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 2))))))) = 0 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.BinOp 1 lib.TypData.Nat (Tactus.Box.mk (lib.RawExp.Var 3 lib.TypData.Int)) (Tactus.Box.mk (lib.RawExp.Var 3 lib.TypData.Int)))) (lib.ExprData.BinOp 1 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))) (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3))))) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.BinOp 1 lib.TypData.Nat (Tactus.Box.mk (lib.RawExp.Var 3 lib.TypData.Int)) (Tactus.Box.mk (lib.RawExp.Var 3 lib.TypData.Int)))) (lib.ExprData.BinOp 1 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))) (Tactus.Box.mk (lib.ExprData.Atom 3))) = 0 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.Call 11 (lib.TypData.Named 100) (Tactus.Box.mk (lib.RawExp.Deref (Tactus.Box.mk (lib.RawExp.Var 4 (lib.TypData.Ref 100))))) (lib.TypData.Named 100))) (lib.ExprData.App 11 (Tactus.Box.mk (lib.ExprData.FieldProj (Tactus.Box.mk (lib.ExprData.Atom 4)) 0))) = 1 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.Call 11 (lib.TypData.Named 100) (Tactus.Box.mk (lib.RawExp.Deref (Tactus.Box.mk (lib.RawExp.Var 4 (lib.TypData.Ref 100))))) (lib.TypData.Named 100))) (lib.ExprData.App 11 (Tactus.Box.mk (lib.ExprData.Atom 4))) = 0 ∧ lib.expr_eq (lib.render_exp (lib.RawExp.BinOp 0 lib.TypData.Bool (Tactus.Box.mk (lib.RawExp.Var 3 lib.TypData.Int)) (Tactus.Box.mk (lib.RawExp.Clip lib.TypData.Nat (Tactus.Box.mk (lib.RawExp.Var 3 lib.TypData.Int)))))) (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.Atom 3)) (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3))))) = 1 ∧ lib.expr_eq (lib.ExprData.Lit 5) (lib.ExprData.Lit 5) = 1 ∧ lib.expr_eq (lib.ExprData.Lit 5) (lib.ExprData.Lit 6) = 0 ∧ lib.expr_size (lib.ExprData.BinOp 1 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))) (Tactus.Box.mk (lib.ExprData.Atom 3))) = 4 ∧ lib.typ_size (lib.TypData.Ref 7) = 1 := by
  decide 
