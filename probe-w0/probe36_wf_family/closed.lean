import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

namespace lib

-- ── wf defs (generator-shaped) ──────────────────────────────────────
def B : Int := 18446744073709551616

def FrameListWf (x : lib.FrameList) : Prop :=
  match x with
  | lib.FrameList.FNil => True
  | lib.FrameList.FBind x0 x1 x2 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ (0 ≤ x1 ∧ x1 < 18446744073709551616) ∧ FrameListWf x2.deref
  | lib.FrameList.FHyp x0 x1 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ FrameListWf x1.deref
  | lib.FrameList.FLet x0 x1 x2 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ (0 ≤ x1 ∧ x1 < 18446744073709551616) ∧ FrameListWf x2.deref
termination_by structural x

def BinderListWf (x : lib.BinderList) : Prop :=
  match x with
  | lib.BinderList.Nil => True
  | lib.BinderList.Cons x0 x1 x2 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ (0 ≤ x1 ∧ x1 < 18446744073709551616) ∧ BinderListWf x2.deref
termination_by structural x

def ParamBoundListWf (x : lib.ParamBoundList) : Prop :=
  match x with
  | lib.ParamBoundList.Nil => True
  | lib.ParamBoundList.NoBound x0 => ParamBoundListWf x0.deref
  | lib.ParamBoundList.Bound x0 x1 x2 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ (0 ≤ x1 ∧ x1 < 18446744073709551616) ∧ ParamBoundListWf x2.deref
termination_by structural x

-- ── SHAPE 1: mutual wf defs over the mutual inductive family ────────
def TypDataWf' (x : lib.TypData) : Prop :=
  match x with
  | lib.TypData.TyInt => True
  | lib.TypData.TyNat => True
  | lib.TypData.TyBool => True
  | lib.TypData.TyNamed x0 => (0 ≤ x0 ∧ x0 < 18446744073709551616)
  | lib.TypData.TyRef x0 => (0 ≤ x0 ∧ x0 < 18446744073709551616)
  | lib.TypData.TyBox x0 => (0 ≤ x0 ∧ x0 < 18446744073709551616)

def BinderIdListWf' (x : lib.BinderIdList) : Prop :=
  match x with
  | lib.BinderIdList.Nil => True
  | lib.BinderIdList.Cons x0 x1 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ BinderIdListWf' x1.deref
termination_by structural x

mutual
def RawExpWf (x : lib.RawExp) : Prop :=
  match x with
  | lib.RawExp.Var x0 x1 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ TypDataWf' x1
  | lib.RawExp.Lit x0 x1 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ TypDataWf' x1
  | lib.RawExp.LitBool _ => True
  | lib.RawExp.Clip x0 x1 => TypDataWf' x0 ∧ RawExpWf x1.deref
  | lib.RawExp.BinOp x0 x1 x2 x3 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ TypDataWf' x1 ∧ RawExpWf x2.deref ∧ RawExpWf x3.deref
  | lib.RawExp.Call x0 x1 x2 x3 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ TypDataWf' x1 ∧ RawExpWf x2.deref ∧ TypDataWf' x3
  | lib.RawExp.Field x0 x1 x2 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ TypDataWf' x1 ∧ RawExpWf x2.deref
  | lib.RawExp.HasType x0 x1 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ RawExpWf x1.deref
  | lib.RawExp.Deref x0 => RawExpWf x0.deref
  | lib.RawExp.Let x0 x1 x2 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ RawExpWf x1.deref ∧ RawExpWf x2.deref
  | lib.RawExp.Not x0 => RawExpWf x0.deref
  | lib.RawExp.Span x0 x1 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ RawExpWf x1.deref
  | lib.RawExp.Ite x0 x1 x2 x3 => TypDataWf' x0 ∧ RawExpWf x1.deref ∧ RawExpWf x2.deref ∧ RawExpWf x3.deref
  | lib.RawExp.MatchR x0 x1 x2 => RawExpWf x0.deref ∧ RawArmListWf x1.deref ∧ TypDataWf' x2
  | lib.RawExp.CallN x0 x1 x2 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ TypDataWf' x1 ∧ RawListWf x2.deref
  | lib.RawExp.ForallR x0 x1 x2 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ TypDataWf' x1 ∧ RawExpWf x2.deref
  | lib.RawExp.ExistsR x0 x1 x2 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ TypDataWf' x1 ∧ RawExpWf x2.deref
termination_by structural x

def RawArmListWf (x : lib.RawArmList) : Prop :=
  match x with
  | lib.RawArmList.Nil => True
  | lib.RawArmList.Cons x0 x1 x2 x3 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ BinderIdListWf' x1 ∧ RawExpWf x2.deref ∧ RawArmListWf x3.deref
termination_by structural x

def RawListWf (x : lib.RawList) : Prop :=
  match x with
  | lib.RawList.Nil => True
  | lib.RawList.Cons x0 x1 => RawExpWf x0.deref ∧ RawListWf x1.deref
termination_by structural x
end

-- ── SHAPE 2: if inside a match arm (havoc_lets) ─────────────────────
theorem havoc_lets_wf (f : lib.FrameList) (mods : lib.BinderList)
    (hf : FrameListWf f) : FrameListWf (lib.havoc_lets f mods) :=
  match f, hf with
  | lib.FrameList.FNil, _ => trivial
  | lib.FrameList.FBind id typ t, ⟨h1, h2, hr⟩ => ⟨h1, h2, havoc_lets_wf t.deref mods hr⟩
  | lib.FrameList.FHyp h t, ⟨h1, hr⟩ => ⟨h1, havoc_lets_wf t.deref mods hr⟩
  | lib.FrameList.FLet id v t, ⟨h1, h2, hr⟩ =>
      if h : lib.binder_has_id mods id = 1 then
        (congrArg FrameListWf (if_pos h)).mpr (havoc_lets_wf t.deref mods hr)
      else
        (congrArg FrameListWf (if_neg h)).mpr ⟨h1, h2, havoc_lets_wf t.deref mods hr⟩
termination_by structural f

-- ── SHAPE 3: nested match on a second wf scrutinee (seed_params) ────
theorem seed_params_wf (params : lib.BinderList) (bounds : lib.ParamBoundList)
    (hp : BinderListWf params) (hb : ParamBoundListWf bounds) :
    FrameListWf (lib.seed_params params bounds) :=
  match params, hp with
  | lib.BinderList.Nil, _ => trivial
  | lib.BinderList.Cons id typ t, ⟨h1, h2, hr⟩ =>
      match bounds, hb with
      | lib.ParamBoundList.Bound hname prop bt, ⟨b1, b2, br⟩ =>
          ⟨h1, h2, b1, b2, seed_params_wf t.deref bt.deref hr br⟩
      | lib.ParamBoundList.NoBound bt, br =>
          ⟨h1, h2, seed_params_wf t.deref bt.deref hr br⟩
      | lib.ParamBoundList.Nil, _ =>
          ⟨h1, h2, seed_params_wf t.deref lib.ParamBoundList.Nil hr trivial⟩
termination_by structural params

-- ── remaining family members (plain archetype) ──────────────────────
theorem frame_append_wf (f g : lib.FrameList)
    (hf : FrameListWf f) (hg : FrameListWf g) :
    FrameListWf (lib.frame_append f g) :=
  match f, hf with
  | lib.FrameList.FNil, _ => hg
  | lib.FrameList.FBind id typ t, ⟨h1, h2, hr⟩ => ⟨h1, h2, frame_append_wf t.deref g hr hg⟩
  | lib.FrameList.FHyp h t, ⟨h1, hr⟩ => ⟨h1, frame_append_wf t.deref g hr hg⟩
  | lib.FrameList.FLet id v t, ⟨h1, h2, hr⟩ => ⟨h1, h2, frame_append_wf t.deref g hr hg⟩
termination_by structural f

theorem binders_to_frame_wf (b : lib.BinderList) (hb : BinderListWf b) :
    FrameListWf (lib.binders_to_frame b) :=
  match b, hb with
  | lib.BinderList.Nil, _ => trivial
  | lib.BinderList.Cons id typ t, ⟨h1, h2, hr⟩ => ⟨h1, h2, binders_to_frame_wf t.deref hr⟩
termination_by structural b

theorem binderprops_to_hyps_wf (b : lib.BinderList) (hb : BinderListWf b) :
    FrameListWf (lib.binderprops_to_hyps b) :=
  match b, hb with
  | lib.BinderList.Nil, _ => trivial
  | lib.BinderList.Cons _name prop t, ⟨h1, h2, hr⟩ => ⟨h2, binderprops_to_hyps_wf t.deref hr⟩
termination_by structural b

theorem seed_binders_hyp_bounds_wf (binders : lib.BinderList) (bounds : lib.ParamBoundList)
    (hp : BinderListWf binders) (hb : ParamBoundListWf bounds) :
    FrameListWf (lib.seed_binders_hyp_bounds binders bounds) :=
  match binders, hp with
  | lib.BinderList.Nil, _ => trivial
  | lib.BinderList.Cons id typ t, ⟨h1, h2, hr⟩ =>
      match bounds, hb with
      | lib.ParamBoundList.Bound _hname prop bt, ⟨b1, b2, br⟩ =>
          ⟨h1, h2, b2, seed_binders_hyp_bounds_wf t.deref bt.deref hr br⟩
      | lib.ParamBoundList.NoBound bt, br =>
          ⟨h1, h2, seed_binders_hyp_bounds_wf t.deref bt.deref hr br⟩
      | lib.ParamBoundList.Nil, _ =>
          ⟨h1, h2, seed_binders_hyp_bounds_wf t.deref lib.ParamBoundList.Nil hr trivial⟩
termination_by structural binders

-- ── SHAPE 4: lets + top-level if + composition (loop_maintain_frame) ─
theorem loop_maintain_frame_wf (f : lib.FrameList) (inv_hyps : lib.BinderList)
    (binders : lib.BinderList) (binder_bounds : lib.ParamBoundList)
    (cond_name cond_ann d_old_name d_old_val : Int)
    (hf : FrameListWf f) (hi : BinderListWf inv_hyps) (hbi : BinderListWf binders)
    (hbb : ParamBoundListWf binder_bounds)
    (h_cond_name_bound : 0 ≤ cond_name ∧ cond_name < 18446744073709551616)
    (h_cond_ann_bound : 0 ≤ cond_ann ∧ cond_ann < 18446744073709551616)
    (h_d_old_name_bound : 0 ≤ d_old_name ∧ d_old_name < 18446744073709551616)
    (h_d_old_val_bound : 0 ≤ d_old_val ∧ d_old_val < 18446744073709551616) :
    FrameListWf (lib.loop_maintain_frame f inv_hyps binders binder_bounds cond_name cond_ann d_old_name d_old_val) := by
  unfold lib.loop_maintain_frame
  have hwf_hv : FrameListWf (lib.havoc_lets f binders) := havoc_lets_wf f binders hf
  have hwf_d_old : FrameListWf (lib.FrameList.FLet d_old_name d_old_val (Tactus.Box.mk lib.FrameList.FNil)) :=
    ⟨h_d_old_name_bound, h_d_old_val_bound, trivial⟩
  by_cases h : lib.has_let (lib.havoc_lets f binders) = 0
  · rw [if_pos h]
    exact frame_append_wf _ _ hwf_hv (frame_append_wf _ _ (seed_params_wf binders binder_bounds hbi hbb)
      (frame_append_wf _ _ (binders_to_frame_wf inv_hyps hi)
        (frame_append_wf _ _ ⟨h_cond_name_bound, h_cond_ann_bound, trivial⟩ hwf_d_old)))
  · rw [if_neg h]
    exact frame_append_wf _ _ hwf_hv (frame_append_wf _ _ (seed_binders_hyp_bounds_wf binders binder_bounds hbi hbb)
      (frame_append_wf _ _ (binderprops_to_hyps_wf inv_hyps hi)
        (frame_append_wf _ _ ⟨h_cond_ann_bound, trivial⟩ hwf_d_old)))

end lib

#print axioms lib.havoc_lets_wf
#print axioms lib.seed_params_wf
#print axioms lib.loop_maintain_frame_wf
#print axioms lib.RawExpWf
