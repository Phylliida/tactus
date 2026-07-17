import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

namespace lib

/-- VERBATIM from the Link emission (TactusLink_lib_exec.lean). -/
def FrameListWf (x : lib.FrameList) : Prop :=
  match x with
  | lib.FrameList.FNil => True
  | lib.FrameList.FBind x0 x1 x2 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ (0 ≤ x1 ∧ x1 < 18446744073709551616) ∧ FrameListWf x2.deref
  | lib.FrameList.FHyp x0 x1 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ FrameListWf x1.deref
  | lib.FrameList.FLet x0 x1 x2 => (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ (0 ≤ x1 ∧ x1 < 18446744073709551616) ∧ FrameListWf x2.deref
termination_by structural x

/-- What the generator will emit for RetBind (RetLet carries two u64s). -/
def RetBindWf' (x : lib.RetBind) : Prop :=
  match x with
  | lib.RetBind.RetNone => True
  | lib.RetBind.RetLet x0 x1 =>
      (0 ≤ x0 ∧ x0 < 18446744073709551616) ∧ (0 ≤ x1 ∧ x1 < 18446744073709551616)

/-- THE ARCHETYPE: preservation through structural recursion + Box.deref.
    No equation lemmas exist (rec_1 gap) — everything rides on defeq iota. -/
theorem frame_append_wf (f g : lib.FrameList)
    (hf : FrameListWf f) (hg : FrameListWf g) :
    FrameListWf (lib.frame_append f g) :=
  match f, hf with
  | lib.FrameList.FNil, _ => hg
  | lib.FrameList.FBind id typ t, ⟨h1, h2, hr⟩ =>
      ⟨h1, h2, frame_append_wf t.deref g hr hg⟩
  | lib.FrameList.FHyp h t, ⟨h1, hr⟩ =>
      ⟨h1, frame_append_wf t.deref g hr hg⟩
  | lib.FrameList.FLet id v t, ⟨h1, h2, hr⟩ =>
      ⟨h1, h2, frame_append_wf t.deref g hr hg⟩
termination_by structural f

/-- Non-recursive composition: the actual wp_stm_sound demand site. -/
theorem ret_frame_wf (f : lib.FrameList) (rb : lib.RetBind)
    (hf : FrameListWf f) (hrb : RetBindWf' rb) :
    FrameListWf (lib.ret_frame f rb) :=
  match rb, hrb with
  | lib.RetBind.RetNone, _ => hf
  | lib.RetBind.RetLet name val, ⟨hn, hv⟩ =>
      frame_append_wf f _ hf ⟨hn, hv, trivial⟩

end lib

#print axioms lib.frame_append_wf
#print axioms lib.ret_frame_wf
