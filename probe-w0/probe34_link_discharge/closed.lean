import lib__u_gapp_nil
import lib__u_gapp_cons
import lib__u_holds_all_nil
import lib__u_holds_all_cons
import lib__u_close_e_nil
import lib__u_holds_leafe
import lib__u_cse_nil
import lib__holds_all_append
import lib__holds_close_e
set_option linter.unusedVariables false
set_option autoImplicit false

-- ══════════════════════════════════════════════════════════════════════
-- probe34 L0 (bootstrap-73, DESIGN-link-discharge.md §7):
-- hand-write the discharge terms the Link generator will emit, against the
-- CURRENT tactus-core emission. Demonstrator = holds_all_append (recursive,
-- entirely bound-free chain); exhibit = holds_close_e FNil arm (bound-free)
-- vs its other arms (blocked by the u64-bound gap — see REPORT.md F1).
-- Q3 (Danielle): `theorem` keyword throughout.
-- ══════════════════════════════════════════════════════════════════════

namespace Probe34

-- ── u_* clean forms: the pkg theorems ARE already premise-free (empty-body
--    lemmas have no weave); the closed form is a direct re-export. ──

theorem u_gapp_nil_closed : ∀ (b : lib.GoalList),
    lib.goals_append lib.GoalList.Nil b = b :=
  _tactus_postcondition_u_gapp_nil_at_lib_3413_13_1

theorem u_gapp_cons_closed : ∀ (g : Tactus.Box lib.GoalData) (t : Tactus.Box lib.GoalList) (b : lib.GoalList),
    lib.goals_append (lib.GoalList.Cons g t) b
      = lib.GoalList.Cons g (Tactus.Box.mk (lib.goals_append t.deref b)) :=
  _tactus_postcondition_u_gapp_cons_at_lib_3416_13_1

theorem u_holds_all_nil_closed : ∀ (hp : Int → (Int → Int) → Prop)
    (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int),
    ∀ (st : Int → Int), lib.holds_all hp he lv lib.GoalList.Nil st = True :=
  _tactus_postcondition_u_holds_all_nil_at_lib_3268_13_1

theorem u_holds_all_cons_closed : ∀ (hp : Int → (Int → Int) → Prop)
    (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int)
    (g : Tactus.Box lib.GoalData) (t : Tactus.Box lib.GoalList),
    ∀ (st : Int → Int), lib.holds_all hp he lv (lib.GoalList.Cons g t) st
      = (lib.holds hp he lv g.deref st ∧ lib.holds_all hp he lv t.deref st) :=
  _tactus_postcondition_u_holds_all_cons_at_lib_3272_13_1

-- ── THE FIX-SYNTHESIS DEMONSTRATOR: holds_all_append_closed ──
-- Recursive over GoalList (Box-wrapped tail ⇒ WF, not structural), clean
-- statement, per-arm dispatch to the emitted VC theorems, IH = the fix's own
-- recursive call, decrease facts = the emitted TERMINATION VC theorem
-- (consumed twice: as the woven height premise AND in decreasing_by).

theorem holds_all_append_closed
    (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop)
    (lv : Int → (Int → Int) → Int) (a b : lib.GoalList) (st : Int → Int) :
    lib.holds_all hp he lv (lib.goals_append a b) st
      = (lib.holds_all hp he lv a st ∧ lib.holds_all hp he lv b st) :=
  match a with
  | lib.GoalList.Nil =>
      _tactus_postcondition_holds_all_append_at_lib_3514_13_3 hp he lv lib.GoalList.Nil b st
        (by simp)                                     -- discriminator: isNil
        () (u_gapp_nil_closed b)
        () (u_holds_all_nil_closed hp he lv)
  | lib.GoalList.Cons g t =>
      have hdec := _tactus_termination_holds_all_append_at_lib_3527_13_7
        hp he lv (lib.GoalList.Cons g t) b st
        (by simp)                                     -- ¬isNil on Cons
        () (u_gapp_cons_closed g t b)
        () (u_holds_all_cons_closed hp he lv g t)
        () (u_holds_all_cons_closed hp he lv g (Tactus.Box.mk (lib.goals_append t.deref b)))
      _tactus_postcondition_holds_all_append_at_lib_3514_13_9 hp he lv (lib.GoalList.Cons g t) b st
        (by simp)                                     -- ¬isNil on Cons
        () (u_gapp_cons_closed g t b)
        () (u_holds_all_cons_closed hp he lv g t)
        () (u_holds_all_cons_closed hp he lv g (Tactus.Box.mk (lib.goals_append t.deref b)))
        hdec                                          -- woven height premise
        () (holds_all_append_closed hp he lv t.deref b st)   -- IH
termination_by lib.GoalList.height a
decreasing_by
  exact (_tactus_termination_holds_all_append_at_lib_3527_13_7
      hp he lv (lib.GoalList.Cons g t) b st
      (by simp) () (u_gapp_cons_closed g t b)
      () (u_holds_all_cons_closed hp he lv g t)
      () (u_holds_all_cons_closed hp he lv g (Tactus.Box.mk (lib.goals_append t.deref b)))
    ).resolve_right (fun h => h.2.elim)

-- ── THE BOUND-GAP EXHIBIT: holds_close_e's FNil arm discharges verbatim
--    (all its callees are scalar-free); the FBind/FHyp/FLet arms CANNOT be
--    discharged from their callees' theorems as emitted — the woven premise
--    is the bare fact at an extrinsically-typed Int projection, while the
--    callee theorem demands h_*_bound. See REPORT.md F1 + design §8. ──

theorem holds_close_e_fnil_arm_closed
    (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop)
    (lv : Int → (Int → Int) → Int) (o : lib.RawExp) :
    ∀ (st : Int → Int),
      lib.holds hp he lv (lib.close_e lib.FrameList.FNil o) st
        = lib.close_sem_e hp he lv lib.FrameList.FNil st o :=
  _tactus_postcondition_holds_close_e_at_lib_3477_13_4 hp he lv lib.FrameList.FNil o
    (by simp)                                         -- discriminator: isFNil
    () (_tactus_postcondition_u_close_e_nil_at_lib_3394_13_1 o)
    () (_tactus_postcondition_u_holds_leafe_at_lib_3264_13_1 hp he lv (lib.render_exp o))
    () (_tactus_postcondition_u_cse_nil_at_lib_3286_13_1 hp he lv o)

-- ── consumption smoke: a downstream file uses the clean theorem by `exact`
--    (the bootstrap-66 spine shape) ──
example (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop)
    (lv : Int → (Int → Int) → Int) (b : lib.GoalList) (st : Int → Int)
    (h : lib.holds_all hp he lv b st) :
    lib.holds_all hp he lv (lib.goals_append lib.GoalList.Nil b) st := by
  rw [holds_all_append_closed]
  exact ⟨(u_holds_all_nil_closed hp he lv st).symm ▸ trivial, h⟩

end Probe34

#print axioms Probe34.holds_all_append_closed
#print axioms Probe34.holds_close_e_fnil_arm_closed
