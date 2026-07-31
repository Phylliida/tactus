import TactusStmts_lib_exec__lib__holds_all_append
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_holds_all_append_at_lib_5419_13_3 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (a : lib.GoalList) (b : lib.GoalList) (st : Int → Int) :
    let decrease_init0 := a;
    let tmp___0 := a;
    /- @rust:tactus-core/lib.rs:5424:9 -/ tmp___0.isNil → (∀ (_tactus_ret_1 : Unit), lib.goals_append lib.GoalList.Nil b = b → (∀ (_tactus_ret_2 : Unit), (∀ (st : Int → Int), lib.holds_all hp he lv lib.GoalList.Nil st = True) → /- @rust:tactus-core/lib.rs:5419:13 -/ lib.holds_all hp he lv (lib.goals_append a b) st = (lib.holds_all hp he lv a st ∧ lib.holds_all hp he lv b st))) := by
  first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))
-- tactus-closer: user
theorem _tactus_termination_holds_all_append_at_lib_5432_13_7 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (a : lib.GoalList) (b : lib.GoalList) (st : Int → Int) :
    let decrease_init0 := a;
    let tmp___0 := a;
    ¬/- @rust:tactus-core/lib.rs:5424:9 -/ tmp___0.isNil → (let g := tmp___0.Cons_val0;
                                                            let t := tmp___0.Cons_val1;
                                                            ∀ (_tactus_ret_4 : Unit), lib.goals_append (lib.GoalList.Cons g t) b = lib.GoalList.Cons g (Tactus.Box.mk (lib.goals_append t.deref b)) → (∀ (_tactus_ret_5 : Unit), (∀ (st : Int → Int), lib.holds_all hp he lv (lib.GoalList.Cons g t) st = (lib.holds hp he lv g.deref st ∧ lib.holds_all hp he lv t.deref st)) → (let tmp__1 := lib.goals_append t.deref b;
                                                                                                                                                                                                                                                                                                                                                                                  ∀ (_tactus_ret_6 : Unit), (∀ (st : Int → Int), lib.holds_all hp he lv (lib.GoalList.Cons g (Tactus.Box.mk tmp__1)) st = (lib.holds hp he lv g.deref st ∧ lib.holds_all hp he lv tmp__1 st)) → /- @rust:tactus-core/lib.rs:5432:13 -/ lib.GoalList.height t.deref < lib.GoalList.height decrease_init0 ∨ lib.GoalList.height t.deref = lib.GoalList.height decrease_init0 ∧ False))) := by
  first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))
-- tactus-closer: user
theorem _tactus_postcondition_holds_all_append_at_lib_5419_13_9 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (a : lib.GoalList) (b : lib.GoalList) (st : Int → Int) :
    let decrease_init0 := a;
    let tmp___0 := a;
    ¬/- @rust:tactus-core/lib.rs:5424:9 -/ tmp___0.isNil → (let g := tmp___0.Cons_val0;
                                                            let t := tmp___0.Cons_val1;
                                                            ∀ (_tactus_ret_4 : Unit), lib.goals_append (lib.GoalList.Cons g t) b = lib.GoalList.Cons g (Tactus.Box.mk (lib.goals_append t.deref b)) → (∀ (_tactus_ret_5 : Unit), (∀ (st : Int → Int), lib.holds_all hp he lv (lib.GoalList.Cons g t) st = (lib.holds hp he lv g.deref st ∧ lib.holds_all hp he lv t.deref st)) → (let tmp__1 := lib.goals_append t.deref b;
                                                                                                                                                                                                                                                                                                                                                                                  ∀ (_tactus_ret_6 : Unit), (∀ (st : Int → Int), lib.holds_all hp he lv (lib.GoalList.Cons g (Tactus.Box.mk tmp__1)) st = (lib.holds hp he lv g.deref st ∧ lib.holds_all hp he lv tmp__1 st)) → lib.GoalList.height t.deref < lib.GoalList.height decrease_init0 ∨ lib.GoalList.height t.deref = lib.GoalList.height decrease_init0 ∧ False → (∀ (_tactus_ret_8 : Unit), lib.holds_all hp he lv (lib.goals_append t.deref b) st = (lib.holds_all hp he lv t.deref st ∧ lib.holds_all hp he lv b st) → /- @rust:tactus-core/lib.rs:5419:13 -/ lib.holds_all hp he lv (lib.goals_append a b) st = (lib.holds_all hp he lv a st ∧ lib.holds_all hp he lv b st))))) := by
  first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))
