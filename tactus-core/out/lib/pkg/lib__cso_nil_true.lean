import TactusStmts_lib_exec__lib__cso_nil_true
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_cso_nil_true_at_lib_3542_13_3 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    /- @rust:lib.rs:3546:9 -/ tmp___0.isFNil → (let tmp__1 := lib.RawExpList.Nil;
                                                ∀ (_tactus_ret_1 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv lib.FrameList.FNil st tmp__1 = lib.obligs_safe he tmp__1 st) → (∀ (_tactus_ret_2 : Unit), (∀ (st : Int → Int), lib.obligs_safe he lib.RawExpList.Nil st = True) → (/- @rust:lib.rs:3542:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st lib.RawExpList.Nil = True))) := by
  first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))
theorem _tactus_termination_cso_nil_true_at_lib_3552_13_5 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:lib.rs:3546:9 -/ tmp___0.isFNil → /- @rust:lib.rs:3550:9 -/ tmp___0.isFBind → (let x := tmp___0.FBind_val0;
                                                                                             let ty := tmp___0.FBind_val1;
                                                                                             let t := tmp___0.FBind_val2;
                                                                                             let tmp__2 := lib.RawExpList.Nil;
                                                                                             ∀ (_tactus_ret_4 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv (lib.FrameList.FBind x ty t) st tmp__2 = (∀ (n : Int), lib.close_sem_obligs hp he lv t.deref (lib.upd st x n) tmp__2)) → /- @rust:lib.rs:3552:13 -/ lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False) := by
  first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))
theorem _tactus_postcondition_cso_nil_true_at_lib_3542_13_7 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:lib.rs:3546:9 -/ tmp___0.isFNil → /- @rust:lib.rs:3550:9 -/ tmp___0.isFBind → (let x := tmp___0.FBind_val0;
                                                                                             let ty := tmp___0.FBind_val1;
                                                                                             let t := tmp___0.FBind_val2;
                                                                                             let tmp__2 := lib.RawExpList.Nil;
                                                                                             ∀ (_tactus_ret_4 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv (lib.FrameList.FBind x ty t) st tmp__2 = (∀ (n : Int), lib.close_sem_obligs hp he lv t.deref (lib.upd st x n) tmp__2)) → lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False → (∀ (_tactus_ret_6 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv t.deref st lib.RawExpList.Nil = True) → (/- @rust:lib.rs:3542:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st lib.RawExpList.Nil = True))) := by
  first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))
theorem _tactus_termination_cso_nil_true_at_lib_3556_13_9 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:lib.rs:3546:9 -/ tmp___0.isFNil → ¬/- @rust:lib.rs:3550:9 -/ tmp___0.isFBind → /- @rust:lib.rs:3554:9 -/ tmp___0.isFHyp → (let h := tmp___0.FHyp_val0;
                                                                                                                                         let t := tmp___0.FHyp_val1;
                                                                                                                                         let tmp__3 := lib.RawExpList.Nil;
                                                                                                                                         ∀ (_tactus_ret_8 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv (lib.FrameList.FHyp h t) st tmp__3 = ((Tactus.Ref.mk hp).deref h st → lib.close_sem_obligs hp he lv t.deref st tmp__3)) → /- @rust:lib.rs:3556:13 -/ lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False) := by
  first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))
theorem _tactus_postcondition_cso_nil_true_at_lib_3542_13_11 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:lib.rs:3546:9 -/ tmp___0.isFNil → ¬/- @rust:lib.rs:3550:9 -/ tmp___0.isFBind → /- @rust:lib.rs:3554:9 -/ tmp___0.isFHyp → (let h := tmp___0.FHyp_val0;
                                                                                                                                         let t := tmp___0.FHyp_val1;
                                                                                                                                         let tmp__3 := lib.RawExpList.Nil;
                                                                                                                                         ∀ (_tactus_ret_8 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv (lib.FrameList.FHyp h t) st tmp__3 = ((Tactus.Ref.mk hp).deref h st → lib.close_sem_obligs hp he lv t.deref st tmp__3)) → lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False → (∀ (_tactus_ret_10 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv t.deref st lib.RawExpList.Nil = True) → (/- @rust:lib.rs:3542:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st lib.RawExpList.Nil = True))) := by
  first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))
theorem _tactus_termination_cso_nil_true_at_lib_3560_13_13 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:lib.rs:3546:9 -/ tmp___0.isFNil → ¬/- @rust:lib.rs:3550:9 -/ tmp___0.isFBind → ¬/- @rust:lib.rs:3554:9 -/ tmp___0.isFHyp → (let x := tmp___0.FLet_val0;
                                                                                                                                          let v := tmp___0.FLet_val1;
                                                                                                                                          let t := tmp___0.FLet_val2;
                                                                                                                                          let tmp__4 := lib.RawExpList.Nil;
                                                                                                                                          ∀ (_tactus_ret_12 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv (lib.FrameList.FLet x v t) st tmp__4 = lib.close_sem_obligs hp he lv t.deref (lib.upd st x ((Tactus.Ref.mk lv).deref v st)) tmp__4) → /- @rust:lib.rs:3560:13 -/ lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False) := by
  first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))
theorem _tactus_postcondition_cso_nil_true_at_lib_3542_13_15 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:lib.rs:3546:9 -/ tmp___0.isFNil → ¬/- @rust:lib.rs:3550:9 -/ tmp___0.isFBind → ¬/- @rust:lib.rs:3554:9 -/ tmp___0.isFHyp → (let x := tmp___0.FLet_val0;
                                                                                                                                          let v := tmp___0.FLet_val1;
                                                                                                                                          let t := tmp___0.FLet_val2;
                                                                                                                                          let tmp__4 := lib.RawExpList.Nil;
                                                                                                                                          ∀ (_tactus_ret_12 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv (lib.FrameList.FLet x v t) st tmp__4 = lib.close_sem_obligs hp he lv t.deref (lib.upd st x ((Tactus.Ref.mk lv).deref v st)) tmp__4) → lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False → (∀ (_tactus_ret_14 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv t.deref st lib.RawExpList.Nil = True) → (/- @rust:lib.rs:3542:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st lib.RawExpList.Nil = True))) := by
  first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))
