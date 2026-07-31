import TactusStmts_lib_exec__lib__wp_sound_bites_assert
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_wp_sound_bites_assert_at_lib_6473_13_4 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (o : lib.RawExp) (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616) (st : Int → Int) (h_req0 : lib.holds_all hp he lv (lib.wp_stm lib.FrameList.FNil (lib.StmData.Assert o 0 h 0)) st) :
    let tmp__1 := lib.FrameList.FNil;
    let tmp__2 := lib.StmData.Assert o 0 h 0;
    ∀ (_tactus_ret_1 : Unit), lib.holds_all hp he lv (lib.wp_stm tmp__1 tmp__2) st = lib.exec_safe_f hp he lv tmp__1 tmp__2 st → (let tmp__3 := lib.FrameList.FNil;
                                                                                                                                  ∀ (_tactus_ret_2 : Unit), (∀ (st : Int → Int), lib.exec_safe_f hp he lv tmp__3 (lib.StmData.Assert o 0 h 0) st = lib.close_sem_e hp he lv tmp__3 st o) → (∀ (_tactus_ret_3 : Unit), (∀ (st : Int → Int), lib.close_sem_e hp he lv lib.FrameList.FNil st o = (Tactus.Ref.mk he).deref (lib.render_exp o) st) → /- @rust:tactus-core/lib.rs:6473:13 -/ he (lib.render_exp o) st)) := by
  first | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])
