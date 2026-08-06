import TactusStmts_lib_exec__lib__frame_append_fnil_right
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_frame_append_fnil_right_at_lib_6450_13_2 (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    /- @rust:tactus-core/lib.rs:6454:9 -/ tmp___0.isFNil → (let tmp__1 := lib.FrameList.FNil;
                                                            ∀ (_tactus_ret_1 : Unit), lib.frame_append lib.FrameList.FNil tmp__1 = tmp__1 → /- @rust:tactus-core/lib.rs:6450:13 -/ lib.frame_append f lib.FrameList.FNil = f) := by
  first | (intros <;> cases f <;> omega) | (intros <;> cases f <;> with_reducible rfl) | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])
-- tactus-closer: user
theorem _tactus_termination_frame_append_fnil_right_at_lib_6459_13_4 (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:tactus-core/lib.rs:6454:9 -/ tmp___0.isFNil → /- @rust:tactus-core/lib.rs:6457:9 -/ tmp___0.isFBind → (let id := tmp___0.FBind_val0;
                                                                                                                     let typ := tmp___0.FBind_val1;
                                                                                                                     let t := tmp___0.FBind_val2;
                                                                                                                     let tmp__2 := lib.FrameList.FNil;
                                                                                                                     ∀ (_tactus_ret_3 : Unit), lib.frame_append (lib.FrameList.FBind id typ t) tmp__2 = lib.FrameList.FBind id typ (Tactus.Box.mk (lib.frame_append t.deref tmp__2)) → /- @rust:tactus-core/lib.rs:6459:13 -/ lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False) := by
  first | (intros <;> cases f <;> omega) | (intros <;> cases f <;> with_reducible rfl) | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])
-- tactus-closer: user
theorem _tactus_postcondition_frame_append_fnil_right_at_lib_6450_13_6 (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:tactus-core/lib.rs:6454:9 -/ tmp___0.isFNil → /- @rust:tactus-core/lib.rs:6457:9 -/ tmp___0.isFBind → (let id := tmp___0.FBind_val0;
                                                                                                                     let typ := tmp___0.FBind_val1;
                                                                                                                     let t := tmp___0.FBind_val2;
                                                                                                                     let tmp__2 := lib.FrameList.FNil;
                                                                                                                     ∀ (_tactus_ret_3 : Unit), lib.frame_append (lib.FrameList.FBind id typ t) tmp__2 = lib.FrameList.FBind id typ (Tactus.Box.mk (lib.frame_append t.deref tmp__2)) → lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False → (∀ (_tactus_ret_5 : Unit), lib.frame_append t.deref lib.FrameList.FNil = t.deref → /- @rust:tactus-core/lib.rs:6450:13 -/ lib.frame_append f lib.FrameList.FNil = f)) := by
  first | (intros <;> cases f <;> omega) | (intros <;> cases f <;> with_reducible rfl) | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])
-- tactus-closer: user
theorem _tactus_termination_frame_append_fnil_right_at_lib_6463_13_8 (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:tactus-core/lib.rs:6454:9 -/ tmp___0.isFNil → ¬/- @rust:tactus-core/lib.rs:6457:9 -/ tmp___0.isFBind → /- @rust:tactus-core/lib.rs:6461:9 -/ tmp___0.isFHyp → (let hn := tmp___0.FHyp_val0;
                                                                                                                                                                             let h := tmp___0.FHyp_val1;
                                                                                                                                                                             let t := tmp___0.FHyp_val2;
                                                                                                                                                                             let tmp__3 := lib.FrameList.FNil;
                                                                                                                                                                             ∀ (_tactus_ret_7 : Unit), lib.frame_append (lib.FrameList.FHyp hn h t) tmp__3 = lib.FrameList.FHyp hn h (Tactus.Box.mk (lib.frame_append t.deref tmp__3)) → /- @rust:tactus-core/lib.rs:6463:13 -/ lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False) := by
  first | (intros <;> cases f <;> omega) | (intros <;> cases f <;> with_reducible rfl) | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])
-- tactus-closer: user
theorem _tactus_postcondition_frame_append_fnil_right_at_lib_6450_13_10 (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:tactus-core/lib.rs:6454:9 -/ tmp___0.isFNil → ¬/- @rust:tactus-core/lib.rs:6457:9 -/ tmp___0.isFBind → /- @rust:tactus-core/lib.rs:6461:9 -/ tmp___0.isFHyp → (let hn := tmp___0.FHyp_val0;
                                                                                                                                                                             let h := tmp___0.FHyp_val1;
                                                                                                                                                                             let t := tmp___0.FHyp_val2;
                                                                                                                                                                             let tmp__3 := lib.FrameList.FNil;
                                                                                                                                                                             ∀ (_tactus_ret_7 : Unit), lib.frame_append (lib.FrameList.FHyp hn h t) tmp__3 = lib.FrameList.FHyp hn h (Tactus.Box.mk (lib.frame_append t.deref tmp__3)) → lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False → (∀ (_tactus_ret_9 : Unit), lib.frame_append t.deref lib.FrameList.FNil = t.deref → /- @rust:tactus-core/lib.rs:6450:13 -/ lib.frame_append f lib.FrameList.FNil = f)) := by
  first | (intros <;> cases f <;> omega) | (intros <;> cases f <;> with_reducible rfl) | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])
-- tactus-closer: user
theorem _tactus_termination_frame_append_fnil_right_at_lib_6467_13_12 (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:tactus-core/lib.rs:6454:9 -/ tmp___0.isFNil → ¬/- @rust:tactus-core/lib.rs:6457:9 -/ tmp___0.isFBind → ¬/- @rust:tactus-core/lib.rs:6461:9 -/ tmp___0.isFHyp → /- @rust:tactus-core/lib.rs:6465:9 -/ tmp___0.isFLetH → (let x := tmp___0.FLetH_val0;
                                                                                                                                                                                                                                      let ty := tmp___0.FLetH_val1;
                                                                                                                                                                                                                                      let v := tmp___0.FLetH_val2;
                                                                                                                                                                                                                                      let en := tmp___0.FLetH_val3;
                                                                                                                                                                                                                                      let ep := tmp___0.FLetH_val4;
                                                                                                                                                                                                                                      let t := tmp___0.FLetH_val5;
                                                                                                                                                                                                                                      let tmp__4 := lib.FrameList.FNil;
                                                                                                                                                                                                                                      ∀ (_tactus_ret_11 : Unit), lib.frame_append (lib.FrameList.FLetH x ty v en ep t) tmp__4 = lib.FrameList.FLetH x ty v en ep (Tactus.Box.mk (lib.frame_append t.deref tmp__4)) → /- @rust:tactus-core/lib.rs:6467:13 -/ lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False) := by
  first | (intros <;> cases f <;> omega) | (intros <;> cases f <;> with_reducible rfl) | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])
-- tactus-closer: user
theorem _tactus_postcondition_frame_append_fnil_right_at_lib_6450_13_14 (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:tactus-core/lib.rs:6454:9 -/ tmp___0.isFNil → ¬/- @rust:tactus-core/lib.rs:6457:9 -/ tmp___0.isFBind → ¬/- @rust:tactus-core/lib.rs:6461:9 -/ tmp___0.isFHyp → /- @rust:tactus-core/lib.rs:6465:9 -/ tmp___0.isFLetH → (let x := tmp___0.FLetH_val0;
                                                                                                                                                                                                                                      let ty := tmp___0.FLetH_val1;
                                                                                                                                                                                                                                      let v := tmp___0.FLetH_val2;
                                                                                                                                                                                                                                      let en := tmp___0.FLetH_val3;
                                                                                                                                                                                                                                      let ep := tmp___0.FLetH_val4;
                                                                                                                                                                                                                                      let t := tmp___0.FLetH_val5;
                                                                                                                                                                                                                                      let tmp__4 := lib.FrameList.FNil;
                                                                                                                                                                                                                                      ∀ (_tactus_ret_11 : Unit), lib.frame_append (lib.FrameList.FLetH x ty v en ep t) tmp__4 = lib.FrameList.FLetH x ty v en ep (Tactus.Box.mk (lib.frame_append t.deref tmp__4)) → lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False → (∀ (_tactus_ret_13 : Unit), lib.frame_append t.deref lib.FrameList.FNil = t.deref → /- @rust:tactus-core/lib.rs:6450:13 -/ lib.frame_append f lib.FrameList.FNil = f)) := by
  first | (intros <;> cases f <;> omega) | (intros <;> cases f <;> with_reducible rfl) | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])
-- tactus-closer: user
theorem _tactus_termination_frame_append_fnil_right_at_lib_6471_13_16 (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:tactus-core/lib.rs:6454:9 -/ tmp___0.isFNil → ¬/- @rust:tactus-core/lib.rs:6457:9 -/ tmp___0.isFBind → ¬/- @rust:tactus-core/lib.rs:6461:9 -/ tmp___0.isFHyp → ¬/- @rust:tactus-core/lib.rs:6465:9 -/ tmp___0.isFLetH → /- @rust:tactus-core/lib.rs:6469:9 -/ tmp___0.isFLet → (let id := tmp___0.FLet_val0;
                                                                                                                                                                                                                                                                                              let v := tmp___0.FLet_val1;
                                                                                                                                                                                                                                                                                              let t := tmp___0.FLet_val2;
                                                                                                                                                                                                                                                                                              let tmp__5 := lib.FrameList.FNil;
                                                                                                                                                                                                                                                                                              ∀ (_tactus_ret_15 : Unit), lib.frame_append (lib.FrameList.FLet id v t) tmp__5 = lib.FrameList.FLet id v (Tactus.Box.mk (lib.frame_append t.deref tmp__5)) → /- @rust:tactus-core/lib.rs:6471:13 -/ lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False) := by
  first | (intros <;> cases f <;> omega) | (intros <;> cases f <;> with_reducible rfl) | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])
-- tactus-closer: user
theorem _tactus_postcondition_frame_append_fnil_right_at_lib_6450_13_18 (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:tactus-core/lib.rs:6454:9 -/ tmp___0.isFNil → ¬/- @rust:tactus-core/lib.rs:6457:9 -/ tmp___0.isFBind → ¬/- @rust:tactus-core/lib.rs:6461:9 -/ tmp___0.isFHyp → ¬/- @rust:tactus-core/lib.rs:6465:9 -/ tmp___0.isFLetH → /- @rust:tactus-core/lib.rs:6469:9 -/ tmp___0.isFLet → (let id := tmp___0.FLet_val0;
                                                                                                                                                                                                                                                                                              let v := tmp___0.FLet_val1;
                                                                                                                                                                                                                                                                                              let t := tmp___0.FLet_val2;
                                                                                                                                                                                                                                                                                              let tmp__5 := lib.FrameList.FNil;
                                                                                                                                                                                                                                                                                              ∀ (_tactus_ret_15 : Unit), lib.frame_append (lib.FrameList.FLet id v t) tmp__5 = lib.FrameList.FLet id v (Tactus.Box.mk (lib.frame_append t.deref tmp__5)) → lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False → (∀ (_tactus_ret_17 : Unit), lib.frame_append t.deref lib.FrameList.FNil = t.deref → /- @rust:tactus-core/lib.rs:6450:13 -/ lib.frame_append f lib.FrameList.FNil = f)) := by
  first | (intros <;> cases f <;> omega) | (intros <;> cases f <;> with_reducible rfl) | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])
-- tactus-closer: user
theorem _tactus_termination_frame_append_fnil_right_at_lib_6475_13_20 (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:tactus-core/lib.rs:6454:9 -/ tmp___0.isFNil → ¬/- @rust:tactus-core/lib.rs:6457:9 -/ tmp___0.isFBind → ¬/- @rust:tactus-core/lib.rs:6461:9 -/ tmp___0.isFHyp → ¬/- @rust:tactus-core/lib.rs:6465:9 -/ tmp___0.isFLetH → ¬/- @rust:tactus-core/lib.rs:6469:9 -/ tmp___0.isFLet → /- @rust:tactus-core/lib.rs:6473:9 -/ tmp___0.isFLetR → (let id := tmp___0.FLetR_val0;
                                                                                                                                                                                                                                                                                                                                                       let v := tmp___0.FLetR_val1;
                                                                                                                                                                                                                                                                                                                                                       let t := tmp___0.FLetR_val2;
                                                                                                                                                                                                                                                                                                                                                       let tmp__6 := lib.FrameList.FNil;
                                                                                                                                                                                                                                                                                                                                                       ∀ (_tactus_ret_19 : Unit), lib.frame_append (lib.FrameList.FLetR id v t) tmp__6 = lib.FrameList.FLetR id v (Tactus.Box.mk (lib.frame_append t.deref tmp__6)) → /- @rust:tactus-core/lib.rs:6475:13 -/ lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False) := by
  first | (intros <;> cases f <;> omega) | (intros <;> cases f <;> with_reducible rfl) | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])
-- tactus-closer: user
theorem _tactus_postcondition_frame_append_fnil_right_at_lib_6450_13_22 (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:tactus-core/lib.rs:6454:9 -/ tmp___0.isFNil → ¬/- @rust:tactus-core/lib.rs:6457:9 -/ tmp___0.isFBind → ¬/- @rust:tactus-core/lib.rs:6461:9 -/ tmp___0.isFHyp → ¬/- @rust:tactus-core/lib.rs:6465:9 -/ tmp___0.isFLetH → ¬/- @rust:tactus-core/lib.rs:6469:9 -/ tmp___0.isFLet → /- @rust:tactus-core/lib.rs:6473:9 -/ tmp___0.isFLetR → (let id := tmp___0.FLetR_val0;
                                                                                                                                                                                                                                                                                                                                                       let v := tmp___0.FLetR_val1;
                                                                                                                                                                                                                                                                                                                                                       let t := tmp___0.FLetR_val2;
                                                                                                                                                                                                                                                                                                                                                       let tmp__6 := lib.FrameList.FNil;
                                                                                                                                                                                                                                                                                                                                                       ∀ (_tactus_ret_19 : Unit), lib.frame_append (lib.FrameList.FLetR id v t) tmp__6 = lib.FrameList.FLetR id v (Tactus.Box.mk (lib.frame_append t.deref tmp__6)) → lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False → (∀ (_tactus_ret_21 : Unit), lib.frame_append t.deref lib.FrameList.FNil = t.deref → /- @rust:tactus-core/lib.rs:6450:13 -/ lib.frame_append f lib.FrameList.FNil = f)) := by
  first | (intros <;> cases f <;> omega) | (intros <;> cases f <;> with_reducible rfl) | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])
-- tactus-closer: user
theorem _tactus_termination_frame_append_fnil_right_at_lib_6479_13_24 (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:tactus-core/lib.rs:6454:9 -/ tmp___0.isFNil → ¬/- @rust:tactus-core/lib.rs:6457:9 -/ tmp___0.isFBind → ¬/- @rust:tactus-core/lib.rs:6461:9 -/ tmp___0.isFHyp → ¬/- @rust:tactus-core/lib.rs:6465:9 -/ tmp___0.isFLetH → ¬/- @rust:tactus-core/lib.rs:6469:9 -/ tmp___0.isFLet → ¬/- @rust:tactus-core/lib.rs:6473:9 -/ tmp___0.isFLetR → (let t := tmp___0.FUserCloser_val0;
                                                                                                                                                                                                                                                                                                                                                        let tmp__7 := lib.FrameList.FNil;
                                                                                                                                                                                                                                                                                                                                                        ∀ (_tactus_ret_23 : Unit), lib.frame_append (lib.FrameList.FUserCloser t) tmp__7 = lib.FrameList.FUserCloser (Tactus.Box.mk (lib.frame_append t.deref tmp__7)) → /- @rust:tactus-core/lib.rs:6479:13 -/ lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False) := by
  first | (intros <;> cases f <;> omega) | (intros <;> cases f <;> with_reducible rfl) | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])
-- tactus-closer: user
theorem _tactus_postcondition_frame_append_fnil_right_at_lib_6450_13_26 (f : lib.FrameList) :
    let decrease_init0 := f;
    let tmp___0 := f;
    ¬/- @rust:tactus-core/lib.rs:6454:9 -/ tmp___0.isFNil → ¬/- @rust:tactus-core/lib.rs:6457:9 -/ tmp___0.isFBind → ¬/- @rust:tactus-core/lib.rs:6461:9 -/ tmp___0.isFHyp → ¬/- @rust:tactus-core/lib.rs:6465:9 -/ tmp___0.isFLetH → ¬/- @rust:tactus-core/lib.rs:6469:9 -/ tmp___0.isFLet → ¬/- @rust:tactus-core/lib.rs:6473:9 -/ tmp___0.isFLetR → (let t := tmp___0.FUserCloser_val0;
                                                                                                                                                                                                                                                                                                                                                        let tmp__7 := lib.FrameList.FNil;
                                                                                                                                                                                                                                                                                                                                                        ∀ (_tactus_ret_23 : Unit), lib.frame_append (lib.FrameList.FUserCloser t) tmp__7 = lib.FrameList.FUserCloser (Tactus.Box.mk (lib.frame_append t.deref tmp__7)) → lib.FrameList.height t.deref < lib.FrameList.height decrease_init0 ∨ lib.FrameList.height t.deref = lib.FrameList.height decrease_init0 ∧ False → (∀ (_tactus_ret_25 : Unit), lib.frame_append t.deref lib.FrameList.FNil = t.deref → /- @rust:tactus-core/lib.rs:6450:13 -/ lib.frame_append f lib.FrameList.FNil = f)) := by
  first | (intros <;> cases f <;> omega) | (intros <;> cases f <;> with_reducible rfl) | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])
