import TactusStmts_lib_exec__lib__ref_wp_sound
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_ref_wp_sound_at_lib_4266_13_3 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (c : lib.FnCtxData) (s : lib.StmData) (st : Int → Int) (_tactus_ret_1 : Unit) (_h_ctx_0 : lib.ref_wp c s = lib.wp_stm (lib.seed_frame c) s) :
    let tmp__1 := lib.seed_frame c;
    ∀ (_tactus_ret_2 : Unit), lib.holds_all hp he lv (lib.wp_stm tmp__1 s) st = lib.exec_safe_f hp he lv tmp__1 s st → /- @rust:lib.rs:4266:13 -/ lib.holds_all hp he lv (lib.ref_wp c s) st = lib.exec_safe_f hp he lv (lib.seed_frame c) s st := by
  first | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])
