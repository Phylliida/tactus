import TactusStmts_lib_exec__lib__ref_wp_sound
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_ref_wp_sound_at_lib_6391_13_3 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (c : lib.FnCtxData) (h_c_bound : 0 ≤ c.closer_default ∧ c.closer_default < 18446744073709551616) (s : lib.StmData) (st : Int → Int) (_tactus_ret_1 : Unit) (_h_hoist_1 : lib.ref_wp c s = lib.wp_stm (lib.poisoned_props c) (lib.seed_frame c) s) :
    let tmp__1 := lib.poisoned_props c;
    let tmp__2 := lib.seed_frame c;
    ∀ (_tactus_ret_2 : Unit), lib.holds_all hp he lv (lib.wp_stm tmp__1 tmp__2 s) st = lib.exec_safe_f tmp__1 hp he lv tmp__2 s st → /- @rust:tactus-core/lib.rs:6391:13 -/ lib.holds_all hp he lv (lib.ref_wp c s) st = lib.exec_safe_f (lib.poisoned_props c) hp he lv (lib.seed_frame c) s st := by
  first | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])
