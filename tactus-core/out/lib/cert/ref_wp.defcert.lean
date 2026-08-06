import TactusDefs_lib_exec
set_option maxRecDepth 8000
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus defs-layer certificate (W7d) — crate `lib`, spec fn `ref_wp`
-- tactus-core-vocab-hash: unvendored
-- Certifies that the INDEPENDENT reference transcription of this
-- def/datatype (VIR-side `raw_vir_*`, rendered by tactus-core `render_*`)
-- agrees with the PRODUCTION `lean_ast`-side transcription (`l*_to_*data`)
-- via `def_eq`/`dt_eq`. It does NOT certify the transcribers (they are the
-- TCB), the leaf-id interning, the frontend, or SST-semantics adequacy (W5).

def cert_ref_wp_raw : lib.RawDef :=
  (lib.RawDef.mk 0 (lib.ParamList.Cons 1 (lib.TypData.TyNamed 2) (Tactus.Box.mk (lib.ParamList.Cons 3 (lib.TypData.TyNamed 4) (Tactus.Box.mk lib.ParamList.Nil)))) (lib.TypData.TyNamed 5) (lib.RawExp.CallN 6 (lib.TypData.TyNamed 5) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Call 10 (lib.TypData.TyNamed 9) (Tactus.Box.mk (lib.RawExp.Var 1 (lib.TypData.TyNamed 2))) (lib.TypData.TyNamed 2))) (lib.TypData.TyNamed 9) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Call 8 (lib.TypData.TyNamed 7) (Tactus.Box.mk (lib.RawExp.Var 1 (lib.TypData.TyNamed 2))) (lib.TypData.TyNamed 2))) (lib.TypData.TyNamed 7) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 3 (lib.TypData.TyNamed 4))) (lib.TypData.TyNamed 4) (Tactus.Box.mk lib.RawList.Nil)))))))))

def cert_ref_wp_defdata : lib.DefData :=
  (lib.DefData.mk 0 (lib.ParamList.Cons 1 (lib.TypData.TyNamed 2) (Tactus.Box.mk (lib.ParamList.Cons 3 (lib.TypData.TyNamed 4) (Tactus.Box.mk lib.ParamList.Nil)))) (lib.TypData.TyNamed 5) (lib.ExprData.AppN 6 (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.App 10 (Tactus.Box.mk (lib.ExprData.Atom 1)))) (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.App 8 (Tactus.Box.mk (lib.ExprData.Atom 1)))) (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom 3)) (Tactus.Box.mk lib.ExprList.Nil)))))))))

example : lib.def_eq (lib.render_def cert_ref_wp_raw) cert_ref_wp_defdata = 1 := by decide
