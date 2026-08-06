import TactusDefs_lib_exec
set_option maxRecDepth 8000
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus defs-layer certificate (W7d) — crate `lib`, datatype `lib.ParamList`
-- tactus-core-vocab-hash: unvendored
-- Certifies that the INDEPENDENT reference transcription of this
-- def/datatype (VIR-side `raw_vir_*`, rendered by tactus-core `render_*`)
-- agrees with the PRODUCTION `lean_ast`-side transcription (`l*_to_*data`)
-- via `def_eq`/`dt_eq`. It does NOT certify the transcribers (they are the
-- TCB), the leaf-id interning, the frontend, or SST-semantics adequacy (W5).

def cert_lib__ParamList_raw : lib.RawDt :=
  (lib.RawDt.mk 0 (lib.CtorList.Cons 1 lib.TypList.Nil (Tactus.Box.mk (lib.CtorList.Cons 2 (lib.TypList.Cons lib.TypData.TyInt (Tactus.Box.mk (lib.TypList.Cons (lib.TypData.TyNamed 3) (Tactus.Box.mk (lib.TypList.Cons (lib.TypData.TyBox 0) (Tactus.Box.mk lib.TypList.Nil)))))) (Tactus.Box.mk lib.CtorList.Nil)))))

def cert_lib__ParamList_dtdata : lib.DtData :=
  (lib.DtData.mk 0 (lib.CtorList.Cons 1 lib.TypList.Nil (Tactus.Box.mk (lib.CtorList.Cons 2 (lib.TypList.Cons lib.TypData.TyInt (Tactus.Box.mk (lib.TypList.Cons (lib.TypData.TyNamed 3) (Tactus.Box.mk (lib.TypList.Cons (lib.TypData.TyBox 0) (Tactus.Box.mk lib.TypList.Nil)))))) (Tactus.Box.mk lib.CtorList.Nil)))))

example : lib.dt_eq (lib.render_dt cert_lib__ParamList_raw) cert_lib__ParamList_dtdata = 1 := by decide
