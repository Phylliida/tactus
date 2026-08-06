import TactusDefs_lib_exec
set_option maxRecDepth 8000
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus defs-layer certificate (W7d) — crate `lib`, spec fn `deref_field`
-- tactus-core-vocab-hash: unvendored
-- Certifies that the INDEPENDENT reference transcription of this
-- def/datatype (VIR-side `raw_vir_*`, rendered by tactus-core `render_*`)
-- agrees with the PRODUCTION `lean_ast`-side transcription (`l*_to_*data`)
-- via `def_eq`/`dt_eq`. It does NOT certify the transcribers (they are the
-- TCB), the leaf-id interning, the frontend, or SST-semantics adequacy (W5).

def cert_deref_field_raw : lib.RawDef :=
  (lib.RawDef.mk 0 lib.ParamList.Nil lib.TypData.TyInt (lib.RawExp.Lit 0 lib.TypData.TyInt))

def cert_deref_field_defdata : lib.DefData :=
  (lib.DefData.mk 0 lib.ParamList.Nil lib.TypData.TyInt (lib.ExprData.Lit 0))

example : lib.def_eq (lib.render_def cert_deref_field_raw) cert_deref_field_defdata = 1 := by decide
