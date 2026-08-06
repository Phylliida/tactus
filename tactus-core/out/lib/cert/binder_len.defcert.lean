import TactusDefs_lib_exec
set_option maxRecDepth 8000
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus defs-layer certificate (W7d) — crate `lib`, spec fn `binder_len`
-- tactus-core-vocab-hash: unvendored
-- Certifies that the INDEPENDENT reference transcription of this
-- def/datatype (VIR-side `raw_vir_*`, rendered by tactus-core `render_*`)
-- agrees with the PRODUCTION `lean_ast`-side transcription (`l*_to_*data`)
-- via `def_eq`/`dt_eq`. It does NOT certify the transcribers (they are the
-- TCB), the leaf-id interning, the frontend, or SST-semantics adequacy (W5).

def cert_binder_len_raw : lib.RawDef :=
  (lib.RawDef.mk 0 (lib.ParamList.Cons 1 (lib.TypData.TyNamed 2) (Tactus.Box.mk lib.ParamList.Nil)) lib.TypData.TyNat (lib.RawExp.MatchR (Tactus.Box.mk (lib.RawExp.Var 1 (lib.TypData.TyNamed 2))) (Tactus.Box.mk (lib.RawArmList.Cons 7 lib.BinderIdList.Nil (Tactus.Box.mk (lib.RawExp.Lit 0 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawArmList.Cons 3 (lib.BinderIdList.Cons 6 (Tactus.Box.mk (lib.BinderIdList.Cons 5 (Tactus.Box.mk (lib.BinderIdList.Cons 4 (Tactus.Box.mk lib.BinderIdList.Nil)))))) (Tactus.Box.mk (lib.RawExp.BinOp 6 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Lit 1 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawExp.Call 0 lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.Var 4 (lib.TypData.TyNamed 2))) (lib.TypData.TyNamed 2))))) (Tactus.Box.mk lib.RawArmList.Nil))))) lib.TypData.TyNat))

def cert_binder_len_defdata : lib.DefData :=
  (lib.DefData.mk 0 (lib.ParamList.Cons 1 (lib.TypData.TyNamed 2) (Tactus.Box.mk lib.ParamList.Nil)) lib.TypData.TyNat (lib.ExprData.Match (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ArmList.Cons 7 lib.BinderIdList.Nil (Tactus.Box.mk (lib.ExprData.Lit 0)) (Tactus.Box.mk (lib.ArmList.Cons 3 (lib.BinderIdList.Cons 6 (Tactus.Box.mk (lib.BinderIdList.Cons 5 (Tactus.Box.mk (lib.BinderIdList.Cons 4 (Tactus.Box.mk lib.BinderIdList.Nil)))))) (Tactus.Box.mk (lib.ExprData.BinOp 6 (Tactus.Box.mk (lib.ExprData.Lit 1)) (Tactus.Box.mk (lib.ExprData.App 0 (Tactus.Box.mk (lib.ExprData.FieldProj (Tactus.Box.mk (lib.ExprData.Atom 4)) 0)))))) (Tactus.Box.mk lib.ArmList.Nil)))))))

example : lib.def_eq (lib.render_def cert_binder_len_raw) cert_binder_len_defdata = 1 := by decide
