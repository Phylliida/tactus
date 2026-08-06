import TactusDefs_lib_exec
set_option maxRecDepth 8000
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus defs-layer certificate (W7d) — crate `lib`, spec fn `raw_list_mentions`
-- tactus-core-vocab-hash: unvendored
-- Certifies that the INDEPENDENT reference transcription of this
-- def/datatype (VIR-side `raw_vir_*`, rendered by tactus-core `render_*`)
-- agrees with the PRODUCTION `lean_ast`-side transcription (`l*_to_*data`)
-- via `def_eq`/`dt_eq`. It does NOT certify the transcribers (they are the
-- TCB), the leaf-id interning, the frontend, or SST-semantics adequacy (W5).

def cert_raw_list_mentions_raw : lib.RawDef :=
  (lib.RawDef.mk 0 (lib.ParamList.Cons 1 (lib.TypData.TyNamed 2) (Tactus.Box.mk (lib.ParamList.Cons 3 (lib.TypData.TyNamed 4) (Tactus.Box.mk lib.ParamList.Nil)))) lib.TypData.TyNat (lib.RawExp.MatchR (Tactus.Box.mk (lib.RawExp.Var 3 (lib.TypData.TyNamed 4))) (Tactus.Box.mk (lib.RawArmList.Cons 11 lib.BinderIdList.Nil (Tactus.Box.mk (lib.RawExp.Lit 0 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawArmList.Cons 5 (lib.BinderIdList.Cons 8 (Tactus.Box.mk (lib.BinderIdList.Cons 7 (Tactus.Box.mk (lib.BinderIdList.Cons 6 (Tactus.Box.mk lib.BinderIdList.Nil)))))) (Tactus.Box.mk (lib.RawExp.Ite lib.TypData.TyNat (Tactus.Box.mk (lib.RawExp.BinOp 0 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.CallN 9 lib.TypData.TyNat (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 1 (lib.TypData.TyNamed 2))) (lib.TypData.TyNamed 2) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 8 (lib.TypData.TyNamed 10))) (lib.TypData.TyNamed 10) (Tactus.Box.mk lib.RawList.Nil))))))) (Tactus.Box.mk (lib.RawExp.Lit 1 lib.TypData.TyNat)))) (Tactus.Box.mk (lib.RawExp.Lit 1 lib.TypData.TyNat)) (Tactus.Box.mk (lib.RawExp.CallN 0 lib.TypData.TyNat (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 1 (lib.TypData.TyNamed 2))) (lib.TypData.TyNamed 2) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 6 (lib.TypData.TyNamed 4))) (lib.TypData.TyNamed 4) (Tactus.Box.mk lib.RawList.Nil))))))))) (Tactus.Box.mk lib.RawArmList.Nil))))) lib.TypData.TyNat))

def cert_raw_list_mentions_defdata : lib.DefData :=
  (lib.DefData.mk 0 (lib.ParamList.Cons 1 (lib.TypData.TyNamed 2) (Tactus.Box.mk (lib.ParamList.Cons 3 (lib.TypData.TyNamed 4) (Tactus.Box.mk lib.ParamList.Nil)))) lib.TypData.TyNat (lib.ExprData.Match (Tactus.Box.mk (lib.ExprData.Atom 3)) (Tactus.Box.mk (lib.ArmList.Cons 11 lib.BinderIdList.Nil (Tactus.Box.mk (lib.ExprData.Lit 0)) (Tactus.Box.mk (lib.ArmList.Cons 5 (lib.BinderIdList.Cons 8 (Tactus.Box.mk (lib.BinderIdList.Cons 7 (Tactus.Box.mk (lib.BinderIdList.Cons 6 (Tactus.Box.mk lib.BinderIdList.Nil)))))) (Tactus.Box.mk (lib.ExprData.Ite (Tactus.Box.mk (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.AppN 9 (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.FieldProj (Tactus.Box.mk (lib.ExprData.Atom 8)) 0)) (Tactus.Box.mk lib.ExprList.Nil))))))) (Tactus.Box.mk (lib.ExprData.Lit 1)))) (Tactus.Box.mk (lib.ExprData.Lit 1)) (Tactus.Box.mk (lib.ExprData.AppN 0 (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom 1)) (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.FieldProj (Tactus.Box.mk (lib.ExprData.Atom 6)) 0)) (Tactus.Box.mk lib.ExprList.Nil))))))))) (Tactus.Box.mk lib.ArmList.Nil)))))))

example : lib.def_eq (lib.render_def cert_raw_list_mentions_raw) cert_raw_list_mentions_defdata = 1 := by decide
