-- W7d defs-layer bridge probe (board bootstrap-32).
--
-- Unlike the W7a probe (probe15), which hand-writes the defs-layer vocabulary
-- in a standalone file, THIS probe imports the REAL emitted tactus-core
-- (`TactusDefs_lib_exec`, carrying the LANDED `render_def`/`def_eq`/`render_dt`/
-- `dt_eq`) and feeds it the EXACT strings the W7c transcribers emit — copied
-- verbatim from the serializer unit tests (`sst_serialize_tests.rs`:
-- `raw_vir_def_tri_header`, `ldef_to_defdata_tri_header`, `raw_vir_dt_tree`,
-- `ldt_to_dtdata_tree`). So this is the def-layer analog of probe9's obligation
-- bridge: it validates that the actual serializer TEXT FORMAT elaborates and
-- that `def_eq`/`dt_eq` close on real transcriber output, without a vargo rebuild.
--
-- Positives must `decide` to `= 1` (bridge closes); mutation negatives must
-- `decide` to `= 0` (the bridge is non-vacuous — a perturbed def/datatype is
-- rejected). rc=0 ⇒ every example elaborated as classified.

import TactusDefs_lib_exec
set_option maxRecDepth 8000
set_option linter.unusedVariables false
set_option autoImplicit false

-- ── the `tri` def (header + trivial `Var n` body — the exact unit-test pin) ──
-- reference: `raw_vir_def` output (name lib::tri = 0, param n = 1 : TyNat,
-- ret TyNat, body RawExp.Var 1 TyNat).
def raw_tri : lib.RawDef :=
  (lib.RawDef.mk 0
     (lib.ParamList.Cons 1 lib.TypData.TyNat (Tactus.Box.mk lib.ParamList.Nil))
     lib.TypData.TyNat
     (lib.RawExp.Var 1 lib.TypData.TyNat))

-- production: `ldef_to_defdata` output — the DefData twin (body ExprData.Atom 1).
def defdata_tri : lib.DefData :=
  (lib.DefData.mk 0
     (lib.ParamList.Cons 1 lib.TypData.TyNat (Tactus.Box.mk lib.ParamList.Nil))
     lib.TypData.TyNat
     (lib.ExprData.Atom 1))

-- ── the `Tree` datatype (FULL emitted fidelity — the exact unit-test pin) ──
-- reference: `raw_vir_dt` output. name lib.Tree = 0; ctor Leaf = 1 [TyInt];
-- ctor Node = 2 [TyBox 0, TyBox 0] — the Box is KEPT (W7a §7 Q4), NOT peeled.
def raw_tree : lib.RawDt :=
  (lib.RawDt.mk 0
     (lib.CtorList.Cons 1
        (lib.TypList.Cons lib.TypData.TyInt (Tactus.Box.mk lib.TypList.Nil))
        (Tactus.Box.mk
           (lib.CtorList.Cons 2
              (lib.TypList.Cons (lib.TypData.TyBox 0)
                 (Tactus.Box.mk (lib.TypList.Cons (lib.TypData.TyBox 0)
                    (Tactus.Box.mk lib.TypList.Nil))))
              (Tactus.Box.mk lib.CtorList.Nil)))))

-- production: `ldt_to_dtdata` output — the DtData twin (byte-identical ctor list).
def dtdata_tree : lib.DtData :=
  (lib.DtData.mk 0
     (lib.CtorList.Cons 1
        (lib.TypList.Cons lib.TypData.TyInt (Tactus.Box.mk lib.TypList.Nil))
        (Tactus.Box.mk
           (lib.CtorList.Cons 2
              (lib.TypList.Cons (lib.TypData.TyBox 0)
                 (Tactus.Box.mk (lib.TypList.Cons (lib.TypData.TyBox 0)
                    (Tactus.Box.mk lib.TypList.Nil))))
              (Tactus.Box.mk lib.CtorList.Nil)))))

-- ── an Ite-BODIED def (exercises render_exp's branch path end-to-end) ──
-- The body strings are the EXACT `raw_exp`/`lexpr_to_exprdata` Ite output
-- (`sst_serialize_tests.rs`: `raw_exp_ite_body` / `lexpr_to_exprdata_ite_body`,
-- interning c=0/t=1/e=2), assembled into a def (synthetic header: name=3, no
-- params, ret TyInt). The RawExp `Ite` vocab is surface-agnostic (SST `raw_exp`
-- and VIR `raw_vir_exp` emit the same shape), so this validates that `def_eq`
-- closes over a NON-trivial body: `render_exp(Ite TyInt …)` must reproduce the
-- production `ExprData.Ite` (all branches TyInt ⇒ no nat-coercion inserted).
def raw_g : lib.RawDef :=
  (lib.RawDef.mk 3 lib.ParamList.Nil lib.TypData.TyInt
     (lib.RawExp.Ite lib.TypData.TyInt
        (Tactus.Box.mk (lib.RawExp.Var 0 lib.TypData.TyInt))
        (Tactus.Box.mk (lib.RawExp.Var 1 lib.TypData.TyInt))
        (Tactus.Box.mk (lib.RawExp.Var 2 lib.TypData.TyInt))))

def defdata_g : lib.DefData :=
  (lib.DefData.mk 3 lib.ParamList.Nil lib.TypData.TyInt
     (lib.ExprData.Ite
        (Tactus.Box.mk (lib.ExprData.Atom 0))
        (Tactus.Box.mk (lib.ExprData.Atom 1))
        (Tactus.Box.mk (lib.ExprData.Atom 2))))

-- ══ POSITIVES: the bridge closes (decide AND rfl) ══
example : lib.def_eq (lib.render_def raw_tri) defdata_tri = 1 := by decide
example : lib.def_eq (lib.render_def raw_tri) defdata_tri = 1 := by rfl
example : lib.def_eq (lib.render_def raw_g) defdata_g = 1 := by decide
example : lib.def_eq (lib.render_def raw_g) defdata_g = 1 := by rfl
example : lib.dt_eq (lib.render_dt raw_tree) dtdata_tree = 1 := by decide
example : lib.dt_eq (lib.render_dt raw_tree) dtdata_tree = 1 := by rfl

-- ══ NEGATIVES (mutation-kill — the bridge rejects a perturbed production side) ══

-- def body atom mutated (wrong var id in the body: `Atom 2` ≠ render of `Var 1`).
def defdata_tri_bad_body : lib.DefData :=
  (lib.DefData.mk 0
     (lib.ParamList.Cons 1 lib.TypData.TyNat (Tactus.Box.mk lib.ParamList.Nil))
     lib.TypData.TyNat
     (lib.ExprData.Atom 2))
example : lib.def_eq (lib.render_def raw_tri) defdata_tri_bad_body = 0 := by decide

-- def ret type mutated (TyInt ≠ the reference's TyNat).
def defdata_tri_bad_ret : lib.DefData :=
  (lib.DefData.mk 0
     (lib.ParamList.Cons 1 lib.TypData.TyNat (Tactus.Box.mk lib.ParamList.Nil))
     lib.TypData.TyInt
     (lib.ExprData.Atom 1))
example : lib.def_eq (lib.render_def raw_tri) defdata_tri_bad_ret = 0 := by decide

-- Ite branch swap (then/else atoms swapped): the body no longer matches the
-- reference render — the branch-order sensitivity of `expr_eq` over `Ite`.
def defdata_g_swapped : lib.DefData :=
  (lib.DefData.mk 3 lib.ParamList.Nil lib.TypData.TyInt
     (lib.ExprData.Ite
        (Tactus.Box.mk (lib.ExprData.Atom 0))
        (Tactus.Box.mk (lib.ExprData.Atom 2))
        (Tactus.Box.mk (lib.ExprData.Atom 1))))
example : lib.def_eq (lib.render_def raw_g) defdata_g_swapped = 0 := by decide

-- THE W7a §7 Q4 KILL: a `Node` field peeled (`TyNamed 0`) instead of kept
-- (`TyBox 0`). This is exactly the mistranslation the Box subtlety guards
-- against — the reference keeps the box, so a peeling production side is rejected.
def dtdata_tree_peeled : lib.DtData :=
  (lib.DtData.mk 0
     (lib.CtorList.Cons 1
        (lib.TypList.Cons lib.TypData.TyInt (Tactus.Box.mk lib.TypList.Nil))
        (Tactus.Box.mk
           (lib.CtorList.Cons 2
              (lib.TypList.Cons (lib.TypData.TyNamed 0)
                 (Tactus.Box.mk (lib.TypList.Cons (lib.TypData.TyNamed 0)
                    (Tactus.Box.mk lib.TypList.Nil))))
              (Tactus.Box.mk lib.CtorList.Nil)))))
example : lib.dt_eq (lib.render_dt raw_tree) dtdata_tree_peeled = 0 := by decide

-- ctor name (id) mutated: `Leaf` interned as 9 instead of 1.
def dtdata_tree_bad_ctor : lib.DtData :=
  (lib.DtData.mk 0
     (lib.CtorList.Cons 9
        (lib.TypList.Cons lib.TypData.TyInt (Tactus.Box.mk lib.TypList.Nil))
        (Tactus.Box.mk
           (lib.CtorList.Cons 2
              (lib.TypList.Cons (lib.TypData.TyBox 0)
                 (Tactus.Box.mk (lib.TypList.Cons (lib.TypData.TyBox 0)
                    (Tactus.Box.mk lib.TypList.Nil))))
              (Tactus.Box.mk lib.CtorList.Nil)))))
example : lib.dt_eq (lib.render_dt raw_tree) dtdata_tree_bad_ctor = 0 := by decide
