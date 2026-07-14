import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 8000

/-
  W3 differential gate — pinpoint evidence (board bootstrap-08).

  Subject: the SOLE tgt exec fn that emits a stage-A cert today,
    tactus-group-theory  runtime::impl__4::clone   —   fn clone(self: &RuntimeSymbol).
  (Derived Copy-clone; trivial WP, which is why it is the one exec fn among tgt's
   9 that clears the serializer's stage-A scope. The other 8 are LOUD scope-
   rejections: 5×StmData::Call + 3×assert-query, emitting no cert.)

  The bridge  goals_eq (ref_wp ctx sst) production = 1  is FALSE. This file
  pinpoint-proves the single divergence: the RetBind-value leaf.

  Leaf table (as emitted by this serializer version):
    leaf 0: ⟦self⟧
    leaf 1: ⟦Tactus.Ref lib.runtime.RuntimeSymbol⟧
    leaf 2: ⟦_return = self.deref⟧                         (ensures)
    leaf 3: ⟦/- @rust:…runtime.rs:19:25 -/ _return = self.deref⟧   (annotated obligation)
    leaf 4: ⟦_return⟧
    leaf 5: ⟦self.deref⟧

  SST RetBind = RetLet(4, 0):  bind _return(id 4) := leaf 0 = ⟦self⟧      (bare param)
  Production goal Let        =  Let 4 5:  _return(id 4) := leaf 5 = ⟦self.deref⟧

  i.e. the serializer renders the return-value binding of the `&`-param as bare
  `self`, not `self.deref` — production applies the `*p → p.deref` subst there,
  the serializer's RetBind-value render does not. Everything else (the ∀ self
  telescope `All 0 1`, the RetLet name 4, the annotated obligation leaf 3)
  matches. NEW site, SAME class as head_exec / bootstrap-18 (the obligation-leaf
  site). Stage A does not certify leaf rendering (DESIGN-W2-refwp.md §2.5), so
  the bridge SOUNDLY does not close: a serializer faithfulness gap, not a refWp
  or production bug.

  These defs are a SNAPSHOT of the emitted cert at this serializer version, kept
  as browsable evidence. The live regenerable cert is at
  out/lib/cert/runtime__impl__4__clone.cert.lean (regen recipe in run.sh header);
  run.sh bridges whatever is on disk. If the serializer is fixed (bootstrap-18 +
  this site) the live bridge will CLOSE and run.sh flags the honest-fail→close as
  a regression to reclassify.
-/

namespace w3pin

@[reducible] def ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)) lib.BinderList.Nil (lib.LeafList.Cons 2 (Tactus.Box.mk lib.LeafList.Nil)))

@[reducible] def sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.LeafList.Cons 3 (Tactus.Box.mk lib.LeafList.Nil))) (lib.RetBind.RetLet 4 0))

-- production goals, verbatim from the cert:
@[reducible] def goals_prod : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.Let 4 5 (Tactus.Box.mk (lib.GoalData.Leaf 3)))))) (Tactus.Box.mk lib.GoalList.Nil)

-- production goals with ONLY the RetLet-value leaf patched 5 (self.deref) → 0 (self):
@[reducible] def goals_patched : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.Let 4 0 (Tactus.Box.mk (lib.GoalData.Leaf 3)))))) (Tactus.Box.mk lib.GoalList.Nil)

-- (0) sanity: shape counts match the cert's own in-file decides.
example : lib.stm_size sst = 2 := by decide
example : lib.goal_count goals_prod = 1 := by decide

-- (1) the real bridge DIVERGES (goals_eq = 0), on real corpus code.
example : lib.goals_eq (lib.ref_wp ctx sst) goals_prod = 0 := by decide

-- (2) patching ONLY the RetLet-value leaf 5→0 makes refWp match: SOLE divergence.
example : lib.goals_eq (lib.ref_wp ctx sst) goals_patched = 1 := by decide

end w3pin
