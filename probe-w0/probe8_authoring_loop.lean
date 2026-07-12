/- W0 pre-probe P8 (FINAL, emitter-native): the tactus-core AUTHORING LOOP
   with ZERO manual edits. Source: bootstrap-fixture/w15_probe.rs with
   #[verifier::structural_decreases] on esize/lsize (W1.5, landed) — the
   emitter itself produces `termination_by structural`; decls below are
   VERBATIM emitted text. Run:
     LEAN_PATH=$(ls -td ~/.cache/tactus/prelude-*/ | head -1) lean probe8_authoring_loop.lean -/
import TactusPrelude
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
inductive w15_probe.PExpr where
  | Lit (val0 : Int)
  | Add (val0 : Tactus.Box w15_probe.PExpr) (val1 : Tactus.Box w15_probe.PExpr)
  deriving Inhabited
@[simp] noncomputable def w15_probe.PExpr.height (s : w15_probe.PExpr) : Nat :=
  match s with | w15_probe.PExpr.Lit _ => 1 | w15_probe.PExpr.Add val0 val1 => 1 + w15_probe.PExpr.height val0.deref + w15_probe.PExpr.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
inductive w15_probe.PList where
  | Nil
  | Cons (val0 : Tactus.Box w15_probe.PExpr) (val1 : Tactus.Box w15_probe.PList)
  deriving Inhabited
@[simp] noncomputable def w15_probe.PList.height (s : w15_probe.PList) : Nat :=
  match s with | w15_probe.PList.Nil => 1 | w15_probe.PList.Cons _ val1 => 1 + w15_probe.PList.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
noncomputable def w15_probe.esize (e : w15_probe.PExpr) : Nat :=
  match e with | w15_probe.PExpr.Lit _v => 1 | w15_probe.PExpr.Add a b => w15_probe.esize a.deref + w15_probe.esize b.deref
termination_by structural e
noncomputable def w15_probe.lsize (l : w15_probe.PList) : Nat :=
  match l with | w15_probe.PList.Nil => 0 | w15_probe.PList.Cons h t => w15_probe.esize h.deref + w15_probe.lsize t.deref
termination_by structural l

-- kernel-computability on unmodified emitter output
example : w15_probe.esize (.Add ⟨.Lit 3⟩ ⟨.Add ⟨.Lit 4⟩ ⟨.Lit 5⟩⟩) = 3 := by decide
example : w15_probe.esize (.Add ⟨.Lit 3⟩ ⟨.Add ⟨.Lit 4⟩ ⟨.Lit 5⟩⟩) = 3 := by rfl
example : w15_probe.lsize (.Cons ⟨.Lit 7⟩ ⟨.Cons ⟨.Add ⟨.Lit 1⟩ ⟨.Lit 2⟩⟩ ⟨.Nil⟩⟩) = 3 := by decide
#print axioms w15_probe.esize
