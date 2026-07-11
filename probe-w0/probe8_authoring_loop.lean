/- W0 pre-probe P8 (regenerated post-fix): the tactus-core AUTHORING LOOP on
   REAL emitter output, against the REAL prelude. Run with:
     LEAN_PATH=~/.cache/tactus/prelude-<hash> lean probe8_authoring_loop.lean
   Source: bootstrap-fixture/w15_probe.rs emitted by the FIXED binary
   (match-arm binder-typ fix); decls verbatim (file lines 1-29); ONE change:
   termination_by -> structural on esize/lsize (the W1.5 feature by hand). -/
import TactusPrelude
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
namespace w15_probe
set_option autoImplicit false
inductive _root_.w15_probe.PExpr where
  | Lit (val0 : Int)
  | Add (val0 : Tactus.Box PExpr) (val1 : Tactus.Box PExpr)
  deriving Inhabited
@[simp] noncomputable def PExpr.height (s : PExpr) : Nat :=
  match s with | PExpr.Lit _ => 1 | PExpr.Add val0 val1 => 1 + PExpr.height val0.deref + PExpr.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
inductive _root_.w15_probe.PList where
  | Nil
  | Cons (val0 : Tactus.Box _root_.w15_probe.PExpr) (val1 : Tactus.Box PList)
  deriving Inhabited
@[simp] noncomputable def PList.height (s : PList) : Nat :=
  match s with | PList.Nil => 1 | PList.Cons _ val1 => 1 + PList.height val1.deref
termination_by sizeOf s
decreasing_by all_goals (simp_all; omega)
noncomputable def _root_.w15_probe.esize (e : _root_.w15_probe.PExpr) : Nat :=
  match e with | _root_.w15_probe.PExpr.Lit _v => 1 | _root_.w15_probe.PExpr.Add a b => esize a.deref + esize b.deref
termination_by structural e
noncomputable def _root_.w15_probe.lsize (l : _root_.w15_probe.PList) : Nat :=
  match l with | _root_.w15_probe.PList.Nil => 0 | _root_.w15_probe.PList.Cons h t => _root_.w15_probe.esize h.deref + lsize t.deref
termination_by structural l
end w15_probe

-- kernel-computability: the W1.5 payoff, on real emitted text
example : w15_probe.esize (.Add ⟨.Lit 3⟩ ⟨.Add ⟨.Lit 4⟩ ⟨.Lit 5⟩⟩) = 3 := by decide
example : w15_probe.esize (.Add ⟨.Lit 3⟩ ⟨.Add ⟨.Lit 4⟩ ⟨.Lit 5⟩⟩) = 3 := by rfl
example : w15_probe.lsize (.Cons ⟨.Lit 7⟩ ⟨.Cons ⟨.Add ⟨.Lit 1⟩ ⟨.Lit 2⟩⟩ ⟨.Nil⟩⟩) = 3 := by decide
#print axioms w15_probe.esize
