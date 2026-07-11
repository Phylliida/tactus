/- W0 pre-probe P8: the tactus-core AUTHORING LOOP, end to end through the
   REAL emitter. Source: bootstrap-fixture/w15_probe.rs emitted by tactus
   (out/w15_probe/use_sizes.lean), datatype+spec-fn decls extracted VERBATIM,
   with exactly ONE mechanical change: `termination_by e` + decreasing_by
   -> `termination_by structural e` (the W1.5 feature, applied by hand).
   Finding feeding this: the emitter ERASES Box in spec datatypes -- match
   arms bind subterms directly; recursion is already structural-shaped. -/

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
  match e with | w15_probe.PExpr.Lit _v => 1 | w15_probe.PExpr.Add a b => w15_probe.esize a + w15_probe.esize b
termination_by structural e
noncomputable def w15_probe.lsize (l : w15_probe.PList) : Nat :=
  match l with | w15_probe.PList.Nil => 0 | w15_probe.PList.Cons h t => w15_probe.esize h + w15_probe.lsize t
termination_by structural l

-- kernel-computability: the W1.5 payoff, on emitted text
example : w15_probe.esize (.Add (.Lit 3) (.Add (.Lit 4) (.Lit 5))) = 3 := by decide
example : w15_probe.esize (.Add (.Lit 3) (.Add (.Lit 4) (.Lit 5))) = 3 := by rfl
example : w15_probe.lsize (.Cons (.Lit 7) (.Cons (.Add (.Lit 1) (.Lit 2)) .Nil)) = 3 := by decide
#print axioms w15_probe.esize
