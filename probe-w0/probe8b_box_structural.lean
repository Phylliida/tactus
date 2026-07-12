/- P8b: the POST-FIX shape — recursion through Box.deref projections.
   Does `termination_by structural` accept it, and does it kernel-reduce? -/
structure Tactus.Box (A : Type u) where
  deref : A
  deriving Inhabited
inductive PExpr where
  | Lit (v : Int)
  | Add (a : Tactus.Box PExpr) (b : Tactus.Box PExpr)
noncomputable def esize (e : PExpr) : Nat :=
  match e with | .Lit _ => 1 | .Add a b => esize a.deref + esize b.deref
termination_by structural e
example : esize (.Add ⟨.Lit 3⟩ ⟨.Add ⟨.Lit 4⟩ ⟨.Lit 5⟩⟩) = 3 := by decide
example : esize (.Add ⟨.Lit 3⟩ ⟨.Add ⟨.Lit 4⟩ ⟨.Lit 5⟩⟩) = 3 := by rfl
#print axioms esize
