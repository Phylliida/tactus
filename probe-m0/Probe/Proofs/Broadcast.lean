import Probe.Stmts.M
namespace Probe

-- the "broadcast lemma" itself: an ordinary theorem (today: an axiom!)
theorem size_pos_thm : size_pos_stmt := by
  intro t
  induction t with
  | leaf => simp [Tree.size]
  | node l r ihl ihr => simp [Tree.size]; omega

-- a consumer using it from the LOCAL CONTEXT the way tactic bodies use
-- broadcast axioms from the environment — parity check for §4.2's
-- "at worst neutral" claim
@[reducible] noncomputable def size_double_stmt : Prop := ∀ (t : Tree), 2 ≤ (Tree.node t t).size

theorem size_double_thm (h_sp : size_pos_stmt) : size_double_stmt := by
  intro t
  have := h_sp t
  simp [Tree.size]
  omega

end Probe
