import Probe.Stmts.M
namespace Probe

-- hypothesis-passing: callee's stmt as a leading binder.
-- Imports Stmts ONLY — a body edit in LemmaA never reaches this module.
theorem lemma_b_thm (h_a : lemma_a_stmt) : lemma_b_stmt := by
  intro x hx
  have := h_a x hx
  omega

end Probe
