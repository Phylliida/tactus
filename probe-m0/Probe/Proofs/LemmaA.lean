import Probe.Stmts.M
namespace Probe

-- leaf lemma: no hypotheses; stmt-name-as-type shape
theorem lemma_a_thm : lemma_a_stmt := by
  intro x hx
  have h0 : (0:Int) ≤ x := hx
  omega

end Probe
