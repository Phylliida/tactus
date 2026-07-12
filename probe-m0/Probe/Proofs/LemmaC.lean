import Probe.Stmts.M
namespace Probe

-- two-deep chain end: direct callee only (b); a arrives transitively
-- through b's *closed* form at link time, not here.
theorem lemma_c_thm (h_b : lemma_b_stmt) : lemma_c_stmt := by
  intro x hx
  have := h_b x hx
  omega

end Probe
