import Probe.Stmts.M
namespace Probe

-- exec fn's own WP theorem: proves its contract using the SHARED
-- req/ens defs from Stmts (self-contained; nobody imports this)
theorem incr_wp : ∀ (x : Int), incr_req x → incr_ens x (x + 1) := by
  intro x hreq
  unfold incr_req at hreq
  unfold incr_ens
  omega

-- a caller's WP goal, referencing the SAME defs (call rule inlines
-- "assert req, assume ens" — the defs are shared, so drift between
-- definition site and call site is structurally impossible). Also
-- consumes a proof-fn lemma as hypothesis, mixing both mechanisms.
theorem caller_wp (h_a : lemma_a_stmt) :
    ∀ (x : Int), 0 ≤ x → x < 999 →
      incr_req x ∧ (∀ ret, incr_ens x ret → 0 < ret + 0) := by
  intro x hx hlt
  refine ⟨?_, ?_⟩
  · unfold incr_req; omega
  · intro ret hens
    unfold incr_ens at hens
    have := h_a ret (by omega)
    omega

end Probe
