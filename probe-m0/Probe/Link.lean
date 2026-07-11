/- Link layer: machine-generated closure. Pure applications in
   dep_order topological order; SCCs close as units. This is the ONLY
   module importing Proofs — so it re-elaborates on any body edit, and
   it must stay cheap (each line is one defeq check between
   syntactically identical types). -/
import Probe.Proofs.LemmaA
import Probe.Proofs.LemmaB
import Probe.Proofs.LemmaC
import Probe.Proofs.Broadcast
import Probe.Proofs.MutualEO
import Probe.Proofs.Generic
import Probe.Proofs.ExecIncr
namespace Probe

theorem lemma_a_closed : lemma_a_stmt := lemma_a_thm
theorem lemma_b_closed : lemma_b_stmt := lemma_b_thm lemma_a_closed
theorem lemma_c_closed : lemma_c_stmt := lemma_c_thm lemma_b_closed
theorem size_pos_closed : size_pos_stmt := size_pos_thm
theorem size_double_closed : size_double_stmt := size_double_thm size_pos_closed
-- mutual SCC: parameterized thms bridge to stmt-typed closed forms
-- (definitional eta makes the direct reference typecheck)
theorem even_odd_closed : even_odd_stmt := even_odd_thm
theorem odd_even_closed : odd_even_stmt := odd_even_thm
theorem generic_closed : generic_stmt := generic_thm
theorem caller_wp_closed :
    ∀ (x : Int), 0 ≤ x → x < 999 →
      incr_req x ∧ (∀ ret, incr_ens x ret → 0 < ret + 0) :=
  caller_wp lemma_a_closed

/- crate axiom-closure check (DESIGN-axiom-closure-check §5): stand-in
   via #print axioms until #tactus_check_axioms lands. Expected here:
   every closed theorem's closure ⊆ {propext, Classical.choice,
   Quot.sound} ∪ ∅ (no prelude axioms in this probe, no Boundary). -/
#print axioms lemma_c_closed
#print axioms size_double_closed
#print axioms even_odd_closed
#print axioms caller_wp_closed

end Probe
