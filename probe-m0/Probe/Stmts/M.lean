/- Stmts layer: each proof fn's ∀-closed requires→ensures as a named
   Prop. `abbrev` (reducible) so that (a) `theorem f_thm : f_stmt` lets
   tactics unfold the goal transparently, (b) the linker's direct
   application `f_thm g_closed : f_stmt` unifies without `unfold`
   gymnastics, (c) hypothesis instantiation `h_a x hx` elaborates.

   CRITICALLY: this module imports Defs only, never Proofs — so its
   olean is byte-stable under any proof-body edit anywhere. -/
import Probe.Defs.M
namespace Probe

-- chained lemmas a → b → c
abbrev lemma_a_stmt : Prop := ∀ (x : Int), 0 ≤ x → x + 0 = x ∧ 0 + x = x
abbrev lemma_b_stmt : Prop := ∀ (x : Int), 0 ≤ x → x + 0 + 0 = x
abbrev lemma_c_stmt : Prop := ∀ (x : Int), 0 ≤ x → (x + 0) + (x + 0) = 2 * x

-- broadcast-style lemma (consumed from local context by simp_all)
abbrev size_pos_stmt : Prop := ∀ (t : Tree), 1 ≤ t.size

-- mutual pair (statements are ordinary separate defs; mutuality lives
-- only in the Proofs module)
abbrev even_odd_stmt : Prop := ∀ (n : Nat), isEven n = true → isOdd n = false
abbrev odd_even_stmt : Prop := ∀ (n : Nat), isOdd n = true → isEven n = false

-- generic + [Nonempty]: validates Prop impredicativity and instance
-- binders inside a stmt def (the nonempty.rs bracketing carried over)
abbrev generic_stmt : Prop :=
  ∀ (A : Type) [Nonempty A] (xs : List A), 0 ≤ xs.length

-- exec fn contract: named req/ens shared by the fn's own WP theorem
-- AND callers' WP goals (kills contract drift by construction)
abbrev incr_req (x : Int) : Prop := 0 ≤ x ∧ x < 1000
abbrev incr_ens (x ret : Int) : Prop := ret = x + 1 ∧ ret ≤ 1000

end Probe
