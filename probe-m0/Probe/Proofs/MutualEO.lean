import Probe.Stmts.M
namespace Probe

/- Mutual SCC in ONE Proofs module. Within-SCC references are DIRECT
   (same mutual block — no hypotheses needed inside the SCC); only
   external callees would arrive as hypotheses. Parameterized form
   (not stmt-name-as-type) because termination_by needs real binders
   — the Link module bridges to the stmt-typed closed forms. -/
mutual
  theorem even_odd_thm (n : Nat) : isEven n = true → isOdd n = false := by
    match n with
    | 0 => intro _; rfl
    | k + 1 => exact odd_even_thm k
  termination_by n

  theorem odd_even_thm (n : Nat) : isOdd n = true → isEven n = false := by
    match n with
    | 0 => intro h; exact absurd h (by decide)
    | k + 1 => exact even_odd_thm k
  termination_by n
end

end Probe
