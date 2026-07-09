/- Defs layer: datatypes + spec fns (stand-in for the crate-defs module).
   Mirrors what `--tactus-crate-defs` emits today: inductives, recursive
   spec fns (kernel-checked termination), mutual spec fns. -/
namespace Probe

inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree

def Tree.size : Tree → Nat
  | .leaf => 1
  | .node l r => l.size + r.size

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

end Probe
