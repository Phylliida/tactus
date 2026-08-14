import Lake
open Lake DSL

package tactus where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib TactusCheck where
  srcDir := "."

lean_lib TactusTutorialHelpers where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.25.0"

-- nla-15: the verified nonlinear_arith tactic (z3's nlsat ported;
-- kernel-checked traces). Same lean+mathlib pin as this package.
require LeanNonlinearArith from "../../lean-nonlinear-arith"
