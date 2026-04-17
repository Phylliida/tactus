import Lake
open Lake DSL

package tactus where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib TactusCheck where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.25.0"
