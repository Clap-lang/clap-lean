import Lake

open System Lake DSL

package clap where
  version := v!"0.1.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"v4.31.0-rc1"

@[default_target] lean_lib Clap where leanOptions := #[⟨`linter.unusedVariables, true⟩, ⟨`autoImplicit, false⟩]

lean_lib R1Serialize where
  leanOptions := #[
    ⟨`linter.unusedVariables, true⟩, ⟨`autoImplicit, false⟩
  ]
  buildType := .relWithDebInfo

lean_exe Milestone where root := `Clap.Milestone
