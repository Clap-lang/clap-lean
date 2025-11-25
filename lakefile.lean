import Lake

open System Lake DSL

package clap where version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.26.0-rc2"

@[default_target] lean_lib Clap where
  moreLeanArgs :=
    #[
      "-Dlinter.unusedVariables=true",
      "-DautoImplicit=false",
      "-Dpp.unicode.fun=true",
      "-Dpp.proofs=true"
    ]
  leanOptions :=
    #[
      ⟨`linter.unusedVariables, true⟩,
      ⟨`autoImplicit, false⟩
    ]
