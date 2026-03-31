import Lake

open System Lake DSL

package clap where version := v!"0.1.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"v4.29.0-rc6"

@[default_target] lean_lib Clap

lean_lib R1Serialize

lean_exe Milestone where root := `Clap.Milestone

lean_exe Compiler where
  root := `Clap.Poseidon.Compiler
  supportInterpreter := true
  leanOptions := #[⟨`maxHeartbeats, 0⟩]
