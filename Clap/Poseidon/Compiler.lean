import Lean
import Clap.Poseidon.Poseidon

def main : IO Unit := do
  Lean.withImportModules #[{module := `Clap.Poseidon.Poseidon}] {} fun env ↦ do
  _
