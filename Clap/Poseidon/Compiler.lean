import Lean
import Clap.Poseidon.Poseidon
import Mathlib.Lean.CoreM

open Lean in
def forceHeartbeats {α : Type} {m : Type → Type} [MonadWithReaderOf Core.Context m]
                    (heartBeats : ℕ) : m α → m α :=
  withTheReader Core.Context ({· with maxHeartbeats := heartBeats})

open Lean in
def forcemaxRecDepth {α : Type} {m : Type → Type} [MonadWithReaderOf Core.Context m]
                     (maxRecDepth : ℕ) : m α → m α :=
  withTheReader Core.Context ({· with maxRecDepth := maxRecDepth})

open Lean in
unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← importModules (loadExts := true)
              #[`Init, `Init.Prelude, `Lean, `Clap.Poseidon.Poseidon, `Clap.Primes] {}
  let fileName := ""
  let options : Options := {}
  let ctx : Core.Context := {fileName, options, fileMap := default }
  let state := {env}
  let _ ← (Lean.Core.CoreM.toIO · ctx state) do
    forcemaxRecDepth 5000 do forceHeartbeats 0 do
      (Clap.Compiler.compileMeta `Poseidon.Test.testPoseidon `Primes.bn254 50).run'.run'
  return 0
  -- CoreM.withImportModules #[] do
  --   (Clap.Compiler.compileMeta `Poseidon.Test.testPoseidon `Primes.bn254 50).run'.run'
