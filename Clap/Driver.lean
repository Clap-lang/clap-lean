/-
 call with: `lake exe Driver`
-/

import Lean
import Clap.Compiler.Deep
import Mathlib.Lean.CoreM

open Lean

def forceHeartbeats {α : Type} {m : Type → Type} [MonadWithReaderOf Core.Context m]
                    (heartBeats : ℕ) : m α → m α :=
  withTheReader Core.Context ({· with maxHeartbeats := heartBeats})

def forcemaxRecDepth {α : Type} {m : Type → Type} [MonadWithReaderOf Core.Context m]
                     (maxRecDepth : ℕ) : m α → m α :=
  withTheReader Core.Context ({· with maxRecDepth := maxRecDepth})

def driver (p : Name) (decl : Expr) : Elab.Term.TermElabM Unit := do
--  dbg_trace s!"{decl}"
  let _ ← Clap.toDeep p decl
  return ()

unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let declModule := `Clap.BenchCircuit
  let declName := `Clap.BenchCircuit.mainCircuit
  let env ← importModules (loadExts := true)
              #[`Init, `Init.Prelude, `Lean, `Clap.Lang, declModule] {}
  let fileName := ""
  let options : Options := {}
  let ctx : Core.Context := {fileName, options, fileMap := default }
  let state := {env}
  discard <| (Lean.Core.CoreM.toIO · ctx state) do
    forcemaxRecDepth 5000 do
    forceHeartbeats 0 do
      let .some decl := (←getEnv).find? declName | throwError m!"Undeclared constant: {declName}"
      let decl := decl.value!
      (driver `Primes.babybear decl).run'.run'
  return 0
