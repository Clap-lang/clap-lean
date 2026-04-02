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

open Lean Meta in
def driver (p : Name) (_decl : Expr) : Elab.Term.TermElabM Unit := do
  let count    := 10000 -- quite fast
--  let count    := 100000 -- more than 8 min ?
  let zmodTy   := mkApp (mkConst ``ZMod) (mkConst p)
  let unitTy   := mkConst ``Unit
  let mut expr ← mkAppM ``Option.some #[mkConst ``Clap.Spec.Compiler.accept]
  for i in List.range count do
    let zero   ← mkAppOptM ``OfNat.ofNat #[zmodTy, mkNatLit i, none]
    let eq0App ← mkAppOptM ``Clap.Spec.Compiler.eq0 #[(mkConst p), zero]
    expr ← mkAppM ``Bind.bind #[eq0App, mkLambda `_ .default unitTy expr]
  let _deep ← Clap.toDeep p expr
--  dbg_trace s!"{← ppExpr deep}"
  dbg_trace s!"deep"
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
