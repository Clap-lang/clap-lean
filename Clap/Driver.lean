/-
 call with: `lake exe Driver`
-/

import Lean
import Clap.Compiler.Deep
import Mathlib.Lean.CoreM

import Clap.Compiler.Basic

namespace Clap

@[irreducible]
def eq0 (n : ℕ) : Option Unit :=
  if n == 0 then some () else none

set_option maxRecDepth 1000000
set_option debug.skipKernelTC true

#check List.range_succ

-- attribute [local unfoldStuff] Option.some_bind List.foldlM_append List.foldlM_cons List.foldlM_nil List.range_zero List.range_succ -- pure_bind bind_pure bind_assoc Option.bind_assoc 

attribute [local unfoldStuff] List.reduceRange List.foldlM_cons List.foldlM Option.pure_def

set_option profiler true

def repeatN_inner (p : ℕ) : Option Unit := do
  (List.range 10000).foldlM (init := ()) fun _ n ↦ do
    eq0 n

end Clap


open Lean

def forceHeartbeats {α : Type} {m : Type → Type} [MonadWithReaderOf Core.Context m]
                    (heartBeats : ℕ) : m α → m α :=
  withTheReader Core.Context ({· with maxHeartbeats := heartBeats})

def forcemaxRecDepth {α : Type} {m : Type → Type} [MonadWithReaderOf Core.Context m]
                     (maxRecDepth : ℕ) : m α → m α :=
  withTheReader Core.Context ({· with maxRecDepth := maxRecDepth})

open Lean Meta in
def driver (p : Name) (_decl : Expr) : Elab.Term.TermElabM Unit := do
  let count    := 10000 -- 43 sec, 2721868 kbytes w/ toDeep, 10 sec w/o
--  let count    := 100000 -- 1m30 w/o deep, more than 16 with toDeep min ?
--  let count    := 1000000 -- 33m 9369204 kbytes w/o toDeep
  let zmodTy   := mkApp (mkConst ``ZMod) (mkConst p)
  let unitTy   := mkConst ``Unit
  let mut expr ← mkAppM ``Option.some #[mkConst ``Clap.Spec.Compiler.accept]
  for i in List.range count do
    let zero   ← mkAppOptM ``OfNat.ofNat #[zmodTy, mkNatLit i, none]
    let eq0App ← mkAppOptM ``Clap.Spec.Compiler.eq0 #[(mkConst p), zero]
    expr ← mkAppM ``Bind.bind #[eq0App, mkLambda `_ .default unitTy expr]
--  let _deep ← Clap.toDeep p expr
--  dbg_trace s!"{← ppExpr deep}"
  dbg_trace s!"{←expr.numObjs}"
  dbg_trace s!"{expr.sizeWithoutSharing}"
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
