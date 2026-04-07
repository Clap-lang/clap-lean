/-
 call with: `lake exe Driver`
-/

import Lean
import Clap.Compiler.Deep
import Mathlib.Lean.CoreM

import Clap.Compiler.Basic

namespace Clap

-- @[irreducible]
-- def eq0 (n : ℕ) : Option Unit :=
--   if n == 0 then some () else none

-- -- set_option maxRecDepth 1000000
-- -- set_option debug.skipKernelTC true

-- -- #check List.range_succ

-- -- attribute [local unfoldStuff] Option.some_bind List.foldlM_append List.foldlM_cons List.foldlM_nil List.range_zero List.range_succ -- pure_bind bind_pure bind_assoc Option.bind_assoc 

-- -- List.reduceRange, List.foldlM_cons, List.foldlM, Option.pure_def
-- -- set_option profiler true

-- -- 10 : 7s
-- -- 100 : 7.5s
-- -- 1000 : 8.1s
-- -- 2000 : 8.4s [size 56005/30014]
-- -- 3000 : 10s [size 84005/45014]
-- -- 4000 : 12s [size 112005/60014]
-- -- 5000 : 14s [size 140005/75014]
-- -- 10000 : 32s [size 280005/150014]
-- -- 20000 : 144s [size 560005/300014]
-- -- 100000 : 

-- -- do a; b; c
-- -- bind a fun _ ↦ bind b fun _ ↦ bind c (return ())

-- -- keyless (a b : F p)
-- -- check₁ (a : F p) → Unit | do let check₁_c := share a; eq0 check₁_c 
-- -- check₂ (b : F p) → Unit | do let check₂_d := share b; eq0 check₂_d

-- def _root_.repeatN_inner (p : ℕ) : Option Unit := do
--   (List.range 100).foldlM (init := ()) fun _ n ↦ do
--     eq0 n


-- def repeatN_inner' (p : ℕ) : Option Unit := do
--   letI n := 30000
--   let x := (List.range n)
--   eq0 x[n - 1]!

end Clap

open Lean

def forceHeartbeats {α : Type} {m : Type → Type} [MonadWithReaderOf Core.Context m]
                    (heartBeats : ℕ) : m α → m α :=
  withTheReader Core.Context ({· with maxHeartbeats := heartBeats})

def forcemaxRecDepth {α : Type} {m : Type → Type} [MonadWithReaderOf Core.Context m]
                     (maxRecDepth : ℕ) : m α → m α :=
  withTheReader Core.Context ({· with maxRecDepth := maxRecDepth})

-- open Lean Meta in
-- def driver (p : Name) (_decl : Expr) : Elab.Term.TermElabM Unit := do
--   let count    := 10000 -- 43 sec, 2721868 kbytes w/ toDeep, 10 sec w/o
-- --  let count    := 100000 -- 1m30 w/o deep, more than 16 with toDeep min ?
-- --  let count    := 1000000 -- 33m 9369204 kbytes w/o toDeep
--   let zmodTy   := mkApp (mkConst ``ZMod) (mkConst p)
--   let unitTy   := mkConst ``Unit
--   let mut expr ← mkAppM ``Option.some #[mkConst ``Clap.Spec.Compiler.accept]
--   for i in List.range count do
--     let zero   ← mkAppOptM ``OfNat.ofNat #[zmodTy, mkNatLit i, none]
--     let eq0App ← mkAppOptM ``Clap.Spec.Compiler.eq0 #[(mkConst p), zero]
--     expr ← mkAppM ``Bind.bind #[eq0App, mkLambda `_ .default unitTy expr]
-- --  let _deep ← Clap.toDeep p expr
-- --  dbg_trace s!"{← ppExpr deep}"
--   dbg_trace s!"{←expr.numObjs}"
--   dbg_trace s!"{expr.sizeWithoutSharing}"
--   return ()

-- attribute [unfoldStuff] List.reduceRange List.foldlM_cons List.foldlM Option.pure_def

set_option trace.Clap.Compiler true

unsafe def main (args : List String) : IO UInt32 := do
  let [file, function, simpset] := args | IO.println s!"usage: main <file> <function> <simpset>;\nargs={args}"; return 1
  let fileComponents := file.splitOn (sep := "/") |>.map Name.mkSimple
  let functionComponents := function.splitOn (sep := ".") |>.map Name.mkSimple
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← importModules (loadExts := true)
              #[`Init, `Init.Prelude, `Lean, `Clap.Lang, `Clap.Driver, `Clap.Test.Compilation.SimpSets,
                Name.fromComponents fileComponents] {}
  let fileName := ""
  let options : Options := {}
  let ctx : Core.Context := {fileName, options, fileMap := default }
  let state := {env}
  discard <| (Lean.Core.CoreM.toIO · ctx state) do
    forcemaxRecDepth 1000000 do
    forceHeartbeats 0 do
      (Clap.Compiler.compileMeta (Name.fromComponents functionComponents) `Primes.bn254 2 {} (Name.mkSimple simpset)).run'.run'
  return 0
