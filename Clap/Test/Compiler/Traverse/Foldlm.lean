import Lean
import Clap.Test.Compiler.Traverse.Prelude
import Clap.Compiler.Wheels

namespace ExampruSym

namespace NewTraversal

open Clap.Compiler

opaque share : ℕ → Option ℕ

def sigma (x : ℕ) : Option (ℕ) := do
  let x2 ← share (x * x)
  let x4 ← share (x2 * x2)
  some (x4 * x)

-- | `f x → some x fun X ↦` |
-- |   `y X` |
-- | `f x >>= y = X` |

abbrev sigma_unshared (x : ℕ) : Option (ℕ) := do
  let x2 ← some (x + x)
  let x4 ← some (x2 + x2)
  -- let x8 ← some (x4 + x4)
  some (x4 + x)


/--
`sym_simp`
[n = 0 | 0.002266s,
 n = 1 | 0.002572s,
 n = 2 | 0.002991s,
 n = 3 | 0.002793s,
 n = 4 | 0.003781s,
 n = 5 | 0.006534s,
 n = 6 | 0.022153s,
 n = 7 | 0.089189s,
 n = 8 | 0.517019s,
 n = 9 | 2.854253s,
 n = 10 | 16.538841s]
-/
def testFoldlM (k : ℕ) : Option ℕ := do
  let xs ← (List.range k).foldlM (fun state r ↦ do
    let s0 ← sigma_unshared state[0]
    state.set 0 s0
    ) #v[0, 1, 2]
  let x ← xs[0]
  return x

def eq_def := sigma_unshared.eq_def
#check Lean.Meta.Sym.mkLambdaFVarsS
-- set_option trace.Clap.Compile.simp.consiliumMagnum true in
-- set_option trace.Clap.Compile.simp.proc.vector_foldlM_stagger true in
-- set_option Clap.traversalDbg true in
-- set_option trace.Clap.Compile.dbg true in
-- -- set_option trace.Clap.Compile.simp.proc.beta true in
-- set_option maxRecDepth 100000 in
-- set_option maxHeartbeats 0 in
-- #eval runOptionNTestByName ``testFoldlM (extraPasses := mkMethods #[
--   (``eq_def, .Pre)
-- ] (atMostOnce := false))

-- THE PLAN
-- use sigma unshared - done
-- write a simproc that takes a list of simprocs and checks whether it itself has been run once from the debug state - done
-- attempts to run these simprocs only if it hasn't - done
-- reset its log in the debug state at the end of each consiliumMagnum iteration - done
-- rejoice - todo

open Lean Meta Elab Tactic

def bench_sym : Lean.MetaM Unit := do
  let rewrite ← Sym.mkSimprocFor #[
    ``testFoldlM.eq_def,
    ``sigma_unshared.eq_def,
    ``bind_assoc,
    ``Option.bind_eq_bind,
    ``Option.bind_some,
    ``List.range.eq_def,
    ``List.range.loop.eq_def,
    ``List.foldlM_cons,
    ``Vector.getElem_mk,
    ``List.getElem_toArray,
    ``List.getElem_cons_zero,
    ``Vector.set_mk,
    ``List.set_toArray,
    ``List.set_cons_zero,
    ``List.foldlM_nil,
    ``Option.pure_def,
    ``Option.bind_fun_some
  ]
  let methods : Sym.Simp.Methods := {
    pre  := Sym.Simp.simpControl
    post := Sym.Simp.evalGround >> rewrite
  }
  let inputSizes : Array Nat := Array.range 11
  let results ← inputSizes.mapM fun inputSize ↦ do
    Sym.SymM.run do
      let expr ← Clap.Compiler.Simp.preprocessExpr
        (((←getEnv).find? ``testFoldlM).get!.value!.beta #[mkNatLit inputSize])
      let (_, time) ← Clap.Dbg.timeS (Sym.simp expr methods)
      return time
      -- logInfo m!"Sym.simp took: {time}s"
      -- logInfo m!"res: {res.getResultExpr expr}"
  let results := results.zip inputSizes
  let results :=
    results.map fun (time, n) ↦ s!"n = {n} | {time}s"
  logInfo m!"{results}"

-- set_option maxHeartbeats 0 in
-- #eval bench

elab "sym_simp" "[" declNames:ident,* "]" : tactic => do
  let rewrite ← Sym.mkSimprocFor (← declNames.getElems.mapM fun s => realizeGlobalConstNoOverload s.raw) Sym.Simp.dischargeSimpSelf
  let methods : Sym.Simp.Methods := {
    pre  := Sym.Simp.simpControl
    post := Sym.Simp.evalGround >> rewrite
  }
  liftMetaTactic1 fun mvarId => Sym.SymM.run do
    let mvarId ← Sym.preprocessMVar mvarId
    let (res, time) ← Clap.Dbg.timeS (Sym.simpGoal mvarId methods)
    logInfo m!"Sym.simp took: {time}s"
    res.toOption

-- 1 = 0.002309s
-- 2 = 0.003176s
-- 4 = 0.004275s
-- 6 = 0.018588s
-- 8 = 0.421613s
-- 12 = 
-- set_option maxHeartbeats 0 in
example : testFoldlM = testFoldlM := by
  sym_simp [
    testFoldlM.eq_def,
    sigma_unshared.eq_def,
    bind_assoc,
    Option.bind_eq_bind,
    Option.bind_some,
    List.range.eq_def,
    List.range.loop.eq_def,
    List.foldlM_cons,
    Vector.getElem_mk,
    List.getElem_toArray,
    List.getElem_cons_zero,
    Vector.set_mk,
    List.set_toArray,
    List.set_cons_zero,
    List.foldlM_nil,
    Option.pure_def,
    Option.bind_fun_some
  ]

end NewTraversal

end ExampruSym
