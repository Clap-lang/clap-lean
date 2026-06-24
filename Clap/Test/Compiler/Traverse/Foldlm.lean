import Lean
import Clap.Test.Compiler.Traverse.Prelude

namespace ExampruSym

namespace NewTraversal

open Clap.Compiler

opaque share : ℕ → Option ℕ

def sigma (x : ℕ) : Option (ℕ) := do
  let x2 ← share (x * x)
  let x4 ← share (x2 * x2)
  some (x4 * x)

def sigma_unshared (x : ℕ) : Option (ℕ) := do
  let x2 ← some (x + x)
  let x4 ← some (x2 + x2)
  -- let x8 ← some (x4 + x4)
  some (x4 + x)

def testFoldlM : Option ℕ := do
  let xs ← (List.range 8).foldlM (fun state r ↦ do
    let s0 ← sigma_unshared state[0]
    state.set 0 s0
    ) #v[0, 1, 2]
  let x ← xs[0]
  return x

def eq_def := sigma_unshared.eq_def

-- set_option trace.Clap.Compile.simp.consiliumMagnum true in
-- set_option trace.Clap.Compile.simp.proc.vector_foldlM_stagger true in
-- set_option Clap.traversalDbg true in
set_option trace.Clap.Compile.dbg true in
-- set_option trace.Clap.Compile.simp.proc.beta true in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
#eval runOptionNTestByName ``testFoldlM (extraPasses := mkMethods #[
  (``eq_def, .Pre)
] (atMostOnce := false))


-- THE PLAN
-- use sigma unshared - done
-- write a simproc that takes a list of simprocs and checks whether it itself has been run once from the debug state - done
-- attempts to run these simprocs only if it hasn't - done
-- reset its log in the debug state at the end of each consiliumMagnum iteration - done
-- rejoice - todo



open Lean Meta Elab Tactic

elab "sym_simp" "[" declNames:ident,* "]" : tactic => do
  let rewrite ← Sym.mkSimprocFor (← declNames.getElems.mapM fun s => realizeGlobalConstNoOverload s.raw) Sym.Simp.dischargeSimpSelf
  let methods : Sym.Simp.Methods := {
    pre  := Sym.Simp.simpControl
    post := Sym.Simp.evalGround >> rewrite
  }
  liftMetaTactic1 fun mvarId => Sym.SymM.run do
    let mvarId ← Sym.preprocessMVar mvarId
    (← Sym.simpGoal mvarId methods).toOption

example : testFoldlM = sorry := by
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
