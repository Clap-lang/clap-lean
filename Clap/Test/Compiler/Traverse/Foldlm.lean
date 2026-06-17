import Clap.Test.Compiler.Traverse.Prelude

namespace ExampruSym

namespace NewTraversal

open Clap.Compiler

opaque share : ℕ → Option ℕ

-- abbrev sigma (x : ℕ) : Option (ℕ) := do
--   let x2 ← share (x * x)
--   let x4 ← share (x2 * x2)
--   some (x4 * x)

def sigma_unshared (x : ℕ) : Option (ℕ) := do
  let x2 ← some (x + x)
  let x4 ← some (x2 + x2)
  some (x4 + x)

def testFoldlM : Option ℕ := do
  let xs ← (List.range 32).foldlM (fun state r ↦ do
    let s0 ← sigma_unshared state[0]
    state.set 0 s0
    ) #v[0, 1, 2]
  let x ← xs[0]
  return x

-- set_option trace.Clap.Compile true in
-- -- set_option Clap.traversalDbg true in
-- set_option trace.Clap.Compile.dbg true in
-- set_option pp.exprSizes true in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
#eval runTestByName ``testFoldlM false

end NewTraversal

end ExampruSym
