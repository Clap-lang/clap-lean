import Clap.Test.Compiler.Traverse.Prelude

namespace ExampruSym

namespace NewTraversal

open Clap.Compiler

opaque share : ℕ → Option ℕ

def sigma (x : ℕ) : Option (ℕ) := do
  let x2 ← share (x * x)
  let x4 ← share (x2 * x2)
  some (x4 * x)

def testFoldlM : Option ℕ := do
  let xs ← (List.range 8).foldlM (fun state r ↦ do
    let s0 ← sigma state[0]
    state.set 0 s0
    ) #v[5, 6, 7]
  let x ← xs[0]
  return x

-- set_option trace.Clap.Compile true in
-- set_option Clap.traversalDbg true in
-- set_option trace.Clap.Compile.dbg true in
set_option maxRecDepth 100000 in
#eval runTestByName ``testFoldlM

end NewTraversal

end ExampruSym
