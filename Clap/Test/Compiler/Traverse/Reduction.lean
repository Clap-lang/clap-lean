import Clap.Test.Compiler.Traverse.Prelude

namespace ExampruSym

namespace NewTraversal

open Clap.Compiler

def testBetaReductionOneArg : Option ℕ := do
  let a ← ((λ x: ℕ => (.some x)) 5)
  return a

def testBetaReductionTwoArgs : Option ℕ := do
  let a ← (λ x y => .some (x - y)) 1 2
  return a


-- set_option trace.Clap.Compile true in
-- set_option Clap.traversalDbg true in
-- set_option trace.Clap.Compile.dbg true in
-- set_option maxRecDepth 100000 in
#eval runTestByName ``testBetaReductionOneArg
#eval runTestByName ``testBetaReductionTwoArgs

end NewTraversal

end ExampruSym
