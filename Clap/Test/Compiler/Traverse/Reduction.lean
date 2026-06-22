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

def testBetaReductionManyArgsSplit : Option ℕ := do
  let a := (λ (a b c d e f g h i j k l m n o p q r s t u v w x y z: ℕ) => Option.some (a - b + c - d + e - f + g - h + i + j + k + l - m - n - o - p + q + r + s - t - u + v + w - x + y + z)) 29837456 78 45 34 90 67
  let a := a 34 23 67 90 78 45 34 67
  let a := a 89 23 76 89 456 43 89 45
  let a ← a 67 45 65 67
  return a

def testBetaReductionManyArgsInline : Option ℕ := do
  let a ← (λ (a b c d e f g h i j k l m n o p q r s t u v w x y z: ℕ) => Option.some (a - b + c - d + e - f + g - h + i + j + k + l - m - n - o - p + q + r + s - t - u + v + w - x + y + z)) 29837456 78 45 34 90 67 34 23 67 90 78 45 34 67 89 23 76 89 456 43 89 45 67 45 65 67
  return a

-- set_option trace.Clap.Compile true in
-- set_option Clap.traversalDbg true in
-- set_option trace.Clap.Compile.dbg true in
-- set_option maxRecDepth 100000 in
#eval runTestByName ``testBetaReductionOneArg
#eval runTestByName ``testBetaReductionTwoArgs
#eval runTestByName ``testBetaReductionManyArgsSplit
#eval runTestByName ``testBetaReductionManyArgsInline

end NewTraversal

end ExampruSym
