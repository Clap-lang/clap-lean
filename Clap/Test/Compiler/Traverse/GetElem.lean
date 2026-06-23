import Clap.Test.Compiler.Traverse.Prelude

namespace ExampruSym

namespace NewTraversal

open Clap.Compiler

def testSmallSimplifiableIndex : Option ℕ := do
  let x := #v[1,2,3,4,5]
  let y := x[0+1]
  y

set_option trace.Clap.Compile true in
set_option trace.Clap.Compile.dbg true in
#eval runOptionNTestByName ``testSmallSimplifiableIndex

def testBigSimplifiableIndex : Option ℕ := do
  let x := #v[1,2,3,4,5]
  let y := x[0+(1*2)/3+4]
  y

set_option trace.Clap.Compile true in
set_option trace.Clap.Compile.dbg true in
#eval runOptionNTestByName ``testBigSimplifiableIndex

end NewTraversal

end ExampruSym
