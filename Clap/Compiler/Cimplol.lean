import Lean

import Clap.Compiler.Basic
import Clap.Compiler.Wheels

namespace Clap.Compiler

open Lean in
elab "cimplol" "(" f:ident ")" : term => do
  let [f] ← realizeGlobalConst f | throwError m!"Undeclared constant:\n{f}"
  let isIdentity := (←getOptions).getBool `Clap.Compiler.cimplolIdentity
  if isIdentity then
    match (←getEnv).find? f with
    | .none => throwError m!"Undeclared constant:\n{f}"
    | .some f => return f.value!
  let (compiledF, _) ← compileMeta (declName := f) (p := sorry) (n := sorry) (σ := {}) (arg := sorry)
  return compiledF

end Clap.Compiler
