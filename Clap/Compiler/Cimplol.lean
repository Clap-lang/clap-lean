import Lean

import Clap.Compiler.Basic
import Clap.Compiler.Wheels

namespace Clap.Compiler

open Lean in
elab "cimplol" "(" f:ident ", " p:ident ", " simpset:ident ")" : term => do
  let [f] ← realizeGlobalConst f | throwError m!"Undeclared constant:\n{f}"
  trace[Clap.Compiler.preprocess] m!"Resolved into: {f}"
  let isIdentity := (←getOptions).getBool `Clap.Compiler.cimplolIdentity
  trace[Clap.Compiler.preprocess] m!"Identity: {isIdentity}"
  if isIdentity then
    match (←getEnv).find? f with
    | .none => throwError m!"Undeclared constant:\n{f}"
    | .some f => return f.value!
  trace[Clap.Compiler.preprocess] m!"declName := {f}\np := {p.getId}\nn := 2048\narg := {simpset.getId}"
  let (compiledF, _) ←
    Meta.withErasedFVars #[
      (←getLCtx).findFromUserName? (
        f.updateLast fun name ↦ String.intercalate "_" (name.splitOn "_").dropLast
      ) |>.get!.fvarId
    ] do
      compileMeta (declName := f)
                  (p := p.getId)
                  (n := 2048)
                  (σ := {})
                  (arg := simpset.getId)
  return compiledF

end Clap.Compiler
