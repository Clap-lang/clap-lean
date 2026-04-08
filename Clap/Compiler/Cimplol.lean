import Lean

import Clap.Compiler.Basic
import Clap.Compiler.Wheels

namespace Clap.Compiler

open Lean

private def originalIdentifier (ident : Name) : Name := 
  ident.updateLast fun name ↦ String.intercalate "_" (name.splitOn "_").dropLast

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
    -- Lean assumes that `def f (n : ℕ) : α := ?_` is recursive and injects
    -- `f : ℕ → α` as a free variable for `?_`, which one has to account for.
    Meta.withErasedFVars #[
      (←getLCtx).findFromUserName? (originalIdentifier f) |>.get!.fvarId
    ] do compileMeta (declName := f)
                     (p := p.getId)
                     (n := 2048)
                     (σ := {})
                     (arg := simpset.getId)
  return compiledF

end Clap.Compiler
