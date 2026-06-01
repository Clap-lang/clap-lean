import Lean

namespace Clap.Compiler

open Lean

structure ConstraintsState where
  constraints : Array Expr := #[]
  deriving Inhabited, Repr

builtin_initialize constraints : EnvExtension ConstraintsState ←
  registerEnvExtension (pure {}) -- (asyncMode := .local)

public def getConstraints : MetaM (Array Expr) := do
  let env ← getEnv
  return (constraints.getState env).constraints

end Clap.Compiler
