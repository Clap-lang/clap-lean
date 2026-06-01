import Lean

namespace Clap.Compiler

open Lean

structure ConstraintsState where
  constraints : Array Expr := #[]
  deriving Inhabited, Repr

initialize constraints : EnvExtension ConstraintsState ←
  registerEnvExtension (pure {}) -- (asyncMode := .local)

def addConstraint (c : Expr) : MetaM Unit := do
  modifyEnv fun e ↦
    constraints.modifyState e fun σ ↦
      ⟨σ.constraints.push c⟩

def getConstraints : MetaM (Array Expr) := do
  let env ← getEnv
  return (constraints.getState env).constraints

end Clap.Compiler
