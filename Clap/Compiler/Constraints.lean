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

initialize counter : EnvExtension Nat ←
  registerEnvExtension (pure 0)

def bump : MetaM Unit := do
  modifyEnv fun e ↦ counter.modifyState e Nat.succ

def getCounter : MetaM Nat := do
  let env ← getEnv
  return counter.getState env

def resetCounter : MetaM Unit := do
  modifyEnv fun e ↦ counter.modifyState e fun _ ↦ 0

structure TraversalDbgState where
  numDown : Nat
  numUp : Nat
  cumulativeSimpTime : Float
  deriving Inhabited, Repr

initialize traversalDbg : EnvExtension TraversalDbgState ←
  registerEnvExtension (pure default)

def getDbgState : MetaM TraversalDbgState :=
  return traversalDbg.getState (←getEnv)

def modifyDbgState (f : TraversalDbgState → TraversalDbgState) : MetaM Unit :=
  modifyEnv (traversalDbg.modifyState (f := f))

def resetDbgState : MetaM Unit :=
  modifyDbgState (fun _ ↦ default)

def getAndResetDbgState : MetaM TraversalDbgState := do
  let σ ← getDbgState
  resetDbgState
  return σ

end Clap.Compiler
