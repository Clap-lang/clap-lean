import Qq

import Clap.Lang

import Clap.eDSLState.Wheels

import Lean

open Lean Meta Qq

namespace Clap

namespace Preprocessor

/--
WIP:
- Currently, we handle only `ZMod p`
- Of course, we need to allow arbitrary collections made of `F p`s
-/
def isCircuitArgument (e : Expr) : Bool :=
  let e := e.getAppFn
  e.isConstOf ``ZMod

def prefixLam (p subst e : Expr) : MetaM Expr := do
  let lam := mkAppN (.const `Clap.Edsl.lam []) #[mkNatLit 57]
  let e ← Meta.transform e (
    pre := fun e ↦ do
      let_expr Clap.Exp.c _ _ x := e | return .continue
      if x != subst then return .continue
      return .done (mkAppN (.const ``Clap.Exp.v []) #[mkNatLit 57, q(Nat), .bvar 0])
  )
  let cont := .lam `ser (.const ``Nat []) e .default
  trace[Clap.Preprocessor.addLambdas] m!"Arg:\n{subst}\n{e}\n==>\n{e}"
  mkAppM ``Bind.bind #[lam, cont]

def addLambdas (p : Expr) (name : Name) : MetaM Expr := do
  let name ← realizeGlobalConstNoOverloadCore name
  trace[Clap.Preprocessor.addLambdas] m!"Adding lambdas in: {name}"
  let circuit : Expr := (←getEnv).find? name |>.get!.value!
  lambdaTelescope circuit fun args body ↦ do
    let (circuitInputs, parameters) ← args.toList.partitionM fun e ↦ do
      return isCircuitArgument (←e.fvarId!.getType)
    trace[Clap.Preprocessor.addLambdas] m!"Circuit inputs: {circuitInputs}\nParameters: {parameters}"
    let circuit ← circuitInputs.foldrM (init := body) (prefixLam (mkNatLit 57))
    let res ← mkLambdaFVars parameters.toArray circuit
    trace[Clap.Preprocessor.addLambdas] m!"Result:\n{res}"
    logInfo m!"Result:\n{res}"
    return res

end Preprocessor

end Clap
