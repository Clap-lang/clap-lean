-- import Lean

-- namespace Clap.Compiler

-- open Lean

-- structure ConstraintsState where
--   constraints : Array Expr := #[]
--   deriving Inhabited, Repr

-- initialize constraints : EnvExtension ConstraintsState ←
--   registerEnvExtension (pure {}) -- (asyncMode := .local)

-- def addConstraint (c : Expr) : MetaM Unit := do
--   modifyEnv fun e ↦
--     constraints.modifyState e fun σ ↦
--       ⟨σ.constraints.push c⟩

-- def getConstraints : MetaM (Array Expr) := do
--   let env ← getEnv
--   return (constraints.getState env).constraints

-- initialize counter : EnvExtension Nat ←
--   registerEnvExtension (pure 0)

-- def bump : MetaM Unit := do
--   modifyEnv fun e ↦ counter.modifyState e Nat.succ

-- def getCounter : MetaM Nat := do
--   let env ← getEnv
--   return counter.getState env

-- def resetCounter : MetaM Unit := do
--   modifyEnv fun e ↦ counter.modifyState e fun _ ↦ 0

-- structure TraversalDbgState where
--   numDown : Nat
--   numUp : Nat
--   cumulativeSimpTimeDown : Float
--   cumulativeSimpTimeUp : Float
--   inlinedHisto : Std.HashMap Expr Nat
--   ruleHisto : Std.HashMap String (Nat × Float)
--   skippedRuleHisto : Std.HashMap String (Nat × Float)
--   deriving Inhabited

-- def sumRuleTime (times: Std.HashMap String (Nat × Float)) : Float :=
--   (times.toList.map (λ (_, (_, time)) => time)).sum

-- def TraversalDbgState.pretty (σ : TraversalDbgState) : MetaM Format := do
--   let text := String.intercalate "\n" ([
--     f!"numDown := {σ.numDown}",
--     f!"numUp := {σ.numUp}",
--     f!"downTime := {σ.cumulativeSimpTimeDown}",
--     f!"upTime := {σ.cumulativeSimpTimeUp}",
--     f!"histoInlined := {repr (←σ.inlinedHisto.toArray.mapM fun (k, v) ↦ do return ((←PrettyPrinter.ppExpr k).pretty, v))}",
--     f!"histoRules := {repr σ.ruleHisto}",
--     f!"totalStepTime := {sumRuleTime σ.ruleHisto}",
--     f!"histoSkippedRules := {repr σ.skippedRuleHisto}",
--     f!"totalSkipTime := {sumRuleTime σ.skippedRuleHisto}",
--   ].map Format.pretty)
--   return f!"{text}"

-- initialize traversalDbg : EnvExtension TraversalDbgState ←
--   registerEnvExtension (pure default)

-- def getDbgState : MetaM TraversalDbgState :=
--   return traversalDbg.getState (←getEnv)

-- def modifyDbgState (f : TraversalDbgState → TraversalDbgState) : MetaM Unit :=
--   modifyEnv (traversalDbg.modifyState (f := f))

-- def resetDbgState : MetaM Unit :=
--   modifyDbgState (fun _ ↦ default)

-- def getAndResetDbgState : MetaM TraversalDbgState := do
--   let σ ← getDbgState
--   resetDbgState
--   return σ

-- def getDbgHisto : MetaM (Std.HashMap Expr Nat) :=
--   TraversalDbgState.inlinedHisto <$> getDbgState

-- def recordDbgHisto (e : Expr) :=
--   modifyDbgState fun σ ↦
--     {σ with inlinedHisto :=
--       if σ.inlinedHisto.contains e
--       then σ.inlinedHisto.modify e Nat.succ
--       else σ.inlinedHisto.insert e 1}

-- def recordRuleDbg (e : String) (timeS : Float := 0.0) :=
--   modifyDbgState fun σ ↦
--     {σ with ruleHisto :=
--       if σ.ruleHisto.contains e
--       then σ.ruleHisto.modify e (fun (n, time) ↦ (Nat.succ n, time + timeS))
--       else σ.ruleHisto.insert e (1, timeS)}

-- def recordSkippedRuleDbg (e : String) (timeS : Float := 0.0) :=
--   modifyDbgState fun σ ↦
--     {σ with skippedRuleHisto :=
--       if σ.skippedRuleHisto.contains e
--       then σ.skippedRuleHisto.modify e (fun (n, time) ↦ (Nat.succ n, time + timeS))
--       else σ.skippedRuleHisto.insert e (1, timeS)}

-- end Clap.Compiler
