import Clap.Compiler.Traverse

instance (priority := high) : Inhabited (Lean.MetaM Lean.Meta.Sym.Simp.Methods) := ⟨pure default⟩

namespace ExampruSym

open Clap.Compiler

opaque F : ℕ → Option ℕ
opaque G : ℕ → Option ℕ
opaque H : ℕ → Option ℕ

open Lean in
def runTest (uncompiledExpr : Expr) (eval : Bool := true) (extraPasses : MetaM Meta.Sym.Simp.Methods := Clap.Compiler.ExampruSym.NewTraversal.Dom.doNothing) := spoon <| do
  let uncompiledTypeExpr ← Meta.inferType uncompiledExpr
  let expectedType := (Option ℕ)

  logInfo m!"Compiling {uncompiledExpr}"
  let (compiled, time) ← Clap.Dbg.timeS (ExampruSym.NewTraversal.Dom.compile uncompiledExpr extraPasses)
  logInfo m!"Compiled to {compiled}"

  let dbgState ← getAndResetDbgState
  logInfo m!"RAW dbg state:\n{←dbgState.pretty}"
  let totalCompileTime := m!"Total compile time: {time}"
  let rulesAppliedTime := sumRuleTime dbgState.ruleHisto
  let rulesSkippedTime := sumRuleTime dbgState.skippedRuleHisto
  let timeSpentInRules := rulesAppliedTime + rulesSkippedTime
  let rulesTotal := m!"Rules[skipped+applied]: {timeSpentInRules}"
  let Δ := time - timeSpentInRules
  logInfo m!"{totalCompileTime}\n{rulesTotal}\nUnaccounted[Δ]: {Δ} | {Δ / time * 100}%"

  if !eval then return compiled

  -- Pretty print (i.e. go back to `Bind.bind`)
  let formatted := (
    ←Lean.Meta.Sym.simp compiled (←SymSets.General.compilerBindEqBind)
  ).getResultExpr compiled
  let defEq ← Lean.Meta.isDefEq uncompiledExpr compiled
  if defEq then
    Lean.logInfo m!"Compiled expression defEq"
  else
    Lean.logInfo m!"Compiled expression not defEq"

  let uncompiledEvaluated ← Lean.Core.tryCatchRuntimeEx
    do
      let uncompiledEvaluated ← (unsafe Lean.Meta.evalExpr expectedType uncompiledTypeExpr uncompiledExpr).run
      return uncompiledEvaluated.1
    fun exception => do
      Lean.logInfo m!"Failed to evaluate uncompiled test expression with given type"
      throwError m!"{exception.toMessageData}"

  let compiledEvaluated ← Lean.Core.tryCatchRuntimeEx
    do
      let compiledEvaluated ← (unsafe Lean.Meta.evalExpr expectedType uncompiledTypeExpr compiled).run
      return compiledEvaluated.1
    fun exception => do
      Lean.logInfo m!"Failed to evaluate compiled test expression with given type"
      throwError m!"{exception.toMessageData}"

  if uncompiledEvaluated == compiledEvaluated then
    Lean.logInfo m!"Compiled expression evalutes equal: {uncompiledEvaluated} == {compiledEvaluated}"
  else
    Lean.logError m!"Compiled expression evaluates unequal\nUncompiled: {uncompiledEvaluated} ≠ Compiled: {compiledEvaluated}"
  return formatted

open Lean in
def runTestByName (testName : Name) (eval : Bool := true) (extraPasses : MetaM Meta.Sym.Simp.Methods := Clap.Compiler.ExampruSym.NewTraversal.Dom.doNothing) : MetaM Unit := do
  let .some constantInfo := (←getEnv).find? testName | throwError m!"Undeclared constant:\n{testName}"
  runTest constantInfo.value! eval extraPasses

end ExampruSym
