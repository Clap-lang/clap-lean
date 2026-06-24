import Clap.Compiler.Traverse

instance (priority := high) : Inhabited (Lean.MetaM Lean.Meta.Sym.Simp.Methods) := ⟨pure default⟩

namespace ExampruSym

open Clap.Compiler

opaque F : ℕ → Option ℕ
opaque G : ℕ → Option ℕ
opaque H : ℕ → Option ℕ

open Lean in
def runTest
  (uncompiledExpr : Expr)
  (eval : Bool := true)
  (extraPasses : MetaM Meta.Sym.Simp.Methods := doNothing)
  (expectedType: Type := Option ℕ)
  (compare : Option (expectedType → expectedType → Bool) := .none)
  (print : expectedType → String)
:= spoon <| do
  let uncompiledTypeExpr ← Meta.inferType uncompiledExpr

  logInfo m!"Compiling {uncompiledExpr}"
  let (compiled, time) ← Clap.Dbg.timeS (compile uncompiledExpr extraPasses)
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
    ←Lean.Meta.Sym.simp compiled (←General.compilerBindEqBind)
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

  let .some compare := compare | return formatted
  if compare uncompiledEvaluated compiledEvaluated then
    Lean.logInfo m!"Compiled expression evalutes equal: {print uncompiledEvaluated} == {print compiledEvaluated}"
  else
    Lean.logError m!"Compiled expression evaluates unequal\nUncompiled: {print uncompiledEvaluated} ≠ Compiled: {print compiledEvaluated}"
  return formatted

open Lean in
def runTestByName
  (testName : Name)
  (eval : Bool := true)
  (extraPasses : MetaM Meta.Sym.Simp.Methods := doNothing)
  (expectedType: Type := Option ℕ)
  (compare : Option (expectedType → expectedType → Bool) := .none)
  (print : expectedType → String := λ _ => s!"<<No print function provided>>")
: MetaM Unit := do
  let .some constantInfo := (←getEnv).find? testName | throwError m!"Undeclared constant:\n{testName}"
  runTest constantInfo.value! eval extraPasses expectedType compare print

open Lean in
def runOptionNTestByName
  (testName : Name)
  (eval : Bool := true)
  (extraPasses : MetaM Meta.Sym.Simp.Methods := doNothing)
: MetaM Unit :=
  runTestByName testName eval extraPasses (Option ℕ) (λ x y: Option ℕ => x == y) (λ x => s!"{x}")

end ExampruSym
