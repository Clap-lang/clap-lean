import Clap.Compiler.Traverse

namespace ExampruSym

open Clap.Compiler

opaque F : ℕ → Option ℕ
opaque G : ℕ → Option ℕ
opaque H : ℕ → Option ℕ

def testSymSet :=
  -- ExampruSym.NewTraversal.Dom.flattenBinds_pre
  -- SymSets.Vector.unwrap_s
  -- ExampruSym.NewTraversal.Dom.flattenBindsAny_pre
  -- ∪ ExampruSym.NewTraversal.Dom.bindPureMany_pre
  -- ∪ Clap.Compiler.ExampruSym.NewTraversal.Dom.strategiaMagna
  -- ∪
  SymSets.General.optionPureApply
  -- ∪ SymSets.Vector.foldlM_stagger_post
  ∪ SymSets.Vector.unfold_generic_collection_functions_pre
  -- ∪ SymSets.Vector.foldlM_post
  ∪ SymSets.General.beta
  ∪ SymSets.General.zeta
  ∪ SymSets.List.range
  ∪ Clap.SymSets.General.ground

open Lean in
def runTest (uncompiledExpr : Expr) (eval : Bool := true)
            (isUsingTopLevelStrategy : Bool := false) := spoon <| do
  let uncompiledTypeExpr ← Meta.inferType uncompiledExpr
  let expectedType := (Option ℕ)

  let time ← IO.monoMsNow
  logInfo m!"Compiling {uncompiledExpr}"
  let compiled ←
    if isUsingTopLevelStrategy
    then ExampruSym.NewTraversal.Dom.compilaCumStrategiaMagna uncompiledExpr (←testSymSet)
    else compileJustSym uncompiledExpr (←testSymSet)
  Clap.Dbg.timeSince time "Compilation took:"
  logInfo m!"Compiled to {compiled}"

  if !eval then return compiled

  let dbgState ← getAndResetDbgState
  logInfo m!"{←dbgState.pretty}"
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
def runTestByName (testName : Name) (eval : Bool := true) (isUsingTopLevelStrategy : Bool := false) : MetaM Unit := do
  let .some constantInfo := (←getEnv).find? testName | throwError m!"Undeclared constant:\n{testName}"
  runTest constantInfo.value! eval isUsingTopLevelStrategy

end ExampruSym
