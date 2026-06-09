import Clap.Compiler.Traverse

namespace ExampruSym

open Clap.Compiler

-- TODO why are we using these when eval gets rid of them, and bEq treats them as equal?
opaque F : ℕ → Option ℕ
opaque G : ℕ → Option ℕ
opaque H : ℕ → Option ℕ

def testSymSet := (SymSets.Vector.mapM_singlePass_pre)


def runTest (name: Lean.Name) := spoon <| do
  let uncompiled := ((←Lean.MonadEnv.getEnv).find? name).get!
  let uncompiledExpr := uncompiled.value!
  let uncompiledTypeExpr := uncompiled.type

  let expectedType := (Option ℕ)

  let compiled ← compileExample name (←testSymSet)
  -- Pretty print (i.e. go back to `Bind.bind`)
  let formatted := (
    ←Lean.Meta.Sym.simp compiled (←SymSets.General.compilerBindEqBind)
  ).getResultExpr compiled
  let defEq ← Lean.Meta.isDefEq uncompiled.value! compiled
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
    Lean.logInfo m!"Compiled expression evaluates unequal"
    Lean.logInfo m!"Uncompiled: {uncompiledEvaluated} ≠ Compiled: {compiledEvaluated}"
  return formatted

end ExampruSym
