import Batteries.Lean.Except
import Lean

initialize Lean.registerTraceClass `Clap.Compiler

/--
`Clap.Compiler.preprocess` reports prime resolution and typeclass instantiation.
-/
initialize Lean.registerTraceClass `Clap.Compiler.preprocess (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.nameResolution (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.numIters (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.unfoldAny (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.unfoldAny.const (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.simplify (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.simplify.exprSizesBeforeSimplify (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.simplify.countHeartbeats (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.beta (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.zeta (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.linearise (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.foldProjs (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.letSome (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.serialise (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.curry (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.sansInterfaceVectors (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.usedConstants (inherited := true)

register_option Clap.Compiler.Debug : Bool := {
  defValue := false
  descr := "Debug mode for the compiler"
}

register_option Clap.Compiler.cimplolIdentity : Bool := {
  defValue := true
  descr := "If false, then reduce underlying definition"
}

initialize Lean.registerTraceClass `Clap.Compiler.Debug

initialize Lean.registerTraceClass `Clap.Compiler.Debug.expressionSizeDelta (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.Debug.revertOnTimeout (inherited := true)

namespace Clap.Compiler.Trace

section

open Lean

variable {m} [Monad m] [MonadLiftT IO m]
             [MonadTrace m] [MonadOptions m]
             [MonadRef m] [AddMessageContext m]

def reportBigSizeDelta (e₁ e₂ : Expr)
                       (descr : String := "") (maxδ : Nat ⊕ Rat := .inr (3/2)) : m Unit := do
  let e₁sz ← e₁.numObjs
  let e₂sz ← e₂.numObjs
  match maxδ with
  | .inl maxδ =>
    let δ := e₂sz - e₁sz
    if δ > maxδ then reportExceeded (.inl δ)
  | .inr maxδ =>
    let δ := (e₂sz : Rat) / e₁sz
    if δ > maxδ then reportExceeded (.inr δ)
  where reportExceeded (esz : Nat ⊕ Rat) : m Unit := do
    trace[Clap.Compiler.Debug.expressionSizeDelta] m!"{descr} (δ = {esz}) (maxδ := {maxδ})"

def withReportSizeDelta (e : Expr) (f : Expr → m Expr)
                        (descr : String := "") (maxδ : Nat ⊕ Rat := .inr (3/2)) : m Expr := do
  let res ← f e
  reportBigSizeDelta e res (descr := descr) (maxδ := maxδ)
  return res

def withReportTimeoutAndRevert [MonadRuntimeException m]
                               (e : Expr) (context : String)
                               (f : Expr → m Expr) : m Expr := do
  let go := f e
  let options ← getOptions
  if options.getBool `trace.Clap.Compiler.Debug.revertOnTimeout
  then tryCatchRuntimeEx go fun _ ↦ do
    trace[Clap.Compiler.Debug.revertOnTimeout] m!"{bombEmoji} Timeout[{context}]"
    return e
  else go

end

open Lean Elab.Term in
def formatExprWith {m : Type _ → Type _} [Monad m]
                   (s : String := "") (res : Except Exception Expr) : m MessageData :=
  return m!"{Except.emoji res} {s}\n{match res with | .error _ => "<Failed>" | .ok res => res}"

end Clap.Compiler.Trace

-- register_simp_attr unfoldStuff

register_simp_attr simpPoseidon

register_simp_attr simpMixS

register_simp_attr simpSynthetic
