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

initialize Lean.registerTraceClass `Clap.Compiler.reduce.dsimp (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.beta (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.zeta (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.linearise (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.foldProjs (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.reduce.letSome (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.serialise (inherited := true)

initialize Lean.registerTraceClass `Clap.Compiler.curry (inherited := true)

namespace Clap.Compiler.Trace

open Lean Elab.Term in
def formatExprWith {m : Type _ → Type _} [Monad m]
                   (s : String) (res : Except Exception Expr) : m MessageData :=
  return m!"{exceptEmoji res} {s}\n{match res with | .error _ => "<Failed>" | .ok res => res}"

end Clap.Compiler.Trace
