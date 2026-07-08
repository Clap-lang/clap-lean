import Lean

@[simp]
theorem Vector.range_one : Vector.range 1 = #v[0] := rfl

namespace Clap

initialize Lean.registerTraceClass `Clap.Preprocessor

initialize Lean.registerTraceClass `Clap.Preprocessor.addLambdas (inherited := true)

end Clap
