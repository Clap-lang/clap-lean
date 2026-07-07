import Lean

namespace Clap

initialize Lean.registerTraceClass `Clap.Preprocessor

initialize Lean.registerTraceClass `Clap.Preprocessor.addLambdas (inherited := true)

end Clap
