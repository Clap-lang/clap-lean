import Clap.eDSLState.Expr

namespace Clap

namespace WitnessGenerator

def share {p : ℕ} (cache : ValueCache p) (trace : Array (ZMod p)) (expr : ExprRef): Array (ZMod p) :=
  trace.push cache[expr]!.get!

end WitnessGenerator

end Clap
