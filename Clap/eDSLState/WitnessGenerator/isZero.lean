import Clap.eDSLState.Expr

namespace Clap

namespace WitnessGenerator

def isZero {p : ℕ} (cache : ValueCache p) (trace : Array (ZMod p)) (expr : ExprRef): Array (ZMod p) :=
  let e := cache[expr]!.get!
  let inv := e.inv
  let o := if e == 0 then 1 else 0
  trace.append #[inv, o]

end WitnessGenerator

end Clap
