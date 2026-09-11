import Clap.eDSLState.Expr
import Clap.BitVec

namespace Clap

namespace WitnessGenerator

def num2bits {p : ℕ}
  (cache : ValueCache p) (trace : Array (ZMod p)) (width : ℕ) (expr : ExprRef) : Array (ZMod p) :=
  let e := cache[expr]!.get!
  let bits := num2bitsLsbPureV width e
  trace.append bits.toArray

end WitnessGenerator

end Clap
