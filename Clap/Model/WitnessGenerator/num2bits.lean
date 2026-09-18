import Clap.Model.Expr
import Clap.Util.BitVec

namespace Clap

namespace WitnessGenerator

def num2bitsUnsafe {p : ℕ}
  (cache : ValueCache p) (trace : Array (ZMod p)) (width : ℕ) (expr : ExprRef) : Array (ZMod p) :=
  let e := cache[expr]!.get!
  let bits := num2bitsLsbPureV width e
  trace ++ bits.toArray

namespace num2bits

def trace_capacity (width : ℕ) : ℕ := width

@[simp, grind =]
lemma trace_size_eq
  {p}
  (cache : ValueCache p)
  (trace : Array (ZMod p))
  (width : ℕ)
  (expr : ExprRef)
:
  (num2bitsUnsafe cache trace width expr).size = trace.size + trace_capacity width
:= by
  simp [num2bitsUnsafe, trace_capacity]

end num2bits

end WitnessGenerator

end Clap
