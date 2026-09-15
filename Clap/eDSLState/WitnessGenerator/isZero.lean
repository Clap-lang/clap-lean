import Clap.eDSLState.Expr

namespace Clap

namespace WitnessGenerator

def isZeroUnsafe {p : ℕ} (cache : ValueCache p) (trace : Array (ZMod p)) (expr : ExprRef) : Array (ZMod p) :=
  let e := cache[expr]!.get!
  let inv := e.inv
  let o := if e == 0 then 1 else 0
  trace ++ #[inv, o]

namespace isZero

def trace_capacity : ℕ := 2

@[simp, grind =]
lemma trace_size_eq
  {p}
  (cache : ValueCache p)
  (trace : Array (ZMod p))
  (expr : ExprRef)
:
  (isZeroUnsafe cache trace expr).size = trace.size + trace_capacity
:= by
  simp [isZeroUnsafe, trace_capacity]

end isZero

end WitnessGenerator

end Clap
