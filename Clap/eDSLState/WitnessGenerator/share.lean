import Clap.eDSLState.Expr

namespace Clap

namespace WitnessGenerator

def share {p : ℕ} (cache : ValueCache p) (trace : Array (ZMod p)) (expr : ExprRef): Array (ZMod p) :=
  trace.push cache[expr]!.get!

namespace share

def trace_capacity : ℕ := 1

@[simp, grind =]
lemma trace_size_eq
  {p}
  (cache : ValueCache p)
  (trace : Array (ZMod p))
  (expr : ExprRef)
:
  (share cache trace expr).size = trace.size + trace_capacity
:= by
  simp [share, trace_capacity]

end share

end WitnessGenerator

end Clap
