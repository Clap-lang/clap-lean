import Clap.eDSLState.Expr

namespace Clap

namespace WitnessGenerator

def eq0 {p : ℕ} (_cache : ValueCache p) (trace : Array (ZMod p)) (_expr : ExprRef) : Array (ZMod p) :=
  trace

namespace eq0

def trace_capacity : ℕ := 0

@[simp, grind =]
lemma trace_size_eq
  {p}
  (cache : ValueCache p)
  (trace : Array (ZMod p))
  (expr : ExprRef)
:
  (eq0 cache trace expr).size = trace.size + trace_capacity
:= rfl

end eq0

end WitnessGenerator

end Clap
