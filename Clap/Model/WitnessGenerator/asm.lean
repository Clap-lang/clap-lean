import Clap.Model.Asm
import Clap.Model.Expr

namespace Clap

namespace WitnessGenerator

def asmUnsafe {p : ℕ}
  (spec : GateSpec p) (cache : ValueCache p) (trace : Array (ZMod p))
  (inputs : Vector ExprRef spec.numInputs) : Array (ZMod p) :=
  trace ++ (spec.witnessInOrder (inputs.map (cache[·]!.get!))).toArray

def asmUnsafeSilly {p p' : ℕ}
  (spec : LawfulGateSpec p') (cache : ValueCache p) (trace : Array (ZMod p))
  (inputs : Vector ExprRef spec.numInputs) : Array (ZMod p) :=
  if h : p' = p then
    match p', spec, inputs, h with
    | _, spec, inputs, rfl => asmUnsafe spec.toGateSpec cache trace inputs
  else
    trace ++ Array.replicate spec.numTotalVariables 0

namespace asm

def trace_capacity {p} (spec : GateSpec p) : ℕ := spec.numTotalVariables

@[simp, grind =]
lemma trace_size_eq
  {p}
  {spec : GateSpec p}
  {cache : ValueCache p}
  {trace : Array (ZMod p)}
  {inputs : Vector ExprRef spec.numInputs} :
  (asmUnsafe spec cache trace inputs).size = trace.size + trace_capacity spec := by
  simp [asmUnsafe, trace_capacity]

end asm

end WitnessGenerator

end Clap
