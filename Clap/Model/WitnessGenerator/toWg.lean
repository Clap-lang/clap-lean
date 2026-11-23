import Clap.Model.Circuit
import Clap.Model.WitnessGenerator.eq0
import Clap.Model.WitnessGenerator.fpMul
import Clap.Model.WitnessGenerator.isZero
import Clap.Model.WitnessGenerator.num2bits
import Clap.Model.WitnessGenerator.share
import Clap.Model.ConstraintSystem.toCs

namespace Clap

structure WitnessGenerator (p : ℕ) where
  numInputs : ℕ
  circuit : Circuit
  σ : HashConsSt p

namespace WitnessGenerator

variable {p : ℕ}

def trace_capacity : Gate → ℕ
  | .eq0 _ => eq0.trace_capacity
  | .share _ => share.trace_capacity
  | .isZero _ => isZero.trace_capacity
  | .num2bits w _ => num2bits.trace_capacity w
  | .fpmul w k .. => fpMul.trace_capacity k w

/-- The expressions a gate reads. -/
def gateArgs : Gate → List ExprRef
  | .eq0 e | .share e | .isZero e | .num2bits _ e => [e]
  | .fpmul _ _ a b p' => a.toList ++ b.toList ++ p'.toList

def fillCache (σ : HashConsSt p) (slots : Array (ZMod p)) (cache : ValueCache p) (lo hi : ℕ) :
    ValueCache p := Id.run do
  let mut cache := cache
  for r in [lo:hi] do
    if (cache[r]?).join.isNone then
      let value : Option (ZMod p) := match σ.exprs[r]? with
        | some (.c k) => some k
        | some (.v i) => slots[i]?
        | some (.binary_op lhs rhs op) =>
          let f : ZMod p → ZMod p → ZMod p := match op with
            | .add => (· + ·)
            | .sub => (· - ·)
            | .mul => (· * ·)
          f <$> (cache[lhs]?).join <*> (cache[rhs]?).join
        | none => none
      cache := if r < cache.size then cache.set! r value else cache.push value
  return cache

/-- One gate of `run?`: fill the cache for its arguments, then append its values to the trace -/
def runStep [Fact (Nat.Prime p)] (acc : ValueCache p × ℕ × Array (ZMod p)) (gi : Gate × ℕ) :
    ExceptT String (HashConsM p) (ValueCache p × ℕ × Array (ZMod p)) := do
  let (cache, done, trace) := acc
  let (gate, g) := gi
  let args := gateArgs gate
  let hi := match args.max? with
    | some m => m + 1
    | none => 0
  let cache := fillCache (← get) trace cache done hi
  let done := max done hi
  for e in args do
    if (cache[e]?).join.isNone then
      throw s!"witness generation: gate {g} reads e{e}, which has no value (it mentions a \
        slot that is not in the trace yet)"
  match gate with
  | .eq0 e => return (cache, done, eq0 cache trace e)
  | .share e => return (cache, done, share cache trace e)
  | .isZero e => return (cache, done, isZeroUnsafe cache trace e)
  | .num2bits width e => return (cache, done, num2bitsUnsafe cache trace width e)
  | .fpmul w _ a b p' =>
    -- Cut the cache back to the filled prefix: fpmul's own constants are evaluated past its
    -- end, and an entry evaluated early (to `none`) past `done` would otherwise be kept.
    let (cache, trace) ← fpMulUnsafe (cache.extract 0 done) trace w a b p'
    return (cache, done, trace)

/-- The trace size of `circuit`'s gates, `(circuit.map trace_capacity).sum`, tail-recursive -/
def traceCapacity (circuit : Circuit) (i acc : ℕ) : ℕ :=
  if h : i < circuit.size then traceCapacity circuit (i + 1) (acc + trace_capacity circuit[i])
  else acc
termination_by circuit.size - i

/-- `runStep` on gates `i, i + 1, …` of `circuit`, threading the heap `σ`: `foldlM runStep` over
`circuit.zipIdx` from gate `i` (tail-recursive loop) -/
def runLoop [Fact (Nat.Prime p)] (circuit : Circuit) (i : ℕ)
    (acc : ValueCache p × ℕ × Array (ZMod p)) (σ : HashConsSt p) :
    Except String (ValueCache p × ℕ × Array (ZMod p)) :=
  if h : i < circuit.size then
    match (runStep acc (circuit[i], i)).run.run σ with
    | (.ok acc, σ) => runLoop circuit (i + 1) acc σ
    | (.error e, _) => .error e
  else .ok acc
termination_by circuit.size - i

/--
The expression cache is filled gate by gate, from the trace so far: a gate argument may read the
outputs of earlier gates (`isZero` of a `share`, say). For a circuit made by `ClapM` this always
succeeds, since every gate emits its gate before allocating its outputs (`ClapM.alloc` after
`tell`) -/
def run? [Fact (Nat.Prime p)] (wg : WitnessGenerator p) (inputs : Vector (ZMod p) wg.numInputs) :
    Except String (Array (ZMod p)) :=
  let init := (#[], 0, inputs.toArray.append
    (Array.emptyWithCapacity (traceCapacity wg.circuit 0 0)))
  (runLoop wg.circuit 0 init wg.σ).map (·.2.2)

/-- Panics if `run?` fails. -/
def run [Fact (Nat.Prime p)] (wg : WitnessGenerator p) (inputs : Vector (ZMod p) wg.numInputs) :
    Array (ZMod p) :=
  match wg.run? inputs with
  | .ok trace => trace
  | .error e => panic! e

end WitnessGenerator

def Circuit.toWg {p : ℕ} (circuit : Circuit) (σ : HashConsSt p) (numInputs : ℕ)
:
  WitnessGenerator p
where
  numInputs := numInputs
  circuit := circuit.filter (λ x => match x with | .eq0 _ => false | _ => true)
  σ := ConstraintSystem.offsetHashConsState numInputs σ circuit

end Clap
