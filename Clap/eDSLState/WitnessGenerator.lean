import Clap.eDSLState.Circuit

namespace Clap

structure WitnessGenerator (p : ℕ) where
  circuit : Circuit
  σ : HashConsSt p

namespace WitnessGenerator

variable {p : ℕ} (wg : WitnessGenerator p)

def trace_capacity : Gate → ℕ
  | .eq0 _ => 0
  | .share _ => 1
  | .isZero _ => 2
  | .num2bits w _ => w
  | .fpmul .. => 42

def run (inputs : Array (ZMod p)) : Array (ZMod p) :=
  let max := (wg.circuit.map (λ gate => match gate with
    | .eq0 _e => 0
    | .share e => e
    | .isZero e => e
    | .num2bits _w e => e
    | .fpmul .. => 42
  )).max?.getD 0
  let cache := Expr.evalWithCache (.ofArray (inputs.zipIdx.map Prod.swap)) #[] ⦃max, wg.σ⦄
  wg.circuit.foldl (λ trace gate => match gate with
    | .eq0 _expr => trace
    | .share expr => trace.push cache[expr]!.get!
    | .isZero expr =>
      let e := cache[expr]!.get!
      let inv := e.inv
      let o := if e == 0 then 1 else 0
      trace.append #[inv, o]
    | .num2bits width expr =>
      let e := cache[expr]!.get!
      let bits := num2bitsLsbPureV width e
      trace.append bits.toArray
    | .fpmul .. =>
      trace.append #[42]
  ) (inputs.append (Array.emptyWithCapacity (wg.circuit.map trace_capacity).sum))

end WitnessGenerator

def Circuit.toWg {p : ℕ} (circuit : Circuit) (σ : HashConsSt p)
:
  WitnessGenerator p
where
  circuit := circuit.filter (λ x => match x with | .eq0 _ => false | _ => true)
  σ

end Clap
