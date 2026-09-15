import Clap.eDSLState.Circuit
import Clap.eDSLState.WitnessGenerator.eq0
import Clap.eDSLState.WitnessGenerator.fpMul
import Clap.eDSLState.WitnessGenerator.isZero
import Clap.eDSLState.WitnessGenerator.num2bits
import Clap.eDSLState.WitnessGenerator.share

namespace Clap

structure WitnessGenerator (p : ℕ) where
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

def run [Fact (Nat.Prime p)] (wg : WitnessGenerator p) (inputs : Array (ZMod p)) : Array (ZMod p) :=
  let max := (wg.circuit.map (λ gate => match gate with
    | .eq0 _e => 0
    | .share e => e
    | .isZero e => e
    | .num2bits _w e => e
    | .fpmul _ k a b p' => if h : k = 0 then 0 else (a ++ b ++ p').toList.max (by simpa)
  )).max?.getD 0
  let cache := Expr.evalWithCache (.ofArray (inputs.zipIdx.map Prod.swap)) #[] ⦃max, wg.σ⦄
  wg.circuit.foldl (λ trace gate => match gate with
    | .eq0 expr => eq0 cache trace expr
    | .share expr => share cache trace expr
    | .isZero expr => isZeroUnsafe cache trace expr
    | .num2bits width expr => num2bitsUnsafe cache trace width expr
    | .fpmul w k a b p' => ((fpMulUnsafe cache trace w a b p').getResult wg.σ).2
  ) (inputs.append (Array.emptyWithCapacity (wg.circuit.map trace_capacity).sum))

end WitnessGenerator

def Circuit.toWg {p : ℕ} (circuit : Circuit) (σ : HashConsSt p)
:
  WitnessGenerator p
where
  circuit := circuit.filter (λ x => match x with | .eq0 _ => false | _ => true)
  σ

end Clap
