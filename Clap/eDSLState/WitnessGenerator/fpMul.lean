import Clap.eDSLState.Expr
import Clap.eDSLState.WitnessGenerator.isZero
import Clap.eDSLState.WitnessGenerator.num2bits

import CompPoly.Univariate.Basic

namespace Clap

section Andrew

open CompPoly

variable {p : ℕ} {var : Type} [inst : Fact (Nat.Prime p)] [inst' : Fact (p > 2)]

namespace WitnessGenerator

def toCompPoly {k : ℕ} (vec : Vector (ZMod p) k) : CPolynomial (ZMod p) :=
  List.foldr (fun i p ↦ p + CPolynomial.C (vec[i]) * CPolynomial.X ^ i.1) 0 (List.finRange k)

def rangeCheckVec
  (cache : ValueCache p) (trace : Array (ZMod p)) {w : ℕ} (vec : Vector ExprRef w) : Array (ZMod p) :=
  vec.foldr (fun e trace ↦ num2bits cache trace w e) trace

def carry (w : ℕ) : List (ZMod p) → ZMod p → List (ZMod p)
| l :: l' :: ls, c => let c' : ZMod p := (l + c) / (2 ^ w); c' :: carry w (l' :: ls) c'
| _ :: []      , _ => []
| []           , _ => []

def checkCarryZero {k : ℕ}
  (cache : ValueCache p) (trace : Array (ZMod p)) (w : ℕ) (t : Vector ExprRef k) : HashConsM p (Array (ZMod p)) := do
  let carry : List (ZMod p) := carry w (t.toList.map (cache[·]!.get!)) 0
  let trace := trace ++ carry
  let num2bits ←
    carry.foldrM (init := trace) fun c trace ↦ do
      return num2bits cache trace (w + Nat.clog 2 k + 2) (←.mkConstant (c + (2 ^ (w + 1) * k)))
  return trace ++ num2bits

def check_lt_wg' {k : ℕ}
  (cache : ValueCache p) (trace : Array (ZMod p)) (w : ℕ) (isLt : HashConsM.BoundRef p)
  (t₀ : Vector (HashConsM.BoundRef p) k) (t₁ : Vector (HashConsM.BoundRef p) k) : HashConsM p (Array (ZMod p)) :=
  match k with
  | .zero => return trace
  | .succ k => do
    let tδ ← t₀[Fin.last k] - t₁[Fin.last k]
    let num2bits_trace := num2bits cache trace w
      (←(←(←.mkConstant 1) - isLt) *
        (←(tδ + (←.mkConstant ((2 ^ w : ZMod p) - 1))))
      )
    let trace := trace ++ num2bits_trace
    let isZero_trace := isZero cache trace tδ
    let trace := trace ++ isZero_trace
    
    -- (fun _ ↦
    --   IsZero.isZero_wg (t₀[Fin.last k] - t₁[Fin.last k])
    --     (fun iz ↦
    --       let isLt' : Expₑ p :=
    --         isLt ||| (1 - .v iz)
    --       check_lt_wg' w isLt' (Vector.ofFn (fun i ↦ t₀[(i.castSucc)])) (Vector.ofFn (fun i ↦ t₁[(i.castSucc)])) cont
    --     )
    -- )
    _

def checkLt {k : ℕ} (w : ℕ) (t : Vector (Expₑ p) k) (t' : Vector (Expₑ p) k) (cont : Wg p) : Wg p :=
  check_lt_wg' w 0 t t' cont

def fpMul {k : ℕ}
  (cache : ValueCache p) (trace : Array (ZMod p))
  (w : ℕ) (a b p' : Vector ExprRef k) : HashConsM p (Array (ZMod p)) := do
  let rangeCheckeda := rangeCheckVec cache trace a
  let rangeCheckedb := rangeCheckVec cache trace b
  let rangeCheckedp' := rangeCheckVec cache trace p'
  let trace := trace ++ rangeCheckeda ++ rangeCheckedb ++ rangeCheckedp'

  let ab := toCompPoly (a.map (cache[·]!.get!)) * toCompPoly (b.map (cache[·]!.get!))
  let ab_trace := Array.range (2 * k -1) |>.map ab.coeff
  let trace := trace ++ ab_trace

  let a_val : ℕ := ∑ i : Fin k, cache[a[i]]!.get!.val * (2 ^ w) ^ i.1
  let b_val : ℕ := ∑ i : Fin k, cache[b[i]]!.get!.val * (2 ^ w) ^ i.1
  let p_val : ℕ := ∑ i : Fin k, cache[p'[i]]!.get!.val * (2 ^ w) ^ i.1
  let q_val : ℕ := (a_val * b_val) / p_val
  let r_val : ℕ := (a_val * b_val) % p_val

  let q_vec := natToLimbsV (p := p) w k q_val
  let trace := trace ++ q_vec.toArray

  let q_vec_constants ← q_vec.mapM .mkConstant
  let rangeCheckedq_vec_constants := rangeCheckVec cache trace q_vec_constants
  let trace := trace ++ rangeCheckedq_vec_constants

  let r_vec := natToLimbsV (p := p) w k r_val
  let trace := trace ++ r_vec.toArray

  let r_vec_constants ← r_vec.mapM .mkConstant
  let rangeCheckedr_vec_constants := rangeCheckVec cache trace r_vec_constants
  let trace := trace ++ rangeCheckedq_vec_constants

  let t := ab - toCompPoly (p'.map (cache[·]!.get!)) * toCompPoly q_vec - toCompPoly r_vec
  let t_trace := List.range (2 * k - 1) |>.map t.coeff
  let trace := trace ++ t_trace

  let checkCarryZero :=
    checkCarryZero cache trace w
      (←Vector.ofFnM (fun i : Fin (2 * k - 1) ↦ .mkConstant (t.coeff i.1)))
  
  check_lt_wg w (r_vec.map .c) p'
  _
  -- let ws :=
  --   (List.finRange (2 * k - 1)).foldr
  --     (fun i (trace : Array (ZMod p)) ↦ trace.push (ab.coeff i)) <|
  --     q_vec.foldr (flip Array.push) <|

end WitnessGenerator

end Andrew

end Clap
