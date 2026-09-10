import Clap.eDSLState.HashCons.Eval
import Clap.eDSLState.ConstraintSystem.num2bits

namespace Clap

namespace ConstraintSystem

section Bob

open HashConsM

def rangeCheckVec {p k : ℕ} (numAlloc width : ℕ) (vec : Vector (BoundRef p) k) : HashConsM p (Array (BoundRef p) × ℕ) := do
  vec.foldlM (b := (#[], numAlloc)) fun (acc, numAlloc) elem ↦ do
    let (cs, numAlloc) ← num2bits width numAlloc elem
    return (acc ++ cs, numAlloc)

def evalPoly {p k : ℕ} (coeffs : Vector (BoundRef p) k) (x : ZMod p) : HashConsM p (BoundRef p) := do
  (List.finRange k).foldrM
    (fun ind acc => do
      let term ← coeffs[ind] * (←mkConstant (x ^ ind.val))
      acc + term
    ) (←mkConstant 0)

def assertPolyEqProd {p k : ℕ}
    (a : Vector (BoundRef p) k)
    (b : Vector (BoundRef p) k)
    (c : Vector (BoundRef p) (2 * k - 1)) : HashConsM p (Array (BoundRef p)) :=
  (Array.range (2 * k - 1)).mapM
    fun (k : ℕ) ↦ do
      let mul ← (←evalPoly a k) * (←evalPoly b k)
      mul - (←evalPoly c k)

def rangeCheckInputs
  {p k : ℕ}
  (constraints : Array (BoundRef p)) (numAlloc : ℕ)
  (width : ℕ)
  (a b p' : Vector (BoundRef p) k)
: HashConsM p (Array (BoundRef p) × ℕ) := do
  let (constraints₁, numAlloc) ← rangeCheckVec numAlloc width a
  let (constraints₂, numAlloc) ← rangeCheckVec numAlloc width b
  let (constraints₃, numAlloc) ← rangeCheckVec numAlloc width p'
  return (constraints ++ constraints₁ ++ constraints₂ ++ constraints₃, numAlloc)

def allocUnchecked
  {p : ℕ}
  (numAlloc : ℕ)
  (k : ℕ)
: HashConsM p (Vector (BoundRef p) k × ℕ) := do
  let vec ← Vector.ofFnM fun i : Fin k ↦ mkVar (numAlloc + i)
  return (vec, numAlloc + k)

def allocRangeChecked
  {p : ℕ}
  (constraints : Array (BoundRef p)) (numAlloc : ℕ)
  (k : ℕ)
  (width : ℕ)
: HashConsM p (Vector (BoundRef p) k × (Array (BoundRef p) × ℕ)) := do
  let (vec, numAlloc) ← allocUnchecked numAlloc k
  let (range_check_constraints, numAlloc) ← rangeCheckVec numAlloc width vec
  return (vec, (constraints ++ range_check_constraints, numAlloc))

def polyMult
  {p k : ℕ}
  (constraints : Array (BoundRef p)) (numAlloc : ℕ)
  (a b : Vector (BoundRef p) k)
: HashConsM p (Vector (BoundRef p) (2*k-1) × (Array (BoundRef p) × ℕ)) := do
  let (ab, numAlloc) ← allocUnchecked numAlloc (2*k-1)
  let prodConstraints ← assertPolyEqProd a b ab
  return (ab, (constraints ++ prodConstraints, numAlloc))

def check_carry_zero
  {p : ℕ}
  {k : ℕ}
  (constraints : Array (BoundRef p)) (numAlloc : ℕ)
  (width : ℕ)
  (t : Vector (BoundRef p) k)
: HashConsM p (Array (BoundRef p) × ℕ) := do
  if _ : k = 0 then return (constraints, numAlloc)
  else
    let (carry, numAlloc) ← allocUnchecked numAlloc (k - 1)
    let (constraints, numAlloc) ← (List.finRange (k - 1)).foldrM (λ (i : Fin (k - 1)) (constraints, numAlloc) => do
      let e ← if _ : i.val = 0
        then pure t[i]
        else t[i] + carry[(⟨i - 1, by omega⟩ : Fin (k - 1))]
      let constraints := constraints.push (←e - (←(←mkConstant (2^width)) * carry[i]))
      let (num2bits_constraints, numAlloc) ← num2bits
          (width := width + Nat.clog 2 k + 2)
          (numAlloc := numAlloc)
          (expr := ← carry[i] + (←mkConstant (k * 2 ^ (width + 1))))
      return (constraints ++ num2bits_constraints, numAlloc)
    ) (constraints, numAlloc)
    let overflow ← t[(⟨k - 1, by omega⟩ : Fin k)] + (
        ←if _ : k = 1 then mkConstant 0
        else pure carry[(⟨k - 2, by omega⟩ : Fin (k - 1))]
    )
    return (constraints.push overflow, numAlloc)

def check_lt_impl
  {p : ℕ}
  {k : ℕ}
  (constraints : Array (BoundRef p)) (numAlloc : ℕ)
  (width : ℕ)
  (isLt : (BoundRef p))
  (a b : Vector (BoundRef p) k)
: HashConsM p (Array (BoundRef p) × ℕ):= do
  match _ : k with
  | .zero => return (constraints.push (←isLt - (←mkConstant 1)), numAlloc)
  | .succ k =>
    let (constraints, numAlloc) ← num2bits
      (numAlloc := numAlloc)
      (width := width)
      (expr := ←
        (←(←mkConstant 1) - isLt) * 
        (←
          (←a[Fin.last k] - b[Fin.last k]) +
          (←mkConstant ((2 ^ width : ZMod p) - 1))
        )
      )

    let x ← mkConstant 0
    return (constraints, numAlloc)


def check_lt
  {p : ℕ}
  {k}
  (constraints : Array (BoundRef p)) (numAlloc : ℕ)
  (width : ℕ)
  (a b : Vector (BoundRef p) k)
: HashConsM p (Array (BoundRef p) × ℕ) := do
  check_lt_impl constraints numAlloc width (←mkConstant 0) a b

def fpMul {p : ℕ} (width k numAlloc : ℕ) (a b p' : Vector (BoundRef p) k) : HashConsM p (Array (BoundRef p) × ℕ) := do
  let (constraints, numAlloc) ← rangeCheckInputs #[] numAlloc width a b p'

  let (ab, (constraints, numAlloc)) ← polyMult constraints numAlloc a b

  let (q, (constraints, numAlloc)) ← allocRangeChecked constraints numAlloc k width
  let (r, (constraints, numAlloc)) ← allocRangeChecked constraints numAlloc k width
  let (t, numAlloc) ← allocUnchecked numAlloc (2*k - 1)

  let constraints ← (List.range (2*k - 1)).foldrM (λ (x : ℕ) constraints ↦ do
    let pq_plus_r ← (←(←evalPoly p' x) * (←evalPoly q x)) + (←evalPoly r x)
    let ab_sub ← (←evalPoly ab x) - pq_plus_r
    let res ← (←evalPoly t x) - ab_sub
    return constraints.push res
  ) (constraints)

  let (constraints, numAlloc) ← check_carry_zero constraints numAlloc width t

  check_lt constraints numAlloc width r p'

end Bob

end ConstraintSystem

end Clap
