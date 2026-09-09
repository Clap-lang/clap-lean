import Clap.eDSLState.HashCons.Eval
import Clap.eDSLState.ConstraintSystem.num2bits

namespace Clap

namespace ConstraintSystem

section Bob

open HashConsM

def rangeCheckVec {p k : ℕ} (numAlloc width : ℕ) (vec : Vector ExprRef k) : HashConsM p (Array ExprRef × ℕ) := do
  vec.foldlM (b := (#[], numAlloc)) fun (acc, numAlloc) elem ↦ do
    let (cs, numAlloc) ← num2bits width numAlloc elem
    return (acc ++ cs, numAlloc)

def evalPoly {p k : ℕ} (coeffs : Vector ExprRef k) (x : ZMod p) : HashConsM p ExprRef := do
  (List.finRange k).foldrM
    (fun ind acc => do
      let term ← mkMul coeffs[ind] (←mkConstant (x ^ ind.val))
      mkAdd acc term
    ) (←mkConstant 0)

def assertPolyEqProd {p k : ℕ}
    (a : Vector ExprRef k)
    (b : Vector ExprRef k)
    (c : Vector ExprRef (2 * k - 1)) : HashConsM p (Array ExprRef) :=
  (Array.range (2 * k - 1)).mapM
    fun (k : ℕ) ↦ do
      let mul ← mkMul (←evalPoly a k) (←evalPoly b k)
      mkSub mul (←evalPoly c k)

def fpMul {p : ℕ} (width k numAlloc : ℕ) (a b p' : Vector ExprRef k) : HashConsM p (Array ExprRef × ℕ) := do
  let (constraints₁, numAlloc) ← rangeCheckVec numAlloc width a
  let (constraints₂, numAlloc) ← rangeCheckVec numAlloc width a
  let (constraints₃, numAlloc) ← rangeCheckVec numAlloc width a
  let constraints := constraints₁ ++ constraints₂ ++ constraints₃

  let ab ← Vector.ofFnM fun i : Fin (2 * k - 1) ↦ mkVar (numAlloc + i)
  let numAlloc := numAlloc + (2 * k - 1)
  let prodConstraints ← assertPolyEqProd a b ab
  let constraints := constraints ++ prodConstraints

  let q ← Vector.ofFnM fun i : Fin k ↦ mkVar (numAlloc + i)
  let numAlloc := numAlloc + k
  let (constraints₄, numAlloc) ← rangeCheckVec numAlloc width q
  let constraints := constraints ++ constraints₄

  let r ← Vector.ofFnM fun i : Fin k ↦ mkVar (numAlloc + i)
  let numAlloc := numAlloc + k
  let (constraints₅, numAlloc) ← rangeCheckVec numAlloc width r
  let constraints := constraints ++ constraints₅
  
  let t ← Vector.ofFnM fun i : Fin (2 * k - 1) ↦ mkVar (numAlloc + i)
  let numAlloc := numAlloc + (2 * k - 1)
  -- range check missing on purpose

  _

end Bob

end ConstraintSystem

end Clap
