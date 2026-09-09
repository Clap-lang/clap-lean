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
    (c : Vector ExprRef (2*k - 1)) : HashConsM p (Array ExprRef) := do
  (List.range (2*k - 1)).mapM
    fun k : ℕ => do
      let mul ← mkMul (←evalPoly a k) (←evalPoly b k)
      let sub ← mkSub mul (←evalPoly c k)

      _
      -- Cs.eq0 ((evalPoly a k) * (evalPoly b k) - (evalPoly c k)) rest

def assert_poly_eq_prod {k : ℕ}
    (a : Vector (Exp p var) k)
    (b : Vector (Exp p var) k)
    (c : Vector (Exp p var) (2*k - 1))
    (rest : Cs p var) : Cs p var :=
  List.foldr
    (fun k rest =>
      Cs.eq0 ((evalPoly a k) * (evalPoly b k) - (evalPoly c k)) rest
    )
    rest
    (List.range (2*k - 1))

def fpMul {p : ℕ} (width k numAlloc : ℕ) (a b p' : Vector ExprRef k) : HashConsM p (Array ExprRef × ℕ) := do
  let (constraints₁, numAlloc) ← rangeCheckVec numAlloc width a
  let (constraints₂, numAlloc) ← rangeCheckVec numAlloc width a
  let (constraints₃, numAlloc) ← rangeCheckVec numAlloc width a
  let constraints := constraints₁ ++ constraints₂ ++ constraints₃
  let ab ← Vector.ofFnM fun i : Fin (2 * k - 1) ↦ mkVar (numAlloc + i)
  let numAlloc := numAlloc + 1
  _

end Bob

end ConstraintSystem

end Clap
