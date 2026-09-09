import Clap.eDSLState.Circuit
import Clap.eDSLState.Varstore
-- import Clap.eDSLState.Convert.Specialised

namespace Clap

structure ConstraintSystem (p : ℕ) where
  eq0s : Array ExprRef
  σ : HashConsSt p

namespace ConstraintSystem

variable {p : ℕ} (cs: ConstraintSystem p)

def runSpec (trace : Array (ZMod p)) : Bool :=
  cs.eq0s.all (λ expr => [.ofArray (trace.zipIdx.map Prod.swap), cs.σ|expr] == .some 0)

-- TODO prove equivalent to runSpec
-- TODO make evalWithArrayCache to avoid the conversion and prove equivalent to evalWithCache
def run (trace : Array (ZMod p)) : Bool :=
  let max := cs.eq0s.max?
  match max with
  | .none => true
  | .some max =>
    let cache := Expr.evalWithCache (.ofArray (trace.zipIdx.map Prod.swap)) #[] ⦃max, cs.σ⦄
    cs.eq0s.all (λ expr => cache[expr]? == .some (0 : ZMod p))

def num_constraints : Gate → ℕ
  | .eq0 _ => 1
  | .share _ => 1
  | .isZero _ => 2
  | .num2bits w _ => w + 1
  | .fpmul w k a b p' => 42

end ConstraintSystem

def HashConsM.mkBits2num {p : ℕ} (bits : Array ExprRef) : HashConsM p ExprRef := do
  let init ← mkConstant 0
  bits.foldrM (λ bit acc => do mkAdd bit (←mkMul (←mkConstant 2) acc)) init

def rangeCheckCircuit (w : ℕ) {k : ℕ} (vec : Vector ExprRef k) : HashConsM p _ :=

def fpMul_circuit
  {p k w : ℕ}
  (a b p' : Vector ExprRef k) : HashConsM p (Array ExprRef × ℕ) := do
  _

open HashConsM in
def Circuit.toCs {p : ℕ} (circuit : Circuit) (σ : HashConsSt p) (numInputs : ℕ)
:
  ConstraintSystem p
:=
  let ((eq0s, _numAlloc), σPost) :=
    (circuit.foldlM (m := HashConsM p) (λ (eq0s, numAlloc) gate => do
      match gate with
        | .eq0 expr => return (eq0s.push expr, numAlloc)
        | .share expr =>
          let v ← mkVar numAlloc
          let s ← mkSub expr v
          return (eq0s.push s, numAlloc + 1)
        | .isZero expr =>
          let inv ← mkVar numAlloc
          let o ← mkVar (numAlloc + 1)
          let constraint1 ← mkSub (←(mkSub (←mkConstant 1) (←mkMul inv expr))) o
          let constraint2 ← mkMul o expr
          return (eq0s.append #[constraint1, constraint2], numAlloc + 2)
        | .num2bits width expr =>
          let bits ← (Array.range width).mapM (λ idx => mkVar (numAlloc + idx))
          let bit_constraints ← bits.mapM (λ bit => do mkMul bit (←mkSub (←mkConstant 1) bit)) -- equivalent to assert_bit_e
          let value_constraint ← mkSub (←mkBits2num bits) expr
          let constraints := bit_constraints.push value_constraint
          return (eq0s.append constraints, numAlloc + width)
        | .fpmul w k a b p' => sorry
    ) (Array.emptyWithCapacity (circuit.map ConstraintSystem.num_constraints).sum , numInputs)).run σ
  ⟨eq0s, σPost⟩

end Clap
