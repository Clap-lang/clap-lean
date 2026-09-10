import Clap.eDSLState.Circuit
import Clap.eDSLState.Varstore
-- import Clap.eDSLState.Convert.Specialised

namespace Clap

open HashConsM

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

-- def rangeCheckCircuit (w : ℕ) {k : ℕ} (vec : Vector ExprRef k) : HashConsM p _ :=

-- def fpMul_circuit
--   {p k w : ℕ}
--   (a b p' : Vector ExprRef k) : HashConsM p (Array ExprRef × ℕ) := do
--   _

def eq0ToCs {p} (constraints : Array ExprRef) (numAlloc : ℕ) (expr : ExprRef) :
  HashConsM p (Array ExprRef × ℕ) :=
  return (constraints.push expr, numAlloc)

def shareToCs {p}
  (constraints : Array ExprRef) (numAlloc : ℕ) (expr : ExprRef)
:
  HashConsM p (ExprRef × Array ExprRef × ℕ)
:= do
  let v ← mkVar numAlloc
  let s ← expr - v
  return (v, constraints.push s, numAlloc + 1)

def isZeroToCs {p} (constraints : Array ExprRef) (numAlloc : ℕ) (expr : ExprRef) :
  HashConsM p (ExprRef × Array ExprRef × ℕ) := do
  let inv ← mkVar numAlloc
  let o ← mkVar (numAlloc + 1)
  let constraint1 ← (←((←mkConstant 1) - (←inv * expr))) - o
  let constraint2 ← o * expr
  return (o, constraints.append #[constraint1, constraint2], numAlloc + 2)

def num2bitsToCs {p} (cs : Array ExprRef) (numAlloc width : ℕ) (expr : BoundRef p) :
  HashConsM p (Array ExprRef × Array ExprRef × ℕ) := do
  let bits ← (Array.range width).mapM (λ idx => mkVar (numAlloc + idx))
  let bit_constraints ← bits.mapM (λ bit => do bit * (←(←mkConstant 1) - bit)) -- equivalent to assert_bit_e
  let value_constraint ← (←mkBits2num bits) - expr
  let constraints := bit_constraints.push value_constraint
  return (bits, cs.append constraints, numAlloc + width)



open HashConsM in
def Circuit.toCs {p : ℕ} (circuit : Circuit) (σ : HashConsSt p) (numInputs : ℕ)
:
  ConstraintSystem p
:=
  let ((eq0s, _numAlloc), σPost) :=
    (circuit.foldlM (m := HashConsM p) (λ (eq0s, numAlloc) gate => do
      match gate with
      | .eq0 expr => eq0ToCs eq0s numAlloc expr
      | .share expr => return (←shareToCs eq0s numAlloc expr).2
      | .isZero expr => return (←isZeroToCs eq0s numAlloc expr).2
      | .num2bits width expr => return (←num2bitsToCs eq0s numAlloc width expr).2
      | .fpmul w k a b p' => sorry
    ) (Array.emptyWithCapacity (circuit.map ConstraintSystem.num_constraints).sum , numInputs)).run σ
  ⟨eq0s, σPost⟩

end Clap
