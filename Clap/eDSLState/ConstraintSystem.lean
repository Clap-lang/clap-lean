import Clap.eDSLState.Circuit

namespace Clap

structure ConstraintSystem (p : ℕ) where
  eq0s : Array ExprRef
  σ : HashConsSt p

namespace ConstraintSystem

variable {p : ℕ} (cs: ConstraintSystem p)

def runSpec (trace : Array (ZMod p)) : Bool :=
  cs.eq0s.all (λ expr => [VarStore.ofArray (trace.zipIdx.map Prod.swap), cs.σ|expr] == .some 0)

-- TODO prove equivalent to runSpec
-- TODO make evalWithArrayCache to avoid the conversion and prove equivalent to evalWithCache
def run (trace : Array (ZMod p)) : Bool :=
  let max := cs.eq0s.max?
  match max with
  | .none => true
  | .some max =>
    let cache := HashConsM.evalWithCache (VarStore.ofArray (trace.zipIdx.map Prod.swap)) max #[] cs.σ
    cs.eq0s.all (λ expr => cache[expr]? == .some (0 : ZMod p))

def num_constraints : Gate p → ℕ
  | .eq0 _ => 1
  | .share _ => 1
  | .isZero _ => 2
  | .num2bits w _ => w + 1

end ConstraintSystem

def HashConsM.mkBits2num {p : ℕ} (bits : Array ExprRef) : HashConsM p ExprRef := do
  let init ← mkConstant 0
  bits.foldrM (λ bit acc => do mkAdd bit (←mkMul (←mkConstant 2) acc)) init


open HashConsM in
def Circuit.toCs {p : ℕ} (circuit : Circuit p) (σ : HashConsSt p) (numInputs : ℕ)
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
    ) (Array.emptyWithCapacity (circuit.map ConstraintSystem.num_constraints).sum , numInputs)).run σ
  ⟨eq0s, σPost⟩

end Clap
