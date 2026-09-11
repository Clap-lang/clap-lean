import Clap.eDSLState.HashCons.Eval

namespace Clap

namespace ConstraintSystem

section Bob

open HashConsM

def mkBits2num {p : ℕ} (bits : Array ExprRef) : HashConsM p ExprRef := do
  let init ← mkConstant 0
  bits.foldrM (λ bit acc => do mkAdd bit (←mkMul (←mkConstant 2) acc)) init

def num2bits_impl {p : ℕ}
  (numAlloc : ℕ)
  (width : ℕ) (expr : ExprRef)
:
  HashConsM p (Array (BoundRef p) × Array ExprRef × ℕ)
:= do
  let bits ← (Array.range width).mapM (λ idx => mkVar (numAlloc + idx))
  let bit_constraints ← bits.mapM (λ bit => do mkMul bit (←mkSub (←mkConstant 1) bit)) -- equivalent to assert_bit_e
  let value_constraint ← mkSub (←mkBits2num bits) expr
  let constraints := bit_constraints.push value_constraint
  return (bits, constraints, numAlloc + width)

def num2bits {p : ℕ}
  (constraints : Array (BoundRef p) )(numAlloc : ℕ)
  (width : ℕ) (expr : ExprRef)
:
  HashConsM p (Array (BoundRef p) × Array ExprRef × ℕ)
:= do
  let (bits, num2bits_constraints, numAlloc) ← num2bits_impl numAlloc width expr
  return (bits, constraints ++ num2bits_constraints, numAlloc)

namespace num2bits

def num_constraints (width : ℕ) : ℕ := width + 1
def numAllocStep (width : ℕ) : ℕ := width

@[simp, grind =]
lemma num_constraints_eq
  {p : ℕ}
  {constraints} {numAlloc}
  {width}
  {expr}
  {σ : HashConsSt p}
:
  ((num2bits constraints numAlloc width expr).getResult σ).2.1.size =
  constraints.size + num_constraints width
:= by
  simp [num2bits, num2bits_impl, num_constraints]

@[simp, grind =]
lemma numAllocStep_eq
  {p : ℕ}
  {constraints} {numAlloc}
  {width}
  {expr}
  {σ : HashConsSt p}
:
  ((num2bits constraints numAlloc width expr).getResult σ).2.2 =
  numAlloc + numAllocStep width
:= by
  simp [num2bits, num2bits_impl, numAllocStep]

end num2bits


end Bob

end ConstraintSystem

end Clap
