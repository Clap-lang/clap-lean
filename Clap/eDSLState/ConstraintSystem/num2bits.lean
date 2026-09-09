import Clap.eDSLState.HashCons.Eval

namespace Clap

namespace ConstraintSystem

section Bob

open HashConsM

def mkBits2num {p : ℕ} (bits : Array ExprRef) : HashConsM p ExprRef := do
  let init ← mkConstant 0
  bits.foldrM (λ bit acc => do mkAdd bit (←mkMul (←mkConstant 2) acc)) init

def num2bits {p : ℕ} (width numAlloc : ℕ) (expr : ExprRef) : HashConsM p (Array ExprRef × ℕ) := do
  let bits ← (Array.range width).mapM (λ idx => mkVar (numAlloc + idx))
  let bit_constraints ← bits.mapM (λ bit => do mkMul bit (←mkSub (←mkConstant 1) bit)) -- equivalent to assert_bit_e
  let value_constraint ← mkSub (←mkBits2num bits) expr
  let constraints := bit_constraints.push value_constraint
  return (constraints, numAlloc + width)

end Bob

end ConstraintSystem

end Clap
