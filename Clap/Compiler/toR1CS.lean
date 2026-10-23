import Clap.Model.ConstraintSystem.toCs
import R1Serialize.R1CS

namespace Clap

namespace ConstraintSystem

/-- `A * B - C` -/
structure NormalQuadratic where
  A : ExprRef
  B : ExprRef
  C : ExprRef

variable {p : ℕ}

open HashConsM

abbrev MemoM (p : ℕ) (α : Type) := StateT (Std.HashMap ExprRef α) (HashConsM p)

def scalarArithmetic₀ (e : ExprRef) : MemoM p (ExprRef ⊕ ZMod p) (ExprRef ⊕ ZMod p) :=
  sorry

/--
Turns expressions into `A * B - C` format that R1CS expects.
Here `A, B, C` are all first order.
-/
def toR1CS (cs : ConstraintSystem p) (numInputs : ℕ) : Option R1CSv1 :=
  sorry

end ConstraintSystem

end Clap
