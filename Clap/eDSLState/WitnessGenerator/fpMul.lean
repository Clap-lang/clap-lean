import Clap.eDSLState.Expr
import CompPoly.Univariate.Basic

namespace Clap

section Andrew

open CompPoly

variable {p : ℕ}

namespace WitnessGenerator

def toCompPoly {k : ℕ} (vec : Vector (ZMod p) k) : CPolynomial (ZMod p) :=
  List.foldr (fun i p ↦ p + CPolynomial.C (vec[i]) * CPolynomial.X ^ i.1) 0 (List.finRange k)

def fpMul {p : ℕ}
  (cache : ValueCache p) (trace : Array (ZMod p)) (width : ℕ) (expr : ExprRef) : Array (ZMod p) :=
  let ab := toCompPoly (a.map (Exp.eval)) * toCompPoly (b.map (Exp.eval))
  _

end WitnessGenerator

end Andrew

end Clap
