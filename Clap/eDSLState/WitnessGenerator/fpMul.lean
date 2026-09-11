import Clap.eDSLState.Expr
import CompPoly.Univariate.Basic

namespace Clap

section Andrew

open CompPoly

variable {p : ℕ} {var : Type} [inst : Fact (Nat.Prime p)] [inst' : Fact (p > 2)]

namespace WitnessGenerator

def toCompPoly {k : ℕ} (vec : Vector (ZMod p) k) : CPolynomial (ZMod p) :=
  List.foldr (fun i p ↦ p + CPolynomial.C (vec[i]) * CPolynomial.X ^ i.1) 0 (List.finRange k)

def fpMul
  (cache : ValueCache p) (trace : Array (ZMod p))
  (w k : ℕ) (a b p' : Vector ExprRef k) : Array (ZMod p) :=
  let ab := toCompPoly (a.map (cache[·]!.get!)) * toCompPoly (b.map (cache[·]!.get!))
  sorry

end WitnessGenerator

end Andrew

end Clap
