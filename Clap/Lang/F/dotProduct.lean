import Clap.Lang.F.F

namespace Clap.Edsl.Lang.F

def dotProduct {p : ℕ} [Fact (p ≥ 2)] {w : ℕ} (a b : Vector (F p) w) : F p :=
  (a.zipWith (· * ·) b).foldl (· + ·) 0

namespace dotProduct

/-- `∑ i, a[i] * b[i]`. -/
def spec (p : ℕ) [Fact (p ≥ 2)] (w : ℕ) : Prop :=
  matchesBinaryFunction p (fun (a b : Vector (ZMod p) w) ↦ ∑ i : Fin w, a[i] * b[i]) (dotProduct (p := p) (w := w))

lemma equiv (p : ℕ) [Fact (p ≥ 2)] (w : ℕ) : spec p w := by sorry

end dotProduct

end Clap.Edsl.Lang.F
