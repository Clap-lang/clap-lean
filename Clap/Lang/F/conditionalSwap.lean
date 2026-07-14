import Clap.Lang.F.F
import Clap.Lang.FB.FB

namespace Clap.Edsl.Lang.F

def conditionalSwap {p : ℕ} [Fact (p ≥ 2)] (sel : FB p) (a b : F p) : F p :=
  (a - b) * sel + b

namespace conditionalSwap

/-- selects `a` when `sel = 1` and `b` when `sel = 0` -/
def spec (p : ℕ) [Fact (p ≥ 2)] : Prop :=
  matchesTernaryFunction p (fun (s : Bool) (a b : ZMod p) ↦ if s then a else b) (conditionalSwap (p := p))

lemma equiv (p : ℕ) [Fact (p ≥ 2)] : spec p := by sorry

end conditionalSwap

end Clap.Edsl.Lang.F
