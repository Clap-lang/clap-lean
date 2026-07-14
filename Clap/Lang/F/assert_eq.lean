import Clap.Lang.F.F

namespace Clap.Edsl.Lang.F

def assert_eq {p : ℕ} [Fact (p ≥ 2)] (a b : F p) : Edsl.CircuitStateM p Unit := do
  Edsl.eq0 (a - b)

namespace assert_eq

def spec (p : ℕ) [Fact (p ≥ 2)] : Prop :=
  matchesBinaryPredicatePure p (fun a b : ZMod p ↦ a = b) assert_eq

lemma equiv (p : ℕ) [Fact (p ≥ 2)] : spec p := by sorry

end assert_eq

end Clap.Edsl.Lang.F
