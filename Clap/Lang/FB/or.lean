import Clap.Lang.FB.FB

namespace Clap.Edsl.Lang.FB

def or {p : ℕ} [Fact (p ≥ 2)] (a b : FB p) : FB p := a + b - a * b

namespace or

def spec (p : ℕ) [Fact (p ≥ 2)] : Prop :=
  matchesBinaryFunction p (· || ·) FB.or

lemma equiv {p : ℕ} [Fact (p ≥ 2)] : spec p := by
  intro a varStore h_isValid
  aesop (add simp [FB.or, toBool,isValid, beq_eq_false_iff_ne.mpr, FixedExp.eval])

end or

end Clap.Edsl.Lang.FB
