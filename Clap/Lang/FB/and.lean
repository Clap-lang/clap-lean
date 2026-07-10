import Clap.Lang.FB.FB

namespace Clap.Edsl.Lang.FB

def and {p : ℕ} [Fact (p ≥ 2)] (a b : FB p) : FB p := a * b

namespace and

def spec (p : ℕ) [Fact (p ≥ 2)] : Prop :=
  matchesBinaryFunction p (· && ·) FB.and

lemma equiv {p : ℕ} [Fact (p ≥ 2)] : spec p := by
  intro a varStore h_isValid
  aesop (add simp [FB.and, toBool,isValid, beq_eq_false_iff_ne.mpr, FixedExp.eval])

end and

end Clap.Edsl.Lang.FB
