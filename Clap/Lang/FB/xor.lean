import Clap.Lang.FB.FB

namespace Clap.Edsl.Lang.FB

def xor {p : ℕ} [Fact (p ≥ 2)] (a b : FB p) : FB p := a + b - 2 * a * b

namespace xor

def spec (p : ℕ) [Fact (p ≥ 2)] : Prop :=
  matchesBinaryFunction p (· ^^ ·) FB.xor

lemma equiv {p : ℕ} [Fact (p ≥ 2)] : spec p := by
  intro a varStore h_isValid h₁ h₂
  aesop (add simp [
    FB.xor, left_inv, right_inv, toBool, FB.false, isValid,
    beq_eq_false_iff_ne.mpr, ofBool, FixedExp.eval
  ])
  norm_num

end xor

end Clap.Edsl.Lang.FB
