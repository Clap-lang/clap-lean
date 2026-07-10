import Clap.Lang.FB.FB

namespace Clap.Edsl.Lang.FB

def not {p : ℕ} [Fact (p ≥ 2)] (a : FB p) : FB p := 1 - a


namespace not

def spec (p : ℕ) [Fact (p ≥ 2)] : Prop := matchesUnaryFunction p (!·) FB.not

lemma equiv {p : ℕ} [Fact (p ≥ 2)] :
  spec p
:= by
  intro a varStore h_isValid
  aesop (add simp [
    FB.not,left_inv,right_inv,toBool,FB.false,FB.true,isValid,
    beq_eq_false_iff_ne.mpr, ofBool, FixedExp.eval
  ])

lemma not_isValid {p} [Fact (p ≥ 2)]
  {x : FB p}
  {varStore : ℕ → Option (ZMod p)} :
  x.isValid varStore → x.not.isValid varStore
:= by
  aesop (add simp [FB.isValid, FB.not, FixedExp.eval])

lemma not_toBool {p} [Fact (p ≥ 2)] {x : FB p} {varStore : ℕ → Option (ZMod p)} :
  x.isValid varStore →
  x.not.toBool varStore = (x.toBool varStore).not
:= by
  intro h_isValid
  simp [toBool, not]
  rcases h_isValid <;> aesop (add simp [FixedExp.eval])

end not

end Clap.Edsl.Lang.FB
