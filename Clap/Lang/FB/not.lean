import Clap.Lang.FB.FB

namespace Clap.Lang.FB

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

end not

end Clap.Lang.FB
