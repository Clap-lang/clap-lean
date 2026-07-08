import Clap.Lang.FB.FB

namespace Clap.Lang.FB

def not {p : ℕ} [Fact (p ≥ 2)] (a : FB p) : FB p := 1 - a

namespace not

def spec (p : ℕ) [Fact (p ≥ 2)] : Prop := matchesUnaryFunction p (!·) FB.not

lemma equiv {p : ℕ} [Fact (p ≥ 2)] : spec p
:= by
  intro a varStore h_isValid
  have : p ≥ 2 := Fact.out
  simp
  obtain h | h := h_isValid
  . simp [
      FB.not,
      show 1 - a = (Exp.c ↑1).sub a by {
        simp [HSub.hSub, Sub.sub, OfNat.ofNat]
      },
      FixedExp.eval,
      h,
      FB.toBool,
      beq_eq_decide,
      show ((0: ZMod p) = 1) = (1 = (0: ZMod p)) by grind,
      ZMod.one_eq_zero_iff,
      show (p = 1) = False by {
        simp
        omega
      },
      FB.ofBool,
      FB.true
    ]
  . simp [
      FB.not,
      show 1 - a = (Exp.c ↑1).sub a by {
        simp [HSub.hSub, Sub.sub, OfNat.ofNat]
      },
      FixedExp.eval,
      h,
      FB.toBool,
      FB.ofBool,
      FB.false
    ]

end not

end Clap.Lang.FB
