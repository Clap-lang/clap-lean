import Clap.Lang.FB.FB

namespace Clap.Lang.FB

def not {p : ℕ} (a : FB p) : FB p := 1 - a

namespace not

def spec (p : ℕ) : Prop := matchesUnaryFunction p (!·) FB.not

#synth HSub (FB 2) (FB 2) (FB 2)

lemma equiv (p : ℕ): spec p
:= by
  unfold spec matchesUnaryFunction
  intro a varStore h_isValid
  obtain h | h := h_isValid
  all_goals simp [FB.not]
  unfold FixedExp.eval
  rewrite [show 1 - a = (Exp.c ↑1).sub a by {
    simp [HSub.hSub, Sub.sub]
  }]
  rewrite []
  unfold FB.not
  unfold_projs
  unfold Nat.cast NatCast.natCast
  aesop (add simp [FB.isValid, FB.toBool, FB.ofBool])
  done

end not

end Clap.Lang.FB
