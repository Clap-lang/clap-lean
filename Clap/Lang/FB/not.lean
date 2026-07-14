import Clap.Lang.FB.FB

namespace Clap.Edsl.Lang.FB

def not {p : ℕ} [Fact (p ≥ 2)] (a : FB p) : FB p := 1 - a

namespace not

def spec (p : ℕ) [Fact (p ≥ 2)] : Prop := matchesUnaryFunction p (!·) (FB.not (p := p))

lemma equiv {p : ℕ} [Fact (p ≥ 2)] :
  spec p
:= by
  intro a varStore h_isValid
  -- NB `Convert.toIdealtoRepresents` in `simp` magics a lot of the reasoning away
  aesop (add simp [FB.isValid_iff, FB.toIdeal_def, FB.not, toBool])

end not

end Clap.Edsl.Lang.FB
