import Clap.Lang.FB.FB

namespace Clap.Edsl.Lang.FB

def not {p : ℕ} [Fact (p ≥ 2)] (a : FB p) : FB p := 1 - a

namespace not

-- TODO we may want to do proofs about [varStore|false/true p].bind
lemma equiv {p : ℕ} [Fact (p ≥ 2)] :
  matchesUnaryFunction p (!·) (FB.not (p := p))
:= by
  intro a varStore h_isValid
  -- NB `Convert.toIdealtoRepresents` in `simp` magics a lot of the reasoning away
  have := isValid_iff_eval_eq_eval_false_or_eval_true.mp h_isValid
  unfold_projs
  simp [FB.toBool, FB.not]
  obtain h | h := this
  <;> simp [h, eval_false, eval_true]

end not

end Clap.Edsl.Lang.FB
