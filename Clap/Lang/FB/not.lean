import Clap.Lang.FB.FB

namespace Clap.Edsl.Lang.FB

section

variable {p : ℕ} [p.AtLeastTwo] {varStore : VarStore p} {x : FB p}

def not {p : ℕ} [p.AtLeastTwo] (a : FB p) : FB p := 1 - a

namespace not

/--
I mean, yes, but also no...
(Unused.)
-/
@[aesop simp, grind .]
lemma _isValid_not_iff :
  IsValid.isValid varStore (not x) ↔ IsValid.isValid varStore x := by
  unfold not
  refine Iff.intro (fun h ↦ ?p₁) (fun h ↦ ?p₂) <;>
  aesop (add simp [FB.isValid_iff, Option.bind, FixedExp.sub_def])

-- TODO we may want to do proofs about [varStore|false/true p].bind
lemma equiv {p : ℕ} [p.AtLeastTwo] :
  matchesUnaryFunction p (!·) (FB.not (p := p))
:= by
  intro a varStore h₁
  unfold not at *
  simp [FixedExp.sub_def, toIdeal_def, toBool]
  grind

end not

end

end Clap.Edsl.Lang.FB
