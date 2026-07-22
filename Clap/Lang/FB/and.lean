import Clap.Lang.FB.FB

namespace Clap.Edsl.Lang.FB

section

variable {p : ℕ} [p.AtLeastTwo] {varStore : VarStore p} {x y : FB p}

def and (a b : FB p) : FB p := a * b

namespace and

@[grind .]
lemma and_false (x_valid : x.isValid varStore) (y_valid : y.isValid varStore) :
  [varStore|x.and y] = [varStore|FB.false p] ↔
  [varStore|x] = [varStore|FB.false p] ∨ [varStore|y] = [varStore|FB.false p]
:= by
  simp [FB.and, FixedExp.mul_def, eval_false]
  constructor
  · rcases [varStore|x] <;> rcases _ : [varStore|y] <;> grind
  · rintro (h₁ | h₂) <;> rcases _ : [varStore|x] <;> grind

@[grind .]
lemma and_true :
  [varStore|x] = [varStore|FB.true p] ∧ [varStore|y] = [varStore|FB.true p] ↔
  x.isValid varStore ∧ y.isValid varStore ∧ [varStore|x.and y] = [varStore|FB.true p]
:= by
  simp [FB.and, FixedExp.mul_def, eval_true]
  rcases _ : [varStore|y] <;> rcases _ : [varStore|x] <;> grind

@[grind .]
lemma and_ofBool {b₁ b₂ : Bool}
  (h: [varStore|x] = [varStore|FB.ofBool p b₁])
  (h: [varStore|y] = [varStore|FB.ofBool p b₂]) :
  [varStore|x.and y] = [varStore|FB.ofBool p (b₁ && b₂)]
:= by
  grind

@[grind .]
lemma toIdeal_and {a b : FB p} {a' b' : Bool}
  (h₁ : Convert.toIdeal varStore a = .some a')
  (h₂ : Convert.toIdeal varStore b = .some b') :
  Convert.toIdeal varStore (a.and b) = .some (a' && b')
:= by
  have valid₁ := (Convert.isValid_iff_isSome_toIdeal varStore a).mpr (by
    rw! [h₁]; rfl
  )
  have valid₂ := (Convert.isValid_iff_isSome_toIdeal varStore b).mpr (by
    rw! [h₂]; rfl
  )
  rewrite [toIdeal_def] at h₁ h₂ ⊢
  unfold toBool at h₁ h₂ ⊢
  simp_all only [beq_iff_eq, isValid_iff]
  cases valid₁ <;> grind

lemma equiv :
  matchesBinaryFunction p (· && ·) (FB.and (p := p))
:= by
  unfold matchesBinaryFunction
  grind

end and

end

end Clap.Edsl.Lang.FB
