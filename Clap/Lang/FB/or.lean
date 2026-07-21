import Clap.Lang.FB.FB

namespace Clap.Edsl.Lang.FB

section

variable {p : ℕ} [p.AtLeastTwo] {varStore : VarStore p} {x y : FB p}

def or (a b : FB p) : FB p := a + b - a * b

namespace or

@[grind .]
lemma or_false (x_valid : x.isValid varStore) (y_valid : y.isValid varStore) :
  [varStore|x.or y] = [varStore|FB.false p] ↔
  [varStore|x] = [varStore|FB.false p] ∧ [varStore|y] = [varStore|FB.false p]
:= by
  simp [FB.or, FixedExp.add_def, FixedExp.mul_def, FixedExp.sub_def, eval_false]
  constructor
  · rcases _ : [varStore|x] <;> rcases _ : [varStore|y] <;> grind
  · aesop

@[grind .]
lemma or_true (x_valid : x.isValid varStore) (y_valid : y.isValid varStore) :
  [varStore|x.or y] = [varStore|FB.true p] ↔
  [varStore|x] = [varStore|FB.true p] ∨ [varStore|y] = [varStore|FB.true p]
:= by
  simp [FB.or, FixedExp.add_def, FixedExp.mul_def, FixedExp.sub_def, eval_true]
  constructor
  · rcases _ : [varStore|x] <;> simp; rcases _ : [varStore|y] <;> grind
  · rcases _ : [varStore|x] <;> rcases _ : [varStore|y] <;> grind

@[grind .]
lemma or_ofBool {b₁ b₂ : Bool}
  (h: [varStore|x] = [varStore|FB.ofBool p b₁])
  (h: [varStore|y] = [varStore|FB.ofBool p b₂]) :
  [varStore|x.or y] = [varStore|FB.ofBool p (b₁ || b₂)]
:= by
  grind

@[grind .]
lemma toIdeal_or {a b : FB p} {a' b' : Bool}
  (h₁ : Convert.toIdeal varStore a = .some a')
  (h₂ : Convert.toIdeal varStore b = .some b') :
  Convert.toIdeal varStore (a.or b) = .some (a' || b')
:= by
  have valid₁ := (Convert.isValid_iff_isSome_toIdeal varStore a).mpr (by
    rw! [h₁]; rfl
  )
  rewrite [toIdeal_def] at h₁ h₂ ⊢
  unfold toBool at h₁ h₂ ⊢
  simp_all only [beq_iff_eq, isValid_iff]
  cases valid₁ <;> grind

lemma equiv :
  matchesBinaryFunction p (· || ·) (FB.or (p := p))
:= by
  unfold matchesBinaryFunction
  grind

end or

end

end Clap.Edsl.Lang.FB
