import Clap.Lang.FB.FB

namespace Clap.Edsl.Lang.FB

section

variable {p : ℕ} [p.AtLeastTwo] {varStore : VarStore p} {x y : FB p}

def xor (a b : FB p) : FB p := a + b - 2 * a * b

namespace xor

@[grind .]
lemma xor_false (x_valid : x.isValid varStore) (y_valid : y.isValid varStore) :
  [varStore|x.xor y] = [varStore|FB.false p] ↔
  [varStore|x] = [varStore|y]
:= by
  simp [FB.xor, FixedExp.sub_def, eval_false]
  constructor
  · rcases [varStore|x] <;> simp
    rcases _ : [varStore|y] <;> grind
  · rcases [varStore|x] <;> (simp; grind)

@[grind .]
lemma xor_true (x_valid : x.isValid varStore) (y_valid : y.isValid varStore) :
  [varStore|x.xor y] = [varStore|FB.true p] ↔
  [varStore|x] ≠ [varStore|y]
:= by
  simp [FB.xor, FixedExp.add_def, FixedExp.mul_def, FixedExp.sub_def, eval_true]
  constructor
  · rcases [varStore|x] <;> simp
    rcases _ : [varStore|y] <;> grind
  · rcases _ : [varStore|x] <;> simp <;> rcases _ : [varStore|y] <;> grind

@[grind .]
lemma xor_ofBool {b₁ b₂ : Bool}
  (h: [varStore|x] = [varStore|FB.ofBool p b₁])
  (h: [varStore|y] = [varStore|FB.ofBool p b₂]) :
  [varStore|x.xor y] = [varStore|FB.ofBool p (b₁ ^^ b₂)]
:= by
  rcases hx : [varStore|x] <;> rcases _ : [varStore|y] <;> try grind

@[grind .]
lemma toIdeal_xor {a b : FB p} {a' b' : Bool}
  (h₁ : Convert.toIdeal varStore a = .some a')
  (h₂ : Convert.toIdeal varStore b = .some b') :
  Convert.toIdeal varStore (a.xor b) = .some (a' ^^ b')
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
  cases valid₁ <;> cases valid₂ <;> grind

lemma equiv :
  matchesBinaryFunction p (· ^^ ·) (FB.xor (p := p))
:= by
  unfold matchesBinaryFunction
  simp; grind

end xor

end

end Clap.Edsl.Lang.FB
