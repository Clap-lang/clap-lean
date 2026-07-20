import Clap.Lang.FB.FB

namespace Clap.Edsl.Lang.FB

section

variable {p : ℕ} [p.AtLeastTwo] {varStore : VarStore p} {x : FB p}

def not {p : ℕ} [p.AtLeastTwo] (a : FB p) : FB p := 1 - a

@[simp, grind =]
lemma bind_true {α} {varStore : VarStore p} {f : ZMod p → Option α} :
  [varStore|true p].bind f = f ([varStore|true p].get (by grind))
:= by
  aesop (add simp [Option.bind, FB.true])

@[simp, grind =]
lemma bind_false {α} {varStore : VarStore p} {f : ZMod p → Option α} :
  [varStore|false p].bind f = f ([varStore|false p].get (by grind))
:= by
  aesop (add simp [Option.bind, FB.false])

@[grind .]
lemma not_true:
  ([varStore|x =Γ FB.true p]) ↔
  ([varStore|x.not =Γ FB.false p])
:= by
  simp [FB.not, FixedExp.sub_def, eval_false, eval_true]
  obtain _ | x := [varStore|x] <;> grind

@[grind .]
lemma not_false
:
  ([varStore|x =Γ FB.false p]) ↔
  ([varStore|x.not =Γ FB.true p])
:= by
  simp [FB.not, FixedExp.sub_def, eval_false, eval_true]
  obtain _ | x := [varStore|x] <;> grind

@[grind .]
lemma not_none
  (h : [varStore|x] = .none)
:
  [varStore|x.not] = .none
:= by
  grind [FB.not]

lemma not_ofBool {b : Bool} (h: [varStore|x] = [varStore|FB.ofBool p b]) :
  [varStore|x.not] = [varStore|FB.ofBool p !b]
:= by
  grind

@[grind .]
lemma toIdeal_not {a : FB p} {b : Bool}
  (h : Convert.toIdeal varStore a = .some b)
:
  Convert.toIdeal varStore a.not =
  .some !b
:= by
  have := (Convert.isValid_iff_isSome_toIdeal varStore a).mpr (by
    rw! [h]
    rfl
  )
  rewrite [toIdeal_def] at h ⊢
  unfold toBool at h ⊢
  grind [isValid_iff]

namespace not

@[aesop simp, grind .]
lemma isValid_not_iff :
  IsValid.isValid varStore (not x) ↔ IsValid.isValid varStore x
:= by
  unfold not
  refine Iff.intro (fun h ↦ ?p₁) (fun h ↦ ?p₂) <;>
  aesop (add simp [FB.isValid_iff, Option.bind, FixedExp.sub_def])

@[grind .]
lemma result_IsValid_iff
:
  unaryFunctionResultIsValidIff p (FB.not (p := p))
:= by
  unfold unaryFunctionResultIsValidIff
  grind

@[grind .]
lemma result_correct
:
  unaryFunctionResultIsCorrect p (!·) (FB.not (p := p))
:= by
  unfold unaryFunctionResultIsCorrect
  grind [FB.toRepresents_def]

@[grind .]
lemma equiv :
  matchesUnaryFunction p (!·) (FB.not (p := p))
:= by
  grind

#spec Bool.not FB.not

end not

end

end Clap.Edsl.Lang.FB
