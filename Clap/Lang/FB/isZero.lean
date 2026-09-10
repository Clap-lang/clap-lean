import Clap.eDSLState.Convert.Specialised

namespace Clap.Lang

variable {p : ℕ}

namespace isZero

@[simp, grind! .]
lemma lt_getNumAlloc
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {a : ExprRef}
:
  numAlloc < (isZero a).getNumAlloc numAlloc σ
:= by
  simp [isZero]

lemma wellFormed {e! : ExprRef} {state} {value : ZMod p}
  (h : Converts F.conversion state e! value)
:
  (isZero e!).wellFormed state.numAlloc state.varStore state.σ
:= by
  obtain ⟨h_varSet, h_wellFormed, h_result⟩ := h
  simp at *
  apply wellFormed_isZero
  . grind
  . have : [state.varStore|⦃e!, state.σ⦄].isSome = true := by grind
    grind
  . grind

lemma converts
  [p.AtLeastTwo]
  {state}
  {a : F p}
  {a_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
:
  Converts FB.conversion
    ((isZero a).getState state)
    ((isZero a).getResult state.numAlloc state.σ)
    (a_val == 0)
:= by
  obtain ⟨a_length, a_varSet, a_wellFormed, a_result⟩ := h_a
  obtain ⟨varStore, σ, numAlloc⟩ := state
  simp [ClapM.getState]
  constructor <;> simp at *
  . intro i h_i
    grind [=isZero, ClapM.getState]
  . simp [isZero]
    rw [Expr.wellFormed_iff_isSome, Expr.deref_mkVar_eq_some]
    rfl
  . simp [isZero, HashConsM.mkVar]
    simp [HashConsM.getHashConsState_saveExpr_of_wellFormed,
          HashConsM.getResult_saveExpr_of_wellFormed]
    split
    · rw [eval_eq_evalRec (by grind)]
      unfold Expr.evalRec
      grind
    · rw [eval_eq_evalRec (by grind)]
      rw [evalRec_eq_of_deref_eq_some_v (idx := numAlloc)]
      · simp
        rw [eval_eq_evalRec (by grind)] at a_result ⊢
        rw [←evalRec_of_wellFormed_of_prefix] at ⊢
        · rw [a_result]
          grind
        · grind
        · grind
      · grind

lemma constraints
  {state : ClapMState p}
  {a}
  {a_val}
  (h_a : Converts F.conversion state a a_val)
:
  ((isZero a).runAndEval state.numAlloc state.varStore state.σ).2.constraints
:= by
  simp
  have : [state.varStore|⦃a, state.σ⦄].isSome := by grind
  exact isSome_eval_of_prefix (by {
    grind [cases Converts]
  }) this (by rfl) (by grind)

lemma convertsM
  [p.AtLeastTwo]
  {state}
  {a : F p}
  {a_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
:
  ConvertsM FB.conversion (isZero a)
    state
    (a_val == 0)
    True
where
  result := converts h_a
  wellFormed := wellFormed h_a
  constraints := iff_true_intro (constraints h_a)

end isZero

end Clap.Lang
