import Clap.Model.Convert.Specialised

namespace Clap.Lang

variable {p : ℕ}

namespace share

lemma wellFormed {e! : ExprRef} {state} {value : ZMod p}
  (h : Converts F.conversion state e! value)
: (share e!).wellFormed state.numAlloc state.varStore state.σ
:= by
  obtain ⟨h_varSet, h_wellFormed, h_result⟩ := h
  simp at *
  apply wellFormed_share
  . grind
  . have : [state.varStore|⦃e!, state.σ⦄].isSome = true := by grind
    grind
  . grind

lemma converts
  {state} {a : F p} {a_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
:
  Converts F.conversion
    ((share a).getState state)
    ((share a).getResult state.numAlloc state.σ)
    a_val
:= by
  obtain ⟨a_length, a_varSet, a_wellFormed, a_result⟩ := h_a
  obtain ⟨varStore, σ, numAlloc⟩ := state
  simp [ClapM.getState]
  constructor <;> simp at *
  . intro i h_i
    grind [=share, ClapM.getState]
  . simp [share]
    rw [Expr.wellFormed_iff_isSome, Expr.deref_mkVar_eq_some]
    rfl
  . simp [share, HashConsM.mkVar]
    simp [HashConsM.getHashConsState_saveExpr_of_wellFormed]
    rw [eval_eq_evalRec (by grind)]
    rw [evalRec_eq_of_deref_eq_some_v (idx := numAlloc)]
    · rw [Std.ExtTreeMap.getElem?_insert_self]
      rw [eval_eq_evalRec (by grind)]
      rw [←evalRec_of_wellFormed_of_prefix (σ := σ) (by grind) (by grind)]
      rw [←eval_eq_evalRec (by grind)]
      rw [a_result]
      rfl
    · grind

lemma constraints
  {state : ClapMState p} {a} {a_val}
  (h_a : Converts F.conversion state a a_val)
:
  ((share a).runAndEval state.numAlloc state.varStore state.σ).2.constraints
:= by
  simp
  have : [state.varStore|⦃a, state.σ⦄].isSome := by grind
  exact isSome_eval_of_prefix (by grind [cases Converts]) this (by rfl) (by grind)

lemma convertsM
  {state} {a : F p} {a_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
:
  ConvertsM F.conversion (share a) state a_val True
where
  result := converts h_a
  wellFormed := wellFormed h_a
  constraints := iff_true_intro (constraints h_a)

end share

end Clap.Lang
