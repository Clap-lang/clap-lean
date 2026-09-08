import Clap.eDSLState.Convert.Specialised

namespace Clap.Lang

variable {p : ℕ}

namespace eq0

lemma wellFormed {e! : ExprRef} {state} {value : ZMod p}
  (h : Converts F.conversion state e! value)
:
  (eq0 e!).wellFormed state.numAlloc state.varStore state.σ
:= by
  obtain ⟨h_varSet, h_wellFormed, h_result⟩ := h
  simp at *
  apply wellFormed_eq0
  . grind
  . have : [state.varStore|⦃e!, state.σ⦄].isSome = true := by grind
    grind
  . grind

lemma converts
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a : F}
:
  Converts FUnit.conversion
    ((eq0 a).getState state)
    ((eq0 a).getResult state.numAlloc state.σ)
    ()
:= by
  constructor <;> simp at *

lemma constraints
  {state : ClapMState p}
  {a}
  {a_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
:
  ((eq0 a).runAndEval state.numAlloc state.varStore state.σ).2.constraints ↔
  (a_val = 0)
:= by
  simp
  have := h_a.value_eq
  simp at this
  simp [this]

lemma convertsM
  [p.AtLeastTwo]
  {state}
  {a : F}
  {a_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
:
  ConvertsM FUnit.conversion (eq0 a)
    state
    ()
    (a_val = 0)
where
  result := converts
  wellFormed := wellFormed h_a
  constraints := constraints h_a

end eq0

end Clap.Lang
