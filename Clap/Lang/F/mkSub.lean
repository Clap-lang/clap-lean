import Clap.eDSLState.Convert.Specialised

namespace Clap.Lang

open HashConsM

variable {p : ℕ}

def mkSub (a b : F p) : ClapM p (F p) :=
  a - b

namespace mkSub

lemma hashConsM_converts
   {state}
   {a b : BoundRef p}
   {a_val b_val : ZMod p}
   (h_a : Converts F.conversion state a a_val)
   (h_b : Converts F.conversion state b b_val)
:
  Converts F.conversion
    (ClapM.getState (a - b) state)
    (ClapM.getResult (a - b) state.numAlloc state.σ)
    (a_val - b_val)
:= by
  simp [ClapM.getState]
  obtain ⟨a_length, a_varSet, a_wellFormed, a_result⟩ := h_a
  obtain ⟨b_length, b_varSet, b_wellFormed, b_result⟩ := h_b
  constructor <;>
  simp at *
  . grind [=Expr.varSet_wellFormed]
  . grind
  . grind

lemma convertsM
  {state : ClapMState p}
  {a b : F p}
  {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
:
  ConvertsM F.conversion (mkSub a b) state (a_val - b_val) True
:= by
  unfold mkSub
  constructor
  . exact hashConsM_converts h_a h_b
  . grind
  . grind [ClapM.runAndEval]

end mkSub

end Clap.Lang
