import Clap.Lang.F.mkSub
import Clap.Lang.FB.isZero

namespace Clap.Lang

variable {p : ℕ}

section eq

def eq {p : ℕ} [p.AtLeastTwo] (a b : F p) : ClapM p (FB p) := do
  isZero (←(a - b))

namespace eq

lemma convertsM
  [p.AtLeastTwo]
  {state}
  {a b : F p}
  {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
:
  ConvertsM FB.conversion (eq a b) state (a_val == b_val) True
:= by
  unfold eq
  rw [sub_def]

  step mkSub.convertsM h_a h_b as sub
  apply convertsM_of_convertsM (isZero.convertsM h_sub)
  . grind
  . grind

end eq
end eq

end Clap.Lang
