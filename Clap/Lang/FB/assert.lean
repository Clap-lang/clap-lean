import Clap.Lang.FB.not
import Clap.Lang.FUnit.eq0

namespace Clap.Lang

variable {p : ℕ}

def assert (a : FB) : ClapM p Unit := do
  eq0 (←not a)

namespace assert

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a : FB}
  {a_val : Bool}
  (h_a : Converts FB.conversion state a a_val)
:
  ConvertsM FUnit.conversion (assert a) state () (a_val = true)
:= by
  unfold assert
  step not.convertsM h_a as not
  have h_not_f := F.converts_of_FB_converts h_not
  apply convertsM_of_convertsM (eq0.convertsM h_not_f)
  . rfl
  . grind

end Clap.Lang.assert
