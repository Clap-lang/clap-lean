import Clap.Lang.F.mkF
import Clap.Lang.F.mkSub

namespace Clap.Lang

variable {p : ℕ}

def not (a : FB) : ClapM p FB := do
  let one ← mkF 1
  mkSub one a

namespace not

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a : FB}
  {a_val : Bool}
  (h_a : Converts FB.conversion state a a_val)
:
  ConvertsM FB.conversion (not a) state (!a_val) True
:= by
  unfold not
  step mkF.convertsM as one
  have h_a_f := F.converts_of_FB_converts h_a
  have h_sub := FB.convertsM_of_F_convertsM (mkSub.convertsM h_one h_a_f)
  apply convertsM_of_convertsM (h_sub _)
  . grind
  . trivial
  . cases a_val <;> simp
  . trivial

end Clap.Lang.not
