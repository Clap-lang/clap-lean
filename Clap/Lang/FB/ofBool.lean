import Clap.Lang.F.mkF

namespace Clap.Lang.FB

variable {p : ℕ}

def ofBool (b : Bool) : ClapM p (FB p) :=
  mkF (if b then 1 else 0)

namespace ofBool

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {b : Bool}
:
  ConvertsM FB.conversion (ofBool (p := p) b) state b True
:= by
  unfold ofBool
  have h := FB.convertsM_of_F_convertsM (mkF.convertsM (state := state) (a := if b then 1 else 0))
  apply convertsM_of_convertsM (h _)
  . cases b <;> simp
  . trivial
  . cases b <;> simp

end Clap.Lang.FB.ofBool
