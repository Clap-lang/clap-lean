import Clap.Lang.FB.eq

namespace Clap.Lang.FB

variable {p : ℕ}

def eq [p.AtLeastTwo] (a b : FB p) : ClapM p (FB p) :=
  _root_.Clap.Lang.eq a b

namespace eq

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a b : FB p}
  {a_val b_val : Bool}
  (h_a : Converts FB.conversion state a a_val)
  (h_b : Converts FB.conversion state b b_val)
:
  ConvertsM FB.conversion (eq a b) state (a_val == b_val) True
:= by
  unfold eq
  have h_a_f := F.converts_of_FB_converts h_a
  have h_b_f := F.converts_of_FB_converts h_b
  apply convertsM_of_convertsM (_root_.Clap.Lang.eq.convertsM h_a_f h_b_f)
  . cases a_val <;> cases b_val <;> simp
  . trivial

end Clap.Lang.FB.eq
