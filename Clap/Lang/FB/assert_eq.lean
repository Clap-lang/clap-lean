import Clap.Lang.FUnit.assert_eq

namespace Clap.Lang.FB

variable {p : ℕ}

def assert_eq (a b : FB p) : ClapM p Unit :=
  _root_.Clap.Lang.assert_eq a b

namespace assert_eq

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a b : FB p}
  {a_val b_val : Bool}
  (h_a : Converts FB.conversion state a a_val)
  (h_b : Converts FB.conversion state b b_val)
:
  ConvertsM FUnit.conversion (assert_eq a b) state () (a_val = b_val)
:= by
  unfold assert_eq
  have h_a_f := F.converts_of_FB_converts h_a
  have h_b_f := F.converts_of_FB_converts h_b
  apply convertsM_of_convertsM (_root_.Clap.Lang.assert_eq.convertsM h_a_f h_b_f)
  . rfl
  . cases a_val <;> cases b_val <;> simp

end Clap.Lang.FB.assert_eq
