import Clap.Lang.F.mkMul

namespace Clap.Lang.FB

variable {p : ℕ}

def and (a b : FB) : ClapM p FB := do
  HashConsM.mkMul (p := p) a b

namespace and

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a b : FB}
  {a_val b_val : Bool}
  (h_a : Converts FB.conversion state a a_val)
  (h_b : Converts FB.conversion state b b_val)
:
  ConvertsM FB.conversion (and a b) state (a_val && b_val) True
:= by
  unfold and
  have h_a_f := F.converts_of_FB_converts h_a
  have h_b_f := F.converts_of_FB_converts h_b
  have h_mul := mkMul.convertsM h_a_f h_b_f
  have h_mul_FB := FB.convertsM_of_F_convertsM h_mul
  apply convertsM_of_convertsM (h_mul_FB _)
  . grind
  . trivial
  . cases a_val <;> cases b_val <;> simp

end Clap.Lang.FB.and
