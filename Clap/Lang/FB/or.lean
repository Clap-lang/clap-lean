import Clap.Lang.F.mkAdd
import Clap.Lang.F.mkMul
import Clap.Lang.F.mkSub

namespace Clap.Lang.FB

variable {p : ℕ}

def or (a b : FB p) : ClapM p (FB p) := do
  let sum ← mkAdd a b
  let prod ← mkMul a b
  mkSub sum prod

namespace or

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a b : FB p}
  {a_val b_val : Bool}
  (h_a : Converts FB.conversion state a a_val)
  (h_b : Converts FB.conversion state b b_val)
:
  ConvertsM FB.conversion (or a b) state (a_val || b_val) True
:= by
  unfold or
  have h_a_f := F.converts_of_FB_converts h_a
  have h_b_f := F.converts_of_FB_converts h_b
  step mkAdd.convertsM h_a_f h_b_f as sum
  step mkMul.convertsM h_a_f h_b_f as prod
  have h_sub := FB.convertsM_of_F_convertsM (mkSub.convertsM h_sum h_prod)
  apply convertsM_of_convertsM (h_sub _)
  . cases a_val <;> cases b_val <;> simp
  . trivial
  . cases a_val <;> cases b_val <;> simp

end Clap.Lang.FB.or
