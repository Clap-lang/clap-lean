import Clap.Lang.F.mkAdd
import Clap.Lang.F.mkF
import Clap.Lang.F.mkMul
import Clap.Lang.F.mkSub

namespace Clap.Lang.FB

variable {p : ℕ}

def xor (a b : FB p) : ClapM p (FB p) := do
  let sum ← mkAdd a b
  let prod ← mkMul a b
  let two ← mkF 2
  let twoProd ← mkMul two prod
  mkSub sum twoProd

namespace xor

/-- The `true ^^ true` case: `simp` does not fold `1 + 1 - 2` on its own. -/
private lemma two_sub : (1 : ZMod p) + 1 - 2 = 0 := by ring

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a b : FB p}
  {a_val b_val : Bool}
  (h_a : Converts FB.conversion state a a_val)
  (h_b : Converts FB.conversion state b b_val)
:
  ConvertsM FB.conversion (xor a b) state (a_val ^^ b_val) True
:= by
  unfold xor
  have h_a_f := F.converts_of_FB_converts h_a
  have h_b_f := F.converts_of_FB_converts h_b
  step mkAdd.convertsM h_a_f h_b_f as sum
  step mkMul.convertsM h_a_f h_b_f as prod
  step mkF.convertsM as two
  step mkMul.convertsM h_two h_prod as twoProd
  have h_sub := FB.convertsM_of_F_convertsM (mkSub.convertsM h_sum h_twoProd)
  apply convertsM_of_convertsM (h_sub _)
  . cases a_val <;> cases b_val <;> simp [two_sub]
  . trivial
  . cases a_val <;> cases b_val <;> simp [two_sub]

end Clap.Lang.FB.xor
