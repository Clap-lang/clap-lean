import Clap.Lang.F.mkSub
import Clap.Lang.FUnit.eq0

namespace Clap.Lang

variable {p : ℕ}

section assert_eq

def assert_eq (a b : F) : ClapM p Unit := do
  let diff ← HashConsM.mkSub (p := p) a b
  eq0 diff

namespace assert_eq

lemma convertsM
  [p.AtLeastTwo]
  {a b} {a_val b_val}
  {state : ClapMState p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
:
  ConvertsM FUnit.conversion (assert_eq a b) state () (a_val = b_val)
:= by
  unfold assert_eq

  step mkSub.convertsM h_a h_b as sub <;> [skip; exact λ _ ↦ True.intro]

  apply convertsM_of_convertsM (eq0.convertsM h_sub)
  . rfl
  . grind

end assert_eq
end assert_eq

end Clap.Lang
