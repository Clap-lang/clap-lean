import Clap.Lang.F.mkSub
import Clap.Lang.FUnit.guardedEq0

namespace Clap.Lang

variable {p : ℕ}

/-- Gated equality: asserts `a == b` only when `guard` is set. -/
def guardedAssertEq (guard : FB p) (a b : F p) : ClapM p Unit := do
  let diff ← a - b
  guardedEq0 guard diff

namespace guardedAssertEq

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {guard : FB p}
  {a b : F p}
  {guard_val : Bool}
  {a_val b_val : ZMod p}
  (h_guard : Converts FB.conversion state guard guard_val)
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
:
  ConvertsM FUnit.conversion (guardedAssertEq guard a b) state ()
    (guard_val = true → a_val = b_val)
:= by
  unfold guardedAssertEq
  step mkSub.convertsM h_a h_b as diff
  apply convertsM_of_convertsM (guardedEq0.convertsM h_guard h_diff)
  . rfl
  . cases guard_val <;> simp [sub_eq_zero]

end Clap.Lang.guardedAssertEq
