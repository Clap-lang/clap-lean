import Clap.Lang.Core.F.mkMul
import Clap.Lang.Gate.eq0
namespace Clap.Lang

variable {p : ℕ}

/-- Gated assertion: asserts `constraint == 0` only when `guard` is set. -/
def guardedEq0 (guard : FB p) (constraint : F p) : ClapM p Unit := do
  let prod ← guard * constraint
  eq0 prod

namespace guardedEq0

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {guard : FB p}
  {constraint : F p}
  {guard_val : Bool}
  {constraint_val : ZMod p}
  (h_guard : Converts FB.conversion state guard guard_val)
  (h_constraint : Converts F.conversion state constraint constraint_val)
:
  ConvertsM FUnit.conversion (guardedEq0 guard constraint) state ()
    (guard_val = true → constraint_val = 0)
:= by
  unfold guardedEq0
  have h_guard_f := F.converts_of_FB_converts h_guard
  step mkMul.convertsM h_guard_f h_constraint as prod
  apply convertsM_of_convertsM (eq0.convertsM h_prod)
  . rfl
  . cases guard_val <;> simp

end Clap.Lang.guardedEq0
