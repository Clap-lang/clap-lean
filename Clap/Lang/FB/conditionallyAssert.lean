import Clap.Lang.FB.and
import Clap.Lang.FB.not
import Clap.Lang.FUnit.eq0

namespace Clap.Lang.FB

variable {p : ℕ}

def conditionallyAssert (antecedent consequent : FB p) : ClapM p Unit := do
  let nc ← not consequent
  let conj ← and antecedent nc
  eq0 conj

namespace conditionallyAssert

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {antecedent consequent : FB p}
  {a_val c_val : Bool}
  (h_a : Converts FB.conversion state antecedent a_val)
  (h_c : Converts FB.conversion state consequent c_val)
:
  ConvertsM FUnit.conversion (conditionallyAssert antecedent consequent) state ()
    (a_val = true → c_val = true)
:= by
  unfold conditionallyAssert
  step not.convertsM h_c as nc
  step and.convertsM h_a h_nc as conj
  have h_conj_f := F.converts_of_FB_converts h_conj
  apply convertsM_of_convertsM (eq0.convertsM h_conj_f)
  . rfl
  . cases a_val <;> cases c_val <;> simp

end Clap.Lang.FB.conditionallyAssert
