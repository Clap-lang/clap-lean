import Clap.Lang.F.mkAdd
import Clap.Lang.F.mkMul
import Clap.Lang.F.mkSub

namespace Clap.Lang

variable {p : ℕ}

/-- Multiplexer: returns `a` when `sel` is set, `b` otherwise. -/
def conditionalSwap (sel : FB p) (a b : F p) : ClapM p (F p) := do
  let diff ← a - b
  let scaled ← diff * sel
  mkAdd scaled b

namespace conditionalSwap

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {sel : FB p}
  {a b : F p}
  {sel_val : Bool}
  {a_val b_val : ZMod p}
  (h_sel : Converts FB.conversion state sel sel_val)
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
:
  ConvertsM F.conversion (conditionalSwap sel a b) state
    (if sel_val then a_val else b_val) True
:= by
  unfold conditionalSwap
  have h_sel_f := F.converts_of_FB_converts h_sel
  step mkSub.convertsM h_a h_b as diff
  step mkMul.convertsM h_diff h_sel_f as scaled
  apply convertsM_of_convertsM (mkAdd.convertsM h_scaled h_b)
  . cases sel_val <;> simp
  . trivial

end Clap.Lang.conditionalSwap
