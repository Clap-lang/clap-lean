import Clap.eDSLState.Convert.Specialised
import Clap.Lang.F.mkAdd

namespace Clap.Lang

variable {p : ℕ}

def lessThan (w : ℕ) (a b : F p) : ClapM p (FB p) := do
  let diff ← a - b
  let pow := 2^w
  let d ← mkAdd diff pow
  let d ← num2bits (w + 1) d
  sorry

namespace lessThen

lemma convertsM
  {state}
  {w : ℕ}
  {a b : F p}
  {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
  (ha : a_val.val < 2^w)
  (hb : b_val.val < 2^w)
  (hw : 2^(w+1) < p)
:
  ConvertsM FB.conversion
    (lessThan w a b)
    state
    (a_val.val < b_val.val)
    True
:= by sorry

end lessThen

end Clap.Lang
