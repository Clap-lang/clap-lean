import Clap.eDSLState.Convert.Specialised

namespace Clap.Lang

variable {p : ℕ}

def num2bits (w : ℕ) (e : F p) : ClapM p (FArray p w) :=
  Clap.num2bits w e

namespace num2bits

lemma convertsM
  {state}
  {w : ℕ}
  {e : F p}
  {e_val : ZMod p}
  (h_e : Converts F.conversion state e e_val)
  :
  ConvertsM FArray.conversion
    (num2bits w e)
    state
    (num2bitsLsbPureV w e_val |>.map fun x ↦ x == 1)
    True
:= by
  sorry

end num2bits

end Clap.Lang
