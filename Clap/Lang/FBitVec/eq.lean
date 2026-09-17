import Clap.Lang.FB.and
import Clap.Lang.FB.eq
import Clap.Lang.FB.ofBool

namespace Clap.Lang.FBitVec

variable {p : ℕ}

def eq₀ [p.AtLeastTwo] {w : ℕ} (init : FB p) (a b : FArray p w) : ClapM p (FB p) :=
  (a.zip b).foldlM (fun acc (x, y) => do FB.and acc (← _root_.Clap.Lang.eq x y)) init

def eq [p.AtLeastTwo] {w : ℕ} (a b : FArray p w) : ClapM p (FB p) := do
  eq₀ (← FB.ofBool true) a b

namespace eq

lemma convertsM
  [p.AtLeastTwo]
  {k}
  {state : ClapMState p}
  {a b : FBitVec p k}
  {a_val b_val : Vector Bool k}
  (h_a : Converts FArray.conversion state a a_val)
  (h_b : Converts FArray.conversion state b b_val)

  :
  ConvertsM FB.conversion (eq a b) state (a_val == b_val) True
:= by
  sorry

end eq
end Clap.Lang.FBitVec
