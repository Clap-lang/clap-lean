import Clap.Lang.FB.assert_eq

namespace Clap.Lang.FBitVec

variable {p : ℕ}

def assert_eq {w : ℕ} (a b : FBitVec p w) : ClapM p Unit :=
  (a.zip b).foldlM (fun () (x, y) => FB.assert_eq x y) ()

namespace assert_eq

lemma convertsM
  [p.AtLeastTwo]
  {k}
  {state : ClapMState p}
  {a b : FBitVec p k}
  {a_val b_val : Vector Bool k}
  :
  ConvertsM FUnit.conversion (assert_eq a b) state () (a_val = b_val)
:= by
  sorry

end assert_eq

end Clap.Lang.FBitVec
