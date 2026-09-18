import Clap.Lang.Data.FArray.eq
namespace Clap.Lang.FBitVec

variable {p : ℕ}

/-- Is one bit vector equal to another, as a circuit bit.

`FBitVec p w` is the same carrier as `FArray p w`, so this is `FArray.eq`; the namespace
exists to mirror the old model's `FBitVec.*`. -/
def eq [p.AtLeastTwo] {w : ℕ} (a b : FBitVec p w) : ClapM p (FB p) :=
  FArray.eq a b

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
  apply convertsM_of_convertsM (FArray.eq.convertsM h_a h_b) _ Iff.rfl
  by_cases h : a_val = b_val <;> simp [h]

end eq

end Clap.Lang.FBitVec
