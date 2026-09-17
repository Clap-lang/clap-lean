import Clap.Lang.FArray.assert_eq

namespace Clap.Lang.FBitVec

variable {p : ℕ}

/-- Assert two bit vectors are equal.

`FBitVec p w` is the same carrier as `FArray p w`, so this is `FArray.assert_eq`; the
namespace exists to mirror the old model's `FBitVec.*`, and the spec below is stated with
vector equality rather than `FArray.assert_eq.convertsM`'s pointwise form. -/
def assert_eq {w : ℕ} (a b : FBitVec p w) : ClapM p Unit :=
  FArray.assert_eq a b

namespace assert_eq

lemma convertsM
  [p.AtLeastTwo]
  {k}
  {state : ClapMState p}
  {a b : FBitVec p k}
  {a_val b_val : Vector Bool k}
  (h_a : Converts FArray.conversion state a a_val)
  (h_b : Converts FArray.conversion state b b_val)
:
  ConvertsM FUnit.conversion (assert_eq a b) state () (a_val = b_val)
:= by
  apply convertsM_of_convertsM (FArray.assert_eq.convertsM h_a h_b) rfl
  constructor
  . intro h
    ext i h_i
    exact h ⟨i, h_i⟩
  . intro h ⟨i, h_i⟩
    rw [h]

end assert_eq

end Clap.Lang.FBitVec
