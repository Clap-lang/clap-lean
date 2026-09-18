import Mathlib.Data.ZMod.Basic

namespace Clap

attribute [simp]
  sub_eq_zero

attribute [grind =]
  Option.isSome_eq_false_iff
  Option.isNone_iff_eq_none

end Clap

@[simp, grind .]
lemma ZMod.val_one_le_one
  {n : ℕ}
:
  ZMod.val (n := n) 1 ≤ 1
:= by
  simp [ZMod.val_one_eq_one_mod, Nat.mod_le]

namespace Clap.Lang

/-- Computes the minimum number of bits necessary to represent `x`. Model-agnostic math, reused
verbatim from the old model's `Clap/Util/Wheels.lean`. -/
def minBits' (x : ℕ) : ℕ :=
  if x = 0 then 1 else Nat.log2 x + 1

lemma lt_two_pow_minBits' (x : ℕ) : x < 2 ^ minBits' x := by
  by_cases hx : x = 0
  · simp [minBits', hx]
  · have h : minBits' x = Nat.log2 x + 1 := by simp [minBits', hx]
    rw [h]
    exact (Nat.log2_lt hx).mp (Nat.lt_succ_self _)

end Clap.Lang
