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
