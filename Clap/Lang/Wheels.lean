import Mathlib.Data.ZMod.Basic

namespace Clap

attribute [simp]
  sub_eq_zero

attribute [grind =]
  Option.isSome_eq_false_iff
  Option.isNone_iff_eq_none

end Clap
