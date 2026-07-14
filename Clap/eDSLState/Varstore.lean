import Mathlib.Data.ZMod.Basic
import Std.Data.ExtTreeMap

namespace Clap

abbrev VarStore (p : ℕ) := Std.ExtTreeMap ℕ (ZMod p) (cmp := compare)

end Clap
