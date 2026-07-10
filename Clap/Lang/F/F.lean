import Clap.eDSLState.eDSL

import Clap.Lang.Wheels

namespace Clap.Edsl.Lang

abbrev F p := FixedExp p

namespace F

variable {p : ℕ}

def isValid (x : F p) (varStore : ℕ → Option (ZMod p)) : Prop :=
  (x.eval varStore).isSome

end F

end Clap.Edsl.Lang
