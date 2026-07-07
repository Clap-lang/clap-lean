import Clap.Lang.FB.FB
import Clap.Lang.FB.not
import Clap.eDSLState.Basic

namespace Clap.Lang.FB

def assert {p : ℕ} [Fact (p ≥ 2)] (a : FB p) : Edsl.CircuitStateM p Unit := do
  Edsl.eq0 (not a)



end Clap.Lang.FB
