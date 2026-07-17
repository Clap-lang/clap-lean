import Mathlib.Control.Monad.Cont

import Clap.Compiler.Back.Circuit

namespace Clap.DSL

variable {p : ℕ} [Fact (Nat.Prime p)]

abbrev CircuitM (p : ℕ) (α : Type) : Type := Cont (Circuitₑ p) α

end Clap.DSL
