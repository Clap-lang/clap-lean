import Clap.Compiler.Back.Cs
import Clap.Compiler.Back.Wg

namespace Clap.IsZero

variable {p : ℕ} {var : Type} [inst : Fact (Nat.Prime p)] [inst' : Fact (p > 2)]

def isZero_circuit (e : Exp p var) (cont : var → Cs p var) : Cs p var :=
  .lam fun inv =>
      .lam fun o =>
        .eq0 (.c 1 - .v inv * e - .v o)
          (.eq0 (.v o * e) (cont o))

end Clap.IsZero
