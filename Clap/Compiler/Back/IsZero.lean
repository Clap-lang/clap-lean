import Clap.Compiler.Back.Cs
import Clap.Compiler.Back.Wg

namespace Clap.IsZero

variable {p : ℕ} {var : Type} [inst : Fact (Nat.Prime p)] [inst' : Fact (p > 2)]

def isZero_circuit (e : Exp p var) (cont : var → Cs p var) : Cs p var :=
  .lam fun inv =>
      .lam fun o =>
        .eq0 (.c 1 - .v inv * e - .v o)
          (.eq0 (.v o * e) (cont o))

def isZero_wg (e : Expₑ p) (cont : ZMod p → Wg p) : Wg p :=
  letI e := e.eval
    let o : ZMod p := if e = 0 then 1 else 0
    .cons e⁻¹ (.cons o (cont o))

end Clap.IsZero
