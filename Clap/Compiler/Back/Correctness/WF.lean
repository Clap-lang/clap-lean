import Clap.Compiler.Back.Circuit

open Clap

namespace Clap

variable {p : ℕ}

def circuitWF : Circuitₑ p → Prop
| .nil => True
| .eq0 _ c => circuitWF c
| .lam c => ∀ i, circuitWF (c i)
| .share _ c => ∀ i, circuitWF (c i)
| .isZero _ c => ∀ i, circuitWF (c i)
| .num2bits w _ c => 2 ^ w < p ∧ ∀ i, circuitWF (c i)
| .fpmul w k _ _ _ c => 2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 4) ≤ p ∧ ∀ i, circuitWF (c i)

end Clap
