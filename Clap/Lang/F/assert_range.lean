import Clap.Lang.F.F
import Clap.Lang.F.assert_eq
import Clap.Lang.F.num2bits

namespace Clap.Edsl.Lang.F

variable {p : ℕ}

/-- Asserts `e` fits in `w` bits, i.e. `e.val < 2^w`. -/
def assert_range [p.AtLeastTwo] (w : ℕ) (e : F p) : Edsl.CircuitStateM p Unit := do
  let bits ← num2bits w e
  assert_eq (bits2num bits) e

namespace assert_range

def spec (p : ℕ) [p.AtLeastTwo] (w : ℕ) : Prop :=
  matchesUnaryAssertion p (assert_range w) (allocatesN := w)
    (constraints := fun (v : ZMod p) => v.val < 2^w)

lemma equiv (p : ℕ) [p.AtLeastTwo] (w : ℕ) : spec p w := by sorry

end assert_range

end Clap.Edsl.Lang.F
