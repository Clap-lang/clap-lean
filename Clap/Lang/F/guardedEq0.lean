import Clap.Lang.F.F
import Clap.Lang.FB.FB

namespace Clap.Edsl.Lang.F

/-- asserts `constraint == 0` only when `guard == 1` -/
def guardedEq0 {p : ℕ} [Fact (p ≥ 2)] (guard : FB p) (constraint : F p) : Edsl.CircuitStateM p Unit :=
  Edsl.eq0 (guard * constraint)

/-- asserts `a == b` only when `guard == 1` -/
def guardedAssertEq {p : ℕ} [Fact (p ≥ 2)] (guard : FB p) (a b : F p) : Edsl.CircuitStateM p Unit :=
  guardedEq0 guard (a - b)

namespace guardedEq0

def guardedEq0_spec (p : ℕ) [Fact (p ≥ 2)] : Prop :=
  matchesBinaryPredicatePure p (fun (g : Bool) (c : ZMod p) ↦ g = true → c = 0) guardedEq0

lemma guardedEq0_equiv (p : ℕ) [Fact (p ≥ 2)] : guardedEq0_spec p := by sorry

def guardedAssertEq_spec (p : ℕ) [Fact (p ≥ 2)] : Prop :=
  matchesTernaryPredicatePure p (fun (g : Bool) (a b : ZMod p) ↦ g = true → a = b) guardedAssertEq

lemma guardedAssertEq_equiv (p : ℕ) [Fact (p ≥ 2)] : guardedAssertEq_spec p := by sorry

end guardedEq0

end Clap.Edsl.Lang.F
