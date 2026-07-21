import Clap.Lang.F.F
import Clap.Lang.FB.FB

namespace Clap.Edsl.Lang.F

/-- asserts `constraint == 0` only when `guard == 1` -/
def guardedEq0 {p : ℕ} [Fact (p ≥ 2)] [p.AtLeastTwo] (guard : FB p) (constraint : F p) : Edsl.CircuitStateM p Unit :=
  Edsl.eq0 (guard * constraint)

/-- asserts `a == b` only when `guard == 1` -/
def guardedAssertEq {p : ℕ} [Fact (p ≥ 2)] [p.AtLeastTwo] (guard : FB p) (a b : F p) : Edsl.CircuitStateM p Unit :=
  guardedEq0 guard (a - b)

namespace guardedEq0

def guardedEq0_spec (p : ℕ) [Fact (p ≥ 2)] [p.AtLeastTwo] : Prop :=
  matchesBinaryAssertion p guardedEq0 (allocatesN := 0)
    (constraints := fun (g : Bool) (c : ZMod p) ↦ g = true → c = 0)

lemma guardedEq0_equiv (p : ℕ) [Fact (p ≥ 2)] [p.AtLeastTwo] : guardedEq0_spec p := by
  intro guard constraint varStore numAlloc hg hc
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp hc
  rw [CircuitStateM.runAndEval_eq]
  unfold guardedEq0
  refine ⟨?_, ?_, ?_⟩
  · rcases hg with hg | hg <;>
      grind [FixedExp.eval_mul_some hg hcv]
  · grind
  · intro n h_n; grind

def guardedAssertEq_spec (p : ℕ) [Fact (p ≥ 2)] [p.AtLeastTwo] : Prop :=
  matchesTernaryAssertion p guardedAssertEq (allocatesN := 0)
    (constraints := fun (g : Bool) (a b : ZMod p) ↦ g = true → a = b)

lemma guardedAssertEq_equiv (p : ℕ) [Fact (p ≥ 2)] [p.AtLeastTwo] : guardedAssertEq_spec p := by
  intro guard a b varStore numAlloc hg ha hb
  obtain ⟨av, hav⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨bv, hbv⟩ := Option.isSome_iff_exists.mp hb
  rw [CircuitStateM.runAndEval_eq]
  unfold guardedAssertEq guardedEq0
  refine ⟨?_, ?_, ?_⟩
  · rcases hg with hg | hg <;>
      grind [FixedExp.eval_mul_some hg (FixedExp.eval_sub_some hav hbv), sub_eq_zero]
  · grind
  · intro n h_n; grind

end guardedEq0

end Clap.Edsl.Lang.F
