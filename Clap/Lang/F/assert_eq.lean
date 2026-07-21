import Clap.Lang.F.F

namespace Clap.Edsl.Lang.F

def assert_eq {p : ℕ} [Fact (p ≥ 2)] (a b : F p) : Edsl.CircuitStateM p Unit := do
  Edsl.eq0 (a - b)

namespace assert_eq

def spec (p : ℕ) [Fact (p ≥ 2)] : Prop :=
  matchesBinaryAssertion p assert_eq (allocatesN := 0)
    (constraints := fun a b : ZMod p ↦ a = b)

lemma equiv (p : ℕ) [Fact (p ≥ 2)] : spec p := by
  intro a b varStore numAlloc ha hb
  obtain ⟨av, hav⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨bv, hbv⟩ := Option.isSome_iff_exists.mp hb
  rw [CircuitStateM.runAndEval_eq]
  unfold assert_eq
  refine ⟨?_, ?_, ?_⟩
  · grind [FixedExp.eval_sub_some hav hbv, sub_eq_zero]
  · grind
  · intro n h_n; grind

end assert_eq

end Clap.Edsl.Lang.F
