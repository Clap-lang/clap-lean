import Lean

import Mathlib.Data.ZMod.Basic

@[simp]
theorem Vector.range_one : Vector.range 1 = #v[0] := rfl

namespace Clap

initialize Lean.registerTraceClass `Clap.Preprocessor

initialize Lean.registerTraceClass `Clap.Preprocessor.addLambdas (inherited := true)

register_simp_attr Clap.monads

@[simp, grind .]
lemma ZMod.zero_ne_one
  {p : ℕ}
  [p_ge_2 : Fact (p ≥ 2)]
:
  (0: ZMod p) ≠ (1 : ZMod p)
:= by
  obtain ⟨p_ge_2⟩ := p_ge_2
  symm
  simp only [ne_eq, ZMod.one_eq_zero_iff]
  omega

end Clap
