import Clap.Lang.F.mkF
import Clap.Lang.F.mkMul
import Clap.Lang.F.mkSub
import Clap.Lang.FUnit.eq0

namespace Clap.Lang.FB

variable {p : ℕ}

def assertBool (f : F p) : ClapM p Unit := do
  let one ← mkF 1
  let comp ← mkSub one f
  let prod ← mkMul f comp
  eq0 prod

namespace assertBool

lemma convertsM
  [Fact (Nat.Prime p)]
  {state : ClapMState p}
  {f : F p}
  {f_val : ZMod p}
  (h_f : Converts F.conversion state f f_val)
:
  ConvertsM FUnit.conversion (assertBool f) state () (f_val = 0 ∨ f_val = 1)
:= by
  haveI : p.AtLeastTwo := ⟨(Fact.out : Nat.Prime p).two_le⟩
  unfold assertBool
  step mkF.convertsM as one
  step mkSub.convertsM h_one h_f as comp
  step mkMul.convertsM h_f h_comp as prod
  apply convertsM_of_convertsM (eq0.convertsM h_prod)
  . rfl
  . -- the preceding steps all have `True` constraints, which `convertsM_bind` threads
    -- through as `True → True → True → _` on the right of the iff
    simp only [true_implies]
    constructor
    . -- soundness: f * (1 - f) = 0 → f = 0 ∨ f = 1
      intro h
      rcases mul_eq_zero.mp h with h | h
      . exact Or.inl h
      . rw [sub_eq_zero] at h
        exact Or.inr h.symm
    . -- completeness: f = 0 ∨ f = 1 → f * (1 - f) = 0
      rintro (rfl | rfl) <;> simp

end Clap.Lang.FB.assertBool
