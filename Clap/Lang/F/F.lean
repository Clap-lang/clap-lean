import Clap.eDSLState.eDSL
import Clap.eDSLState.Spec

import Clap.Lang.Wheels

namespace Clap.Edsl.Lang

abbrev F p := FixedExp p

namespace F

variable {p : ℕ}

def isValid (x : F p) (varStore : ℕ → Option (ZMod p)) : Prop :=
  (x.eval varStore).isSome

instance : IsValid p (F p) := ⟨fun Γ x ↦ F.isValid x Γ⟩

instance : VarStoreSize p (F p) where
  size := 1
  toLinear Γ x := #v[x.eval Γ |>.getD 42]

instance : Convert p (F p) (ZMod p) where
  toIdeal Γ x := x.eval Γ
  toRepresents v := .c v
  someOfIsValid := fun _ _ h ↦ h
  toIdealtoRepresents := fun _ _ ↦ by simp [FixedExp.eval]
  toRepresentstoIdeal := fun Γ x h ↦ by simp [FixedExp.eval, Option.some_get]

end F

end Clap.Edsl.Lang
