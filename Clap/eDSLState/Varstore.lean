import Mathlib.Data.ZMod.Basic
import Std.Data.ExtTreeMap

namespace Clap

def VarStore (p : ℕ) := Std.ExtTreeMap ℕ (ZMod p) (cmp := compare)
deriving Inhabited, Repr

instance {p : ℕ} : EmptyCollection (VarStore p) := inferInstanceAs (EmptyCollection (Std.ExtTreeMap ℕ (ZMod p)))

instance {p : ℕ} : GetElem? (VarStore p) ℕ (ZMod p) (λ Γ x ↦ Γ.contains x) where
  getElem  Γ x h := Γ.get x h
  getElem? Γ x   := Γ.get? x

instance {p : ℕ} : HasSubset (VarStore p) where
  Subset Γ1 Γ2 := ∀ k : ℕ, Γ1[k]?.isSome → Γ1[k]? = Γ2[k]?

def VarStore.ofArray {p : ℕ} (elem : Array (ℕ × ZMod p)) : VarStore p :=
  Std.ExtTreeMap.ofArray elem (cmp := compare)

end Clap
