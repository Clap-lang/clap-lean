import Mathlib.Data.ZMod.Basic
import Std.Data.ExtTreeMap

namespace Clap

abbrev VarStore (p : ℕ) := Std.ExtTreeMap ℕ (ZMod p) (cmp := compare)

namespace VarStore

@[grind =]
instance {p : ℕ} : HasSubset (VarStore p) where
  Subset Γ1 Γ2 := ∀ k : ℕ, Γ1[k]?.isSome → Γ1[k]? = Γ2[k]?

lemma hasSubset_def {p} {Γ₁ Γ₂ : VarStore p} :
  (Γ₁ ⊆ Γ₂) = ∀ k : ℕ, Γ₁[k]?.isSome → Γ₁[k]? = Γ₂[k]? := rfl

lemma subset_insert {p} {Γ : VarStore p} {k} {v} {h : k ∉ Γ}:
  Γ ⊆ Γ.insert k v
:= by
  aesop (add simp hasSubset_def) (add safe (by grind))

@[grind _=_]
lemma mem_iff_mem_keys {p} {Γ : VarStore p} {k}:
  k ∈ Γ ↔ k ∈ Γ.keys
:= by
  grind

end Clap.VarStore
