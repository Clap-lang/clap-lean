import Mathlib.Data.ZMod.Basic
import Std.Data.ExtTreeMap

namespace Clap

abbrev VarStore (p : ℕ) := Std.ExtTreeMap ℕ (ZMod p) (cmp := compare)
-- deriving Inhabited, Repr

-- def VarStore.contains {p : ℕ} (Γ : VarStore p) (x : ℕ) : Bool := Std.ExtTreeMap.contains Γ x

-- instance {p : ℕ} : EmptyCollection (VarStore p) := inferInstanceAs (EmptyCollection (Std.ExtTreeMap ℕ (ZMod p)))

-- instance instVarStoreGetElem? {p : ℕ} : GetElem? (VarStore p) ℕ (ZMod p) (λ (Γ : VarStore p) x ↦ Γ.contains x) where
--   getElem  Γ x h := Γ.get x h
--   getElem? Γ x   := Γ.get? x

-- instance {p : ℕ} : LawfulGetElem (VarStore p) ℕ (ZMod p) (λ (Γ : VarStore p) x ↦ Γ.contains x) where
--   getElem?_def Γ x inst := by
--     have : LawfulGetElem (Std.ExtTreeMap ℕ (ZMod p)) ℕ (ZMod p) (λ m x ↦ m.contains x) := inferInstance
--     obtain ⟨h_getElem, _⟩ := this
--     specialize h_getElem Γ x
--     unfold VarStore.contains
--     unfold_projs at h_getElem ⊢
--     convert h_getElem

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

end Clap.VarStore
