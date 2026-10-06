import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Vectors as polynomials (Fiat–Shamir)

The algebra behind the Fiat–Shamir string checks. A vector `v` is read as the polynomial
`Σ v[i] · Xⁱ`, and evaluated at a challenge `α`. Vectors are compared through `ext v i`, their zero
extension, so no index bounds appear. A nonzero polynomial has few roots, which bounds the
challenges a false instance passes at.

The gadget-specific identities, with their specs `SubstrAt` and `IsConcat`, live with their
gadgets in `Lang/Data/FString/isSubstring.lean` and `Lang/Data/FString/assertIsConcatenation.lean`.
-/

open Polynomial

namespace Clap.FiatShamir

variable {p : ℕ}

/-- The zero extension of `v`: `v[i]` inside, `0` beyond. -/
def ext {n : ℕ} (v : Vector (ZMod p) n) (i : ℕ) : ZMod p := (v[i]?).getD 0

lemma ext_of_lt {n : ℕ} (v : Vector (ZMod p) n) {i : ℕ} (h : i < n) : ext v i = v[i] := by
  simp [ext, h]

lemma ext_of_le {n : ℕ} (v : Vector (ZMod p) n) {i : ℕ} (h : n ≤ i) : ext v i = 0 := by
  simp [ext, show ¬ i < n by omega]

/-- `Σ v[i] · Xⁱ`. -/
noncomputable def vecPoly {n : ℕ} (v : Vector (ZMod p) n) : (ZMod p)[X] :=
  ∑ i : Fin n, C v[i] * X ^ (i : ℕ)

/-- `Σ v[i] · αⁱ`, what `dotProduct v (powers α n)` computes. -/
def evalAt {n : ℕ} (v : Vector (ZMod p) n) (α : ZMod p) : ZMod p :=
  ∑ i : Fin n, v[i] * α ^ (i : ℕ)

lemma coeff_vecPoly {n : ℕ} (v : Vector (ZMod p) n) (m : ℕ) : (vecPoly v).coeff m = ext v m := by
  unfold vecPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases h : m < n
  · rw [Finset.sum_eq_single ⟨m, h⟩]
    · simp [ext_of_lt v h]
    · intro i _ hi
      have : m ≠ i.val := fun h' ↦ hi (Fin.ext h'.symm)
      simp [this]
    · simp
  · rw [ext_of_le v (by omega)]
    apply Finset.sum_eq_zero
    intro i _
    have : m ≠ i.val := by omega
    simp [this]

lemma eval_vecPoly {n : ℕ} (v : Vector (ZMod p) n) (α : ZMod p) :
    (vecPoly v).eval α = evalAt v α := by
  simp [vecPoly, evalAt, eval_finsetSum]

lemma natDegree_vecPoly_le {n : ℕ} (v : Vector (ZMod p) n) : (vecPoly v).natDegree ≤ n - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_vecPoly, ext_of_le v]
  have : n - 1 < N := by exact_mod_cast hN
  omega

lemma coeff_X_pow_mul_vecPoly {n : ℕ} (v : Vector (ZMod p) n) (s m : ℕ) :
    (X ^ s * vecPoly v).coeff m = if s ≤ m then ext v (m - s) else 0 := by
  rw [coeff_X_pow_mul', coeff_vecPoly]

lemma natDegree_X_pow_mul_vecPoly_le {n : ℕ} (v : Vector (ZMod p) n) (s : ℕ) :
    (X ^ s * vecPoly v).natDegree ≤ s + (n - 1) := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  have hN' : s + (n - 1) < N := by exact_mod_cast hN
  rw [coeff_X_pow_mul_vecPoly]
  split
  · rw [ext_of_le v (by omega)]
  · rfl

/-! ## Counting accepting challenges -/

/-- A nonzero polynomial of degree at most `d` vanishes at no more than `d` points -/
lemma card_roots_le [Fact (Nat.Prime p)] {P : (ZMod p)[X]} (hP : P ≠ 0) {d : ℕ}
    (hd : P.natDegree ≤ d) :
    (Finset.univ.filter fun α : ZMod p ↦ P.eval α = 0).card ≤ d := by
  classical
  calc (Finset.univ.filter fun α : ZMod p ↦ P.eval α = 0).card
      ≤ P.roots.toFinset.card := by
        apply Finset.card_le_card
        intro α hα
        simp only [Finset.mem_filter] at hα
        simp [Multiset.mem_toFinset, mem_roots hP, IsRoot, hα.2]
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ ≤ d := hd

end Clap.FiatShamir
