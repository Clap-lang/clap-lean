import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.DepRewrite

import Clap.Primes
import Clap.Wheels

namespace Clap

def nat2bitsLsb (n : ℕ) (f : ℕ) : Vector ℕ n :=
  Vector.ofFn (fun i : Fin n => f / 2 ^ i.val % 2)

variable {p : ℕ}

/-- Computes the `n` bit binary representation of `f`.
    If `n < minBits f` the result is truncated.
    If `n > minBits f` the result is padded with zeros.
-/
def num2bitsLsbPure (n : ℕ) (f : ZMod p) : Vector (ZMod p) n :=
  Vector.ofFn (fun i : Fin n => (f.val / 2 ^ i.val % 2 : ℕ))

lemma num2bitsLsbPure_bits {w : ℕ} {v : ZMod p} :
    ∀ i : Fin w, (num2bitsLsbPure w v)[i] = 0 ∨ (num2bitsLsbPure w v)[i] = 1 := by
  intro i
  simp only [num2bitsLsbPure]
  rcases Nat.mod_two_eq_zero_or_one (v.val / 2 ^ i.val) with h | h <;> simp [h]

#guard (num2bitsLsbPure (p := Primes.babybear) 3 1).toList = [1, 0, 0]
#guard (num2bitsLsbPure (p := Primes.babybear) 3 4).toList = [0, 0, 1]
#guard (num2bitsLsbPure (p := Primes.babybear) 4 1).toList = [1, 0, 0, 0]

def num2bitsMsbPure (n : ℕ) (f : ZMod p) : Vector (ZMod p) n :=
  (num2bitsLsbPure n f).reverse

#guard (num2bitsMsbPure (p := Primes.babybear) 3 1).toList = [0, 0, 1]
#guard (num2bitsMsbPure (p := Primes.babybear) 4 1).toList = [0, 0, 0, 1]

def bits2num {n : ℕ} (bits : Vector (ZMod p) n) : ZMod p :=
  bits.toList.foldr (fun b acc => b + 2 * acc) 0

private lemma ofFn_foldr_spec {n : ℕ} (f : Fin n → ZMod p) :
    (List.ofFn f).foldr (fun b acc => b + 2 * acc) 0 = ∑ i : Fin n, 2 ^ i.1 * f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.foldr_cons]
    rw [show (List.ofFn fun i => f i.succ).foldr (fun b acc => b + 2 * acc) 0 =
             ∑ i : Fin n, 2 ^ i.1 * f i.succ from ih _]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros i _
    rw [Fin.val_succ, pow_succ]; ring

lemma bits2num_spec {n : ℕ} {bits : Vector (ZMod p) n} :
    bits2num bits = ∑ i : Fin n, 2 ^ i.1 * bits[i] := by
  simp only [bits2num]
  have key : bits.toList = List.ofFn (fun i : Fin n => bits[i.val]) := by
    apply List.ext_getElem
    · simp
    · intro i h1 _
      simp only [List.getElem_ofFn]
      simp [Vector.toList]
  rw [key]
  exact ofFn_foldr_spec (fun i : Fin n => bits[i.val])

variable [inst : Fact (Nat.Prime p)] [inst' : Fact (2 < p)]

lemma sum_pow_2_eq {w : ℕ} {f : Fin w → ZMod p} :
    2 ^ w < p → (∀ i, f i = 0 ∨ f i = 1) →
      (∑ i, 2 ^ i.1 * f i).val = ∑ i, 2 ^ i.1 * (f i).val := by
  intros h₁ h₂
  rw [ZMod.val_sum]
  have : (∑ i, (2 ^ i.1 * f i).val) = (∑ i, 2 ^ i.1 * (f i).val) := by
    congr; ext i
    rw [ZMod.val_mul]
    rcases h₂ i with h₂ | h₂ <;> rw [h₂]
    · simp
    · have p_fact : 2 < p := by
        refine Nat.two_lt_of_ne ?_ ?_ ?_ <;> intros h
        · rw [h] at inst; exact Nat.prime_zero_false inst.out
        · rw [h] at inst; exact Nat.prime_one_false inst.out
        · rw [h] at inst'; simpa using inst'.out
      have : ZMod.val (2 : ZMod p) ^ i.1 < p := by
        rw [ZMod.val_ofNat_of_lt p_fact]
        have : OfNat.ofNat 2 = 2 := by decide
        rw [this]
        transitivity
        exact (Nat.pow_lt_pow_iff_right (by decide)).mpr i.isLt
        exact h₁
      rw [ZMod.val_pow this, ZMod.val_one, mul_one, mul_one]
      rw [ZMod.val_ofNat_of_lt p_fact, Nat.mod_eq_of_lt]
      transitivity
      · exact (Nat.pow_lt_pow_iff_right (by decide)).mpr i.isLt
      · exact h₁
  rw [this, Nat.mod_eq_of_lt]
  apply lt_of_le_of_lt
  apply Finset.sum_le_sum
  intros i _
  have {a b : ℕ} : b = 0 ∨ b = 1 → a * b ≤ a := by aesop
  apply this
  rcases h₂ i with h₂ | h₂ <;> rw [h₂]
  · aesop
  · right; exact ZMod.val_one p
  refine lt_trans ?_ h₁
  rw [Fin.sum_univ_eq_sum_range, Nat.geomSum_eq]
  simp; rfl

lemma bits2num_bound {n : ℕ} {bits : Vector (ZMod p) n} :
    (∀ i : Fin n, bits[i] = 0 ∨ bits[i] = 1) → (bits2num bits).val < 2 ^ n := by
  intros h
  by_cases h' : 2 ^ n < p
  · rw [bits2num_spec, sum_pow_2_eq h' h]
    apply lt_of_le_of_lt
    · apply Finset.sum_le_sum
      intros i _
      have {a b : ℕ} : b = 0 ∨ b = 1 → a * b ≤ a := by aesop
      apply this
      rcases h i with hi | hi <;> simp [hi, ZMod.val_one]
    · rw [Fin.sum_univ_eq_sum_range, Nat.geomSum_eq (by decide)]
      simp
  · rw [not_lt] at h'
    exact lt_of_lt_of_le (ZMod.val_lt _) h'

lemma num2bitsLsbPure_of_bits2num_eq {n : ℕ} {bits : Vector (ZMod p) n} :
    2 ^ n < p →
    (∀ i : Fin n, bits[i] = 0 ∨ bits[i] = 1) →
    (num2bitsLsbPure n (bits2num bits)) = bits := by
  sorry

lemma bits2num_of_num2bitsLsbPure_eq {n : ℕ} {v : ZMod p} :
    v.val < 2 ^ n → bits2num (num2bitsLsbPure n v) = v := by
  sorry

end Clap
