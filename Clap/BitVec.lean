import Clap.Primes
import Mathlib.FieldTheory.Finite.Basic

namespace Clap

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Computes the `n` bit binary representation of `f`.
    If `n < minBits f` the result is truncated.
    If `n > minBits f` the result is padded with zeros.
-/

def num2bitsLsbPure (n : ℕ) (f : ZMod p) : List (ZMod p) :=
  match n with
  | 0 => []
  | n+1 =>
    let bit := f.val % 2
    let rem := f.val / 2
    bit::(num2bitsLsbPure n rem)

#guard num2bitsLsbPure (p := Primes.babybear) 3 1 = [1,0,0]
#guard num2bitsLsbPure (p := Primes.babybear) 3 4 = [0,0,1]
#guard num2bitsLsbPure (p := Primes.babybear) 4 1 = [1,0,0,0]

def num2bitsMsbPure (n : ℕ) (f : ZMod p) : List (ZMod p) :=
  num2bitsLsbPure n f |> List.reverse

#guard num2bitsMsbPure (p := Primes.babybear) 3 1 = [0,0,1]
#guard num2bitsMsbPure (p := Primes.babybear) 4 1 = [0,0,0,1]

def bits2num (bits : List (ZMod p)) : (ZMod p) :=
  List.foldr (fun b acc => b + 2 * acc) 0 bits

lemma bits2num_spec {bits : List (ZMod p)} : bits2num bits = ∑ i : Fin bits.length, 2 ^ i.1 * bits[i] := by
  unfold bits2num
  set w := bits.toArray.toList.length with w_eq
  have h₁ {i : ℕ} (h : i < w) : List.drop (w - (i + 1)) (List.finRange w) = ⟨w - (i + 1), by omega⟩ :: List.drop (w - i) (List.finRange w) := by
    have : w - i = (w - (i + 1)) + 1 := by omega
    rw [this, List.drop_add_one_eq_tail_drop]
    have : List.drop (w - (i + 1)) (List.finRange w) ≠ [] := by
      simp_all only [ne_eq,
        List.drop_eq_nil_iff, List.length_finRange, not_le, tsub_lt_self_iff, add_pos_iff, zero_lt_one, or_true,
        and_true]
      omega
    rw (occs := .pos [1]) [←List.cons_head_tail this]
    congr
    simp
  have : List.foldr (fun b acc => b + 2 * acc) 0 bits.toArray.toList = List.foldr (fun i acc => bits[i] + 2 * acc) 0 (List.finRange w) := by
    generalize ls_eq : bits.toArray.toList = ls
    have : ls.length = w := by
      rw [←ls_eq, ←w_eq]
    set i := w with i_eq
    have w_sub_i_eq_zero : w - i = 0 := by
      rw [i_eq, tsub_self]
    have : ls = ls.drop (w - i) := by
      rw [w_sub_i_eq_zero, List.drop_zero]
    rw [this]; clear this
    have : List.finRange w = (List.finRange w).drop (w - i) := by
      rw [w_sub_i_eq_zero, List.drop_zero]
    rw [this]; clear this
    induction i with
    | zero =>
      have h₁ : List.drop (w - 0) ls = [] := by aesop (config := { useSimpAll  := false})
      have h₂ : List.drop (w - 0) (List.finRange w) = [] := by aesop (config := { useSimpAll  := false})
      rw [h₁, h₂]
      simp
    | succ i ih =>
      by_cases h : w ≤ i
      · have : w - i = w - (i + 1) := by omega
        rw [←this]
        exact ih
      · rw [not_le] at h
        have ls_drop_neq_nil : (List.drop (w - (i + 1)) ls) ≠ [] := by
          apply List.ne_nil_of_length_pos
          apply List.lt_length_drop
          omega
        have := Eq.symm (List.cons_head_tail ls_drop_neq_nil)
        have arith : w - (i + 1) + 1 = w - i := by omega
        rw [h₁ h, this, List.foldr_cons, List.foldr_cons, List.tail_drop, arith, ih, add_left_inj, List.head_drop]
        simp [←ls_eq]
  simp only [this, Fin.getElem_fin]
  have {f : Fin w → ZMod p} : (∑ i : Fin w, f i) = ((List.finRange w).map f).sum := rfl
  rw [this, List.sum, List.foldr_map]
  clear this
  have : List.foldr (fun i acc => bits[i.1] + 2 * acc) 0 (List.finRange w) = 2 ^ 0 * List.foldr (fun i acc => bits[i.1] + 2 * acc) 0 (List.finRange w) := by
    simp
  rw [this]
  clear this
  have : List.finRange w = (List.finRange w).drop 0 := by simp
  rw [this]
  clear this
  set i := (w : ℕ) with i_eq
  have : w - i = 0 := by
    simp [i_eq]
  simp only [←this]
  clear i_eq this
  induction i with
  | zero =>
    have : (List.finRange w).drop w = [] := by
      simp
    simp [this]
  | succ i ih =>
    by_cases h : i ≥ w
    · have : w - (i + 1) = w - i := by
        omega
      rw [this]
      exact ih
    · rw [ge_iff_le, not_le] at h
      have {a : ZMod p} : a ^ (w - (i + 1)) * a = a ^ (w - i) := by
        rw [←pow_succ]
        grind
      simp only [h₁ h, Nat.cast_ofNat, List.foldr_cons, LeftDistribClass.left_distrib, ←mul_assoc, this]
      erw [ih]

end Clap
