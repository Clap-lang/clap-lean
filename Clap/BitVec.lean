import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.DepRewrite

import Clap.Primes
import Clap.Wheels

namespace Clap

def nat2bitsLsb (n : ℕ) (f : ℕ) : List ℕ :=
  match n with
  | 0 => []
  | n+1 =>
    let bit := f % 2
    let rem := f / 2
    bit::(nat2bitsLsb n rem)

variable {p : ℕ}

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

lemma num2bitsLsbPure_length {w : ℕ} {v : ZMod p} : (num2bitsLsbPure w v).length = w := by
  revert v
  induction w with
  | zero => simp [num2bitsLsbPure]
  | succ w ih =>
    intros v
    unfold num2bitsLsbPure
    simp [ih]

lemma num2bitsLsbPure_bits {w : ℕ} {v : ZMod p} : ∀ i : Fin _, (num2bitsLsbPure w v)[i] = 0 ∨ (num2bitsLsbPure w v)[i] = 1 := by
  revert v
  induction w with
  | zero =>
    intros _ i
    erw [List.length_nil] at i
    exact Fin.elim0 i
  | succ w ih =>
    intros v
    rw! (castMode := .all) [num2bitsLsbPure_length] at ⊢
    intros i
    simp only [num2bitsLsbPure]
    by_cases h : i = 0
    · simp only [h, Fin.getElem_fin, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero]
      rcases Nat.mod_two_eq_zero_or_one v.val <;> aesop
    · have : ∃ i' : Fin w, i'.succ = i := by
        use ⟨i.val - 1, by omega⟩
        have : i.val - 1 + 1 = i.val := by
          apply Nat.sub_add_cancel
          by_contra h'
          apply h
          simpa using h'
        simp only [Fin.succ_mk, this]
      rcases this with ⟨i', this⟩
      rw [←this]
      simp only [Fin.getElem_fin, Fin.val_succ, List.getElem_cons_succ]
      specialize @ih  ((v.val / 2) : ℕ)
      rw! (castMode := .all) [num2bitsLsbPure_length] at ih
      exact ih i'

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

variable [inst : Fact (Nat.Prime p)]  [inst' : Fact (2 < p)]

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
        · rw [h] at inst
          exact Nat.prime_zero_false inst.out
        · rw [h] at inst
          exact Nat.prime_one_false inst.out
        · rw [h] at inst'
          simpa using inst'.out
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

lemma bits2num_bound {bits : List (ZMod p)} :
    (∀ i : Fin bits.length, bits[i] = 0 ∨ bits[i] = 1) → (bits2num bits).val < 2 ^ bits.length := by
  intros h
  by_cases h' : 2 ^ bits.length < p
  · rw [bits2num_spec, sum_pow_2_eq h' h]
    apply lt_of_le_of_lt
    · apply Finset.sum_le_sum
      intros i _
      have {a b : ℕ} : b = 0 ∨ b = 1 → a * b ≤ a := by
        aesop
      apply this
      rcases h i with h | h <;> simp [h, ZMod.val_one]
    · rw [Fin.sum_univ_eq_sum_range, Nat.geomSum_eq (by decide)]
      simp
  · rw [not_lt] at h'
    exact lt_of_lt_of_le (ZMod.val_lt _) h'

lemma num2bitsLsbPure_of_bits2num_eq {ls : List (ZMod p)} :
  2 ^ ls.length < p →
  (∀ i : Fin ls.length, ls[i] = 0 ∨ ls[i] = 1) →
  (num2bitsLsbPure ls.length (bits2num ls)) = ls := by
    intros p_bound h'
    rw [bits2num_spec]
    induction ls with
    | nil =>
     simp [num2bitsLsbPure]
    | cons l ls ih =>
      simp only [List.length_cons, Fin.getElem_fin, num2bitsLsbPure, List.cons.injEq]
      simp only [List.length_cons] at p_bound
      have := sum_pow_2_eq p_bound h'
      rw [←show Fin.fintype (ls.length + 1) = Fin.fintype (l :: ls).length from rfl]
      simp at this; rw [this]
      have len_bound : 2 ^ ls.length < p := by rw [pow_succ] at p_bound; nlinarith
      specialize ih len_bound (fun i ↦ by simpa using h' i.succ)
      have : ∑ i : Fin (ls.length + 1), 2 ^ i.1 * (l :: ls)[i.1].val = l.val + 2 * ∑ i : Fin ls.length, 2 ^ i.1 * ls[i].val := by
        induction ls with
        | nil => simp
        | cons l' ls ih' =>
          rw [Fin.univ_succ]
          simp only [Finset.sum_cons, List.length_cons, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero,
            List.getElem_cons_zero, one_mul, Finset.sum_map, Function.Embedding.coeFn_mk,
            Fin.val_succ, List.getElem_cons_succ, Fin.getElem_fin, add_right_inj, Finset.mul_sum]
          grind
      have l_lt_2 : l.val < 2 := by
        simp only [List.length_cons] at h'
        specialize h' 0; simp only [Fin.getElem_fin, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
          List.getElem_cons_zero] at h'
        rcases h' with h' | h' <;> simp [h', ZMod.val_one]
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l_lt_2]
      apply And.intro (by simp)
      have l_div_2_eq : l.val / 2 = 0 := by
        apply Nat.div_eq_of_lt
        have : (l :: ls).length = ls.length + 1 := by simp
        simp only [List.length_cons] at h'
        rcases h' 0 with h' | h' <;> simp only [Fin.getElem_fin, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
          List.getElem_cons_zero] at h' <;> simp [h', ZMod.val_one]
      have : ∀ (i : Fin ls.length), ls[i] = 0 ∨ ls[i] = 1 :=
        fun i ↦ by simpa [List.length_cons] using h' i.succ
      rw [Nat.add_mul_div_left _ _ ((by decide) : 0 < 2), l_div_2_eq, zero_add, ←sum_pow_2_eq len_bound this]
      convert ih
      exact ZMod.natCast_zmod_val _

lemma bits2num_of_num2bitsLsbPure_eq {w : ℕ} {v : ZMod p} : v.val < 2 ^ w → bits2num (num2bitsLsbPure w v) = v := by
  revert v
  induction w with
  | zero =>
    intros _ h
    simp only [pow_zero, Nat.lt_one_iff, ZMod.val_eq_zero] at h
    simp [h, num2bitsLsbPure, bits2num]
  | succ w ih =>
    intros v h
    unfold num2bitsLsbPure bits2num
    simp only [List.foldr_cons]
    unfold bits2num at ih
    have h' : (((v.val / 2) : ℕ) : ZMod p).val < 2 ^ w := by
      simp only [ZMod.val_natCast]
      apply lt_of_le_of_lt (Nat.mod_le _ _)
      exact Nat.nat_repr_len_aux v.val 2 w (by decide) h
    rw [ih h']
    apply ZMod.val_injective
    rw [ZMod.val_add, ZMod.val_mul]
    simp [ZMod.val_ofNat_of_lt inst'.out]
    rw [Nat.mod_add_div, Nat.mod_eq_of_lt]
    exact ZMod.val_lt v

end Clap
