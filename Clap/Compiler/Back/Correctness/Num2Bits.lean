import Clap.Compiler.Back.Compilation
import Clap.Compiler.Back.Correctness.WF
import Clap.Compiler.Back.IsZero
import Clap.Compiler.Back.Num2Bits
import Clap.Compiler.Back.Simulation

variable {p : ℕ} {var : Type} [inst : Fact (Nat.Prime p)] [inst' : Fact (p > 2)]

open Clap Simulation

namespace Clap.Num2Bits

omit inst' in
lemma assert_bits_e_wrap {wg : Wg p} {ls : List (ZMod p)} {rest : Cs p (ZMod p)} :
    wrap wg (Num2Bits.assert_bits_e ls rest) = Num2Bits.assert_bits_e ls (wrap wg rest) := by
  unfold Num2Bits.assert_bits_e Num2Bits.assert_bit_e
  induction ls with
  | nil => simp
  | cons l ls ih => simpa [wrap] using ih

lemma num2bits_soundness {w : ℕ} {e : Exp p (ZMod p)} {c : List (ZMod p) → Circuit p (ZMod p)}
      (ih : ∀ (a : List (ZMod p)), circuitWF (c a) → wrBisim (c a).eval (c a).toCs.eval) :
    circuitWF (Circuit.num2bits w e c) → wrBisim (Circuit.num2bits w e c).eval (Circuit.num2bits w e c).toCs.eval := by
  rintro ⟨inv, h⟩
  simp [Circuit.eval, Circuit.toCs]
  apply rw_bisim_uncurry
  intros args
  by_cases cond₁ : Num2Bits.assert_bits args.toList <;> by_cases cond₂ : Exp.eval e = bits2num args.toList
  · rw [Num2Bits.reduce ⟨cond₁, cond₂⟩]
    have : e.eval.val < 2 ^ w := by
      have : w = args.toArray.toList.length := by
        rw [Array.length_toList, Vector.size_toArray]
      simp only [cond₂, this]
      exact Num2Bits.bits2num_val_lt_2_pow_w_of_assert_bits cond₁
    simp [this]
    have : (num2bitsLsbPure w (bits2num args.toList)) = args.toList := by
      rw [Num2Bits.assert_bits_spec] at cond₁
      have : args.toArray.toList.length = w := by simp
      convert num2bitsLsbPure_of_bits2num_eq (by convert inv; grind) cond₁
      exact this.symm
    unfold Vector.toList at this
    erw [cond₂, this]
    exact ih _ (h args.toArray.toList)
  · rw [Num2Bits.reduce₁ cond₁, Num2Bits.fail₂ cond₂]
    exact wrBisim.none
  · rw [Num2Bits.fail₁ cond₁]
    exact wrBisim.none
  · rw [Num2Bits.fail₁ cond₁]
    exact wrBisim.none

lemma num2bits_completeness {w : ℕ} {e : Exp p (ZMod p)} {c : List (ZMod p) → Circuit p (ZMod p)}
    (ih : ∀ (a : List (ZMod p)), circuitWF (c a) → (c a).eval = (wrap (c a).toWg (c a).toCs).eval) :
    circuitWF (Circuit.num2bits w e c) →
      (Circuit.num2bits w e c).eval = (wrap (Circuit.num2bits w e c).toWg (Circuit.num2bits w e c).toCs).eval := by
  intros cWF
  unfold circuitWF at cWF
  rcases cWF with ⟨w_bound, cWF⟩
  unfold Circuit.eval Circuit.toWg Circuit.toCs Num2Bits.num2bits_wg Num2Bits.num2bits_circuit
  rw [foldr_curry num2bitsLsbPure_length]
  rw [Vector.toList, Num2Bits.assert_bits_e_wrap]
  unfold wrap
  simp only
  rw [Num2Bits.reduce₁ Num2Bits.assert_bits_of_num2bits]
  split_ifs with h
  · simp [ih _ (cWF _), Num2Bits.reduce₂ (bits2num_of_num2bitsLsbPure_eq h).symm]
  · rw [not_lt] at h
    unfold Cs.eval
    split_ifs with h'
    · exfalso
      have h' := add_eq_of_eq_sub h'.symm
      rw [zero_add] at h'
      rw [h', Num2Bits.bits2num_eq_eval_bits2num_e] at h
      have : (bits2num (num2bitsLsbPure w e.eval)).val < 2 ^ w := by
        have := @bits2num_bound p _ _ (num2bitsLsbPure w e.eval) num2bitsLsbPure_bits
        rw [num2bitsLsbPure_length] at this
        exact this
      linarith
    · rfl


end Clap.Num2Bits
