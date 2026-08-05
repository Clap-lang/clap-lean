import Mathlib.LinearAlgebra.Lagrange

import CompPoly.Univariate.Basic
import CompPoly.Univariate.ToPoly.Equiv
import CompPoly.Univariate.ToPoly.Degree

import Clap.Compiler.Back.Compilation
import Clap.Compiler.Back.Correctness.Basic
import Clap.Compiler.Back.Correctness.Num2Bits
import Clap.Compiler.Back.Correctness.WF
import Clap.Compiler.Back.IsZero
import Clap.Compiler.Back.Num2Bits
import Clap.Compiler.Back.Simulation

variable {p : ℕ}  [inst : Fact (Nat.Prime p)] [inst' : Fact (p > 2)]

instance : NeZero p where
  out := by grind [inst'.out]

namespace Clap.FpMul

open Clap Simulation CompPoly CompPoly.CPolynomial

private lemma num2bits_wrBisim_cont
  {w : ℕ} {e : Expₑ p} {rest : Csₑ p} {d : denotation (ZMod p)} :
    (e.eval.val < 2 ^ w → wrBisim d rest.eval) →
      wrBisim d (Num2Bits.num2bits_circuit w e (fun _ ↦ rest)).eval := by
  intros hbisim
  unfold Num2Bits.num2bits_circuit
  apply rw_bisim_uncurry
  intro args
  simp only [Num2Bits.assert_bits_e_spec]
  split_ifs with h
  · simp only [Cs.eval]
    split_ifs with h'
    · apply hbisim
      rw [Exp.eval_sub] at h'
      rw [sub_eq_zero] at h'
      rw [←h']
      generalize h_eq : args.toList = ls
      rw [h_eq] at h' h
      have : w = ls.length := by grind
      rw [this]
      clear h_eq h' this
      induction ls with
      | nil =>
        simp [Num2Bits.bits2num_e, Exp.eval]
      | cons l ls ih =>
        specialize ih (fun i ↦ by simpa using h i.succ)
        simp [Num2Bits.bits2num_e, Exp.eval, ZMod.val_add, ZMod.val_mul] at ih ⊢
        apply Nat.mod_lt_of_lt
        have ih' : 2 * (List.foldr (fun b acc => Exp.v b + Exp.c 2 * acc) (Exp.c 0) ls).eval.val < 2 ^ (ls.length + 1) - 1 := by
          grind
        have : l.val ≤ 1 := by
          have := h ⟨0, by grind⟩
          simp at this
          rcases this with h | h <;> rw [h] <;> simp
          rw [ZMod.val_one_eq_one_mod]
          exact Nat.mod_le 1 p
        have := Nat.add_lt_add_of_le_of_lt this ih'
        have eq : 1 + (2 ^ (ls.length + 1) - 1) = 2 ^ (ls.length + 1) := by grind
        rw [eq] at this
        convert this
        exact ZMod.val_ofNat_of_lt inst'.out
    · exact wrBisim.none
  · exact wrBisim.none

lemma range_check_vec_circuit_spec
  {k : ℕ} {w : ℕ} {vec : Vector (Expₑ p) k} {cont : Csₑ p} {d : denotation (ZMod p)} :
    ((∀ i : Fin k, vec[i].eval.val < 2 ^ w) → wrBisim d cont.eval) →
      wrBisim d (range_check_vec_circuit w vec cont).eval := by
  intro hbisim
  unfold range_check_vec_circuit
  have : k = (List.finRange k).length := by simp
  revert this
  induction' k with k ih;
  · exact fun h => hbisim fun i => Fin.elim0 i;
  · simp [ List.finRange_succ ] at *;
    convert num2bits_wrBisim_cont _ using 1;
    · exact ⟨ inst'.out ⟩;
    · contrapose! ih;
      use Vector.ofFn (fun i : Fin k => vec[i.val + 1]);
      simp_all +decide [ Fin.forall_fin_succ, List.foldr_map ]

/-! ### Part 1: eval_poly evaluates to the expected sum -/
/-
The Exp-level fold in eval_poly evaluates to the corresponding ℤ/pℤ sum.
-/
omit inst' in
lemma eval_poly_eq_sum {n : ℕ} (v : Vector (Expₑ p) n) (x : ZMod p) :
    (eval_poly v x).eval = ∑ i : Fin n, v[i].eval * x ^ i.1 := by
      -- By definition of `eval_poly`, we can expand it as a sum of terms.
      have h_expand : eval_poly v x = List.foldr (fun (ind : Fin n) (acc : Expₑ p) => acc + v[ind] * .c (x ^ ind.1)) (.c 0) (List.finRange n) := by
        rfl;
      -- By definition of `eval`, we can expand it as a sum of terms.
      have h_expand_eval : ∀ (l : List (Fin n)), (List.foldr (fun (ind : Fin n) (acc : Expₑ p) => acc + v[ind] * .c (x ^ ind.1)) (.c 0) l).eval = List.sum (List.map (fun (ind : Fin n) => v[ind].eval * x ^ ind.1) l) := by
        intro l; induction l <;> simp_all +decide [ Exp.eval ] ;
        ring;
      convert h_expand_eval ( List.finRange n ) using 1
      aesop
      aesop

/-! ### Part 2: toCompPoly evaluated equals the expected sum -/
/-
CPolynomial.eval of toCompPoly equals the corresponding sum.
-/
omit inst' in
lemma toCompPoly_eval_eq_sum {n : ℕ} (w : Vector (ZMod p) n) (x : ZMod p) :
    CPolynomial.eval x (toCompPoly w) = ∑ i : Fin n, w[i] * x ^ i.1 := by
      -- By definition of `eval`, we know that `eval x (toCompPoly w)` is equal to `eval x (toPoly (toCompPoly w))`.
      rw [eval_toPoly];
      have h_toPoly : (toCompPoly w).toPoly = ∑ i : Fin n, Polynomial.C (w[i]) * Polynomial.X ^ i.val := by
        convert toPoly_sum
        rotate_left
        rotate_left
        exact inferInstance
        exact _root_.instLawfulBEq
        exact instDecidableEqFin n
        use fun i => CPolynomial.C ( w[i] ) * CPolynomial.X ^ i.val
        · unfold toCompPoly
          rw [ Finset.sum_eq_multiset_sum ]
          erw [ Multiset.map_coe ]
          norm_num
          induction ( List.finRange n ) <;> simp +decide [ * ]
          ring
        · simp
          grind +suggestions;
      simp +decide [ h_toPoly, Polynomial.eval_finset_sum ]

/-! ### Connecting eval_poly to toCompPoly (combines parts 1 and 2) -/
omit inst' in
lemma eval_poly_eval_eq {n : ℕ} (v : Vector (Expₑ p) n) (x : ZMod p) :
    (eval_poly v x).eval = CPolynomial.eval x (toCompPoly (v.map Exp.eval)) := by
  rw [eval_poly_eq_sum, toCompPoly_eval_eq_sum]
  congr 1; ext i; simp

omit inst' in
/-- The `toPoly` of `toCompPoly v` is the expected sum-of-monomials Polynomial. -/
lemma toPoly_toCompPoly {n : ℕ} (v : Vector (ZMod p) n) :
    (toCompPoly v).toPoly = ∑ i : Fin n, Polynomial.C (v[i]) * Polynomial.X ^ i.val := by
  convert toPoly_sum
  rotate_left
  rotate_left
  exact inferInstance
  exact _root_.instLawfulBEq
  exact instDecidableEqFin n
  use fun i => CPolynomial.C ( v[i] ) * CPolynomial.X ^ i.val
  · unfold toCompPoly
    rw [ Finset.sum_eq_multiset_sum ]
    erw [ Multiset.map_coe ]
    norm_num
    induction ( List.finRange n ) <;> simp +decide [ * ]
    ring
  · simp
    grind +suggestions

omit inst' in
/-- Coefficient of `toCompPoly v` at index `i`: returns `v[i]` if in bounds, else `0`. -/
lemma coeff_toCompPoly {n : ℕ} (v : Vector (ZMod p) n) (i : ℕ) :
    (toCompPoly v).coeff i = if h : i < n then v[i] else 0 := by
  rw [CPolynomial.coeff_toPoly]
  rw [toPoly_toCompPoly, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨i, h⟩ : Fin n)]
    · simp
    · intros j _ hj
      have hne : ¬ (i = j.val) := fun he => hj (Fin.ext he.symm)
      simp [hne]
    · intros h_no
      exact absurd (Finset.mem_univ _) h_no
  · apply Finset.sum_eq_zero
    intros j _
    have hne : ¬ (i = j.val) := fun he => h (he ▸ j.is_lt)
    simp [hne]

/-! ### Polynomial identity testing via toPoly -/
/-
Key polynomial identity testing: if two CPolynomials of bounded degree agree at
    enough distinct points, they are equal. Uses the toPoly isomorphism.
-/
omit inst' in
lemma cpoly_eq_of_eval_range {n : ℕ} (f g : CPolynomial (ZMod p))
    (hf : f.degree < (n : WithBot ℕ)) (hg : g.degree < (n : WithBot ℕ))
    (hn : n < p)
    (heq : ∀ i : ℕ, i < n → CPolynomial.eval (i : ZMod p) f = CPolynomial.eval (i : ZMod p) g) :
    f = g := by
      convert Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero _ _ _;
      any_goals exact Finset.image ( fun i : ℕ => ( i : ZMod p ) ) ( Finset.range n );
      rotate_left;
      all_goals try infer_instance;
      exact f.toPoly - g.toPoly;
      · rw [ Finset.card_image_of_injOn ];
        · refine' lt_of_le_of_lt ( Polynomial.degree_sub_le _ _ ) _;
          convert max_lt hf hg using 1;
          · rw [ CPolynomial.degree_toPoly, CPolynomial.degree_toPoly ]
          · norm_num
        · exact fun x hx y hy hxy => Nat.mod_eq_of_lt ( show x < p from lt_of_lt_of_le ( Finset.mem_range.mp hx ) hn.le ) ▸ Nat.mod_eq_of_lt ( show y < p from lt_of_lt_of_le ( Finset.mem_range.mp hy ) hn.le ) ▸ by simpa [ ZMod.natCast_eq_natCast_iff' ] using hxy
      · simp_all [ Polynomial.eval_sub, eval_toPoly ]
      · simp [ sub_eq_zero ]
        exact ⟨ fun h => h ▸ rfl, fun h => CPolynomial.toPolyLinearEquiv.injective h ⟩

/-! ### Degree bounds for toCompPoly -/
/-
toCompPoly has degree < n.
-/
omit inst' in
lemma toCompPoly_degree_lt {n : ℕ} (v : Vector (ZMod p) n) :
    (toCompPoly v).degree < (n : WithBot ℕ) := by
      rw [ CPolynomial.degree_lt_iff_coeff_zero ];
      intro k hk; rw [ CPolynomial.coeff_toPoly ] ;
      unfold toCompPoly;
      induction' ( List.finRange n ) with i l ih <;> simp_all
      · unfold toPoly; aesop;
      · convert Polynomial.coeff_add _ _ _ using 1;
        congr! 1;
        convert toPoly_add _ _;
        grind +suggestions

/-
The product of toCompPolys of size k has degree < 2k - 1 (as a nat).
-/
omit inst' in
lemma toCompPoly_mul_degree_lt {k : ℕ} (a b : Vector (ZMod p) k) :
    (toCompPoly a * toCompPoly b).degree < ((2 * k - 1 : ℕ) : WithBot ℕ) := by
      convert Polynomial.degree_mul_le _ _ |> lt_of_le_of_lt <| ?_ using 1;
      rotate_left;
      exact ZMod p;
      exact inferInstance;
      exact toCompPoly a |> CPolynomial.toPoly
      exact toCompPoly b |> CPolynomial.toPoly
      generalize_proofs at *;
      · have h_deg : (toCompPoly a).toPoly.degree < k ∧ (toCompPoly b).toPoly.degree < k := by
          convert toCompPoly_degree_lt a |> fun h => And.intro h ( toCompPoly_degree_lt b ) using 1; all_goals rw [ ← CPolynomial.degree_toPoly ];
        rcases k with ( _ | k ) <;> simp_all +decide [ two_mul ];
        by_cases ha : ( toCompPoly a ).toPoly = 0 <;> by_cases hb : ( toCompPoly b ).toPoly = 0 <;> simp_all +decide [ Polynomial.degree_eq_natDegree ];
        norm_cast at * ; linarith;
      · rw [ ← CPolynomial.toPoly_mul ];
        rw [ ← CPolynomial.degree_toPoly ]

omit inst' in
/-- CPolynomial.eval distributes over multiplication. -/
lemma cpoly_eval_mul (x : ZMod p) (f g : CPolynomial (ZMod p)) :
    CPolynomial.eval x (f * g) = CPolynomial.eval x f * CPolynomial.eval x g := by
  have h1 : CPolynomial.eval x f = Polynomial.eval x f.toPoly := by
    unfold CPolynomial.eval CPolynomial.toPoly
    exact (Raw.eval_toPoly_eq_eval x f.val).symm
  have h2 : CPolynomial.eval x g = Polynomial.eval x g.toPoly := by
    unfold CPolynomial.eval CPolynomial.toPoly
    exact (Raw.eval_toPoly_eq_eval x g.val).symm
  have h3 : CPolynomial.eval x (f * g) = Polynomial.eval x (f * g).toPoly := by
    unfold CPolynomial.eval CPolynomial.toPoly
    exact (Raw.eval_toPoly_eq_eval x (f * g).val).symm
  rw [h1, h2, h3, toPoly_mul, Polynomial.eval_mul]

omit inst' in
lemma assert_poly_eq_prod_spec {k : ℕ} {a b : Vector (Expₑ p) k}
  {c : Vector (ZMod p) (2 * k - 1)} {rest : Csₑ p} {d : denotation (ZMod p)} (hp : 2 * k - 1 < p)  :
    (toCompPoly c = toCompPoly (Vector.map Exp.eval a) * toCompPoly (Vector.map Exp.eval b) → wrBisim d rest.eval) →
      wrBisim d (assert_poly_eq_prod a b (c.map .v) rest).eval := by
  intro h;
  convert foldr_eq0_wrBisim _;
  any_goals assumption;
  rotate_left;
  exact fun i => ( eval_poly a i ) * ( eval_poly b i ) - ( eval_poly ( c.map Exp.v ) i );
  exact List.range ( 2 * k - 1 );
  · intro h';
    apply h;
    apply cpoly_eq_of_eval_range;
    exact toCompPoly_degree_lt c;
    · convert toCompPoly_mul_degree_lt ( Vector.map Exp.eval a ) ( Vector.map Exp.eval b ) using 1;
    · exact hp;
    · intro i hi; specialize h' i ( List.mem_range.mpr hi ) ; simp_all +decide [ eval_poly_eval_eq ] ;
      rw [ sub_eq_zero ] at h';
      rw [ cpoly_eval_mul, h' ];
      congr! 2;
      ext i; simp +decide [ Exp.eval ] ;
  · unfold assert_poly_eq_prod;
    induction ( List.range ( 2 * k - 1 ) ) <;> aesop

omit inst' in
/-- CPolynomial.eval distributes over subtraction. -/
private lemma cpoly_eval_sub (x : ZMod p) (f g : CPolynomial (ZMod p)) :
    CPolynomial.eval x (f - g) = CPolynomial.eval x f - CPolynomial.eval x g := by
  rw [eval_toPoly, eval_toPoly, eval_toPoly, toPoly_sub, Polynomial.eval_sub]

omit inst' in
lemma eq_check_spec {k : ℕ} {t ab : Vector (Expₑ p) (2*k - 1)} {q r p' : Vector (Expₑ p) k} {cont : Csₑ p} {d : denotation (ZMod p)} (hp : 2 * k - 1 < p) :
  (toCompPoly (t.map Exp.eval) = toCompPoly (ab.map Exp.eval) - (toCompPoly (p'.map Exp.eval)) * (toCompPoly (q.map Exp.eval)) - toCompPoly (r.map Exp.eval) → wrBisim d cont.eval) →
    wrBisim d
      (List.foldr
        (fun (i : ZMod p) ↦ Cs.eq0 (eval_poly t i - (eval_poly ab i - ((eval_poly p' i) * (eval_poly q i) + eval_poly r i))))
        cont
        (List.range (2*k - 1))
      ).eval := by
  intro h
  convert foldr_eq0_wrBisim _
  any_goals assumption
  rotate_left
  exact fun i => eval_poly t i - (eval_poly ab i - (eval_poly p' i * eval_poly q i + eval_poly r i))
  exact List.range (2 * k - 1)
  · intro h'
    apply h
    apply cpoly_eq_of_eval_range
    · exact toCompPoly_degree_lt (t.map Exp.eval)
    · -- (toCompPoly ab - toCompPoly p' * toCompPoly q - toCompPoly r).degree < 2*k-1
      -- Convert via toPoly and use Polynomial.degreeLT submodule
      rw [CPolynomial.degree_toPoly, toPoly_sub, toPoly_sub, toPoly_mul]
      apply Polynomial.mem_degreeLT.mp
      apply Submodule.sub_mem
      · apply Submodule.sub_mem
        · apply Polynomial.mem_degreeLT.mpr
          rw [← CPolynomial.degree_toPoly]
          exact toCompPoly_degree_lt (ab.map Exp.eval)
        · apply Polynomial.mem_degreeLT.mpr
          rw [← toPoly_mul, ← CPolynomial.degree_toPoly]
          exact toCompPoly_mul_degree_lt (p'.map Exp.eval) (q.map Exp.eval)
      · apply Polynomial.degreeLT_mono (by omega : k ≤ 2 * k - 1)
        apply Polynomial.mem_degreeLT.mpr
        rw [← CPolynomial.degree_toPoly]
        exact toCompPoly_degree_lt (r.map Exp.eval)
    · exact hp
    · intro i hi
      specialize h' i (List.mem_range.mpr hi)
      -- h' : (eval_poly t i - (eval_poly ab i - (eval_poly p' i * eval_poly q i + eval_poly r i))).eval = 0
      rw [Exp.eval_sub, Exp.eval_sub, Exp.eval_add, Exp.eval_mul] at h'

      simp only [eval_poly_eval_eq] at h'
      rw [cpoly_eval_sub, cpoly_eval_sub, cpoly_eval_mul]
      grind
  · -- foldr structural equality: bridge do-notation list to map then apply foldr_flatMap.
    simp only [List.flatMap, pure, bind]
    rw [← List.flatMap_def, List.foldr_flatMap]
    simp

omit inst' in
private lemma carry_partial_sum_aux {m w : ℕ}
    (t : ℕ → ZMod p) (c : Fin m → ZMod p)
    (heq : ∀ i : Fin m,
        (if i.1 = 0 then t 0 else t i.1 + c ⟨i.1 - 1, by have := i.2; omega⟩)
          = (2 ^ w : ZMod p) * c i)
    (k : ℕ) (hk : k < m) :
    ∑ i ∈ Finset.range (k + 1), t i * (2 ^ w : ZMod p) ^ i =
      c ⟨k, hk⟩ * (2 ^ w : ZMod p) ^ (k + 1) := by
  induction k with
  | zero =>
    rw [Finset.sum_range_one]
    have h := heq ⟨0, hk⟩
    simp only [↓reduceIte] at h
    rw [h]; ring
  | succ k ih =>
    have hk' : k < m := by omega
    rw [Finset.sum_range_succ, ih hk']
    have hcons := heq ⟨k + 1, hk⟩
    have hne : (k + 1 : ℕ) ≠ 0 := by omega
    simp only [hne, ↓reduceIte] at hcons
    have h_idx : (⟨(k + 1) - 1, by omega⟩ : Fin m) = ⟨k, hk'⟩ := by
      apply Fin.ext; simp
    rw [h_idx] at hcons
    have hrw :
        c ⟨k, hk'⟩ * (2 ^ w : ZMod p) ^ (k + 1) + t (k + 1) * (2 ^ w : ZMod p) ^ (k + 1) =
          (t (k + 1) + c ⟨k, hk'⟩) * (2 ^ w : ZMod p) ^ (k + 1) := by ring
    rw [hrw, hcons]; ring

omit inst' in
private lemma carry_eqs_imp_sum_zero {n w : ℕ}
    (t : Fin n → ZMod p) (c : Fin (n - 1) → ZMod p)
    (h_n_pos : 0 < n)
    (heq : ∀ i : Fin (n - 1),
        (if i.1 = 0 then t ⟨0, h_n_pos⟩
         else t ⟨i.1, by have := i.2; omega⟩ + c ⟨i.1 - 1, by have := i.2; omega⟩)
          = (2 ^ w : ZMod p) * c i)
    (hbase :
        t ⟨n - 1, by omega⟩ +
          (if h : n = 1 then (0 : ZMod p) else c ⟨n - 2, by omega⟩) = 0) :
    ∑ i : Fin n, t i * (2 ^ w : ZMod p) ^ i.1 = 0 := by
  -- Lift `t` to ℕ-indexed for `Finset.range`.
  let t' : ℕ → ZMod p := fun i => if h : i < n then t ⟨i, h⟩ else 0
  have h_conv : ∑ i : Fin n, t i * (2 ^ w : ZMod p) ^ i.1 =
                ∑ i ∈ Finset.range n, t' i * (2 ^ w : ZMod p) ^ i := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => t' j * (2 ^ w : ZMod p) ^ j) n]
    apply Finset.sum_congr rfl
    intro i _
    simp only [t', dif_pos i.2]
  have heq' : ∀ i : Fin (n - 1),
      (if i.1 = 0 then t' 0 else t' i.1 + c ⟨i.1 - 1, by have := i.2; omega⟩)
        = (2 ^ w : ZMod p) * c i := by
    intro i
    have h := heq i
    have hi : i.1 < n := by have := i.2; omega
    by_cases hi0 : i.1 = 0
    · simp only [hi0, ↓reduceIte] at h ⊢
      simp only [t', dif_pos h_n_pos]
      exact h
    · simp only [hi0, ↓reduceIte] at h ⊢
      simp only [t', dif_pos hi]
      exact h
  rw [h_conv]
  by_cases hn1 : n = 1
  · -- n = 1: only `t 0` in the sum, base equation forces it to 0.
    subst hn1
    rw [Finset.sum_range_one]
    simp at hbase
    have ht0 : t' 0 = t 0 := by simp [t']
    rw [ht0, hbase]; ring
  · -- n ≥ 2
    have h_n_ge_2 : 2 ≤ n := by omega
    -- Peel off the last term
    rw [show n = (n - 1) + 1 by omega, Finset.sum_range_succ]
    have hk : n - 2 < n - 1 := by omega
    rw [show (n - 1) = (n - 2) + 1 by omega]
    rw [carry_partial_sum_aux t' c heq' (n - 2) hk]
    have hpow : (n - 2) + 1 = n - 1 := by omega
    rw [hpow]
    have hbase' : t' (n - 1) + c ⟨n - 2, by omega⟩ = 0 := by
      simp only [t', dif_pos (show n - 1 < n by omega)]
      simp only [dif_neg hn1] at hbase
      exact hbase
    have : c ⟨n - 2, by omega⟩ * (2 ^ w : ZMod p) ^ (n - 1) +
            t' (n - 1) * (2 ^ w : ZMod p) ^ (n - 1) =
            (t' (n - 1) + c ⟨n - 2, by omega⟩) * (2 ^ w : ZMod p) ^ (n - 1) := by ring
    rw [this, hbase']; ring

/--
  After all carries are introduced, peel off the chained `eq0` and
  `num2bits` constraints one at a time. We track which carry-equation
  indices have already been verified via `hverified`. When `lst = []`
  all equations are verified; we then consume the base `eq0` and apply
  `hbisim` (which packages the call to `carry_eqs_imp_sum_zero` upstream).
-/
private lemma check_carry_foldr_wrBisim {n w : ℕ}
    (t_pol : Vector (ZMod p) n) (carry : Vector (ZMod p) (n - 1))
    (cont : Csₑ p) (d : denotation (ZMod p))
    (h_n_pos : 0 < n)
    (hbisim :
      (∀ i : Fin (n - 1),
          (if i.1 = 0 then t_pol[(⟨0, h_n_pos⟩ : Fin n)]
           else t_pol[(⟨i.1, by have := i.2; omega⟩ : Fin n)] +
                carry[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (n - 1))])
            = (2 ^ w : ZMod p) * carry[i]) →
        t_pol[(⟨n - 1, by omega⟩ : Fin n)] +
          (if h : n = 1 then (0 : ZMod p) else carry[(⟨n - 2, by omega⟩ : Fin (n - 1))]) = 0 →
        (∀ i : Fin (n - 1),
            (carry[i] + ((2 ^ (w + 1) * n : ℕ) : ZMod p)).val < 2 ^ (w + Nat.clog 2 n + 2)) →
        wrBisim d cont.eval)
    (lst : List (Fin (n - 1)))
    (hverified : ∀ i : Fin (n - 1), i ∉ lst →
        (if i.1 = 0 then t_pol[(⟨0, h_n_pos⟩ : Fin n)]
         else t_pol[(⟨i.1, by have := i.2; omega⟩ : Fin n)] +
              carry[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (n - 1))])
          = (2 ^ w : ZMod p) * carry[i])
    (hverified_rc : ∀ i : Fin (n - 1), i ∉ lst →
        (carry[i] + ((2 ^ (w + 1) * n : ℕ) : ZMod p)).val < 2 ^ (w + Nat.clog 2 n + 2)) :
    wrBisim d
      (List.foldr (fun (i : Fin (n - 1)) rest =>
                      Cs.eq0
                        ((if h : i.1 = 0
                          then (Vector.map Exp.v t_pol)[i]
                          else (Vector.map Exp.v t_pol)[i] +
                               (.v carry[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (n - 1))])) -
                          (.c (2 ^ w) * .v carry[i]))
                        (Num2Bits.num2bits_circuit (w + Nat.clog 2 n + 2)
                          (.v carry[i] + .c (2 ^ (w + 1) * (n : ZMod p))) (fun _ ↦ rest)))
                  (Cs.eq0
                    ((Vector.map Exp.v t_pol)[(⟨n - 1, by omega⟩ : Fin n)] +
                      (if h' : n = 1 then .c 0
                       else .v carry[(⟨n - 2, by omega⟩ : Fin (n - 1))]))
                    cont)
                  lst).eval := by
  induction lst with
  | nil =>
    simp only [List.foldr_nil]
    apply eq0_wrBisim_cont
    intro h_base
    -- Translate Exp.eval = 0 → ZMod p equation.
    have h_base' :
        t_pol[(⟨n - 1, by omega⟩ : Fin n)] +
          (if h : n = 1 then (0 : ZMod p) else carry[(⟨n - 2, by omega⟩ : Fin (n - 1))]) = 0 := by
      by_cases hn1 : n = 1
      · simp only [dif_pos hn1] at h_base ⊢
        simp [Exp.eval, Vector.getElem_map] at h_base
        simpa [Fin.getElem_fin] using h_base
      · simp only [dif_neg hn1] at h_base ⊢
        simp [Exp.eval, Vector.getElem_map] at h_base
        exact h_base
    refine hbisim ?_ h_base' ?_
    · intro i; apply hverified; simp
    · intro i; apply hverified_rc; simp
  | cons head tail ih =>
    simp only [List.foldr_cons]
    apply eq0_wrBisim_cont
    intro h_cons
    have h_cons' :
        (if head.1 = 0 then t_pol[(⟨0, h_n_pos⟩ : Fin n)]
         else t_pol[(⟨head.1, by have := head.2; omega⟩ : Fin n)] +
              carry[(⟨head.1 - 1, by have := head.2; omega⟩ : Fin (n - 1))])
          = (2 ^ w : ZMod p) * carry[head] := by
      simp only [Fin.getElem_fin, Vector.getElem_map] at h_cons
      by_cases hh : head.1 = 0
      · -- Case head.1 = 0
        simp only [dif_pos hh] at h_cons
        simp only [if_pos hh]
        have h_clean : t_pol[head.1]'(by have := head.2; omega) -
                       (2 ^ w : ZMod p) * carry[head.1]'head.2 = 0 := h_cons
        have h_idx : t_pol[head.1]'(by have := head.2; omega) =
            t_pol[(⟨0, h_n_pos⟩ : Fin n)] := by
          show t_pol[head.1]'_ = t_pol[0]'h_n_pos
          congr 1
        have h_idx_c : carry[head.1]'head.2 = carry[head] := by
          rw [Fin.getElem_fin]
        rw [h_idx, h_idx_c] at h_clean
        linear_combination h_clean
      · -- Case head.1 ≠ 0
        simp only [dif_neg hh] at h_cons
        simp only [if_neg hh]
        have h_clean : t_pol[head.1]'(by have := head.2; omega) +
                       carry[head.1 - 1]'(by have := head.2; omega) -
                       (2 ^ w : ZMod p) * carry[head.1]'head.2 = 0 := h_cons
        have h_idx : t_pol[head.1]'(by have := head.2; omega) =
            t_pol[(⟨head.1, by have := head.2; omega⟩ : Fin n)] := by
          rw [Fin.getElem_fin]
        have h_idx_c1 :
            carry[head.1 - 1]'(by have := head.2; omega) =
            carry[(⟨head.1 - 1, by have := head.2; omega⟩ : Fin (n - 1))] := by
          rw [Fin.getElem_fin]
        have h_idx_c2 : carry[head.1]'head.2 = carry[head] := by
          rw [Fin.getElem_fin]
        rw [h_idx, h_idx_c1, h_idx_c2] at h_clean
        linear_combination h_clean
    apply num2bits_wrBisim_cont
    intro h_rc
    -- Translate `h_rc` (Exp.eval form) into ZMod p form on `carry[head]`.
    have h_rc' :
        (carry[head] + ((2 ^ (w + 1) * n : ℕ) : ZMod p)).val <
          2 ^ (w + Nat.clog 2 n + 2) := by
      simp only [Exp.eval, Fin.getElem_fin] at h_rc
      have h_eq : carry[head] + ((2 ^ (w + 1) * n : ℕ) : ZMod p) =
          carry[(head : Fin (n-1))] + 2 ^ (w + 1) * (n : ZMod p) := by
        push_cast; ring
      rw [h_eq]
      exact h_rc
    apply ih
    · intro i hi
      by_cases hieq : i = head
      · subst hieq; exact h_cons'
      · apply hverified
        simp [hieq, hi, List.mem_cons]
    · intro i hi
      by_cases hieq : i = head
      · subst hieq; exact h_rc'
      · apply hverified_rc
        simp [hieq, hi, List.mem_cons]

def zmod_int_cast (offset : ℕ) (a : ZMod p) : ℤ :=
  if a.val < offset
  then a.val
  else - ((-a).val : ℤ)

omit inst' in
private lemma carry_partial_sum_aux_int {m w : ℕ}
    (t : ℕ → ℤ) (c : Fin m → ℤ)
    (heq : ∀ i : Fin m,
        (if i.1 = 0 then t 0 else t i.1 + c ⟨i.1 - 1, by have := i.2; omega⟩)
          = (2 ^ w : ℤ) * c i)
    (k : ℕ) (hk : k < m) :
    ∑ i ∈ Finset.range (k + 1), t i * (2 ^ w : ℤ) ^ i =
      c ⟨k, hk⟩ * (2 ^ w : ℤ) ^ (k + 1) := by
  induction k with
  | zero =>
    rw [Finset.sum_range_one]
    have h := heq ⟨0, hk⟩
    simp only [↓reduceIte] at h
    rw [h]; ring
  | succ k ih =>
    have hk' : k < m := by omega
    rw [Finset.sum_range_succ, ih hk']
    have hcons := heq ⟨k + 1, hk⟩
    have hne : (k + 1 : ℕ) ≠ 0 := by omega
    simp only [hne, ↓reduceIte] at hcons
    have h_idx : (⟨(k + 1) - 1, by omega⟩ : Fin m) = ⟨k, hk'⟩ := by
      apply Fin.ext; simp
    rw [h_idx] at hcons
    have hrw :
        c ⟨k, hk'⟩ * (2 ^ w : ℤ) ^ (k + 1) + t (k + 1) * (2 ^ w : ℤ) ^ (k + 1) =
          (t (k + 1) + c ⟨k, hk'⟩) * (2 ^ w : ℤ) ^ (k + 1) := by ring
    rw [hrw, hcons]; ring

omit inst' in
private lemma carry_eqs_imp_sum_zero_int {n w : ℕ}
    (t : Fin n → ℤ) (c : Fin (n - 1) → ℤ)
    (h_n_pos : 0 < n)
    (heq : ∀ i : Fin (n - 1),
        (if i.1 = 0 then t ⟨0, h_n_pos⟩
         else t ⟨i.1, by have := i.2; omega⟩ + c ⟨i.1 - 1, by have := i.2; omega⟩)
          = (2 ^ w : ℤ) * c i)
    (hbase :
        t ⟨n - 1, by omega⟩ +
          (if h : n = 1 then (0 : ℤ) else c ⟨n - 2, by omega⟩) = 0) :
    ∑ i : Fin n, t i * (2 ^ w : ℤ) ^ i.1 = 0 := by
  let t' : ℕ → ℤ := fun i => if h : i < n then t ⟨i, h⟩ else 0
  have h_conv : ∑ i : Fin n, t i * (2 ^ w : ℤ) ^ i.1 =
                ∑ i ∈ Finset.range n, t' i * (2 ^ w : ℤ) ^ i := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => t' j * (2 ^ w : ℤ) ^ j) n]
    apply Finset.sum_congr rfl
    intro i _
    simp only [t', dif_pos i.2]
  have heq' : ∀ i : Fin (n - 1),
      (if i.1 = 0 then t' 0 else t' i.1 + c ⟨i.1 - 1, by have := i.2; omega⟩)
        = (2 ^ w : ℤ) * c i := by
    intro i
    have h := heq i
    have hi : i.1 < n := by have := i.2; omega
    by_cases hi0 : i.1 = 0
    · simp only [hi0, ↓reduceIte] at h ⊢
      simp only [t', dif_pos h_n_pos]
      exact h
    · simp only [hi0, ↓reduceIte] at h ⊢
      simp only [t', dif_pos hi]
      exact h
  rw [h_conv]
  by_cases hn1 : n = 1
  · subst hn1
    rw [Finset.sum_range_one]
    simp at hbase
    have ht0 : t' 0 = t 0 := by simp [t']
    rw [ht0, hbase]; ring
  · have h_n_ge_2 : 2 ≤ n := by omega
    rw [show n = (n - 1) + 1 by omega, Finset.sum_range_succ]
    have hk : n - 2 < n - 1 := by omega
    rw [show (n - 1) = (n - 2) + 1 by omega]
    rw [carry_partial_sum_aux_int t' c heq' (n - 2) hk]
    have hpow : (n - 2) + 1 = n - 1 := by omega
    rw [hpow]
    have hbase' : t' (n - 1) + c ⟨n - 2, by omega⟩ = 0 := by
      simp only [t', dif_pos (show n - 1 < n by omega)]
      simp only [dif_neg hn1] at hbase
      exact hbase
    have : c ⟨n - 2, by omega⟩ * (2 ^ w : ℤ) ^ (n - 1) +
            t' (n - 1) * (2 ^ w : ℤ) ^ (n - 1) =
            (t' (n - 1) + c ⟨n - 2, by omega⟩) * (2 ^ w : ℤ) ^ (n - 1) := by ring
    rw [this, hbase']; ring

/-- Characterization of `zmod_int_cast`: if `(z : ZMod p) = a` and `z` lies in
the signed window `[offset - p, offset)`, then `zmod_int_cast offset a = z`. -/
lemma zmod_int_cast_eq_of_repr (offset : ℕ) (a : ZMod p) (z : ℤ)
    (hp_off : offset ≤ p)
    (hp_off2 : (offset : ℤ) + offset ≤ p)
    (h_eq : (z : ZMod p) = a)
    (h_lower : -((offset : ℤ)) ≤ z)
    (h_upper : z < offset) :
    zmod_int_cast offset a = z := by
  unfold zmod_int_cast
  have hp_pos : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  -- Key fact: ((a.val : ℕ) : ℤ) % p = z % p
  have h_val_mod : ((a.val : ℕ) : ℤ) % p = z % p := by
    rw [show ((z : ℤ) % p) = ((z : ℤ) : ZMod p).val from by rw [ZMod.val_intCast]]
    rw [h_eq]
    exact (Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast a.val_lt))
  have h_aval_nn : (0 : ℤ) ≤ ((a.val : ℕ) : ℤ) := Int.natCast_nonneg _
  have h_aval_lt : ((a.val : ℕ) : ℤ) < p := by exact_mod_cast a.val_lt
  have h_aval_mod : ((a.val : ℕ) : ℤ) % p = ((a.val : ℕ) : ℤ) :=
    Int.emod_eq_of_lt h_aval_nn h_aval_lt
  by_cases hz_neg : z < 0
  · -- z < 0, branch: a.val ≥ offset, returns -((-a).val)
    have hp_ge_off : (offset : ℤ) ≤ p := by exact_mod_cast hp_off
    -- z % p = z + p in this range
    have h_zp_nn : (0 : ℤ) ≤ z + p := by omega
    have h_zp_lt : z + p < p := by omega
    have hz_p : z % p = z + p := by
      conv_lhs => rw [show z = (z + p) - p from by ring]
      rw [Int.sub_emod, Int.emod_self, sub_zero]
      rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
      exact Int.emod_eq_of_lt h_zp_nn h_zp_lt
    -- Combine: a.val = z + p
    have ha_val : ((a.val : ℕ) : ℤ) = z + p := by
      rw [← h_aval_mod, h_val_mod, hz_p]
    have h_aval_ge_int : ((a.val : ℕ) : ℤ) ≥ offset := by rw [ha_val]; omega
    have h_aval_ge : a.val ≥ offset := by exact_mod_cast h_aval_ge_int
    have h_aval_pos_int : (0 : ℤ) < ((a.val : ℕ) : ℤ) := by rw [ha_val]; omega
    have h_aval_pos : 0 < a.val := by exact_mod_cast h_aval_pos_int
    have h_a_ne : a ≠ 0 := by
      intro h
      rw [h, ZMod.val_zero] at h_aval_pos
      exact Nat.lt_irrefl _ h_aval_pos
    have h_neg_val : (-a).val = p - a.val := by
      haveI : NeZero a := ⟨h_a_ne⟩
      exact ZMod.val_neg_of_ne_zero a
    rw [if_neg (by omega : ¬ a.val < offset)]
    rw [h_neg_val]
    have hle : a.val ≤ p := le_of_lt a.val_lt
    have h_sub_cast : ((p - a.val : ℕ) : ℤ) = (p : ℤ) - ((a.val : ℕ) : ℤ) := by
      push_cast [Nat.sub_eq_iff_eq_add hle]
      omega
    rw [h_sub_cast, ha_val]
    ring
  · push_neg at hz_neg
    have hp_ge_off : (offset : ℤ) ≤ p := by exact_mod_cast hp_off
    have hz_lt_p : z < p := by omega
    have hz_mod : z % p = z := Int.emod_eq_of_lt hz_neg hz_lt_p
    have ha_val : ((a.val : ℕ) : ℤ) = z := by
      rw [← h_aval_mod, h_val_mod, hz_mod]
    have h_val_lt : a.val < offset := by
      have : ((a.val : ℕ) : ℤ) < offset := by rw [ha_val]; exact h_upper
      exact_mod_cast this
    rw [if_pos h_val_lt, ha_val]

/--
  Numeric bounds shared by the soundness and completeness proofs of
  `check_carry_zero`. Both directions need the same relationships between the
  constants `c_off = 2^(w+1) * n`, `c_bd = 2^(w + clog 2 n + 2)`, and
  `t_off = 2^(2w + clog 2 n + 3)`, all rooted in the single input hypothesis
  `2^(2w + clog 2 n + 4) ≤ p`.
-/
private structure CheckCarryBounds (p n w : ℕ) : Prop where
  /-- `2 * c_off ≤ c_bd` -/
  two_coff_le_cbd : 2 * (2 ^ (w + 1) * n) ≤ 2 ^ (w + Nat.clog 2 n + 2)
  /-- `c_off ≤ c_bd` -/
  coff_le_cbd : 2 ^ (w + 1) * n ≤ 2 ^ (w + Nat.clog 2 n + 2)
  /-- `c_bd * 2 ≤ t_off` -/
  cbd_two_le_toff : 2 ^ (w + Nat.clog 2 n + 2) * 2 ≤ 2 ^ (2 * w + Nat.clog 2 n + 3)
  /-- `2 * t_off ≤ p` -/
  two_toff_le_p : 2 * 2 ^ (2 * w + Nat.clog 2 n + 3) ≤ p
  /-- `t_off ≤ p` -/
  toff_le_p : 2 ^ (2 * w + Nat.clog 2 n + 3) ≤ p
  /-- `c_bd ≤ p` -/
  cbd_le_p : 2 ^ (w + Nat.clog 2 n + 2) ≤ p
  /-- `2 * c_bd ≤ p` -/
  two_cbd_le_p : 2 * 2 ^ (w + Nat.clog 2 n + 2) ≤ p
  /-- `c_off ≤ p` -/
  coff_le_p : 2 ^ (w + 1) * n ≤ p

omit inst inst' in
private lemma check_carry_bounds {n w : ℕ}
    (hp_bound : 2 ^ (2 * w + Nat.clog 2 n + 4) ≤ p) :
    CheckCarryBounds p n w := by
  have hn_le_clog : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by omega) n
  have two_coff_le_cbd : 2 * (2 ^ (w + 1) * n) ≤ 2 ^ (w + Nat.clog 2 n + 2) := by
    calc 2 * (2 ^ (w + 1) * n)
        = 2 ^ (w + 2) * n := by ring
      _ ≤ 2 ^ (w + 2) * 2 ^ Nat.clog 2 n := Nat.mul_le_mul_left _ hn_le_clog
      _ = 2 ^ (w + Nat.clog 2 n + 2) := by rw [← pow_add]; congr 1; ring
  have cbd_two_le_toff : 2 ^ (w + Nat.clog 2 n + 2) * 2 ≤ 2 ^ (2 * w + Nat.clog 2 n + 3) := by
    calc 2 ^ (w + Nat.clog 2 n + 2) * 2
        = 2 ^ (w + Nat.clog 2 n + 3) := by ring
      _ ≤ 2 ^ (2 * w + Nat.clog 2 n + 3) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
  have two_toff_le_p : 2 * 2 ^ (2 * w + Nat.clog 2 n + 3) ≤ p := by
    have h_eq : 2 * 2 ^ (2 * w + Nat.clog 2 n + 3) = 2 ^ (2 * w + Nat.clog 2 n + 4) := by ring
    rw [h_eq]; exact hp_bound
  refine ⟨two_coff_le_cbd, by omega, cbd_two_le_toff, two_toff_le_p, ?_, ?_, ?_, ?_⟩ <;> omega

/--
  Generalized version of `check_carry_spec` over any vector length `n`.
-/
private lemma check_carry_zero_circuit_wrBisim {n w : ℕ}
    {t_pol : Vector (ZMod p) n} {cont : Csₑ p} {d : denotation (ZMod p)}
    (hp_bound : 2 ^ (2 * w + Nat.clog 2 n + 4) ≤ p)
    (hbisim : ∑ i : Fin n, zmod_int_cast (2 ^ (2 * w + Nat.clog 2 n + 3)) t_pol[i] * (2 ^ w : ℤ) ^ i.1 = 0 → wrBisim d cont.eval) :
    wrBisim d (check_carry_zero_circuit w (Vector.map Exp.v t_pol) cont).eval := by
  unfold check_carry_zero_circuit
  by_cases hn : n = 0
  · subst hn
    simp only [↓reduceDIte]
    apply hbisim
    simp
  · simp only [hn, ↓reduceDIte]
    apply rw_bisim_uncurry
    intro carry
    have h_n_pos : 0 < n := Nat.pos_of_ne_zero hn
    -- Useful constants:
    set c_off : ℕ := 2 ^ (w + 1) * n with hc_off
    set c_bd : ℕ := 2 ^ (w + Nat.clog 2 n + 2) with hc_bd
    set t_off : ℕ := 2 ^ (2 * w + Nat.clog 2 n + 3) with ht_off
    -- Numeric bounds derived from `hp_bound`, shared with the completeness proof.
    have h_bounds := check_carry_bounds hp_bound
    have h_2coff_le_cbd : 2 * c_off ≤ c_bd := h_bounds.two_coff_le_cbd
    have h_coff_le_cbd : c_off ≤ c_bd := h_bounds.coff_le_cbd
    have h_cbd_le_toff : c_bd * 2 ≤ t_off := h_bounds.cbd_two_le_toff
    have h_toff_2_le_p : 2 * t_off ≤ p := h_bounds.two_toff_le_p
    have h_toff_le_p : t_off ≤ p := h_bounds.toff_le_p
    have h_cbd_le_p : c_bd ≤ p := h_bounds.cbd_le_p
    have h_cbd_2_le_p : 2 * c_bd ≤ p := h_bounds.two_cbd_le_p
    have h_coff_le_p : c_off ≤ p := h_bounds.coff_le_p
    apply check_carry_foldr_wrBisim t_pol carry cont d h_n_pos
      (lst := List.finRange (n - 1))
    · intro heq hbase hrc
      apply hbisim
      -- Define the integer-lifted carries.
      let ec : Fin (n - 1) → ℤ := fun i =>
        zmod_int_cast c_bd (carry[i] + (c_off : ZMod p)) - (c_off : ℤ)
      -- Verify (ec i : ZMod p) = carry[i] and bounds on ec.
      have hec_zmod : ∀ i : Fin (n - 1), ((ec i : ℤ) : ZMod p) = carry[i] ∧
          -(c_off : ℤ) ≤ ec i ∧ ec i < (c_bd : ℤ) - (c_off : ℤ) := by
        intro i
        have hrc_i := hrc i
        rw [show ((2 ^ (w + 1) * n : ℕ) : ZMod p) = (c_off : ZMod p) from by
              simp [hc_off]] at hrc_i
        -- Apply characterization to a = carry[i] + c_off, z = (carry[i] + c_off).val
        -- We get ec i = (carry[i] + c_off).val - c_off.
        have h_aval_lt : (carry[i] + (c_off : ZMod p)).val < c_bd := hrc_i
        have h_cast :
            zmod_int_cast c_bd (carry[i] + (c_off : ZMod p)) =
              ((carry[i] + (c_off : ZMod p)).val : ℤ) := by
          unfold zmod_int_cast
          rw [if_pos h_aval_lt]
        have h_ec_eq :
            ec i = ((carry[i] + (c_off : ZMod p)).val : ℤ) - (c_off : ℤ) := by
          simp only [ec, h_cast]
        refine ⟨?_, ?_, ?_⟩
        · -- (ec i : ZMod p) = carry[i]
          rw [h_ec_eq]
          push_cast
          rw [ZMod.natCast_val, ZMod.cast_id]
          ring
        · rw [h_ec_eq]
          have : (0 : ℤ) ≤ ((carry[i] + (c_off : ZMod p)).val : ℤ) :=
            Int.natCast_nonneg _
          omega
        · rw [h_ec_eq]
          have : ((carry[i] + (c_off : ZMod p)).val : ℤ) < (c_bd : ℤ) := by
            exact_mod_cast h_aval_lt
          omega
      have hec_zmod_eq : ∀ i, ((ec i : ℤ) : ZMod p) = carry[i] := fun i => (hec_zmod i).1
      have hec_bound : ∀ i, |ec i| < (c_bd : ℤ) := by
        intro i
        have h := hec_zmod i
        have : (c_off : ℤ) ≤ (c_bd : ℤ) := by exact_mod_cast h_coff_le_cbd
        rcases h with ⟨_, h_low, h_up⟩
        rw [abs_lt]
        refine ⟨?_, ?_⟩
        · have : -(c_bd : ℤ) < -(c_off : ℤ) ∨ -(c_bd : ℤ) ≤ -(c_off : ℤ) := by omega
          omega
        · omega
      -- Define lifted t_pol
      let es : Fin n → ℤ := fun i =>
        if hL : i.1 = n - 1 then
          (if h1 : n = 1 then (0 : ℤ) else -ec ⟨n - 2, by omega⟩)
        else if h0 : i.1 = 0 then
          (2 ^ w : ℤ) * ec ⟨0, by have := i.2; omega⟩
        else
          (2 ^ w : ℤ) * ec ⟨i.1, by
            have := i.2
            -- i.1 ≠ 0, i.1 ≠ n - 1, so i.1 < n - 1
            omega⟩ - ec ⟨i.1 - 1, by have := i.2; omega⟩
      -- es satisfies the carry equations.
      have hes_carry : ∀ i : Fin (n - 1),
          (if i.1 = 0 then es ⟨0, h_n_pos⟩
           else es ⟨i.1, by have := i.2; omega⟩ + ec ⟨i.1 - 1, by have := i.2; omega⟩)
            = (2 ^ w : ℤ) * ec i := by
        intro i
        -- Note: i : Fin (n - 1) so i.1 < n - 1, hence i.1 ≠ n - 1.
        have h_iL_global : i.1 ≠ n - 1 := by have := i.2; omega
        by_cases hi0 : i.1 = 0
        · simp only [hi0, ↓reduceIte]
          simp only [es]
          -- es ⟨0, _⟩: outer test 0 = n - 1 fails (because Fin(n-1) is non-empty here)
          have hpos : 0 < n - 1 := lt_of_le_of_lt (Nat.zero_le _) i.2
          have h_0_ne : (0 : ℕ) ≠ n - 1 := by omega
          rw [dif_neg h_0_ne]
          -- Inner test 0 = 0 is true
          simp only [↓reduceDIte]
          have h_i_eq : i = (⟨0, hpos⟩ : Fin (n - 1)) := Fin.ext hi0
          rw [h_i_eq]
        · simp only [hi0, ↓reduceIte]
          have h_i_lt : i.1 < n - 1 := by have := i.2; omega
          simp only [es]
          rw [dif_neg h_iL_global, dif_neg hi0]
          have : (⟨i.1, by have := i.2; omega⟩ : Fin (n - 1)) = i := Fin.ext rfl
          rw [this]
          ring
      -- es satisfies the base equation.
      have hes_base : es ⟨n - 1, by omega⟩ +
          (if h : n = 1 then (0 : ℤ) else ec ⟨n - 2, by omega⟩) = 0 := by
        simp only [es]
        -- Outer test: n - 1 = n - 1, true
        simp only [↓reduceDIte]
        by_cases hn1 : n = 1
        · rw [dif_pos hn1, dif_pos hn1]; ring
        · rw [dif_neg hn1, dif_neg hn1]
          ring
      -- (es i : ZMod p) = t_pol[i]
      have hes_tpol : ∀ i : Fin n, ((es i : ℤ) : ZMod p) = t_pol[i] := by
        intro i
        -- Generalize t_pol[i] via the index value
        have h_tpol_idx : ∀ j (h : j < n) (heq_ij : j = i.1),
            t_pol[(⟨j, h⟩ : Fin n)] = t_pol[i] := by
          intros j h heq_ij; congr 1; exact Fin.ext heq_ij
        by_cases hiL : i.1 = n - 1
        · -- i.1 = n - 1: use hbase
          simp only [es, dif_pos hiL]
          by_cases hn1 : n = 1
          · -- n = 1: t_pol[⟨n-1,_⟩] = 0
            rw [dif_pos hn1]
            have hb := hbase
            rw [dif_pos hn1] at hb
            simp only [_root_.add_zero] at hb
            rw [← h_tpol_idx (n - 1) (by omega) hiL.symm]
            rw [hb]
            push_cast; rfl
          · rw [dif_neg hn1]
            have hb := hbase
            rw [dif_neg hn1] at hb
            have h_sub : t_pol[(⟨n - 1, by omega⟩ : Fin n)] =
                -carry[(⟨n - 2, by omega⟩ : Fin (n - 1))] := by linear_combination hb
            rw [← h_tpol_idx (n - 1) (by omega) hiL.symm]
            rw [h_sub]
            push_cast
            rw [hec_zmod_eq ⟨n - 2, by omega⟩]
        · by_cases hi0 : i.1 = 0
          · -- 0 < n - 1 (else hiL would hold via 0 = n - 1)
            simp only [es, dif_neg hiL, dif_pos hi0]
            have hpos_nm1 : 0 < n - 1 := by omega
            have heq0 := heq ⟨0, hpos_nm1⟩
            simp only [↓reduceIte] at heq0
            rw [← h_tpol_idx 0 h_n_pos hi0.symm]
            rw [heq0]
            push_cast
            rw [hec_zmod_eq ⟨0, hpos_nm1⟩]
          · -- 0 < i.1 < n - 1
            simp only [es, dif_neg hiL, dif_neg hi0]
            have h_iL : i.1 < n - 1 := by have := i.2; omega
            have hpos_nm1 : 0 < n - 1 := by omega
            have heq_i := heq ⟨i.1, h_iL⟩
            simp only [hi0, ↓reduceIte] at heq_i
            rw [← h_tpol_idx i.1 (by have := i.2; omega) rfl]
            have h_sub : t_pol[(⟨i.1, by have := i.2; omega⟩ : Fin n)] =
                (2 ^ w : ZMod p) * carry[(⟨i.1, h_iL⟩ : Fin (n - 1))] -
                carry[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (n - 1))] := by
              linear_combination heq_i
            rw [h_sub]
            push_cast
            rw [hec_zmod_eq, hec_zmod_eq]
      -- es bound: |es i| < t_off
      have hes_bound : ∀ i : Fin n, |es i| < (t_off : ℤ) := by
        intro i
        have h_2w_pos : (0 : ℤ) < 2 ^ w := by positivity
        have h_cbd_pos : (0 : ℤ) < (c_bd : ℤ) := by
          have : 0 < c_bd := Nat.pos_of_neZero _
          exact_mod_cast this
        have h_cbd2_le_toff : (2 : ℤ) * c_bd ≤ t_off := by
          have : (2 : ℕ) * c_bd ≤ t_off := by omega
          exact_mod_cast this
        have h_cbd_le_toff_int : (c_bd : ℤ) ≤ t_off := by
          exact_mod_cast (by omega : c_bd ≤ t_off)
        have h_pow_w_cbd_le : (2 ^ w : ℤ) * c_bd ≤ t_off := by
          have h_eq : (2 ^ w : ℤ) * c_bd = (2 ^ (2 * w + Nat.clog 2 n + 2) : ℕ) := by
            simp only [hc_bd]; push_cast; rw [← pow_add]; congr 1; ring
          rw [h_eq]
          have : (2 ^ (2 * w + Nat.clog 2 n + 2) : ℕ) ≤ t_off := by
            simp only [ht_off]
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
          exact_mod_cast this
        by_cases hiL : i.1 = n - 1
        · simp only [es, dif_pos hiL]
          by_cases hn1 : n = 1
          · rw [dif_pos hn1]
            simp only [abs_zero]
            have : 0 < t_off := Nat.pos_of_neZero _
            exact_mod_cast this
          · rw [dif_neg hn1]
            have hpos : 0 < n - 1 := by omega
            have hb := hec_bound ⟨n - 2, by omega⟩
            rw [abs_neg]
            omega
        · by_cases hi0 : i.1 = 0
          · simp only [es, dif_neg hiL, dif_pos hi0]
            rw [abs_mul]
            have h_pow : |(2 ^ w : ℤ)| = 2 ^ w := abs_of_pos h_2w_pos
            rw [h_pow]
            have hpos : 0 < n - 1 := by omega
            have hb := hec_bound ⟨0, hpos⟩
            have h_mul_lt : (2 ^ w : ℤ) * |ec ⟨0, hpos⟩| < (2 ^ w : ℤ) * c_bd :=
              Int.mul_lt_mul_of_pos_left hb h_2w_pos
            omega
          · simp only [es, dif_neg hiL, dif_neg hi0]
            have h_iL : i.1 < n - 1 := by have := i.2; omega
            have hb1 := hec_bound ⟨i.1, h_iL⟩
            have hb2 := hec_bound ⟨i.1 - 1, by have := i.2; omega⟩
            have h_pow : |(2 ^ w : ℤ)| = 2 ^ w := abs_of_pos h_2w_pos
            have h_total : |(2 ^ w : ℤ) * ec ⟨i.1, h_iL⟩ -
                ec ⟨i.1 - 1, by have := i.2; omega⟩| ≤
                |(2 ^ w : ℤ) * ec ⟨i.1, h_iL⟩| + |ec ⟨i.1 - 1, by have := i.2; omega⟩| := by
              exact abs_sub _ _
            rw [abs_mul, h_pow] at h_total
            have h_mul_lt : (2 ^ w : ℤ) * |ec ⟨i.1, h_iL⟩| < (2 ^ w : ℤ) * c_bd :=
              Int.mul_lt_mul_of_pos_left hb1 h_2w_pos
            have h_2pw1 : (2 ^ w : ℤ) + 1 ≤ 2 ^ (w + 1) := by
              have : (2 ^ (w + 1) : ℤ) = 2 * 2 ^ w := by ring
              have h_one_le : (1 : ℤ) ≤ 2 ^ w := by
                have : (1 : ℕ) ≤ 2 ^ w := Nat.one_le_two_pow
                exact_mod_cast this
              linarith
            have h_pow_w1_bd : (2 ^ (w + 1) : ℤ) * c_bd ≤ t_off := by
              have h_eq : (2 ^ (w + 1) : ℤ) * c_bd = (t_off : ℤ) := by
                simp only [hc_bd, ht_off]; push_cast; rw [← pow_add]; congr 1; ring
              rw [h_eq]
            have h_sum_lt : (2 ^ w : ℤ) * c_bd + c_bd ≤ (2 ^ (w + 1) : ℤ) * c_bd := by
              have : ((2 ^ w : ℤ) + 1) * c_bd ≤ (2 ^ (w + 1) : ℤ) * c_bd :=
                mul_le_mul_of_nonneg_right h_2pw1 (le_of_lt h_cbd_pos)
              linarith
            omega
      -- zmod_int_cast t_off t_pol[i] = es i
      have h_cast_es : ∀ i : Fin n, zmod_int_cast t_off t_pol[i] = es i := by
        intro i
        apply zmod_int_cast_eq_of_repr t_off t_pol[i] (es i) h_toff_le_p
        · have : (t_off : ℤ) + (t_off : ℤ) = 2 * (t_off : ℤ) := by ring
          rw [this]
          exact_mod_cast h_toff_2_le_p
        · exact hes_tpol i
        · have := hes_bound i
          have := abs_lt.mp this
          omega
        · have := hes_bound i
          have := abs_lt.mp this
          omega
      -- Apply integer telescoping.
      have h_sum_es : ∑ i : Fin n, es i * (2 ^ w : ℤ) ^ i.1 = 0 :=
        carry_eqs_imp_sum_zero_int es ec h_n_pos hes_carry hes_base
      -- Now translate to t_pol via h_cast_es
      have h_rewrite : ∑ i : Fin n, zmod_int_cast (2 ^ (2 * w + Nat.clog 2 n + 3)) t_pol[i] *
          (2 ^ w : ℤ) ^ i.1 = ∑ i : Fin n, es i * (2 ^ w : ℤ) ^ i.1 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show (2 ^ (2 * w + Nat.clog 2 n + 3) : ℕ) = t_off from rfl]
        rw [h_cast_es i]
      rw [h_rewrite, h_sum_es]
    · intro i hi
      exact absurd (List.mem_finRange i) hi
    · intro i hi
      exact absurd (List.mem_finRange i) hi

lemma check_carry_spec {k w : ℕ} {t_pol : Vector (ZMod p) (2 * k - 1)} {cont : Csₑ p} {d : denotation (ZMod p)} :
  2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 4) ≤ p →
  (∑ i : Fin (2 * k - 1), zmod_int_cast (2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 3)) t_pol[i] * (2 ^ w : ℤ) ^ i.1 = 0 → wrBisim d cont.eval) →
    wrBisim d (check_carry_zero_circuit w (Vector.map Exp.v t_pol) cont).eval := by
  intro _hp hbisim
  apply check_carry_zero_circuit_wrBisim _hp hbisim

-- set_option maxHeartbeats 400000 in
-- /--
--   Generalized auxiliary lemma for `check_lt'`. The recursion accumulates the
--   `isLt` flag, so the spec is parametrized over the current value of `isLt`.

--   The invariant `(isLt.eval = 1 ∧ multi-prec_≤) ∨ multi-prec_<` says: the
--   continuation should be entered if either (a) we have already determined a
--   strict inequality at some more-significant position (tracked in `isLt`) AND
--   the current `(r_pol, p')` is multi-prec_≤ (which the recursion will enforce
--   limb-wise), OR (b) the current `(r_pol, p')` is itself multi-prec_<.
-- -/
-- private lemma check_lt'_wrBisim {k w : ℕ}
--     {isLt : Expₑ p}
--     {r_pol : Vector (ZMod p) k}
--     {p' : Vector (Expₑ p) k}
--     {cont : Csₑ p}
--     {d : denotation (ZMod p)}
--     (hp_bound : 2 ^ (w + 1) ≤ p)
--     (hr_rc : ∀ i : Fin k, r_pol[i].val < 2 ^ w)
--     (hp_rc : ∀ i : Fin k, p'[i].eval.val < 2 ^ w) :
--     (((isLt.eval = 1 ∧
--           ∑ i : Fin k, r_pol[i].val * (2 ^ w) ^ i.1 ≤
--             ∑ i : Fin k, p'[i].eval.val * (2 ^ w) ^ i.1) ∨
--         ∑ i : Fin k, r_pol[i].val * (2 ^ w) ^ i.1 <
--           ∑ i : Fin k, p'[i].eval.val * (2 ^ w) ^ i.1) →
--       wrBisim d cont.eval) →
--     wrBisim d (check_lt_circuit' w isLt (Vector.map Exp.v r_pol) p' cont).eval := by
--   induction k generalizing isLt with
--   | zero =>
--     intro hbisim
--     unfold check_lt_circuit'
--     simp only [Cs.eval, Exp.eval_sub, Exp.eval_ofNat]
--     split_ifs with h
--     · apply hbisim
--       left
--       refine ⟨?_, ?_⟩
--       · have := sub_eq_zero.mp h
--         simpa using this
--       · simp
--     · exact wrBisim.none
--   | succ k ih =>
--     intro hbisim
--     unfold check_lt_circuit'
--     apply num2bits_wrBisim_cont
--     intro h_nb
--     set a : ℕ := r_pol[Fin.last k].val with ha_def
--     set b : ℕ := p'[Fin.last k].eval.val with hb_def
--     have ha_rc : a < 2 ^ w := hr_rc (Fin.last k)
--     have hb_rc : b < 2 ^ w := hp_rc (Fin.last k)
--     have h_msb_le : a ≤ b := by
--       by_contra h_not_le
--       push Not at h_not_le
--       have h_eval : ((Vector.map Exp.v r_pol)[Fin.last k] - p'[Fin.last k] +
--           Exp.c (2 ^ w - 1)).eval = r_pol[Fin.last k] - p'[Fin.last k].eval +
--           ((2 ^ w - 1 : ZMod p)) := by
--         simp [Exp.eval, Vector.getElem_map]
--       rw [h_eval] at h_nb
--       have hp_gt_1 : 1 < p := by have := inst'.out; omega
--       haveI : Fact (1 < p) := ⟨hp_gt_1⟩
--       have h_pow_two_pos : (1 : ℕ) ≤ 2 ^ w := Nat.one_le_two_pow
--       have h_2pw_lt_p : 2 ^ w < p := by
--         have : 2 ^ w < 2 ^ (w + 1) := by
--           apply Nat.pow_lt_pow_right (by norm_num); omega
--         omega
--       have h_pow_cast : ((2 : ZMod p) ^ w) = ((2 ^ w : ℕ) : ZMod p) := by push_cast; ring
--       have h_2pw_val : ((2 : ZMod p) ^ w).val = 2 ^ w := by
--         rw [h_pow_cast, ZMod.val_natCast_of_lt h_2pw_lt_p]
--       have h_one_val : (1 : ZMod p).val = 1 := ZMod.val_one p
--       have h_2pw_sub_one_val : ((2 ^ w : ZMod p) - 1).val = 2 ^ w - 1 := by
--         rw [ZMod.val_sub]
--         · rw [h_2pw_val, h_one_val]
--         · rw [h_2pw_val, h_one_val]; exact h_pow_two_pos
--       have h_pp_le_r : p'[Fin.last k].eval.val ≤ r_pol[Fin.last k].val :=
--         Nat.le_of_lt h_not_le
--       have h_sub_val :
--           (r_pol[Fin.last k] - p'[Fin.last k].eval).val =
--             r_pol[Fin.last k].val - p'[Fin.last k].eval.val :=
--         ZMod.val_sub h_pp_le_r
--       have h_sum_lt_p :
--           (r_pol[Fin.last k] - p'[Fin.last k].eval).val + ((2 ^ w : ZMod p) - 1).val < p := by
--         rw [h_sub_val, h_2pw_sub_one_val, ← ha_def, ← hb_def]
--         have : 2 * (2 ^ w - 1) < 2 ^ (w + 1) := by
--           rw [two_mul, pow_succ]; omega
--         omega
--       have h_total_val :
--           (r_pol[Fin.last k] - p'[Fin.last k].eval + ((2 ^ w : ZMod p) - 1)).val =
--             (r_pol[Fin.last k].val - p'[Fin.last k].eval.val) + (2 ^ w - 1) := by
--         rw [ZMod.val_add_of_lt h_sum_lt_p, h_sub_val, h_2pw_sub_one_val]
--       rw [h_total_val, ← ha_def, ← hb_def] at h_nb
--       omega
--     unfold IsZero.isZero_circuit
--     apply wrBisim.right
--     intro inv
--     simp only [Cs.eval]
--     apply wrBisim.right
--     intro o
--     split_ifs with h_iz1 h_iz2
--     · have h_o_or_eq :
--           o = 0 ∨ r_pol[Fin.last k] = p'[Fin.last k].eval := by
--         have h := h_iz2
--         simp only [Vector.getElem_map, Exp.eval,
--           Fin.getElem_fin, Fin.val_last] at h
--         rcases mul_eq_zero.mp h with ho | he
--         · exact Or.inl ho
--         · right
--           have he' : r_pol[Fin.last k] - p'[Fin.last k].eval = 0 := by
--             aesop
--           exact sub_eq_zero.mp he'
--       have h_map_ofFn :
--           Vector.ofFn (fun i : Fin k ↦ (Vector.map Exp.v r_pol)[i.castSucc]) =
--             Vector.map (Exp.v (p := p) (var := ZMod p))
--               (Vector.ofFn (fun i : Fin k ↦ r_pol[i.castSucc])) := by
--         ext i hi
--         simp [Vector.getElem_ofFn, Vector.getElem_map]
--       rw [h_map_ofFn]
--       refine ih
--         (isLt := isLt ||| (1 - Exp.v o))
--         (r_pol := Vector.ofFn (fun i ↦ r_pol[i.castSucc]))
--         (p' := Vector.ofFn (fun i ↦ p'[i.castSucc]))
--         (fun i => by simp [Vector.getElem_ofFn]; exact hr_rc i.castSucc)
--         (fun i => by simp [Vector.getElem_ofFn]; exact hp_rc i.castSucc)
--         ?_
--       rintro (⟨h_isLt', h_le'⟩ | h_lt')
--       · have h_le'' :
--             ∑ x : Fin k, r_pol[x.castSucc].val * (2 ^ w) ^ x.val ≤
--               ∑ x : Fin k, p'[x.castSucc].eval.val * (2 ^ w) ^ x.val := by
--           simpa using h_le'
--         have h_unfold_or : isLt.eval + (1 - o) - isLt.eval * (1 - o) = 1 := by
--           have h := h_isLt'
--           change (isLt + (1 - Exp.v o) - isLt * (1 - Exp.v o)).eval = 1 at h
--           simpa [Exp.eval] using h
--         have h_or_zero : o * (isLt.eval - 1) = 0 := by linear_combination h_unfold_or
--         rcases mul_eq_zero.mp h_or_zero with ho | hisLt
--         · apply hbisim
--           right
--           have h_a_lt : a < b := by
--             rcases lt_or_eq_of_le h_msb_le with h | h_a_eq
--             · exact h
--             · exfalso
--               have h_val_eq : r_pol[Fin.last k].val = p'[Fin.last k].eval.val := by
--                 rw [← ha_def, ← hb_def]; exact h_a_eq
--               have h_e_eq : r_pol[Fin.last k] = p'[Fin.last k].eval :=
--                 ZMod.val_injective p h_val_eq
--               have h_simp : (1 : ZMod p) - inv * (r_pol[Fin.last k] - p'[Fin.last k].eval) - o = 0 := by
--                 have := h_iz1
--                 rw [Exp.eval_sub, Exp.eval_sub, Exp.eval_mul, Exp.eval_sub] at this
--                 simp [Vector.getElem_map, Fin.getElem_fin, Fin.val_last, Exp.eval] at this
--                 simpa
--               rw [h_e_eq, sub_self, MulZeroClass.mul_zero, sub_zero] at h_simp
--               have h_o_one : o = 1 := (sub_eq_zero.mp h_simp).symm
--               rw [ho] at h_o_one
--               exact zero_ne_one h_o_one
--           rw [Fin.sum_univ_castSucc (n := k), Fin.sum_univ_castSucc (n := k)]
--           simp only [Fin.val_last, Fin.val_castSucc, ← ha_def, ← hb_def]
--           have h_pow_pos : (0 : ℕ) < (2 ^ w) ^ k := by
--             exact Nat.pos_of_neZero ((2 ^ w) ^ k)
--           have h_msb_mul_strict : a * (2 ^ w) ^ k < b * (2 ^ w) ^ k := by
--             have : (a + 1) * (2 ^ w) ^ k ≤ b * (2 ^ w) ^ k := Nat.mul_le_mul_right _ h_a_lt
--             linarith [this, Nat.add_mul a 1 ((2 ^ w) ^ k), h_pow_pos]
--           exact Nat.add_lt_add_of_le_of_lt h_le'' h_msb_mul_strict
--         · have h_isLt_eq : isLt.eval = 1 := by linear_combination hisLt
--           apply hbisim
--           left
--           refine ⟨h_isLt_eq, ?_⟩
--           rw [Fin.sum_univ_castSucc (n := k), Fin.sum_univ_castSucc (n := k)]
--           simp only [Fin.val_last, Fin.val_castSucc, ← ha_def, ← hb_def]
--           have h_msb_mul : a * (2 ^ w) ^ k ≤ b * (2 ^ w) ^ k :=
--             Nat.mul_le_mul_right ((2 ^ w) ^ k) h_msb_le
--           linarith [h_le'', h_msb_mul]
--       · apply hbisim
--         right
--         have h_lt'' :
--             ∑ x : Fin k, r_pol[x.castSucc].val * (2 ^ w) ^ x.val <
--               ∑ x : Fin k, p'[x.castSucc].eval.val * (2 ^ w) ^ x.val := by
--           simpa using h_lt'
--         rw [Fin.sum_univ_castSucc (n := k), Fin.sum_univ_castSucc (n := k)]
--         simp only [Fin.val_last, Fin.val_castSucc, ← ha_def, ← hb_def]
--         have h_msb_mul : a * (2 ^ w) ^ k ≤ b * (2 ^ w) ^ k :=
--           Nat.mul_le_mul_right ((2 ^ w) ^ k) h_msb_le
--         linarith [h_lt'', h_msb_mul]
--     · exact wrBisim.none
--     · exact wrBisim.none

omit inst inst' in
/-- Geometric sum bound: `∑_{i<k} c[i] * (2^w)^i < (2^w)^k` when each `c[i] < 2^w`. -/
private lemma tail_bd_geom' {w k : ℕ} (h_w_pos : 0 < 2 ^ w) (f : ℕ → ℕ)
    (hf : ∀ i, i < k → f i < 2 ^ w) :
    ∑ i ∈ Finset.range k, f i * (2 ^ w) ^ i < (2 ^ w) ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h_ih : ∑ i ∈ Finset.range n, f i * (2 ^ w) ^ i < (2 ^ w) ^ n :=
      ih (fun i hi => hf i (by omega))
    have h_last : f n * (2 ^ w) ^ n ≤ (2 ^ w - 1) * (2 ^ w) ^ n :=
      Nat.mul_le_mul_right _ (by have := hf n (by omega); omega)
    have h_pow_n_pos : 1 ≤ (2 ^ w) ^ n := Nat.one_le_pow n _ h_w_pos
    have h_sub : (2 ^ w - 1) * (2 ^ w) ^ n =
        (2 ^ w) * (2 ^ w) ^ n - (2 ^ w) ^ n := by
      rw [Nat.sub_mul, _root_.one_mul]
    have h_pow_2w_ge : (2 ^ w) ^ n ≤ (2 ^ w) * (2 ^ w) ^ n :=
      Nat.le_mul_of_pos_left _ h_w_pos
    have h_pow_succ : (2 ^ w) ^ (n + 1) = 2 ^ w * (2 ^ w) ^ n := by
      rw [pow_succ]; ring
    omega

/-- Small helper: bound on tail sum, geometric series style. -/
private lemma tail_lt_pow_of_range {k w : ℕ} (h_w_pos : 0 < 2 ^ w)
    (v : Fin (k + 1) → ℕ) (hv : ∀ i : Fin (k + 1), v i < 2 ^ w) :
    ∑ i : Fin k, v i.castSucc * (2 ^ w) ^ i.1 < (2 ^ w) ^ k := by
  let f : ℕ → ℕ := fun i => if h : i < k + 1 then v ⟨i, h⟩ else 0
  have h_conv : ∑ i : Fin k, v i.castSucc * (2 ^ w) ^ i.1 =
                ∑ i ∈ Finset.range k, f i * (2 ^ w) ^ i := by
    trans (∑ i : Fin k, f i.val * (2 ^ w) ^ i.val)
    · apply Finset.sum_congr rfl
      intro i _
      have h_i_lt : i.val < k + 1 := by have := i.2; omega
      simp only [f, dif_pos h_i_lt]
      rfl
    · exact Fin.sum_univ_eq_sum_range (fun i => f i * (2 ^ w) ^ i) k
  rw [h_conv]
  apply tail_bd_geom' h_w_pos f
  intro i hi
  have h_i_lt : i < k + 1 := by omega
  simp only [f, dif_pos h_i_lt]
  exact hv ⟨i, h_i_lt⟩

set_option maxHeartbeats 400000 in
/--
  Generalized soundness helper for `check_lt'`. The invariant
  `(isLt.eval = 1) ∨ (isLt.eval = 0 ∧ sum_r < sum_p')` says: either we have
  already determined strict less-than at a more-significant position (tracked
  in `isLt`), or the current chunk itself is strictly less.
-/
private lemma check_lt'_wrBisim {k w : ℕ}
    {isLt : Expₑ p}
    {r_pol : Vector (ZMod p) k}
    {p' : Vector (Expₑ p) k}
    {cont : Csₑ p}
    {d : denotation (ZMod p)}
    (hp_bound : 2 ^ (w + 1) ≤ p)
    (hr_rc : ∀ i : Fin k, r_pol[i].val < 2 ^ w)
    (hp_rc : ∀ i : Fin k, p'[i].eval.val < 2 ^ w)
    (h_isLt_bool : isLt.eval = 0 ∨ isLt.eval = 1) :
    ((isLt.eval = 1 ∨
        (isLt.eval = 0 ∧
          ∑ i : Fin k, r_pol[i].val * (2 ^ w) ^ i.1 <
            ∑ i : Fin k, p'[i].eval.val * (2 ^ w) ^ i.1)) →
      wrBisim d cont.eval) →
    wrBisim d (check_lt_circuit' w isLt (Vector.map Exp.v r_pol) p' cont).eval := by
  induction k generalizing isLt with
  | zero =>
    intro hbisim
    unfold check_lt_circuit'
    simp only [Cs.eval, Exp.eval_sub, Exp.eval_ofNat]
    split_ifs with h
    · apply hbisim
      left
      have := sub_eq_zero.mp h
      simpa using this
    · exact wrBisim.none
  | succ k ih =>
    intro hbisim
    unfold check_lt_circuit'
    apply num2bits_wrBisim_cont
    intro h_nb
    -- `h_nb : ((1 - isLt) * (r_msb - p'_msb + (2^w - 1))).val < 2^w`.
    set a : ℕ := r_pol[Fin.last k].val with ha_def
    set b : ℕ := p'[Fin.last k].eval.val with hb_def
    have ha_rc : a < 2 ^ w := hr_rc (Fin.last k)
    have hb_rc : b < 2 ^ w := hp_rc (Fin.last k)
    have hp_gt_1 : 1 < p := by have := inst'.out; omega
    have h_pow_two_pos : (1 : ℕ) ≤ 2 ^ w := Nat.one_le_two_pow
    have h_2pw_lt_p : 2 ^ w < p := by
      have : 2 ^ w < 2 ^ (w + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have h_pow_cast : ((2 : ZMod p) ^ w) = ((2 ^ w : ℕ) : ZMod p) := by push_cast; ring
    have h_2pw_val : ((2 : ZMod p) ^ w).val = 2 ^ w := by
      rw [h_pow_cast, ZMod.val_natCast_of_lt h_2pw_lt_p]
    have h_one_val : (1 : ZMod p).val = 1 := ZMod.val_one p
    have h_2pw_sub_one_val : ((2 ^ w : ZMod p) - 1).val = 2 ^ w - 1 := by
      rw [ZMod.val_sub]
      · rw [h_2pw_val, h_one_val]
      · rw [h_2pw_val, h_one_val]; exact h_pow_two_pos
    -- If `isLt.eval = 0`, `h_nb` reduces to `t_msb ≤ p'_msb`.
    have h_msb_le_of_isLt_zero : isLt.eval = 0 → a ≤ b := by
      intro h_isLt_zero
      by_contra h_not_le
      push_neg at h_not_le
      -- Compute the value being num2bits'd.
      have h_val_expand : ((1 - isLt) *
          ((Vector.map Exp.v r_pol)[Fin.last k] -
            p'[Fin.last k] + Exp.c ((2 ^ w : ZMod p) - 1))).eval =
          (r_pol[Fin.last k] - p'[Fin.last k].eval + ((2 ^ w : ZMod p) - 1)) := by
        have h_map : (Vector.map Exp.v r_pol)[Fin.last k].eval =
            r_pol[Fin.last k] := by
          simp [Vector.getElem_map, Exp.eval]
        simp only [Exp.eval_mul, Exp.eval_sub, Exp.eval_add, Exp.eval_ofNat,
                   Nat.cast_one, Exp.eval, h_map]
        rw [h_isLt_zero]; ring
      rw [h_val_expand] at h_nb
      have h_pp_le_r : b ≤ a := Nat.le_of_lt h_not_le
      have h_sub_val :
          (r_pol[Fin.last k] - p'[Fin.last k].eval).val = a - b :=
        ZMod.val_sub h_pp_le_r
      have h_sum_lt_p :
          (r_pol[Fin.last k] - p'[Fin.last k].eval).val +
            ((2 ^ w : ZMod p) - 1).val < p := by
        rw [h_sub_val, h_2pw_sub_one_val]
        have : 2 * (2 ^ w - 1) < 2 ^ (w + 1) := by
          rw [two_mul, pow_succ]; omega
        omega
      have h_total_val :
          (r_pol[Fin.last k] - p'[Fin.last k].eval + ((2 ^ w : ZMod p) - 1)).val =
            (a - b) + (2 ^ w - 1) := by
        rw [ZMod.val_add_of_lt h_sum_lt_p, h_sub_val, h_2pw_sub_one_val]
      rw [h_total_val] at h_nb
      omega
    -- Peel isZero.
    unfold IsZero.isZero_circuit
    apply wrBisim.right
    intro inv
    simp only [Cs.eval]
    apply wrBisim.right
    intro o
    split_ifs with h_iz1 h_iz2
    · -- Both eq0s succeeded.
      -- `o * (r_msb - p'_msb) = 0`, so either o = 0 or r_msb = p'_msb.
      have h_o_or_eq :
          o = 0 ∨ r_pol[Fin.last k] = p'[Fin.last k].eval := by
        have h := h_iz2
        have h_map_r : (Vector.map Exp.v r_pol)[Fin.last k].eval =
            r_pol[Fin.last k] := by simp [Vector.getElem_map, Exp.eval]
        simp only [Exp.eval_mul, Exp.eval_sub, Exp.eval, h_map_r] at h
        rcases mul_eq_zero.mp h with ho | he
        · exact Or.inl ho
        · right
          exact sub_eq_zero.mp he
      -- Set up truncated arguments.
      have h_map_ofFn :
          Vector.ofFn (fun i : Fin k ↦ (Vector.map Exp.v r_pol)[i.castSucc]) =
            Vector.map (Exp.v (p := p) (var := ZMod p))
              (Vector.ofFn (fun i : Fin k ↦ r_pol[i.castSucc])) := by
        ext i hi
        simp [Vector.getElem_ofFn, Vector.getElem_map]
      rw [h_map_ofFn]
      -- Show new isLt ∈ {0, 1}.
      -- We know o ∈ {0, 1} from isZero constraints (h_o_or_eq gives o = 0 case; if o ≠ 0, MSBs equal, then h_iz1 forces o = 1).
      have h_o_bool : o = 0 ∨ o = 1 := by
        rcases h_o_or_eq with ho_zero | h_msb_eq
        · exact Or.inl ho_zero
        · right
          -- MSBs equal: e = 0. Then h_iz1: 1 - inv*0 - o = 0, so 1 - o = 0, so o = 1.
          have h_e_zero : r_pol[Fin.last k] - p'[Fin.last k].eval = 0 :=
            sub_eq_zero.mpr h_msb_eq
          have h_simp := h_iz1
          have h_map_r : (Vector.map Exp.v r_pol)[Fin.last k].eval =
              r_pol[Fin.last k] := by simp [Vector.getElem_map, Exp.eval]
          simp only [Exp.eval_sub, Exp.eval_mul, Exp.eval, h_map_r,
                     Exp.eval_ofNat, Nat.cast_one] at h_simp
          rw [h_e_zero, MulZeroClass.mul_zero, sub_zero, sub_eq_zero] at h_simp
          exact h_simp.symm
      have h_new_isLt_bool :
          (isLt + (1 - Exp.v o) - isLt * (1 - Exp.v o)).eval = 0 ∨
          (isLt + (1 - Exp.v o) - isLt * (1 - Exp.v o)).eval = 1 := by
        rcases h_isLt_bool with h_isLt_0 | h_isLt_1
        · rcases h_o_bool with h_o_0 | h_o_1
          · right
            change (isLt + (1 - Exp.v o) - isLt * (1 - Exp.v o)).eval = 1
            simp only [Exp.eval_add, Exp.eval_sub, Exp.eval_mul, Exp.eval,
                       Exp.eval_ofNat, Nat.cast_one]
            rw [h_isLt_0, h_o_0]; ring
          · left
            change (isLt + (1 - Exp.v o) - isLt * (1 - Exp.v o)).eval = 0
            simp only [Exp.eval_add, Exp.eval_sub, Exp.eval_mul, Exp.eval,
                       Exp.eval_ofNat, Nat.cast_one]
            rw [h_isLt_0, h_o_1]; ring
        · right
          change (isLt + (1 - Exp.v o) - isLt * (1 - Exp.v o)).eval = 1
          simp only [Exp.eval_add, Exp.eval_sub, Exp.eval_mul, Exp.eval,
                     Exp.eval_ofNat, Nat.cast_one]
          rw [h_isLt_1]; ring
      refine ih
        (isLt := isLt ||| (1 - Exp.v o))
        (r_pol := Vector.ofFn (fun i ↦ r_pol[i.castSucc]))
        (p' := Vector.ofFn (fun i ↦ p'[i.castSucc]))
        (fun i => by simp [Vector.getElem_ofFn]; exact hr_rc i.castSucc)
        (fun i => by simp [Vector.getElem_ofFn]; exact hp_rc i.castSucc)
        h_new_isLt_bool
        ?_
      rintro (h_new_isLt_1 | ⟨h_new_isLt_0, h_tail_lt⟩)
      · -- new_isLt = 1. Need to derive outer invariant.
        apply hbisim
        -- new_isLt = isLt + (1 - o) - isLt * (1 - o).
        have h_new_isLt_eval :
            (isLt.eval + (1 - o) - isLt.eval * (1 - o)) = 1 := by
          have h := h_new_isLt_1
          change (isLt + (1 - Exp.v o) - isLt * (1 - Exp.v o)).eval = 1 at h
          simpa [Exp.eval] using h
        -- Rearrange: o * (isLt.eval - 1) = 0, so o = 0 or isLt = 1.
        have h_or_zero : o * (isLt.eval - 1) = 0 := by linear_combination h_new_isLt_eval
        rcases mul_eq_zero.mp h_or_zero with ho_zero | h_isLt_one
        · -- o = 0. Combined with h_o_or_eq: either o = 0 (this case) or MSBs equal.
          -- With o = 0, and h_iz1 (asserting 1 - inv*e - o = 0), we derive inv*e = 1, so e ≠ 0, so MSBs unequal.
          -- With isLt.eval, from num2bits we get (if isLt = 0) that a ≤ b. Combined with MSBs unequal, a < b.
          -- Then full_r < full_p' (via MSB strict less + tail bound).
          by_cases h_isLt_z : isLt.eval = 0
          · right
            refine ⟨h_isLt_z, ?_⟩
            have h_msb_le := h_msb_le_of_isLt_zero h_isLt_z
            -- MSBs unequal: derive from h_iz1 with o = 0.
            have h_msb_ne : r_pol[Fin.last k] ≠ p'[Fin.last k].eval := by
              intro h_eq
              have h_simp := h_iz1
              have h_map_r : (Vector.map Exp.v r_pol)[Fin.last k].eval =
                  r_pol[Fin.last k] := by simp [Vector.getElem_map, Exp.eval]
              simp only [Exp.eval_sub, Exp.eval_mul, Exp.eval, h_map_r,
                         Exp.eval_ofNat, Nat.cast_one] at h_simp
              -- h_simp: 1 - inv * (r_pol[Fin.last k] - p'[Fin.last k].eval) - o = 0
              rw [h_eq, sub_self, MulZeroClass.mul_zero, sub_zero,
                  sub_eq_zero] at h_simp
              rw [ho_zero] at h_simp
              exact zero_ne_one h_simp.symm
            have h_a_lt : a < b := by
              rcases lt_or_eq_of_le h_msb_le with h | h_a_eq
              · exact h
              · exfalso
                apply h_msb_ne
                exact ZMod.val_injective p h_a_eq
            -- Now full_r = tail_r + a * (2^w)^k, full_p' = tail_p' + b * (2^w)^k.
            -- With a < b and tail_r < (2^w)^k, full_r < full_p'.
            rw [Fin.sum_univ_castSucc (n := k), Fin.sum_univ_castSucc (n := k)]
            simp only [Fin.val_last, Fin.val_castSucc, ← ha_def, ← hb_def]
            have h_2w_pos : 0 < 2 ^ w := Nat.pos_of_neZero _
            have h_tail_r_bd : ∑ i : Fin k, r_pol[i.castSucc].val * (2 ^ w) ^ i.1 <
                (2 ^ w) ^ k :=
              tail_lt_pow_of_range h_2w_pos (fun i => r_pol[i].val) hr_rc
            have h_msb_gap : (a + 1) * (2 ^ w) ^ k ≤ b * (2 ^ w) ^ k :=
              Nat.mul_le_mul_right _ h_a_lt
            have h_expand : (a + 1) * (2 ^ w) ^ k = a * (2 ^ w) ^ k + (2 ^ w) ^ k := by ring
            rw [h_expand] at h_msb_gap
            have h_tail_p'_nn : 0 ≤ ∑ i : Fin k, p'[i.castSucc].eval.val * (2 ^ w) ^ i.1 :=
              Nat.zero_le _
            omega
          · -- isLt.eval ≠ 0. From `h_isLt_bool`, isLt.eval = 1.
            left
            rcases h_isLt_bool with h | h
            · exact absurd h h_isLt_z
            · exact h
        · -- isLt.eval - 1 = 0, so isLt.eval = 1.
          left
          linear_combination h_isLt_one
      · -- new_isLt = 0 ∧ tail < tail. Combined with MSBs equal (from below), derive full <.
        apply hbisim
        -- Given h_isLt_bool, isLt.eval ∈ {0, 1}. new_isLt = 0 forces isLt = 0.
        have h_new_isLt_eval :
            (isLt.eval + (1 - o) - isLt.eval * (1 - o)) = 0 := by
          have h := h_new_isLt_0
          change (isLt + (1 - Exp.v o) - isLt * (1 - Exp.v o)).eval = 0 at h
          simpa [Exp.eval] using h
        have h_isLt_zero : isLt.eval = 0 := by
          rcases h_isLt_bool with h | h
          · exact h
          · -- isLt = 1: then new_isLt = 1 + (1 - o) - (1 - o) = 1, contradicting = 0.
            exfalso
            rw [h] at h_new_isLt_eval
            have h_one_zero : (1 : ZMod p) = 0 := by linear_combination h_new_isLt_eval
            exact absurd h_one_zero one_ne_zero
        -- With isLt.eval = 0: new_isLt = 0 + (1 - o) - 0 = 1 - o. Setting = 0: o = 1.
        have ho : o = 1 := by
          rw [h_isLt_zero] at h_new_isLt_eval
          linear_combination -h_new_isLt_eval
        -- With o = 1 and h_iz2 (o * e = 0): e = 0, so MSBs equal.
        have h_msb_eq : r_pol[Fin.last k] = p'[Fin.last k].eval := by
          rcases h_o_or_eq with ho' | he
          · rw [ho] at ho'; exact absurd ho' one_ne_zero
          · exact he
        -- With MSBs equal and tail <, full <.
        right
        refine ⟨h_isLt_zero, ?_⟩
        -- full_r < full_p' via MSBs equal + tail <.
        rw [Fin.sum_univ_castSucc (n := k), Fin.sum_univ_castSucc (n := k)]
        simp only [Fin.val_last, Fin.val_castSucc, ← ha_def, ← hb_def]
        have h_val_eq : a = b := by
          rw [ha_def, hb_def]; congr 1
        have h_msb_mul : a * (2 ^ w) ^ k = b * (2 ^ w) ^ k :=
          congrArg (· * (2 ^ w) ^ k) h_val_eq
        -- h_tail_lt is about the truncated vectors (Vector.ofFn).
        have h_tail_conv :
            ∑ i : Fin k, (Vector.ofFn (fun j : Fin k ↦ r_pol[j.castSucc]))[i].val *
                (2 ^ w) ^ i.1 =
            ∑ i : Fin k, r_pol[i.castSucc].val * (2 ^ w) ^ i.1 :=
          Finset.sum_congr rfl (fun i _ => by simp [Vector.getElem_ofFn])
        have h_tail_conv' :
            ∑ i : Fin k, (Vector.ofFn (fun j : Fin k ↦ p'[j.castSucc]))[i].eval.val *
                (2 ^ w) ^ i.1 =
            ∑ i : Fin k, p'[i.castSucc].eval.val * (2 ^ w) ^ i.1 :=
          Finset.sum_congr rfl (fun i _ => by simp [Vector.getElem_ofFn])
        rw [h_tail_conv, h_tail_conv'] at h_tail_lt
        omega
    · exact wrBisim.none
    · exact wrBisim.none

lemma check_lt_spec {k w : ℕ} {r_pol : Vector (ZMod p) k} {p' : Vector (Expₑ p) k}
    {cont : Csₑ p} {d : denotation (ZMod p)}
    (hp_bound : 2 ^ (w + 1) ≤ p)
    (hr_rc : ∀ i : Fin k, r_pol[i].val < 2 ^ w)
    (hp_rc : ∀ i : Fin k, p'[i].eval.val < 2 ^ w) :
  (∑ i : Fin _, r_pol[i].val * (2 ^ w) ^ i.1 < ∑ i : Fin _, p'[i].eval.val * (2 ^ w) ^ i.1 → wrBisim d cont.eval) →
    wrBisim d ((check_lt_circuit w (Vector.map Exp.v r_pol) p' cont).eval) := by
  intro hbisim
  unfold check_lt_circuit
  apply check_lt'_wrBisim hp_bound hr_rc hp_rc (Or.inl (by simp [Exp.eval]))
  rintro (h_isLt_one | ⟨_, h_lt⟩)
  · -- `(0 : Expₑ p).eval = 1` is impossible (since `p > 2`).
    exfalso
    simp [Exp.eval] at h_isLt_one
  · exact hbisim h_lt

omit inst' in
/-- Cauchy product: the product of two truncated power series with vanishing coefficients
beyond index `k` equals a single sum of convolutions over `range (2*k - 1)`. -/
private lemma sum_mul_sum_conv_eq (k : ℕ) (f g : ℕ → ℤ) (x : ℤ)
    (hf : ∀ j, k ≤ j → f j = 0) (hg : ∀ j, k ≤ j → g j = 0) (hk : 1 ≤ k) :
    (∑ j ∈ Finset.range k, f j * x ^ j) * (∑ j ∈ Finset.range k, g j * x ^ j) =
    ∑ n ∈ Finset.range (2 * k - 1),
      (∑ j ∈ Finset.range (n + 1), f j * g (n - j)) * x ^ n := by
  -- Use Polynomial.coeff_mul. Define A, B with A.coeff = f for j < k, else 0.
  set A : Polynomial ℤ := ∑ j ∈ Finset.range k, Polynomial.monomial j (f j) with hA_def
  set B : Polynomial ℤ := ∑ j ∈ Finset.range k, Polynomial.monomial j (g j) with hB_def
  have hA_eval : A.eval x = ∑ j ∈ Finset.range k, f j * x ^ j := by
    rw [hA_def, Polynomial.eval_finset_sum]
    apply Finset.sum_congr rfl
    intros j _
    rw [Polynomial.eval_monomial]
  have hB_eval : B.eval x = ∑ j ∈ Finset.range k, g j * x ^ j := by
    rw [hB_def, Polynomial.eval_finset_sum]
    apply Finset.sum_congr rfl
    intros j _
    rw [Polynomial.eval_monomial]
  have hA_coeff : ∀ j, A.coeff j = if j < k then f j else 0 := by
    intro j
    rw [hA_def, Polynomial.finset_sum_coeff]
    split_ifs with h
    · rw [Finset.sum_eq_single j]
      · rw [Polynomial.coeff_monomial_same]
      · intros i _ hi
        exact Polynomial.coeff_monomial_of_ne _ (Ne.symm hi)
      · intros h_no; exact absurd (Finset.mem_range.mpr h) h_no
    · apply Finset.sum_eq_zero
      intros i hi
      rw [Finset.mem_range] at hi
      exact Polynomial.coeff_monomial_of_ne _ (fun he => h (he ▸ hi))
  have hB_coeff : ∀ j, B.coeff j = if j < k then g j else 0 := by
    intro j
    rw [hB_def, Polynomial.finset_sum_coeff]
    split_ifs with h
    · rw [Finset.sum_eq_single j]
      · rw [Polynomial.coeff_monomial_same]
      · intros i _ hi
        exact Polynomial.coeff_monomial_of_ne _ (Ne.symm hi)
      · intros h_no; exact absurd (Finset.mem_range.mpr h) h_no
    · apply Finset.sum_eq_zero
      intros i hi
      rw [Finset.mem_range] at hi
      exact Polynomial.coeff_monomial_of_ne _ (fun he => h (he ▸ hi))
  -- Compute (A * B).coeff n = ∑ j ∈ range (n+1), A.coeff j * B.coeff (n - j).
  have hAB_coeff : ∀ n, (A * B).coeff n =
      ∑ j ∈ Finset.range (n + 1), A.coeff j * B.coeff (n - j) := by
    intro n
    rw [Polynomial.coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  -- (A * B).coeff n equals the convolution sum for n < 2k-1, zero otherwise.
  have hAB_coeff_conv : ∀ n, n < 2 * k - 1 →
      (A * B).coeff n = ∑ j ∈ Finset.range (n + 1), f j * g (n - j) := by
    intros n hn
    rw [hAB_coeff]
    apply Finset.sum_congr rfl
    intros j hj
    rw [Finset.mem_range] at hj
    rw [hA_coeff, hB_coeff]
    by_cases hjk : j < k
    · rw [if_pos hjk]
      by_cases hnjk : n - j < k
      · rw [if_pos hnjk]
      · rw [if_neg hnjk, hg (n - j) (by omega)]
    · rw [if_neg hjk, hf j (by omega)]
      simp
  -- (A * B).coeff n = 0 for n ≥ 2k - 1
  have hAB_coeff_zero : ∀ n, 2 * k - 1 ≤ n → (A * B).coeff n = 0 := by
    intros n hn
    rw [hAB_coeff]
    apply Finset.sum_eq_zero
    intros j hj
    rw [Finset.mem_range] at hj
    rw [hA_coeff, hB_coeff]
    by_cases hjk : j < k
    · rw [if_pos hjk]
      have hnjk : ¬ n - j < k := by omega
      rw [if_neg hnjk]
      simp
    · rw [if_neg hjk]
      simp
  -- Use hAB_coeff_zero to bound the degree of A * B.
  have hAB_degree : (A * B).degree < (2 * k - 1 : ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intros m hm
    exact hAB_coeff_zero m (by exact_mod_cast hm)
  have hAB_natDegree : (A * B).natDegree < 2 * k - 1 := by
    by_cases h : A * B = 0
    · rw [h]; simp; omega
    · rw [← Polynomial.natDegree_lt_iff_degree_lt h] at hAB_degree
      exact_mod_cast hAB_degree
  -- Now apply eval_eq_sum_range' to (A * B).
  have hAB_eval_sum : (A * B).eval x =
      ∑ n ∈ Finset.range (2 * k - 1), (A * B).coeff n * x ^ n := by
    exact Polynomial.eval_eq_sum_range' hAB_natDegree x
  -- Combine everything.
  rw [← hA_eval, ← hB_eval, ← Polynomial.eval_mul, hAB_eval_sum]
  apply Finset.sum_congr rfl
  intros n hn
  rw [Finset.mem_range] at hn
  rw [hAB_coeff_conv n hn]

set_option maxHeartbeats 4000000 in
lemma fpmul_soundness {w k : ℕ} {a b p' : Vector (Exp p (ZMod p)) k} {c : Vector (ZMod p) k → Circuit p (ZMod p)}
      (ih : ∀ (a : Vector (ZMod p) k), circuitWF (c a) → wrBisim (c a).eval (c a).toCs.eval) :
    circuitWF (Circuit.fpmul w k a b p' c) →
      wrBisim (Circuit.fpmul w k a b p' c).eval (Circuit.fpmul w k a b p' c).toCs.eval := by
  intros h
  unfold circuitWF at h
  have invariant := h.1
  have h := h.2
  unfold Circuit.eval
  split_ifs with cond
  · unfold Circuit.toCs fpMul_circuit
    apply range_check_vec_circuit_spec
    intros a_rc
    apply range_check_vec_circuit_spec
    intros b_rc
    apply range_check_vec_circuit_spec
    intros p'_rc
    apply rw_bisim_uncurry
    intros ab_pol
    have k_bound : 2 * k - 1 < p := by
      have h1 : 2 * k - 1 ≤ 2 ^ Nat.clog 2 (2 * k - 1) :=
        Nat.le_pow_clog (b := 2) (by omega) (2 * k - 1)
      have h2 : 2 ^ Nat.clog 2 (2 * k - 1) < 2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 4) :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    apply assert_poly_eq_prod_spec k_bound
    intros ab_honest
    apply rw_bisim_uncurry
    intros q_pol
    apply range_check_vec_circuit_spec
    intros q_rc
    apply rw_bisim_uncurry
    intros r_pol
    apply range_check_vec_circuit_spec
    intros r_rc
    apply rw_bisim_uncurry
    intros t_pol
    apply eq_check_spec k_bound
    intros t_honest
    apply check_carry_spec invariant
    intros t_carry
    apply check_lt_spec
      (by
        -- `2 ^ (w + 1) ≤ p` from `invariant : 2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 4) ≤ p`
        have h1 : (2 : ℕ) ^ (w + 1) ≤ 2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 4) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega)
      (fun i => by aesop)
      p'_rc
    intros r_lt_p'
    simp
    have :
      Circuit.nat2words p w k
        (((∑ x : Fin k, a[x].eval.val * (2 ^ w) ^ x.1) * ∑ x : Fin k, b[↑x].eval.val * (2 ^ w) ^ x.1) %
          ∑ x : Fin k, p'[x].eval.val * (2 ^ w) ^ x.1) = r_pol := by
      generalize a_eq : ∑ x : Fin k, a[x].eval.val * (2 ^ w) ^ x.1 = a_val
      generalize b_eq : ∑ x : Fin k, b[x].eval.val * (2 ^ w) ^ x.1 = b_val
      generalize p'_eq : ∑ x : Fin k, p'[x].eval.val * (2 ^ w) ^ x.1 = p'_val
      generalize r_eq : ∑ x : Fin k, r_pol[x].val * (2 ^ w) ^ x.1 = r_val
      have : a_val * b_val % p'_val = r_val % p'_val := by
        -- Introduce q_val and simplify t_honest.
        set q_val : ℕ := ∑ x : Fin k, q_pol[x].val * (2 ^ w) ^ x.1 with q_val_def
        simp only [Vector.map_map, show (Exp.eval (p := p) ∘ Exp.v) = id from
          funext (fun x => by simp [Exp.eval])] at t_honest
        simp only [Vector.map_id] at t_honest
        by_cases hk0 : k = 0
        · subst hk0
          have ha : a_val = 0 := by rw [← a_eq]; simp
          have hb : b_val = 0 := by rw [← b_eq]; simp
          have hp : p'_val = 0 := by rw [← p'_eq]; simp
          have hr : r_val = 0 := by rw [← r_eq]; simp
          rw [ha, hb, hp, hr]
        have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have h_2km1_pos : 0 < 2 * k - 1 := by omega
        set t_off : ℕ := 2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 3) with ht_off
        have h_pow_succ : t_off ≤ 2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 4) := by
          rw [ht_off]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        have h_toff_le_p : t_off ≤ p := le_trans h_pow_succ invariant
        have h_2toff_le_p : 2 * t_off ≤ p := by
          have h_eq : 2 * t_off = 2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 4) := by
            rw [ht_off]; ring
          rw [h_eq]; exact invariant
        -- Integer lifts.
        let aint : ℕ → ℤ := fun j => if h : j < k then (a[j].eval.val : ℤ) else 0
        let bint : ℕ → ℤ := fun j => if h : j < k then (b[j].eval.val : ℤ) else 0
        let pint : ℕ → ℤ := fun j => if h : j < k then ((p'[j].eval).val : ℤ) else 0
        let qint : ℕ → ℤ := fun j => if h : j < k then (q_pol[j].val : ℤ) else 0
        let rint : ℕ → ℤ := fun j => if h : j < k then (r_pol[j].val : ℤ) else 0
        let diff : ℕ → ℤ := fun n =>
          (∑ j ∈ Finset.range (n + 1), aint j * bint (n - j)) -
          (∑ j ∈ Finset.range (n + 1), pint j * qint (n - j)) -
          rint n
        have h_aint_bound : ∀ j, 0 ≤ aint j ∧ aint j < (2 ^ w : ℤ) := fun j => by
          simp only [aint]; split_ifs with hj
          · exact ⟨Int.natCast_nonneg _, by exact_mod_cast a_rc ⟨j, hj⟩⟩
          · exact ⟨le_refl 0, by positivity⟩
        have h_bint_bound : ∀ j, 0 ≤ bint j ∧ bint j < (2 ^ w : ℤ) := fun j => by
          simp only [bint]; split_ifs with hj
          · exact ⟨Int.natCast_nonneg _, by exact_mod_cast b_rc ⟨j, hj⟩⟩
          · exact ⟨le_refl 0, by positivity⟩
        have h_pint_bound : ∀ j, 0 ≤ pint j ∧ pint j < (2 ^ w : ℤ) := fun j => by
          simp only [pint]; split_ifs with hj
          · exact ⟨Int.natCast_nonneg _, by exact_mod_cast p'_rc ⟨j, hj⟩⟩
          · exact ⟨le_refl 0, by positivity⟩
        have h_qint_bound : ∀ j, 0 ≤ qint j ∧ qint j < (2 ^ w : ℤ) := fun j => by
          simp only [qint]; split_ifs with hj
          · refine ⟨Int.natCast_nonneg _, ?_⟩
            have h_nat : q_pol[j].val < 2 ^ w := by simpa [Exp.eval] using q_rc ⟨j, hj⟩
            exact_mod_cast h_nat
          · exact ⟨le_refl 0, by positivity⟩
        have h_rint_bound : ∀ j, 0 ≤ rint j ∧ rint j < (2 ^ w : ℤ) := fun j => by
          simp only [rint]; split_ifs with hj
          · refine ⟨Int.natCast_nonneg _, ?_⟩
            have h_nat : r_pol[j].val < 2 ^ w := by simpa [Exp.eval] using r_rc ⟨j, hj⟩
            exact_mod_cast h_nat
          · exact ⟨le_refl 0, by positivity⟩
        have h_2w_pos : (0 : ℤ) < (2 ^ w : ℤ) := by positivity
        have h_2pw_pow : (2 ^ w : ℤ) * (2 ^ w : ℤ) = (2 ^ (2 * w) : ℤ) := by
          rw [← pow_add]; congr 1; ring
        have h_diff_bound : ∀ n : ℕ, n < 2 * k - 1 →
            -(t_off : ℤ) ≤ diff n ∧ diff n < (t_off : ℤ) := by
          intro n hn
          have h_term_ab : ∀ j, aint j * bint (n - j) ≤ (2 ^ w : ℤ) * (2 ^ w : ℤ) := fun j =>
            mul_le_mul (le_of_lt (h_aint_bound j).2) (le_of_lt (h_bint_bound (n - j)).2)
              (h_bint_bound (n - j)).1 (le_of_lt h_2w_pos)
          have h_term_pq : ∀ j, pint j * qint (n - j) ≤ (2 ^ w : ℤ) * (2 ^ w : ℤ) := fun j =>
            mul_le_mul (le_of_lt (h_pint_bound j).2) (le_of_lt (h_qint_bound (n - j)).2)
              (h_qint_bound (n - j)).1 (le_of_lt h_2w_pos)
          have h_term_ab_nn : ∀ j, 0 ≤ aint j * bint (n - j) := fun j =>
            mul_nonneg (h_aint_bound j).1 (h_bint_bound (n - j)).1
          have h_term_pq_nn : ∀ j, 0 ≤ pint j * qint (n - j) := fun j =>
            mul_nonneg (h_pint_bound j).1 (h_qint_bound (n - j)).1
          have h_ab_sum_nn : 0 ≤ ∑ j ∈ Finset.range (n + 1), aint j * bint (n - j) :=
            Finset.sum_nonneg (fun j _ => h_term_ab_nn j)
          have h_pq_sum_nn : 0 ≤ ∑ j ∈ Finset.range (n + 1), pint j * qint (n - j) :=
            Finset.sum_nonneg (fun j _ => h_term_pq_nn j)
          have h_ab_sum_le : ∑ j ∈ Finset.range (n + 1), aint j * bint (n - j) ≤
              ((n + 1 : ℕ) : ℤ) * ((2 ^ w : ℤ) * (2 ^ w : ℤ)) := by
            calc ∑ j ∈ Finset.range (n + 1), aint j * bint (n - j)
                ≤ ∑ _j ∈ Finset.range (n + 1), (2 ^ w : ℤ) * (2 ^ w : ℤ) :=
                  Finset.sum_le_sum (fun j _ => h_term_ab j)
              _ = ((n + 1 : ℕ) : ℤ) * ((2 ^ w : ℤ) * (2 ^ w : ℤ)) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have h_pq_sum_le : ∑ j ∈ Finset.range (n + 1), pint j * qint (n - j) ≤
              ((n + 1 : ℕ) : ℤ) * ((2 ^ w : ℤ) * (2 ^ w : ℤ)) := by
            calc ∑ j ∈ Finset.range (n + 1), pint j * qint (n - j)
                ≤ ∑ _j ∈ Finset.range (n + 1), (2 ^ w : ℤ) * (2 ^ w : ℤ) :=
                  Finset.sum_le_sum (fun j _ => h_term_pq j)
              _ = ((n + 1 : ℕ) : ℤ) * ((2 ^ w : ℤ) * (2 ^ w : ℤ)) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have h_rn := h_rint_bound n
          have h_2km1_le_pow : (2 * k - 1 : ℕ) ≤ 2 ^ Nat.clog 2 (2 * k - 1) :=
            Nat.le_pow_clog (b := 2) (by omega) _
          have h_n1_le_pow : (n + 1 : ℕ) ≤ 2 ^ Nat.clog 2 (2 * k - 1) := by omega
          have h_2w_le_22w : (2 ^ w : ℕ) ≤ 2 ^ (2 * w) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          have h_toff_unfold : (t_off : ℤ) = 8 * (2 ^ (2 * w) : ℤ) * (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) := by
            rw [ht_off]
            push_cast
            rw [show 2 * w + Nat.clog 2 (2 * k - 1) + 3 = 3 + 2 * w + Nat.clog 2 (2 * k - 1) from by ring,
                pow_add, pow_add]
            ring
          have h_n1_le_int : ((n + 1 : ℕ) : ℤ) ≤ (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) := by
            exact_mod_cast h_n1_le_pow
          have h_2w_le_int : (2 ^ w : ℤ) ≤ (2 ^ (2 * w) : ℤ) := by exact_mod_cast h_2w_le_22w
          have h_22w_pos : (0 : ℤ) < (2 ^ (2 * w) : ℤ) := by positivity
          have h_clog_pos : (1 : ℤ) ≤ (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) := by
            have := Nat.one_le_two_pow (n := Nat.clog 2 (2 * k - 1))
            exact_mod_cast this
          have h_prod_pos : (0 : ℤ) <
              (2 ^ (2 * w) : ℤ) * (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) := by
            exact mul_pos h_22w_pos (by linarith)
          have h_key : 2 * ((n + 1 : ℕ) : ℤ) * ((2 ^ w : ℤ) * (2 ^ w : ℤ)) + (2 ^ w : ℤ) <
              (t_off : ℤ) := by
            rw [h_2pw_pow, h_toff_unfold]
            calc 2 * ((n + 1 : ℕ) : ℤ) * (2 ^ (2 * w) : ℤ) + (2 ^ w : ℤ)
                ≤ 2 * (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) * (2 ^ (2 * w) : ℤ) + (2 ^ (2 * w) : ℤ) := by
                  have h1 : 2 * ((n + 1 : ℕ) : ℤ) * (2 ^ (2 * w) : ℤ) ≤
                      2 * (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) * (2 ^ (2 * w) : ℤ) := by
                    have := mul_le_mul_of_nonneg_right h_n1_le_int (le_of_lt h_22w_pos)
                    linarith
                  linarith
              _ ≤ 2 * (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) * (2 ^ (2 * w) : ℤ) +
                    (2 ^ (2 * w) : ℤ) * (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) := by
                  have h1 : (2 ^ (2 * w) : ℤ) ≤ (2 ^ (2 * w) : ℤ) * (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) := by
                    have := mul_le_mul_of_nonneg_left h_clog_pos (le_of_lt h_22w_pos)
                    linarith
                  linarith
              _ < 8 * (2 ^ (2 * w) : ℤ) * (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) := by nlinarith [h_prod_pos]
          refine ⟨?_, ?_⟩
          · simp only [diff]
            linarith [h_ab_sum_nn, h_pq_sum_le, h_rn.2, h_rn.1, h_key]
          · simp only [diff]
            linarith [h_ab_sum_le, h_pq_sum_nn, h_rn.2, h_rn.1, h_key]
        -- Coefficient relation via polynomial identity.
        have h_diff_cast : ∀ n : ℕ, ∀ (hn : n < 2 * k - 1),
            ((diff n : ℤ) : ZMod p) = t_pol[(⟨n, hn⟩ : Fin (2 * k - 1))] := by
          intro n hn
          have h_tpol_coeff : t_pol[(⟨n, hn⟩ : Fin (2 * k - 1))] = (toCompPoly t_pol).coeff n := by
            rw [coeff_toCompPoly]; simp [hn]
          have h_abpol_coeff : ab_pol[(⟨n, hn⟩ : Fin (2 * k - 1))] = (toCompPoly ab_pol).coeff n := by
            rw [coeff_toCompPoly]; simp [hn]
          have h_prod_coeff :
              (toCompPoly (Vector.map Exp.eval p') * toCompPoly q_pol).coeff n =
                ∑ j ∈ Finset.range (n + 1),
                  (toCompPoly (Vector.map Exp.eval p')).coeff j *
                  (toCompPoly q_pol).coeff (n - j) :=
            CPolynomial.coeff_mul _ _ _
          have h_prod_coeff_ab :
              (toCompPoly (Vector.map Exp.eval a) * toCompPoly (Vector.map Exp.eval b)).coeff n =
                ∑ j ∈ Finset.range (n + 1),
                  (toCompPoly (Vector.map Exp.eval a)).coeff j *
                  (toCompPoly (Vector.map Exp.eval b)).coeff (n - j) :=
            CPolynomial.coeff_mul _ _ _
          have h_t_eq : t_pol[(⟨n, hn⟩ : Fin (2 * k - 1))] =
              ab_pol[(⟨n, hn⟩ : Fin (2 * k - 1))] -
              (toCompPoly (Vector.map Exp.eval p') * toCompPoly q_pol).coeff n -
              (if h : n < k then r_pol[(⟨n, h⟩ : Fin k)] else 0) := by
            rw [h_tpol_coeff, t_honest]
            rw [CPolynomial.coeff_sub, CPolynomial.coeff_sub]
            congr 1
            · congr 1
              rw [h_abpol_coeff]
            · rw [coeff_toCompPoly]
              split_ifs with h <;> rfl
          have h_ab_eq : ab_pol[(⟨n, hn⟩ : Fin (2 * k - 1))] =
              ∑ j ∈ Finset.range (n + 1),
                (toCompPoly (Vector.map Exp.eval a)).coeff j *
                (toCompPoly (Vector.map Exp.eval b)).coeff (n - j) := by
            rw [h_abpol_coeff, ab_honest, h_prod_coeff_ab]
          rw [h_t_eq, h_ab_eq, h_prod_coeff]
          have h_a_coeff : ∀ j, (toCompPoly (Vector.map Exp.eval a)).coeff j =
              if h : j < k then a[j].eval else 0 := by
            intro j; rw [coeff_toCompPoly]
            split_ifs with h
            · simp [Vector.getElem_map]
            · rfl
          have h_b_coeff : ∀ j, (toCompPoly (Vector.map Exp.eval b)).coeff j =
              if h : j < k then b[j].eval else 0 := by
            intro j; rw [coeff_toCompPoly]
            split_ifs with h
            · simp [Vector.getElem_map]
            · rfl
          have h_p_coeff : ∀ j, (toCompPoly (Vector.map Exp.eval p')).coeff j =
              if h : j < k then (p'[j].eval) else 0 := by
            intro j; rw [coeff_toCompPoly]
            split_ifs with h
            · simp [Vector.getElem_map]
            · rfl
          have h_q_coeff : ∀ j, (toCompPoly q_pol).coeff j =
              if h : j < k then q_pol[j] else 0 := fun j => by rw [coeff_toCompPoly]
          simp_rw [h_a_coeff, h_b_coeff, h_p_coeff, h_q_coeff]
          simp only [diff]
          push_cast
          have h_aint_cast : ∀ j : ℕ, ((aint j : ℤ) : ZMod p) =
              if h : j < k then a[j].eval else 0 := by
            intro j; simp only [aint]
            split_ifs with h
            · push_cast; rw [ZMod.natCast_zmod_val]
            · simp
          have h_bint_cast : ∀ j : ℕ, ((bint j : ℤ) : ZMod p) =
              if h : j < k then b[j].eval else 0 := by
            intro j; simp only [bint]
            split_ifs with h
            · push_cast; rw [ZMod.natCast_zmod_val]
            · simp
          have h_pint_cast : ∀ j : ℕ, ((pint j : ℤ) : ZMod p) =
              if h : j < k then (p'[j].eval) else 0 := by
            intro j; simp only [pint]
            split_ifs with h
            · push_cast; rw [ZMod.natCast_zmod_val]
            · simp
          have h_qint_cast : ∀ j : ℕ, ((qint j : ℤ) : ZMod p) =
              if h : j < k then q_pol[j] else 0 := by
            intro j; simp only [qint]
            split_ifs with h
            · push_cast; rw [ZMod.natCast_zmod_val]
            · simp
          have h_rint_cast : ((rint n : ℤ) : ZMod p) =
              if h : n < k then r_pol[(⟨n, h⟩ : Fin k)] else 0 := by
            simp only [rint]
            split_ifs with h
            · push_cast; rw [ZMod.natCast_zmod_val]; rfl
            · simp
          simp_rw [h_aint_cast, h_bint_cast, h_pint_cast, h_qint_cast]
          rw [h_rint_cast]
        have h_zmod_int_eq : ∀ i : Fin (2 * k - 1),
            zmod_int_cast t_off t_pol[i] = diff i.1 := by
          intro i
          apply zmod_int_cast_eq_of_repr t_off t_pol[i] (diff i.1) h_toff_le_p
          · rw [show ((t_off : ℕ) : ℤ) + ((t_off : ℕ) : ℤ) = ((2 * t_off : ℕ) : ℤ) from by push_cast; ring]
            exact_mod_cast h_2toff_le_p
          · convert h_diff_cast i.1 i.2
          · exact (h_diff_bound i.1 i.2).1
          · exact (h_diff_bound i.1 i.2).2
        have h_diff_sum_zero : ∑ i : Fin (2 * k - 1), diff i.1 * (2 ^ w : ℤ) ^ i.1 = 0 := by
          rw [← t_carry]
          apply Finset.sum_congr rfl
          intros i _
          congr 1
          rw [h_zmod_int_eq i]
        -- Extend integer sums from range k to range (2*k - 1) for combinatorial expansion.
        have h_aint_zero : ∀ j, k ≤ j → aint j = 0 := fun j hj => by
          simp only [aint]; rw [dif_neg (by omega)]
        have h_bint_zero : ∀ j, k ≤ j → bint j = 0 := fun j hj => by
          simp only [bint]; rw [dif_neg (by omega)]
        have h_pint_zero : ∀ j, k ≤ j → pint j = 0 := fun j hj => by
          simp only [pint]; rw [dif_neg (by omega)]
        have h_qint_zero : ∀ j, k ≤ j → qint j = 0 := fun j hj => by
          simp only [qint]; rw [dif_neg (by omega)]
        have h_rint_zero : ∀ j, k ≤ j → rint j = 0 := fun j hj => by
          simp only [rint]; rw [dif_neg (by omega)]
        have h_aval_int : (a_val : ℤ) = ∑ j ∈ Finset.range k, aint j * (2 ^ w : ℤ) ^ j := by
          rw [← a_eq]
          push_cast
          rw [← Fin.sum_univ_eq_sum_range]
          apply Finset.sum_congr rfl
          intros x _
          show ((a[x].eval.val * (2 ^ w) ^ (x : ℕ) : ℕ) : ℤ) = aint x.1 * (2 ^ w : ℤ) ^ x.1
          simp only [aint]; rw [dif_pos x.2]
          push_cast
          simp only [Fin.getElem_fin]
        have h_bval_int : (b_val : ℤ) = ∑ j ∈ Finset.range k, bint j * (2 ^ w : ℤ) ^ j := by
          rw [← b_eq]
          push_cast
          rw [← Fin.sum_univ_eq_sum_range]
          apply Finset.sum_congr rfl
          intros x _
          show ((b[x].eval.val * (2 ^ w) ^ (x : ℕ) : ℕ) : ℤ) = bint x.1 * (2 ^ w : ℤ) ^ x.1
          simp only [bint]; rw [dif_pos x.2]
          push_cast
          simp only [Fin.getElem_fin]
        have h_pval_int : (p'_val : ℤ) = ∑ j ∈ Finset.range k, pint j * (2 ^ w : ℤ) ^ j := by
          rw [← p'_eq]
          push_cast
          rw [← Fin.sum_univ_eq_sum_range]
          apply Finset.sum_congr rfl
          intros x _
          show ((p'[x].eval.val * (2 ^ w) ^ (x : ℕ) : ℕ) : ℤ) = pint x.1 * (2 ^ w : ℤ) ^ x.1
          simp only [pint]; rw [dif_pos x.2]
          push_cast
          simp only [Fin.getElem_fin]
        have h_qval_int : (q_val : ℤ) = ∑ j ∈ Finset.range k, qint j * (2 ^ w : ℤ) ^ j := by
          rw [q_val_def]
          push_cast
          rw [← Fin.sum_univ_eq_sum_range]
          apply Finset.sum_congr rfl
          intros x _
          show ((q_pol[x].val * (2 ^ w) ^ (x : ℕ) : ℕ) : ℤ) = qint x.1 * (2 ^ w : ℤ) ^ x.1
          simp only [qint]; rw [dif_pos x.2]
          push_cast
          simp only [Fin.getElem_fin]
        have h_rval_int : (r_val : ℤ) = ∑ j ∈ Finset.range k, rint j * (2 ^ w : ℤ) ^ j := by
          rw [← r_eq]
          push_cast
          rw [← Fin.sum_univ_eq_sum_range]
          apply Finset.sum_congr rfl
          intros x _
          show ((r_pol[x].val * (2 ^ w) ^ (x : ℕ) : ℕ) : ℤ) = rint x.1 * (2 ^ w : ℤ) ^ x.1
          simp only [rint]; rw [dif_pos x.2]
          push_cast
          simp only [Fin.getElem_fin]
        -- Combinatorial expansion: ∑ diff n * x^n = a*b - p'*q - r in ℤ.
        -- We use `sum_mul_sum_conv_eq` (helper lemma below) to expand the products.
        have h_ab_prod : (a_val : ℤ) * b_val =
            ∑ n ∈ Finset.range (2 * k - 1),
              (∑ j ∈ Finset.range (n + 1), aint j * bint (n - j)) * (2 ^ w : ℤ) ^ n := by
          rw [h_aval_int, h_bval_int]
          exact sum_mul_sum_conv_eq k aint bint (2 ^ w : ℤ) h_aint_zero h_bint_zero hk1
        have h_pq_prod : (p'_val : ℤ) * q_val =
            ∑ n ∈ Finset.range (2 * k - 1),
              (∑ j ∈ Finset.range (n + 1), pint j * qint (n - j)) * (2 ^ w : ℤ) ^ n := by
          rw [h_pval_int, h_qval_int]
          exact sum_mul_sum_conv_eq k pint qint (2 ^ w : ℤ) h_pint_zero h_qint_zero hk1
        have h_rval_ext : (r_val : ℤ) =
            ∑ n ∈ Finset.range (2 * k - 1), rint n * (2 ^ w : ℤ) ^ n := by
          rw [h_rval_int]
          rw [show (2 * k - 1) = k + ((2 * k - 1) - k) from by omega, Finset.sum_range_add]
          have hzero : ∑ j ∈ Finset.range (2 * k - 1 - k), rint (k + j) * (2 ^ w : ℤ) ^ (k + j) = 0 := by
            apply Finset.sum_eq_zero
            intros j _
            rw [h_rint_zero (k + j) (by omega)]; ring
          linarith
        have h_sum_expand : ∑ i : Fin (2 * k - 1), diff i.1 * (2 ^ w : ℤ) ^ i.1 =
            (a_val : ℤ) * b_val - (p'_val : ℤ) * q_val - r_val := by
          rw [h_ab_prod, h_pq_prod, h_rval_ext]
          rw [Fin.sum_univ_eq_sum_range (fun i => diff i * (2 ^ w : ℤ) ^ i)]
          rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intros n _
          simp only [diff]
          ring
        have h_int_eq : (a_val : ℤ) * b_val = (p'_val : ℤ) * q_val + r_val := by
          have h0 := h_diff_sum_zero
          rw [h_sum_expand] at h0
          linarith
        have h_nat_eq : a_val * b_val = p'_val * q_val + r_val := by exact_mod_cast h_int_eq
        rw [h_nat_eq, show p'_val * q_val + r_val = r_val + p'_val * q_val from by ring]
        exact Nat.add_mul_mod_self_left _ _ _
      rw [r_eq, p'_eq] at r_lt_p'
      rw [this, Nat.mod_eq_of_lt r_lt_p']
      rw [←r_eq]
      apply Circuit.nat2words_of_sum
      · -- `2 ^ w < p` from `invariant : 2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 4) ≤ p`
        have h1 : (2 : ℕ) ^ w < 2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 4) :=
          Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      · intro i
        have := r_rc i
        simpa [Exp.eval] using this
    simp at this
    rw [this]
    exact (ih r_pol ∘ fun a => h r_pol) p
  · simp only [Fin.getElem_fin, Classical.not_and_iff_not_or_not] at cond
    unfold Circuit.toCs fpMul_circuit
    apply range_check_vec_circuit_spec
    intros a_rc
    apply range_check_vec_circuit_spec
    intros b_rc
    apply range_check_vec_circuit_spec
    intros p'_rc
    rcases cond with h | h | h | h
    · exfalso
      apply h
      exact a_rc
    · exfalso
      apply h
      exact b_rc
    · exfalso
      apply h
      exact p'_rc
    · simp only [not_lt, nonpos_iff_eq_zero, Finset.sum_eq_zero_iff, Finset.mem_univ, mul_eq_zero,
      ZMod.val_eq_zero, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, false_and, or_false,
      forall_const] at h
      -- p' is identically zero, so `∑ r[i].val * (2^w)^i < 0` is impossible.
      -- Walk the constraint chain using existing specs with d = .n, ending at
      -- check_lt_spec with a vacuously satisfiable hypothesis.
      have k_bound : 2 * k - 1 < p := by
        have h1 : (2 * k - 1 : ℕ) ≤ 2 ^ Nat.clog 2 (2 * k - 1) :=
          Nat.le_pow_clog (b := 2) (by omega) _
        have h2 : 2 ^ Nat.clog 2 (2 * k - 1) < 2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 4) :=
          Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      apply rw_bisim_uncurry
      intros ab_pol
      apply assert_poly_eq_prod_spec k_bound
      intros _ab_honest
      apply rw_bisim_uncurry
      intros q_pol
      apply range_check_vec_circuit_spec
      intros q_rc
      apply rw_bisim_uncurry
      intros r_pol
      apply range_check_vec_circuit_spec
      intros r_rc
      apply rw_bisim_uncurry
      intros t_pol
      apply eq_check_spec k_bound
      intros _t_honest
      apply check_carry_spec invariant
      intros _t_carry
      apply check_lt_spec
        (by
          have h1 : (2 : ℕ) ^ (w + 1) ≤ 2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 4) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          omega)
        (fun i => by
          have := r_rc i
          simpa [Exp.eval] using this)
        p'_rc
      intros r_lt_p'
      -- Contradiction: sum of naturals cannot be < 0, and p' evaluates to 0 identically.
      exfalso
      have h_p_zero : ∑ i : Fin k, p'[i].eval.val * (2 ^ w) ^ i.1 = 0 := by
        apply Finset.sum_eq_zero
        intros i _
        simp only [Fin.getElem_fin]
        rw [show p'[i.1].eval = 0 from h i]
        simp
      rw [h_p_zero] at r_lt_p'
      omega

omit inst' in
private lemma wrap_eq0 {wg : Wg p} {e : Expₑ p} {cs : Csₑ p} :
    wrap wg (Cs.eq0 e cs) = Cs.eq0 e (wrap wg cs) := by
  cases wg <;> rfl

private lemma num2bits_wrap_step
    {w : ℕ} {ea eb : Expₑ p} {wg : Wg p} {cs : Csₑ p}
    (h_range : ea.eval.val < 2 ^ w) (h_eq : ea.eval = eb.eval) :
    (wrap (Num2Bits.num2bits_wg w ea (fun _ ↦ wg))
          (Num2Bits.num2bits_circuit w eb (fun _ ↦ cs))).eval
      = (wrap wg cs).eval := by
  unfold Num2Bits.num2bits_wg Num2Bits.num2bits_circuit
  rw [foldr_curry num2bitsLsbPure_length]
  rw [Vector.toList, Num2Bits.assert_bits_e_wrap, wrap_eq0]
  rw [Num2Bits.reduce₁ Num2Bits.assert_bits_of_num2bits]
  apply Num2Bits.reduce₂
  rw [← h_eq]
  exact (bits2num_of_num2bitsLsbPure_eq h_range).symm

omit inst inst' in
private lemma vector_foldr_eq_finRange_foldr {α β : Type*} {n : ℕ}
    (f : α → β → β) (init : β) (v : Vector α n) :
    v.foldr f init =
      List.foldr (fun i acc ↦ f v[i] acc) init (List.finRange n) := by
  have h : v = Vector.ofFn (fun i ↦ v[i]) := by
    apply Vector.ext; intros i hi; simp
  conv_lhs => rw [h]
  simp only [Vector.foldr, Vector.toArray_ofFn, ← Array.foldr_toList,
             Array.toList_ofFn, List.ofFn_eq_map, List.foldr_map]

lemma range_check_vec_completeness_succ {w k : ℕ} {a b : Vector (Exp p (ZMod p)) k} {c_wg : Wg p} {c_cs : Csₑ p} :
    (∀ (i : Fin k), a[i].eval.val < 2 ^ w) → (∀ i : Fin _, a[i].eval = b[i].eval) →
      (wrap (range_check_vec_wg w a c_wg) (range_check_vec_circuit w b c_cs)).eval = (wrap c_wg c_cs).eval := by
  unfold range_check_vec_wg range_check_vec_circuit
  rw [vector_foldr_eq_finRange_foldr]
  induction k generalizing c_wg c_cs with
  | zero =>
    intros _ _
    simp
  | succ k ih =>
    intros h_range h_eq
    rw [List.finRange_succ]
    simp only [List.foldr_cons, List.foldr_map]
    rw [num2bits_wrap_step (h_range 0) (h_eq 0)]
    have ih' := @ih (Vector.ofFn (fun i : Fin k ↦ a[i.succ]))
                    (Vector.ofFn (fun i : Fin k ↦ b[i.succ])) c_wg c_cs
                    (fun i ↦ by simpa using h_range i.succ)
                    (fun i ↦ by simpa using h_eq i.succ)
    simpa using ih'

/-- Variant of `num2bits_wrap_step_fail` allowing distinct wg/cs expressions
    that agree evaluationally. -/
private lemma num2bits_wrap_step_fail'
    {w : ℕ} {ea eb : Expₑ p} {wg : Wg p} {cs : Csₑ p}
    (h_eq : ea.eval = eb.eval)
    (h_fail : ¬ ea.eval.val < 2 ^ w) :
    (wrap (Num2Bits.num2bits_wg w ea (fun _ ↦ wg))
          (Num2Bits.num2bits_circuit w eb (fun _ ↦ cs))).eval = .n := by
  unfold Num2Bits.num2bits_wg Num2Bits.num2bits_circuit
  rw [foldr_curry num2bitsLsbPure_length]
  rw [Vector.toList, Num2Bits.assert_bits_e_wrap, wrap_eq0]
  rw [Num2Bits.reduce₁ Num2Bits.assert_bits_of_num2bits]
  apply Num2Bits.fail₂
  intro h
  apply h_fail
  rw [← h_eq] at h
  rw [h]
  have := @bits2num_bound p _ _ (num2bitsLsbPure w ea.eval) num2bitsLsbPure_bits
  rw [num2bitsLsbPure_length] at this
  exact this

private lemma num2bits_wrap_step_fail
    {w : ℕ} {ea : Expₑ p} {wg : Wg p} {cs : Csₑ p}
    (h_fail : ¬ ea.eval.val < 2 ^ w) :
    (wrap (Num2Bits.num2bits_wg w ea (fun _ ↦ wg))
          (Num2Bits.num2bits_circuit w ea (fun _ ↦ cs))).eval = .n := by
  unfold Num2Bits.num2bits_wg Num2Bits.num2bits_circuit
  rw [foldr_curry num2bitsLsbPure_length]
  rw [Vector.toList, Num2Bits.assert_bits_e_wrap, wrap_eq0]
  rw [Num2Bits.reduce₁ Num2Bits.assert_bits_of_num2bits]
  apply Num2Bits.fail₂
  intro h
  apply h_fail
  rw [h]
  have := @bits2num_bound p _ _ (num2bitsLsbPure w ea.eval) num2bitsLsbPure_bits
  rw [num2bitsLsbPure_length] at this
  exact this

lemma range_check_vec_completeness_fail {w k : ℕ} {a : Vector (Exp p (ZMod p)) k} {c_wg : Wg p} {c_cs : Csₑ p} :
    ¬ (∀ (i : Fin k), a[i].eval.val < 2 ^ w) →
      (wrap (range_check_vec_wg w a c_wg) (range_check_vec_circuit w a c_cs)).eval = .n := by
  unfold range_check_vec_wg range_check_vec_circuit
  rw [vector_foldr_eq_finRange_foldr]
  induction k generalizing c_wg c_cs with
  | zero =>
    intro h_fail
    exfalso
    exact h_fail (fun i ↦ i.elim0)
  | succ k ih =>
    intro h_fail
    rw [List.finRange_succ]
    simp only [List.foldr_cons, List.foldr_map]
    by_cases h0 : a[0].eval.val < 2 ^ w
    · refine (num2bits_wrap_step (ea := a[0]) (eb := a[0]) h0 rfl).trans ?_
      have ih' := @ih (Vector.ofFn (fun i : Fin k ↦ a[i.succ])) c_wg c_cs
                      (fun h_all ↦ h_fail (fun i ↦ by
                        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
                        · exact h0
                        · simpa using h_all j))
      simpa using ih'
    · exact num2bits_wrap_step_fail (ea := a[0]) h0

omit inst' in
lemma assert_poly_eq_prod_eval_succ {k : ℕ} {a b : Vector (Expₑ p) k} {c : Vector (Expₑ p) (2 * k - 1)} {rest : Cs p (ZMod p)} :
    -- let prod : Vector (Expₑ p) (2 * k - 1) := Vector.ofFn (fun i ↦ (toCompPoly (Vector.map Exp.eval a) * toCompPoly (Vector.map Exp.eval b)).coeff i.1)
    (∀ i, (c.get i).eval = (toCompPoly (Vector.map Exp.eval a) * toCompPoly (Vector.map Exp.eval b)).coeff i.1) →
      (assert_poly_eq_prod a b c rest).eval = rest.eval := by
  intros h_coeff
  have h_eq : toCompPoly (c.map Exp.eval) =
              toCompPoly (a.map Exp.eval) * toCompPoly (b.map Exp.eval) := by
    apply CPolynomial.eq_iff_coeff.mpr
    intro i
    rw [coeff_toCompPoly]
    by_cases h : i < 2 * k - 1
    · rw [dif_pos h]
      have hh := h_coeff ⟨i, h⟩
      simp only [Vector.getElem_map] at hh ⊢
      exact hh
    · rw [dif_neg h]
      push_neg at h
      symm
      rw [CPolynomial.coeff_mul]
      apply Finset.sum_eq_zero
      intros j hj
      rw [Finset.mem_range] at hj
      rw [coeff_toCompPoly, coeff_toCompPoly]
      by_cases hj_k : j < k
      · have hij : ¬ (i - j < k) := by omega
        rw [dif_pos hj_k, dif_neg hij, MulZeroClass.mul_zero]
      · rw [dif_neg hj_k, MulZeroClass.zero_mul]
  unfold assert_poly_eq_prod
  generalize List.range (2 * k - 1) = ls
  induction ls with
  | nil => rfl
  | cons head tail ih =>
    show (Cs.eq0 _ _).eval = rest.eval
    rw [show ∀ e c, (Cs.eq0 e c : Csₑ p).eval = if e.eval = 0 then c.eval else .n from fun _ _ ↦ rfl]
    split_ifs with h_zero
    · exact ih
    · exfalso
      apply h_zero
      simp only [Exp.eval_sub, Exp.eval_mul, sub_eq_zero]
      rw [eval_poly_eval_eq, eval_poly_eval_eq, eval_poly_eval_eq, h_eq]
      rw [eval_toPoly, eval_toPoly, eval_toPoly, toPoly_mul, Polynomial.eval_mul]

omit inst' in
lemma assert_poly_eq_prod_wrap {k : ℕ} {wg : Wg p} {a b : Vector (Expₑ p) k} {c : Vector (Expₑ p) (2 * k - 1)} {rest : Cs p (ZMod p)} :
    wrap wg (assert_poly_eq_prod a b c rest) = assert_poly_eq_prod a b c (wrap wg rest) := by
  unfold FpMul.assert_poly_eq_prod
  generalize List.range (2 * k - 1) = ls
  induction ls with
  | nil => simp
  | cons l ls ih => simpa [wrap] using ih

omit inst' in
private lemma nat2words_val_lt {w : ℕ} :
    ∀ (k n i : ℕ) (h : i < k), ((Circuit.nat2words p w k n)[i]'h).val < 2 ^ w := by
  have hp_pos : 0 < p := (Fact.out (p := Nat.Prime p)).pos
  haveI : NeZero p := ⟨Nat.pos_iff_ne_zero.mp hp_pos⟩
  have h2w : 0 < 2 ^ w := pow_pos (by norm_num) _
  intro k
  induction k with
  | zero => intro _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    intro n i h
    match i, h with
    | 0, _ =>
      have h_zero : (Circuit.nat2words p w (k + 1) n)[0] = ((n % 2 ^ w : ℕ) : ZMod p) :=
        Lean.Grind.Semiring.ofNat_eq_natCast _
      rw [h_zero, ZMod.val_natCast]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ h2w)
    | j + 1, h =>
      have h_succ : (Circuit.nat2words p w (k + 1) n)[j + 1]'h =
          (Circuit.nat2words p w k (n / 2 ^ w))[j]'(by omega) := rfl
      rw [h_succ]
      exact ih (n / 2 ^ w) j (by omega)

omit inst' in
private lemma nat2words_map_c_val_lt {w k : ℕ} (n : ℕ) :
    ∀ i : Fin k, ((Circuit.nat2words p w k n).map Exp.c)[i].eval.val < 2 ^ w := by
  intro i
  rw [show ((Circuit.nat2words p w k n).map Exp.c)[i] =
        Exp.c ((Circuit.nat2words p w k n)[i.1]'i.2) from
      by simp [Fin.getElem_fin]]
  exact nat2words_val_lt k n i.1 i.2

omit inst' in
lemma foldr_eq0_wrap {α : Type} {wg : Wg p} {cs : Csₑ p} {ls : List α} {f : α → Expₑ p} : wrap wg (List.foldr (fun i ↦ Cs.eq0 (f i)) cs ls) = List.foldr (fun i ↦ Cs.eq0 (f i)) (wrap wg cs) ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.foldr_cons]
    rewrite (occs := .pos [1]) [wrap, ih]; rfl

-- example {k w : ℕ} {t : Vector (Expₑ p) k} {wg : Wg p} {cs : Csₑ p} : (wrap (check_carry_zero_wg w t wg) (check_carry_zero_circuit w t cs)).eval = (wrap wg cs).eval := by sorry

-- example {k w : ℕ} {t : Vector (Expₑ p) k} {wg : Wg p} {cs : Csₑ p} : (wrap (check_carry_zero_wg w t wg) (check_carry_zero_circuit w t cs)).eval = .n := by sorry

omit inst' in
private lemma carry_length {w : ℕ} : ∀ (ls : List (ZMod p)) (c : ZMod p),
    (carry w ls c).length = ls.length - 1
  | [], _ => rfl
  | [_], _ => rfl
  | l :: l' :: ls, c => by
    show ((l + c) / (2 ^ w) :: carry w (l' :: ls) ((l + c) / (2 ^ w))).length = _
    rw [List.length_cons, carry_length (l' :: ls) _]
    simp

private lemma zmod_two_ne_zero : (2 : ZMod p) ≠ 0 := by
  intro h
  have hp_gt_2 : p > 2 := inst'.out
  have h_cast : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have h_dvd : (p : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h_cast
  exact absurd (Nat.le_of_dvd (by norm_num) h_dvd) (by omega)

private lemma zmod_two_pow_ne_zero (w : ℕ) : (2 : ZMod p) ^ w ≠ 0 :=
  pow_ne_zero w zmod_two_ne_zero

omit inst' in
/-- `zmod_int_cast` produces an integer whose reduction mod `p` recovers `a`. -/
private lemma zmod_int_cast_cast (offset : ℕ) (a : ZMod p) :
    ((zmod_int_cast offset a : ℤ) : ZMod p) = a := by
  unfold zmod_int_cast
  split_ifs with h
  · push_cast
    exact ZMod.natCast_zmod_val a
  · push_cast
    rw [ZMod.natCast_zmod_val]
    ring

omit inst' in
/-- ZMod-p version of `carry_partial_sum_aux_int`: the honest carries produce
    a partial sum that telescopes to a single carry-scaled term. -/
private lemma carry_partial_sum_aux_zmod {m w : ℕ}
    (t : ℕ → ZMod p) (c : Fin m → ZMod p)
    (heq : ∀ i : Fin m,
        (if i.1 = 0 then t 0 else t i.1 + c ⟨i.1 - 1, by have := i.2; omega⟩)
          = (2 ^ w : ZMod p) * c i)
    (k : ℕ) (hk : k < m) :
    ∑ i ∈ Finset.range (k + 1), t i * (2 ^ w : ZMod p) ^ i =
      c ⟨k, hk⟩ * (2 ^ w : ZMod p) ^ (k + 1) := by
  induction k with
  | zero =>
    rw [Finset.sum_range_one]
    have h := heq ⟨0, hk⟩
    simp only [↓reduceIte] at h
    rw [h]; ring
  | succ k ih =>
    have hk' : k < m := by omega
    rw [Finset.sum_range_succ, ih hk']
    have hcons := heq ⟨k + 1, hk⟩
    have hne : (k + 1 : ℕ) ≠ 0 := by omega
    simp only [hne, ↓reduceIte] at hcons
    have h_idx : (⟨(k + 1) - 1, by omega⟩ : Fin m) = ⟨k, hk'⟩ := by
      apply Fin.ext; simp
    rw [h_idx] at hcons
    have hrw :
        c ⟨k, hk'⟩ * (2 ^ w : ZMod p) ^ (k + 1) +
          t (k + 1) * (2 ^ w : ZMod p) ^ (k + 1) =
          (t (k + 1) + c ⟨k, hk'⟩) * (2 ^ w : ZMod p) ^ (k + 1) := by ring
    rw [hrw, hcons]; ring

omit inst' in
/-- ZMod-p reverse: from the ZMod-p sum being zero and the carry equations,
    derive the base equation. -/
private lemma sum_and_carry_imp_hbase_zmod {n w : ℕ}
    (t : Fin n → ZMod p) (c : Fin (n - 1) → ZMod p)
    (h_n_pos : 0 < n)
    (h_2w_pow_ne : (2 ^ w : ZMod p) ^ (n - 1) ≠ 0)
    (heq : ∀ i : Fin (n - 1),
        (if i.1 = 0 then t ⟨0, h_n_pos⟩
         else t ⟨i.1, by have := i.2; omega⟩ + c ⟨i.1 - 1, by have := i.2; omega⟩)
          = (2 ^ w : ZMod p) * c i)
    (hsum : ∑ i : Fin n, t i * (2 ^ w : ZMod p) ^ i.1 = 0) :
    t ⟨n - 1, by omega⟩ +
      (if h : n = 1 then (0 : ZMod p) else c ⟨n - 2, by omega⟩) = 0 := by
  -- Lift `t` to a total function `t' : ℕ → ZMod p`.
  let t' : ℕ → ZMod p := fun i => if h : i < n then t ⟨i, h⟩ else 0
  have h_conv : ∑ i : Fin n, t i * (2 ^ w : ZMod p) ^ i.1 =
                ∑ i ∈ Finset.range n, t' i * (2 ^ w : ZMod p) ^ i := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => t' j * (2 ^ w : ZMod p) ^ j) n]
    apply Finset.sum_congr rfl
    intro i _
    simp only [t', dif_pos i.2]
  have heq' : ∀ i : Fin (n - 1),
      (if i.1 = 0 then t' 0 else t' i.1 + c ⟨i.1 - 1, by have := i.2; omega⟩)
        = (2 ^ w : ZMod p) * c i := by
    intro i
    have h := heq i
    have hi : i.1 < n := by have := i.2; omega
    by_cases hi0 : i.1 = 0
    · simp only [hi0, ↓reduceIte] at h ⊢
      simp only [t', dif_pos h_n_pos]
      exact h
    · simp only [hi0, ↓reduceIte] at h ⊢
      simp only [t', dif_pos hi]
      exact h
  rw [h_conv] at hsum
  by_cases hn1 : n = 1
  · -- n = 1: sum reduces to t[0], and hbase's else vanishes.
    subst hn1
    simp [dif_pos rfl]
    rw [Finset.sum_range_one] at hsum
    simp at hsum
    have ht0 : t' 0 = t ⟨0, h_n_pos⟩ := by simp [t']
    rw [ht0] at hsum
    exact hsum
  · -- n ≥ 2: telescope + division.
    have h_n_ge_2 : 2 ≤ n := by omega
    rw [show n = (n - 1) + 1 by omega, Finset.sum_range_succ] at hsum
    have hk : n - 2 < n - 1 := by omega
    rw [show (n - 1) = (n - 2) + 1 by omega] at hsum
    rw [carry_partial_sum_aux_zmod t' c heq' (n - 2) hk] at hsum
    have hpow : (n - 2) + 1 = n - 1 := by omega
    rw [hpow] at hsum
    -- hsum : c ⟨n - 2, hk⟩ * (2^w)^(n-1) + t' (n-1) * (2^w)^(n-1) = 0
    have h_factor : (c ⟨n - 2, hk⟩ + t' (n - 1)) * (2 ^ w : ZMod p) ^ (n - 1) = 0 := by
      linear_combination hsum
    have h_sum_zero : c ⟨n - 2, hk⟩ + t' (n - 1) = 0 := by
      rcases mul_eq_zero.mp h_factor with h | h
      · exact h
      · exact absurd h h_2w_pow_ne
    have ht_n1 : t' (n - 1) = t ⟨n - 1, by omega⟩ := by
      simp only [t', dif_pos (show n - 1 < n by omega)]
    rw [ht_n1] at h_sum_zero
    simp only [dif_neg hn1]
    -- goal: t ⟨n - 1, _⟩ + c ⟨n - 2, _⟩ = 0
    -- have: c ⟨n - 2, hk⟩ + t ⟨n - 1, _⟩ = 0
    linear_combination h_sum_zero

/--
  Characterization of `carry`: at index `i`, the honest carry `c[i]` satisfies
  the carry equation `2^w * c[i] = ls[i] + (c[i-1] or the initial c)` in `ZMod p`.
  This is essentially the definition of `carry`, cross-multiplied using
  invertibility of `2^w`.
-/
private lemma carry_get_eq (w : ℕ) :
    ∀ (ls : List (ZMod p)) (c : ZMod p) (i : ℕ)
      (h : i < (carry w ls c).length),
    (2 : ZMod p) ^ w * (carry w ls c)[i]'h =
      ls[i]'(by have := carry_length (w := w) ls c; omega) +
      (if i = 0 then c else (carry w ls c)[i - 1]'(by omega))
  | [], _, _, h => by simp [carry] at h
  | [_], _, _, h => by simp [carry] at h
  | l :: l' :: rest, c, 0, h => by
    show (2 : ZMod p) ^ w * (carry w (l :: l' :: rest) c)[0] = _
    show (2 : ZMod p) ^ w * ((l + c) / (2 ^ w)) = _
    rw [mul_div_cancel₀ _ (zmod_two_pow_ne_zero w)]
    show l + c = (l :: l' :: rest)[0] + (if (0 : ℕ) = 0 then c else _)
    simp
  | l :: l' :: rest, c, i + 1, h => by
    have h_ls_len : (l :: l' :: rest).length = rest.length + 2 := by simp
    have h_carry_step : carry w (l :: l' :: rest) c =
        ((l + c) / (2 ^ w)) :: carry w (l' :: rest) ((l + c) / (2 ^ w)) := rfl
    have h_tail_len : i < (carry w (l' :: rest) ((l + c) / (2 ^ w))).length := by
      have := h
      rw [h_carry_step, List.length_cons] at this
      omega
    -- The following are all definitional equalities from unfolding `carry` and List indexing.
    have h_index_succ : (carry w (l :: l' :: rest) c)[i + 1]'h =
        (carry w (l' :: rest) ((l + c) / (2 ^ w)))[i]'h_tail_len := rfl
    rw [h_index_succ]
    -- Apply IH.
    rw [carry_get_eq w (l' :: rest) ((l + c) / (2 ^ w)) i h_tail_len]
    -- (l :: l' :: rest)[i+1] = (l' :: rest)[i] definitionally.
    have h_ls_get : (l :: l' :: rest)[i + 1]'(by
        have := carry_length (w := w) (l :: l' :: rest) c
        omega) = (l' :: rest)[i]'(by
        have := carry_length (w := w) (l' :: rest) ((l + c) / (2 ^ w))
        omega) := rfl
    rw [h_ls_get]
    congr 1
    by_cases hi : i = 0
    · subst hi
      simp only [if_pos rfl, if_neg (by omega : ¬ (0 + 1 : ℕ) = 0)]
      -- LHS: (l + c) / (2 ^ w)
      -- RHS: (carry w (l :: l' :: rest) c)[0] = (l + c) / 2^w (definitional)
      rfl
    · rw [if_neg hi, if_neg (by omega : ¬ (i + 1 : ℕ) = 0)]
      -- Since carry w (l :: l' :: rest) c = c₀ :: carry w (l' :: rest) c₀ (definitional),
      -- (carry w (l :: l' :: rest) c)[i] = (carry w (l' :: rest) c₀)[i-1] when i ≥ 1.
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      show (carry w (l' :: rest) ((l + c) / (2 ^ w)))[j.succ - 1] =
        (carry w (l :: l' :: rest) c)[j.succ]
      simp only [Nat.succ_sub_one]
      rfl

/--
  Peel-off induction for the wrap of `check_carry_zero_wg` and
  `check_carry_zero_circuit` (after `foldr_curry` has consumed the carries).
  Given honest carries that satisfy the carry equations (`h_heq`), base equation
  (`h_hbase`), and range checks (`h_hrc`), each `Cs.eq0` constraint evaluates to
  zero and each `num2bits_wg`/`num2bits_circuit` pair collapses via
  `num2bits_wrap_step`, reducing to `(wrap wg cs).eval`.

  The wg foldr is re-indexed over `List.finRange (k-1)` (fetching the carry via
  `carries[i]`) so both foldrs share the same processing list, allowing a clean
  induction.
-/
private lemma check_carry_peel_wrap {k w : ℕ}
    (t_cs : Vector (Expₑ p) k) (carries : Vector (ZMod p) (k - 1))
    (wg_end : Wg p) (cs_end : Csₑ p)
    (h_k_pos : 0 < k)
    (h_heq : ∀ i : Fin (k - 1),
        (if i.1 = 0 then (t_cs[i] : Expₑ p).eval
         else (t_cs[i] : Expₑ p).eval +
              carries[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (k - 1))])
          = (2 ^ w : ZMod p) * carries[i])
    (h_hbase : (t_cs[(⟨k - 1, by omega⟩ : Fin k)] : Expₑ p).eval +
        (if h : k = 1 then (0 : ZMod p) else
          carries[(⟨k - 2, by omega⟩ : Fin (k - 1))]) = 0)
    (h_hrc : ∀ i : Fin (k - 1),
        (carries[i] + (2 ^ (w + 1) * (k : ZMod p))).val <
          2 ^ (w + Nat.clog 2 k + 2))
    (lst : List (Fin (k - 1))) :
    (wrap
      (List.foldr (fun (i : Fin (k - 1)) rest =>
        Num2Bits.num2bits_wg (w + Nat.clog 2 k + 2)
          (Exp.c (carries[i] + (2 ^ (w + 1) * (k : ZMod p)))) (fun _ => rest)) wg_end lst)
      (List.foldr (fun (i : Fin (k - 1)) rest =>
        Cs.eq0
          ((if h : i.1 = 0 then (t_cs[i] : Expₑ p)
            else (t_cs[i] : Expₑ p) +
                 (Exp.v carries[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (k - 1))])) -
           (Exp.c (2 ^ w) * Exp.v carries[i]))
          (Num2Bits.num2bits_circuit (w + Nat.clog 2 k + 2)
            (Exp.v carries[i] + Exp.c (2 ^ (w + 1) * (k : ZMod p))) (fun _ => rest)))
        (Cs.eq0 (t_cs[(⟨k - 1, by omega⟩ : Fin k)] +
                (if h : k = 1 then Exp.c 0 else
                  Exp.v carries[(⟨k - 2, by omega⟩ : Fin (k - 1))])) cs_end)
        lst)
    ).eval = (wrap wg_end cs_end).eval := by
  induction lst with
  | nil =>
    show (wrap wg_end (Cs.eq0 _ cs_end)).eval = _
    rw [wrap_eq0]
    show (if _ = _ then _ else _) = _
    have h_base_eval :
        (t_cs[(⟨k - 1, by omega⟩ : Fin k)] +
          (if h : k = 1 then Exp.c 0 else
            Exp.v carries[(⟨k - 2, by omega⟩ : Fin (k - 1))])).eval = 0 := by
      by_cases hk1 : k = 1
      · simp only [dif_pos hk1] at h_hbase ⊢
        show (t_cs[(⟨k - 1, by omega⟩ : Fin k)] : Expₑ p).eval + (0 : ZMod p) = 0
        linear_combination h_hbase
      · simp only [dif_neg hk1] at h_hbase ⊢
        show (t_cs[(⟨k - 1, by omega⟩ : Fin k)] : Expₑ p).eval +
            carries[(⟨k - 2, by omega⟩ : Fin (k - 1))] = 0
        exact h_hbase
    rw [if_pos h_base_eval]
  | cons head tail ih =>
    simp only [List.foldr_cons]
    show (wrap
      (Num2Bits.num2bits_wg _ _ _)
      (Cs.eq0 _ (Num2Bits.num2bits_circuit _ _ _))).eval = _
    rw [wrap_eq0]
    show (if _ = _ then _ else _) = _
    have h_constraint :
        ((if h : head.1 = 0 then (t_cs[head] : Expₑ p)
          else (t_cs[head] : Expₑ p) +
               (Exp.v carries[(⟨head.1 - 1, by have := head.2; omega⟩ : Fin (k - 1))])) -
         (Exp.c (2 ^ w) * Exp.v carries[head])).eval = 0 := by
      have heq_h := h_heq head
      by_cases hhd : head.1 = 0
      · simp only [dif_pos hhd]
        simp only [hhd, ↓reduceIte] at heq_h
        show (t_cs[head] : Expₑ p).eval -
              (2 ^ w : ZMod p) * carries[head] = 0
        linear_combination heq_h
      · simp only [dif_neg hhd]
        simp only [hhd, ↓reduceIte] at heq_h
        show (t_cs[head] : Expₑ p).eval +
              carries[(⟨head.1 - 1, by have := head.2; omega⟩ : Fin (k - 1))] -
              (2 ^ w : ZMod p) * carries[head] = 0
        linear_combination heq_h
    rw [if_pos h_constraint]
    rw [num2bits_wrap_step]
    · exact ih
    · show (carries[head] + (2 ^ (w + 1) * (k : ZMod p))).val <
        2 ^ (w + Nat.clog 2 k + 2)
      exact h_hrc head
    · show carries[head] + (2 ^ (w + 1) * (k : ZMod p)) =
        carries[head] + (2 ^ (w + 1) * (k : ZMod p))
      rfl

/--
  Peel-off induction variant of `check_carry_peel_wrap` for the failure case:
  when some position in `lst` has an out-of-range carry (num2bits fails), the
  whole wrap evaluates to `.n`.
-/
private lemma check_carry_peel_wrap_fail_rc {k w : ℕ}
    (t_cs : Vector (Expₑ p) k) (carries : Vector (ZMod p) (k - 1))
    (wg_end : Wg p) (cs_end : Csₑ p)
    (h_k_pos : 0 < k)
    (h_heq : ∀ i : Fin (k - 1),
        (if i.1 = 0 then (t_cs[i] : Expₑ p).eval
         else (t_cs[i] : Expₑ p).eval +
              carries[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (k - 1))])
          = (2 ^ w : ZMod p) * carries[i])
    (lst : List (Fin (k - 1)))
    (h_fail : ∃ i ∈ lst,
        ¬((carries[i] + (2 ^ (w + 1) * (k : ZMod p))).val <
          2 ^ (w + Nat.clog 2 k + 2))) :
    (wrap
      (List.foldr (fun (i : Fin (k - 1)) rest =>
        Num2Bits.num2bits_wg (w + Nat.clog 2 k + 2)
          (Exp.c (carries[i] + (2 ^ (w + 1) * (k : ZMod p)))) (fun _ => rest)) wg_end lst)
      (List.foldr (fun (i : Fin (k - 1)) rest =>
        Cs.eq0
          ((if h : i.1 = 0 then (t_cs[i] : Expₑ p)
            else (t_cs[i] : Expₑ p) +
                 (Exp.v carries[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (k - 1))])) -
           (Exp.c (2 ^ w) * Exp.v carries[i]))
          (Num2Bits.num2bits_circuit (w + Nat.clog 2 k + 2)
            (Exp.v carries[i] + Exp.c (2 ^ (w + 1) * (k : ZMod p))) (fun _ => rest)))
        (Cs.eq0 (t_cs[(⟨k - 1, by omega⟩ : Fin k)] +
                (if h : k = 1 then Exp.c 0 else
                  Exp.v carries[(⟨k - 2, by omega⟩ : Fin (k - 1))])) cs_end)
        lst)
    ).eval = .n := by
  induction lst with
  | nil =>
    obtain ⟨i, hi, _⟩ := h_fail
    exact absurd hi (List.not_mem_nil)
  | cons head tail ih =>
    simp only [List.foldr_cons]
    show (wrap
      (Num2Bits.num2bits_wg _ _ _)
      (Cs.eq0 _ (Num2Bits.num2bits_circuit _ _ _))).eval = _
    rw [wrap_eq0]
    show (if _ = _ then _ else _) = _
    have h_constraint :
        ((if h : head.1 = 0 then (t_cs[head] : Expₑ p)
          else (t_cs[head] : Expₑ p) +
               (Exp.v carries[(⟨head.1 - 1, by have := head.2; omega⟩ : Fin (k - 1))])) -
         (Exp.c (2 ^ w) * Exp.v carries[head])).eval = 0 := by
      have heq_h := h_heq head
      by_cases hhd : head.1 = 0
      · simp only [dif_pos hhd]
        simp only [hhd, ↓reduceIte] at heq_h
        show (t_cs[head] : Expₑ p).eval -
              (2 ^ w : ZMod p) * carries[head] = 0
        linear_combination heq_h
      · simp only [dif_neg hhd]
        simp only [hhd, ↓reduceIte] at heq_h
        show (t_cs[head] : Expₑ p).eval +
              carries[(⟨head.1 - 1, by have := head.2; omega⟩ : Fin (k - 1))] -
              (2 ^ w : ZMod p) * carries[head] = 0
        linear_combination heq_h
    rw [if_pos h_constraint]
    by_cases h_head_ok : (carries[head] + (2 ^ (w + 1) * (k : ZMod p))).val <
          2 ^ (w + Nat.clog 2 k + 2)
    · -- head passes: advance and continue
      rw [num2bits_wrap_step]
      · apply ih
        obtain ⟨j, hj, hjfail⟩ := h_fail
        rcases List.mem_cons.mp hj with hj_head | hj_tail
        · subst hj_head; exact absurd h_head_ok hjfail
        · exact ⟨j, hj_tail, hjfail⟩
      · show (carries[head] + (2 ^ (w + 1) * (k : ZMod p))).val <
          2 ^ (w + Nat.clog 2 k + 2)
        exact h_head_ok
      · show carries[head] + (2 ^ (w + 1) * (k : ZMod p)) =
          carries[head] + (2 ^ (w + 1) * (k : ZMod p))
        rfl
    · -- head fails: use num2bits_wrap_step_fail'
      exact num2bits_wrap_step_fail'
        (by show (carries[head] + (2 ^ (w + 1) * (k : ZMod p))) =
              carries[head] + (2 ^ (w + 1) * (k : ZMod p)); rfl)
        h_head_ok

/--
  Peel-off induction variant for the case when the final base equation fails
  while all num2bits range checks hold. The walk succeeds through each
  num2bits step (via `h_hrc`) and then the base `.eq0` doesn't fire.
-/
private lemma check_carry_peel_wrap_fail_base {k w : ℕ}
    (t_cs : Vector (Expₑ p) k) (carries : Vector (ZMod p) (k - 1))
    (wg_end : Wg p) (cs_end : Csₑ p)
    (h_k_pos : 0 < k)
    (h_heq : ∀ i : Fin (k - 1),
        (if i.1 = 0 then (t_cs[i] : Expₑ p).eval
         else (t_cs[i] : Expₑ p).eval +
              carries[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (k - 1))])
          = (2 ^ w : ZMod p) * carries[i])
    (h_base_ne : (t_cs[(⟨k - 1, by omega⟩ : Fin k)] : Expₑ p).eval +
        (if h : k = 1 then (0 : ZMod p) else
          carries[(⟨k - 2, by omega⟩ : Fin (k - 1))]) ≠ 0)
    (h_hrc : ∀ i : Fin (k - 1),
        (carries[i] + (2 ^ (w + 1) * (k : ZMod p))).val <
          2 ^ (w + Nat.clog 2 k + 2))
    (lst : List (Fin (k - 1))) :
    (wrap
      (List.foldr (fun (i : Fin (k - 1)) rest =>
        Num2Bits.num2bits_wg (w + Nat.clog 2 k + 2)
          (Exp.c (carries[i] + (2 ^ (w + 1) * (k : ZMod p)))) (fun _ => rest)) wg_end lst)
      (List.foldr (fun (i : Fin (k - 1)) rest =>
        Cs.eq0
          ((if h : i.1 = 0 then (t_cs[i] : Expₑ p)
            else (t_cs[i] : Expₑ p) +
                 (Exp.v carries[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (k - 1))])) -
           (Exp.c (2 ^ w) * Exp.v carries[i]))
          (Num2Bits.num2bits_circuit (w + Nat.clog 2 k + 2)
            (Exp.v carries[i] + Exp.c (2 ^ (w + 1) * (k : ZMod p))) (fun _ => rest)))
        (Cs.eq0 (t_cs[(⟨k - 1, by omega⟩ : Fin k)] +
                (if h : k = 1 then Exp.c 0 else
                  Exp.v carries[(⟨k - 2, by omega⟩ : Fin (k - 1))])) cs_end)
        lst)
    ).eval = .n := by
  induction lst with
  | nil =>
    show (wrap wg_end (Cs.eq0 _ cs_end)).eval = _
    rw [wrap_eq0]
    show (if _ = _ then _ else _) = _
    have h_base_eval :
        (t_cs[(⟨k - 1, by omega⟩ : Fin k)] +
          (if h : k = 1 then Exp.c 0 else
            Exp.v carries[(⟨k - 2, by omega⟩ : Fin (k - 1))])).eval ≠ 0 := by
      by_cases hk1 : k = 1
      · simp only [dif_pos hk1] at h_base_ne ⊢
        show (t_cs[(⟨k - 1, by omega⟩ : Fin k)] : Expₑ p).eval + (0 : ZMod p) ≠ 0
        exact h_base_ne
      · simp only [dif_neg hk1] at h_base_ne ⊢
        show (t_cs[(⟨k - 1, by omega⟩ : Fin k)] : Expₑ p).eval +
            carries[(⟨k - 2, by omega⟩ : Fin (k - 1))] ≠ 0
        exact h_base_ne
    rw [if_neg h_base_eval]
  | cons head tail ih =>
    simp only [List.foldr_cons]
    show (wrap
      (Num2Bits.num2bits_wg _ _ _)
      (Cs.eq0 _ (Num2Bits.num2bits_circuit _ _ _))).eval = _
    rw [wrap_eq0]
    show (if _ = _ then _ else _) = _
    have h_constraint :
        ((if h : head.1 = 0 then (t_cs[head] : Expₑ p)
          else (t_cs[head] : Expₑ p) +
               (Exp.v carries[(⟨head.1 - 1, by have := head.2; omega⟩ : Fin (k - 1))])) -
         (Exp.c (2 ^ w) * Exp.v carries[head])).eval = 0 := by
      have heq_h := h_heq head
      by_cases hhd : head.1 = 0
      · simp only [dif_pos hhd]
        simp only [hhd, ↓reduceIte] at heq_h
        show (t_cs[head] : Expₑ p).eval -
              (2 ^ w : ZMod p) * carries[head] = 0
        linear_combination heq_h
      · simp only [dif_neg hhd]
        simp only [hhd, ↓reduceIte] at heq_h
        show (t_cs[head] : Expₑ p).eval +
              carries[(⟨head.1 - 1, by have := head.2; omega⟩ : Fin (k - 1))] -
              (2 ^ w : ZMod p) * carries[head] = 0
        linear_combination heq_h
    rw [if_pos h_constraint]
    rw [num2bits_wrap_step]
    · exact ih
    · show (carries[head] + (2 ^ (w + 1) * (k : ZMod p))).val <
        2 ^ (w + Nat.clog 2 k + 2)
      exact h_hrc head
    · show carries[head] + (2 ^ (w + 1) * (k : ZMod p)) =
        carries[head] + (2 ^ (w + 1) * (k : ZMod p))
      rfl

set_option maxHeartbeats 1000000000 in
/--
  Failure counterpart of `check_carry_zero_wrap_succ`. When the signed-integer
  interpretation of the `t_wg` coefficients does not sum to zero, the wrap of
  `check_carry_zero_wg` and `check_carry_zero_circuit` evaluates to `.n`.
-/
lemma check_carry_zero_wrap_fail {k w : ℕ} {t_wg t_cs : Vector (Expₑ p) k}
    {wg : Wg p} {cs : Csₑ p} :
  2 ^ (2 * w + Nat.clog 2 k + 4) ≤ p →
  (∀ i : Fin k, t_wg[i].eval = t_cs[i].eval) →
  ∑ i : Fin k, zmod_int_cast (2 ^ (2 * w + Nat.clog 2 k + 3)) t_wg[i].eval * (2 ^ w : ℤ) ^ i.1 ≠ 0 →
    (wrap (check_carry_zero_wg w t_wg wg) (check_carry_zero_circuit w t_cs cs)).eval = .n := by
  intros hp_bound hval_eq hsum_ne
  by_cases hk : k = 0
  · -- k = 0: the sum is empty, so hsum_ne is 0 ≠ 0, contradiction.
    subst hk
    exfalso; apply hsum_ne
    simp
  · have h_k_pos : 0 < k := Nat.pos_of_ne_zero hk
    unfold check_carry_zero_wg check_carry_zero_circuit
    simp only [hk, ↓reduceDIte]
    set carries : List (ZMod p) := carry w (t_wg.toList.map Exp.eval) 0 with h_carries_def
    have h_carries_len : carries.length = k - 1 := by
      rw [h_carries_def, carry_length, List.length_map, Vector.length_toList]
    rw [foldr_curry h_carries_len]
    by_cases hk1 : k = 1
    · -- k = 1: reduce to `.eq0 (t_cs[0] + 0)` and use hsum_ne to derive t_cs[0] ≠ 0.
      subst hk1
      have h_carries_nil : carries = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using h_carries_len)
      -- t_wg[0].eval ≠ 0 from hsum_ne
      have h_t0_wg_ne : (t_wg[0] : Expₑ p).eval ≠ 0 := by
        intro h_zero
        apply hsum_ne
        rw [Fin.sum_univ_one]
        have h_pow : (2 ^ w : ℤ) ^ (0 : Fin 1).1 = 1 := by simp
        rw [h_pow, _root_.mul_one]
        show zmod_int_cast _ (t_wg[0] : Expₑ p).eval = 0
        rw [h_zero]
        simp [zmod_int_cast]
      have h_t0_cs_ne : (t_cs[0] : Expₑ p).eval ≠ 0 :=
        fun h => h_t0_wg_ne ((hval_eq 0).trans h)
      simp only [h_carries_nil, List.foldr_nil]
      show (wrap wg (Cs.eq0 ((t_cs[0] : Expₑ p) + Exp.c 0) cs)).eval = _
      rw [wrap_eq0]
      show (if _ = _ then _ else _) = _
      have h_eval_ne : ((t_cs[0] : Expₑ p) + Exp.c 0).eval ≠ 0 := by
        show (t_cs[0] : Expₑ p).eval + 0 ≠ 0
        rw [_root_.add_zero]
        exact h_t0_cs_ne
      rw [if_neg h_eval_ne]
    · -- k ≥ 2: Since the wg computes honest carries `carries[i] = (t[i] + c_{i-1}) / 2^w`
      -- in ZMod p, all the `eq0` carry equations automatically hold in the wrap.
      -- The wrap can still produce `.n` from one of two sources:
      --   (a) The base equation `t_cs[k-1] + carry[k-2] = 0` fails in ZMod p, or
      --   (b) One of the num2bits checks on `carry[i] + 2^(w+1)*k` fails.
      have h_k_ge_2 : 2 ≤ k := by omega
      set carries_vec : Vector (ZMod p) (k - 1) :=
        ⟨⟨carries⟩, h_carries_len⟩ with h_carries_vec
      -- Convert the wg foldr from list-indexed to Fin-indexed (matches peel helper).
      have h_wg_convert :
          List.foldr (fun c rest => Num2Bits.num2bits_wg (w + Nat.clog 2 k + 2)
              (Exp.c (c + (2 ^ (w + 1) * (k : ZMod p)))) (fun _ => rest)) wg carries =
          List.foldr (fun (i : Fin (k - 1)) rest => Num2Bits.num2bits_wg (w + Nat.clog 2 k + 2)
              (Exp.c (carries_vec[i] + (2 ^ (w + 1) * (k : ZMod p)))) (fun _ => rest))
            wg (List.finRange (k - 1)) := by
        have h_toList : carries_vec.toList = carries := by
          simp [h_carries_vec, Vector.toList]
        rw [← h_toList]
        have h_v_eq : carries_vec = Vector.ofFn (fun i => carries_vec[i]) := by
          apply Vector.ext; intros i hi; simp
        conv_lhs =>
          rw [h_v_eq]
          rw [show (Vector.ofFn (fun i => carries_vec[i])).toList =
                List.ofFn (fun i => carries_vec[i]) from Vector.toList_ofFn]
          rw [List.ofFn_eq_map]
        rw [List.foldr_map]
      rw [h_wg_convert]
      -- The honest carries always satisfy the carry equations in ZMod p.
      have h_heq : ∀ i : Fin (k - 1),
          (if i.1 = 0 then (t_cs[i] : Expₑ p).eval
           else (t_cs[i] : Expₑ p).eval +
                carries_vec[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (k - 1))])
            = (2 ^ w : ZMod p) * carries_vec[i] := by
        intro i
        have h_i_lt_k : i.1 < k := by have := i.2; omega
        have h_i_lt_list : i.1 < (t_wg.toList.map Exp.eval).length := by
          rw [List.length_map, Vector.length_toList]; exact h_i_lt_k
        have h_bd : i.1 < (carry w (t_wg.toList.map Exp.eval) 0).length := by
          rw [carry_length, List.length_map, Vector.length_toList]; have := i.2; omega
        have h_get := carry_get_eq w (t_wg.toList.map Exp.eval) 0 i.1 h_bd
        have h_cv_eq : (carries_vec[i] : ZMod p) =
            (carry w (t_wg.toList.map Exp.eval) 0)[i.1]'h_bd := rfl
        have h_list_eq : (t_wg.toList.map Exp.eval)[i.1]'h_i_lt_list =
            (t_wg[i] : Expₑ p).eval := by
          simp [List.getElem_map, Vector.getElem_toList, Fin.getElem_fin]
        have h_val : (t_wg[i] : Expₑ p).eval = (t_cs[i] : Expₑ p).eval := by
          have := hval_eq ⟨i.1, h_i_lt_k⟩
          exact this
        by_cases hi : i.1 = 0
        · simp only [if_pos hi] at h_get
          rw [h_list_eq, h_val] at h_get
          rw [_root_.add_zero] at h_get
          simp only [if_pos hi]
          rw [h_cv_eq]
          exact h_get.symm
        · simp only [if_neg hi] at h_get
          rw [h_list_eq, h_val] at h_get
          simp only [if_neg hi]
          rw [h_cv_eq]
          have h_prev_eq : (carries_vec[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (k - 1))]
                : ZMod p) =
              (carry w (t_wg.toList.map Exp.eval) 0)[i.1 - 1]'(by
                rw [carry_length]; omega) := rfl
          rw [h_prev_eq]
          exact h_get.symm
      -- Case split: either all num2bits range checks hold, or some fails.
      by_cases h_all_rc : ∀ i : Fin (k - 1),
          (carries_vec[i] + (2 ^ (w + 1) * (k : ZMod p))).val <
            2 ^ (w + Nat.clog 2 k + 2)
      · -- All rc hold: case split on the base equation
        by_cases h_base : ((t_cs[(⟨k - 1, by omega⟩ : Fin k)] : Expₑ p).eval +
            (if _ : k = 1 then (0 : ZMod p) else
              carries_vec[(⟨k - 2, by omega⟩ : Fin (k - 1))])) = 0
        · -- Both hold: contradict hsum_ne by mirroring the soundness derivation.
          exfalso; apply hsum_ne
          -- The setup below is essentially the same as inside
          -- `check_carry_zero_circuit_wrBisim` (lines 771–1026), constructing an
          -- integer lift of the carries + t_pol and applying `carry_eqs_imp_sum_zero_int`.
          set c_off : ℕ := 2 ^ (w + 1) * k with hc_off
          set c_bd : ℕ := 2 ^ (w + Nat.clog 2 k + 2) with hc_bd
          set t_off : ℕ := 2 ^ (2 * w + Nat.clog 2 k + 3) with ht_off
          have h_bounds := check_carry_bounds hp_bound
          have h_2coff_le_cbd : 2 * c_off ≤ c_bd := h_bounds.two_coff_le_cbd
          have h_coff_le_cbd : c_off ≤ c_bd := h_bounds.coff_le_cbd
          have h_cbd_le_toff : c_bd * 2 ≤ t_off := h_bounds.cbd_two_le_toff
          have h_toff_2_le_p : 2 * t_off ≤ p := h_bounds.two_toff_le_p
          have h_toff_le_p : t_off ≤ p := h_bounds.toff_le_p
          have h_cbd_le_p : c_bd ≤ p := h_bounds.cbd_le_p
          have h_cbd_2_le_p : 2 * c_bd ≤ p := h_bounds.two_cbd_le_p
          have h_coff_le_p : c_off ≤ p := h_bounds.coff_le_p
          -- Integer lift of the honest carries.
          let ec : Fin (k - 1) → ℤ := fun i =>
            zmod_int_cast c_bd (carries_vec[i] + (c_off : ZMod p)) - (c_off : ℤ)
          have hec_zmod : ∀ i : Fin (k - 1), ((ec i : ℤ) : ZMod p) = carries_vec[i] ∧
              -(c_off : ℤ) ≤ ec i ∧ ec i < (c_bd : ℤ) - (c_off : ℤ) := by
            intro i
            have hrc_i := h_all_rc i
            have h_off_eq : (2 ^ (w + 1) * (k : ZMod p)) = (c_off : ZMod p) := by
              simp only [hc_off]; push_cast; ring
            rw [h_off_eq] at hrc_i
            have h_aval_lt : (carries_vec[i] + (c_off : ZMod p)).val < c_bd := hrc_i
            have h_cast :
                zmod_int_cast c_bd (carries_vec[i] + (c_off : ZMod p)) =
                  ((carries_vec[i] + (c_off : ZMod p)).val : ℤ) := by
              unfold zmod_int_cast
              rw [if_pos h_aval_lt]
            have h_ec_eq :
                ec i = ((carries_vec[i] + (c_off : ZMod p)).val : ℤ) - (c_off : ℤ) := by
              simp only [ec, h_cast]
            refine ⟨?_, ?_, ?_⟩
            · rw [h_ec_eq]; push_cast; rw [ZMod.natCast_val, ZMod.cast_id]; ring
            · rw [h_ec_eq]
              have : (0 : ℤ) ≤ ((carries_vec[i] + (c_off : ZMod p)).val : ℤ) :=
                Int.natCast_nonneg _
              omega
            · rw [h_ec_eq]
              have : ((carries_vec[i] + (c_off : ZMod p)).val : ℤ) < (c_bd : ℤ) := by
                exact_mod_cast h_aval_lt
              omega
          have hec_zmod_eq : ∀ i, ((ec i : ℤ) : ZMod p) = carries_vec[i] :=
            fun i => (hec_zmod i).1
          have hec_bound : ∀ i, |ec i| < (c_bd : ℤ) := by
            intro i
            have h := hec_zmod i
            have : (c_off : ℤ) ≤ (c_bd : ℤ) := by exact_mod_cast h_coff_le_cbd
            rcases h with ⟨_, h_low, h_up⟩
            rw [abs_lt]
            refine ⟨?_, ?_⟩
            · have : -(c_bd : ℤ) < -(c_off : ℤ) ∨ -(c_bd : ℤ) ≤ -(c_off : ℤ) := by omega
              omega
            · omega
          -- Integer lift of t_cs[i].eval.
          let es : Fin k → ℤ := fun i =>
            if hL : i.1 = k - 1 then
              (if h1 : k = 1 then (0 : ℤ) else -ec ⟨k - 2, by omega⟩)
            else if h0 : i.1 = 0 then
              (2 ^ w : ℤ) * ec ⟨0, by have := i.2; omega⟩
            else
              (2 ^ w : ℤ) * ec ⟨i.1, by have := i.2; omega⟩ -
              ec ⟨i.1 - 1, by have := i.2; omega⟩
          have hes_carry : ∀ i : Fin (k - 1),
              (if i.1 = 0 then es ⟨0, h_k_pos⟩
               else es ⟨i.1, by have := i.2; omega⟩ +
                    ec ⟨i.1 - 1, by have := i.2; omega⟩)
                = (2 ^ w : ℤ) * ec i := by
            intro i
            have h_iL_global : i.1 ≠ k - 1 := by have := i.2; omega
            by_cases hi0 : i.1 = 0
            · simp only [hi0, ↓reduceIte]
              simp only [es]
              have hpos : 0 < k - 1 := lt_of_le_of_lt (Nat.zero_le _) i.2
              have h_0_ne : (0 : ℕ) ≠ k - 1 := by omega
              rw [dif_neg h_0_ne]
              simp only [↓reduceDIte]
              have h_i_eq : i = (⟨0, hpos⟩ : Fin (k - 1)) := Fin.ext hi0
              rw [h_i_eq]
            · simp only [hi0, ↓reduceIte]
              have h_i_lt : i.1 < k - 1 := by have := i.2; omega
              simp only [es]
              rw [dif_neg h_iL_global, dif_neg hi0]
              have : (⟨i.1, by have := i.2; omega⟩ : Fin (k - 1)) = i := Fin.ext rfl
              rw [this]
              ring
          have hes_base : es ⟨k - 1, by omega⟩ +
              (if h : k = 1 then (0 : ℤ) else ec ⟨k - 2, by omega⟩) = 0 := by
            simp only [es]
            simp only [↓reduceDIte]
            by_cases hn1 : k = 1
            · rw [dif_pos hn1, dif_pos hn1]; ring
            · rw [dif_neg hn1, dif_neg hn1]; ring
          -- (es i : ZMod p) = t_cs[i].eval
          have hes_tpol : ∀ i : Fin k, ((es i : ℤ) : ZMod p) = (t_cs[i] : Expₑ p).eval := by
            intro i
            have h_tpol_idx : ∀ j (h : j < k) (heq_ij : j = i.1),
                (t_cs[(⟨j, h⟩ : Fin k)] : Expₑ p).eval = (t_cs[i] : Expₑ p).eval := by
              intros j h heq_ij; congr 2; exact Fin.ext heq_ij
            by_cases hiL : i.1 = k - 1
            · simp only [es, dif_pos hiL]
              by_cases hn1 : k = 1
              · rw [dif_pos hn1]
                have hb := h_base
                rw [dif_pos hn1] at hb
                simp only [_root_.add_zero] at hb
                rw [← h_tpol_idx (k - 1) (by omega) hiL.symm]
                have : (t_cs[(⟨k - 1, by omega⟩ : Fin k)] : Expₑ p).eval = 0 := hb
                rw [this]
                push_cast; rfl
              · rw [dif_neg hn1]
                have hb := h_base
                rw [dif_neg hn1] at hb
                have h_sub : (t_cs[(⟨k - 1, by omega⟩ : Fin k)] : Expₑ p).eval =
                    -carries_vec[(⟨k - 2, by omega⟩ : Fin (k - 1))] := by
                  linear_combination hb
                rw [← h_tpol_idx (k - 1) (by omega) hiL.symm]
                rw [h_sub]
                push_cast
                rw [hec_zmod_eq ⟨k - 2, by omega⟩]
            · by_cases hi0 : i.1 = 0
              · simp only [es, dif_neg hiL, dif_pos hi0]
                have hpos_nm1 : 0 < k - 1 := by omega
                have heq0 := h_heq ⟨0, hpos_nm1⟩
                simp only [↓reduceIte] at heq0
                rw [← h_tpol_idx 0 h_k_pos hi0.symm]
                have h_ti_eq : (t_cs[(⟨0, h_k_pos⟩ : Fin k)] : Expₑ p) =
                    t_cs[(⟨0, hpos_nm1⟩ : Fin (k - 1))] := by
                  simp [Fin.getElem_fin]
                rw [h_ti_eq]
                rw [heq0]
                push_cast
                rw [hec_zmod_eq ⟨0, hpos_nm1⟩]
              · simp only [es, dif_neg hiL, dif_neg hi0]
                have h_iL : i.1 < k - 1 := by have := i.2; omega
                have heq_i := h_heq ⟨i.1, h_iL⟩
                simp only [hi0, ↓reduceIte] at heq_i
                rw [← h_tpol_idx i.1 (by have := i.2; omega) rfl]
                have h_ti_eq : (t_cs[(⟨i.1, by have := i.2; omega⟩ : Fin k)] : Expₑ p) =
                    t_cs[(⟨i.1, h_iL⟩ : Fin (k - 1))] := by
                  simp [Fin.getElem_fin]
                rw [h_ti_eq]
                have h_sub : (t_cs[(⟨i.1, h_iL⟩ : Fin (k - 1))] : Expₑ p).eval =
                    (2 ^ w : ZMod p) * carries_vec[(⟨i.1, h_iL⟩ : Fin (k - 1))] -
                    carries_vec[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (k - 1))] := by
                  linear_combination heq_i
                rw [h_sub]
                push_cast
                rw [hec_zmod_eq, hec_zmod_eq]
          have hes_bound : ∀ i : Fin k, |es i| < (t_off : ℤ) := by
            intro i
            have h_2w_pos : (0 : ℤ) < 2 ^ w := by positivity
            have h_cbd_pos : (0 : ℤ) < (c_bd : ℤ) := by
              have : 0 < c_bd := Nat.pos_of_neZero _
              exact_mod_cast this
            have h_cbd2_le_toff : (2 : ℤ) * c_bd ≤ t_off := by
              have : (2 : ℕ) * c_bd ≤ t_off := by omega
              exact_mod_cast this
            have h_cbd_le_toff_int : (c_bd : ℤ) ≤ t_off := by
              exact_mod_cast (by omega : c_bd ≤ t_off)
            have h_pow_w_cbd_le : (2 ^ w : ℤ) * c_bd ≤ t_off := by
              have h_eq : (2 ^ w : ℤ) * c_bd = (2 ^ (2 * w + Nat.clog 2 k + 2) : ℕ) := by
                simp only [hc_bd]; push_cast; rw [← pow_add]; congr 1; ring
              rw [h_eq]
              have : (2 ^ (2 * w + Nat.clog 2 k + 2) : ℕ) ≤ t_off := by
                simp only [ht_off]
                exact Nat.pow_le_pow_right (by norm_num) (by omega)
              exact_mod_cast this
            by_cases hiL : i.1 = k - 1
            · simp only [es, dif_pos hiL]
              by_cases hn1 : k = 1
              · rw [dif_pos hn1]
                simp only [abs_zero]
                have : 0 < t_off := Nat.pos_of_neZero _
                exact_mod_cast this
              · rw [dif_neg hn1]
                have hb := hec_bound ⟨k - 2, by omega⟩
                rw [abs_neg]
                omega
            · by_cases hi0 : i.1 = 0
              · simp only [es, dif_neg hiL, dif_pos hi0]
                rw [abs_mul]
                have h_pow : |(2 ^ w : ℤ)| = 2 ^ w := abs_of_pos h_2w_pos
                rw [h_pow]
                have hpos : 0 < k - 1 := by omega
                have hb := hec_bound ⟨0, hpos⟩
                have h_mul_lt : (2 ^ w : ℤ) * |ec ⟨0, hpos⟩| < (2 ^ w : ℤ) * c_bd :=
                  Int.mul_lt_mul_of_pos_left hb h_2w_pos
                omega
              · simp only [es, dif_neg hiL, dif_neg hi0]
                have h_iL : i.1 < k - 1 := by have := i.2; omega
                have hb1 := hec_bound ⟨i.1, h_iL⟩
                have hb2 := hec_bound ⟨i.1 - 1, by have := i.2; omega⟩
                have h_pow : |(2 ^ w : ℤ)| = 2 ^ w := abs_of_pos h_2w_pos
                have h_total : |(2 ^ w : ℤ) * ec ⟨i.1, h_iL⟩ -
                    ec ⟨i.1 - 1, by have := i.2; omega⟩| ≤
                    |(2 ^ w : ℤ) * ec ⟨i.1, h_iL⟩| + |ec ⟨i.1 - 1, by have := i.2; omega⟩| :=
                  abs_sub _ _
                rw [abs_mul, h_pow] at h_total
                have h_mul_lt : (2 ^ w : ℤ) * |ec ⟨i.1, h_iL⟩| < (2 ^ w : ℤ) * c_bd :=
                  Int.mul_lt_mul_of_pos_left hb1 h_2w_pos
                have h_2pw1 : (2 ^ w : ℤ) + 1 ≤ 2 ^ (w + 1) := by
                  have : (2 ^ (w + 1) : ℤ) = 2 * 2 ^ w := by ring
                  have h_one_le : (1 : ℤ) ≤ 2 ^ w := by
                    have : (1 : ℕ) ≤ 2 ^ w := Nat.one_le_two_pow
                    exact_mod_cast this
                  linarith
                have h_pow_w1_bd : (2 ^ (w + 1) : ℤ) * c_bd ≤ t_off := by
                  have h_eq : (2 ^ (w + 1) : ℤ) * c_bd = (t_off : ℤ) := by
                    simp only [hc_bd, ht_off]; push_cast; rw [← pow_add]; congr 1; ring
                  rw [h_eq]
                have h_sum_lt : (2 ^ w : ℤ) * c_bd + c_bd ≤ (2 ^ (w + 1) : ℤ) * c_bd := by
                  have : ((2 ^ w : ℤ) + 1) * c_bd ≤ (2 ^ (w + 1) : ℤ) * c_bd :=
                    mul_le_mul_of_nonneg_right h_2pw1 (le_of_lt h_cbd_pos)
                  linarith
                omega
          -- zmod_int_cast t_off t_wg[i].eval = es i
          have h_cast_es : ∀ i : Fin k,
              zmod_int_cast t_off (t_wg[i] : Expₑ p).eval = es i := by
            intro i
            apply zmod_int_cast_eq_of_repr t_off (t_wg[i] : Expₑ p).eval (es i) h_toff_le_p
            · have : (t_off : ℤ) + (t_off : ℤ) = 2 * (t_off : ℤ) := by ring
              rw [this]
              exact_mod_cast h_toff_2_le_p
            · rw [hes_tpol i]; exact (hval_eq i).symm
            · have := hes_bound i
              have := abs_lt.mp this
              omega
            · have := hes_bound i
              have := abs_lt.mp this
              omega
          -- Apply integer telescoping.
          have h_sum_es : ∑ i : Fin k, es i * (2 ^ w : ℤ) ^ i.1 = 0 :=
            carry_eqs_imp_sum_zero_int es ec h_k_pos hes_carry hes_base
          -- Translate back to zmod_int_cast form.
          have h_rewrite : ∑ i : Fin k, zmod_int_cast t_off (t_wg[i] : Expₑ p).eval *
              (2 ^ w : ℤ) ^ i.1 = ∑ i : Fin k, es i * (2 ^ w : ℤ) ^ i.1 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [h_cast_es i]
          rw [h_rewrite, h_sum_es]
        · -- Base fails: use the peel-fail-base helper.
          exact check_carry_peel_wrap_fail_base t_cs carries_vec wg cs h_k_pos h_heq
            h_base h_all_rc (List.finRange (k - 1))
      · -- Some rc fails: apply the peel-fail helper.
        push_neg at h_all_rc
        obtain ⟨j, hj⟩ := h_all_rc
        exact check_carry_peel_wrap_fail_rc t_cs carries_vec wg cs h_k_pos h_heq
          (List.finRange (k - 1))
          ⟨j, List.mem_finRange j, not_lt.mpr hj⟩

set_option maxHeartbeats 1000000000 in
/--
  Failure variant of `check_carry_zero_wrap_fail` when the *range check* on
  some carry fails (rather than the sum being nonzero). Since the failing
  num2bits check produces `.n` at that peel step, the whole wrap = `.n`.
-/
lemma check_carry_zero_wrap_fail_hrc {k w : ℕ} {t_wg t_cs : Vector (Expₑ p) k}
    {wg : Wg p} {cs : Csₑ p} :
  2 ^ (2 * w + Nat.clog 2 k + 4) ≤ p →
  (∀ i : Fin k, t_wg[i].eval = t_cs[i].eval) →
  (∃ (j : Fin (k - 1)) (h : j.1 < (carry w (t_wg.toList.map Exp.eval) 0).length),
      ¬ ((carry w (t_wg.toList.map Exp.eval) 0)[j.1]'h +
          2 ^ (w + 1) * (k : ZMod p)).val <
        2 ^ (w + Nat.clog 2 k + 2)) →
    (wrap (check_carry_zero_wg w t_wg wg) (check_carry_zero_circuit w t_cs cs)).eval = .n := by
  intros hp_bound hval_eq h_hrc_fail
  by_cases hk : k = 0
  · -- k = 0: (k - 1) is 0, so Fin (k-1) is empty and h_hrc_fail is impossible.
    subst hk
    obtain ⟨j, _, _⟩ := h_hrc_fail
    exact absurd j.2 (by simp)
  · have h_k_pos : 0 < k := Nat.pos_of_ne_zero hk
    unfold check_carry_zero_wg check_carry_zero_circuit
    simp only [hk, ↓reduceDIte]
    set carries : List (ZMod p) := carry w (t_wg.toList.map Exp.eval) 0 with h_carries_def
    have h_carries_len : carries.length = k - 1 := by
      rw [h_carries_def, carry_length, List.length_map, Vector.length_toList]
    rw [foldr_curry h_carries_len]
    by_cases hk1 : k = 1
    · -- k = 1: (k - 1) = 0, but h_hrc_fail requires a j : Fin 0, impossible.
      subst hk1
      obtain ⟨j, _, _⟩ := h_hrc_fail
      exact absurd j.2 (by simp)
    · -- k ≥ 2: mirror the "h_all_rc fails" branch from `check_carry_zero_wrap_fail`.
      set carries_vec : Vector (ZMod p) (k - 1) :=
        ⟨⟨carries⟩, h_carries_len⟩ with h_carries_vec
      have h_wg_convert :
          List.foldr (fun c rest => Num2Bits.num2bits_wg (w + Nat.clog 2 k + 2)
              (Exp.c (c + (2 ^ (w + 1) * (k : ZMod p)))) (fun _ => rest)) wg carries =
          List.foldr (fun (i : Fin (k - 1)) rest => Num2Bits.num2bits_wg (w + Nat.clog 2 k + 2)
              (Exp.c (carries_vec[i] + (2 ^ (w + 1) * (k : ZMod p)))) (fun _ => rest))
            wg (List.finRange (k - 1)) := by
        have h_toList : carries_vec.toList = carries := by
          simp [h_carries_vec, Vector.toList]
        rw [← h_toList]
        have h_v_eq : carries_vec = Vector.ofFn (fun i => carries_vec[i]) := by
          apply Vector.ext; intros i hi; simp
        conv_lhs =>
          rw [h_v_eq]
          rw [show (Vector.ofFn (fun i => carries_vec[i])).toList =
                List.ofFn (fun i => carries_vec[i]) from Vector.toList_ofFn]
          rw [List.ofFn_eq_map]
        rw [List.foldr_map]
      rw [h_wg_convert]
      have h_heq : ∀ i : Fin (k - 1),
          (if i.1 = 0 then (t_cs[i] : Expₑ p).eval
           else (t_cs[i] : Expₑ p).eval +
                carries_vec[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (k - 1))])
            = (2 ^ w : ZMod p) * carries_vec[i] := by
        intro i
        have h_i_lt_k : i.1 < k := by have := i.2; omega
        have h_i_lt_list : i.1 < (t_wg.toList.map Exp.eval).length := by
          rw [List.length_map, Vector.length_toList]; exact h_i_lt_k
        have h_bd : i.1 < (carry w (t_wg.toList.map Exp.eval) 0).length := by
          rw [carry_length, List.length_map, Vector.length_toList]; have := i.2; omega
        have h_get := carry_get_eq w (t_wg.toList.map Exp.eval) 0 i.1 h_bd
        have h_cv_eq : (carries_vec[i] : ZMod p) =
            (carry w (t_wg.toList.map Exp.eval) 0)[i.1]'h_bd := rfl
        have h_list_eq : (t_wg.toList.map Exp.eval)[i.1]'h_i_lt_list =
            (t_wg[i] : Expₑ p).eval := by
          simp [List.getElem_map, Vector.getElem_toList, Fin.getElem_fin]
        have h_val : (t_wg[i] : Expₑ p).eval = (t_cs[i] : Expₑ p).eval := by
          have := hval_eq ⟨i.1, h_i_lt_k⟩
          exact this
        by_cases hi : i.1 = 0
        · simp only [if_pos hi] at h_get
          rw [h_list_eq, h_val] at h_get
          rw [_root_.add_zero] at h_get
          simp only [if_pos hi]
          rw [h_cv_eq]
          exact h_get.symm
        · simp only [if_neg hi] at h_get
          rw [h_list_eq, h_val] at h_get
          simp only [if_neg hi]
          rw [h_cv_eq]
          have h_prev_eq : (carries_vec[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (k - 1))]
                : ZMod p) =
              (carry w (t_wg.toList.map Exp.eval) 0)[i.1 - 1]'(by
                rw [carry_length]; omega) := rfl
          rw [h_prev_eq]
          exact h_get.symm
      -- Extract the failing index from h_hrc_fail (in carries form) and pass to peel_fail_rc.
      obtain ⟨j, h_j_bd, h_j_fail⟩ := h_hrc_fail
      have h_j_bd_vec : j.1 < k - 1 := by
        have : j.1 < carries.length := h_j_bd
        rw [h_carries_len] at this; exact this
      have h_carries_vec_eq : carries_vec[j] =
          (carry w (t_wg.toList.map Exp.eval) 0)[j.1]'h_j_bd := rfl
      exact check_carry_peel_wrap_fail_rc t_cs carries_vec wg cs h_k_pos h_heq
        (List.finRange (k - 1))
        ⟨j, List.mem_finRange j, by rw [h_carries_vec_eq]; exact h_j_fail⟩

lemma check_carry_zero_wrap_succ {k w : ℕ} {t_wg t_cs : Vector (Expₑ p) k}
    {wg : Wg p} {cs : Csₑ p} :
  2 ^ (2 * w + Nat.clog 2 k + 4) ≤ p →
  (∀ i : Fin k, t_wg[i].eval = t_cs[i].eval) →
  ∑ i : Fin k, zmod_int_cast (2 ^ (2 * w + Nat.clog 2 k + 3)) t_wg[i].eval * (2 ^ w : ℤ) ^ i.1 = 0 →
  (∀ (i : Fin (k - 1))
    (h : i.1 < (carry w (t_wg.toList.map Exp.eval) 0).length),
    ((carry w (t_wg.toList.map Exp.eval) 0)[i.1]'h +
      2 ^ (w + 1) * (k : ZMod p)).val <
    2 ^ (w + Nat.clog 2 k + 2)) →
    (wrap (check_carry_zero_wg w t_wg wg) (check_carry_zero_circuit w t_cs cs)).eval =
      (wrap wg cs).eval := by
  intros hp_bound hval_eq hsum h_hrc_hyp
  by_cases hk : k = 0
  · subst hk
    have h_toList : t_wg.toList = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [Vector.length_toList]
    have h_wg_eq : check_carry_zero_wg w t_wg wg = wg := by
      unfold check_carry_zero_wg
      simp only [h_toList, List.map_nil]
      show List.foldr _ (List.foldr _ wg (carry w [] 0)) (carry w [] 0) = wg
      rfl
    have h_cs_eq : check_carry_zero_circuit w t_cs cs = cs := by
      unfold check_carry_zero_circuit
      simp
    rw [h_wg_eq, h_cs_eq]
  · -- k ≥ 1: completeness counterpart of `check_carry_zero_circuit_wrBisim`.
    have h_k_pos : 0 < k := Nat.pos_of_ne_zero hk
    unfold check_carry_zero_wg check_carry_zero_circuit
    simp only [hk, ↓reduceDIte]
    set carries : List (ZMod p) := carry w (t_wg.toList.map Exp.eval) 0 with h_carries_def
    have h_carries_len : carries.length = k - 1 := by
      rw [h_carries_def, carry_length, List.length_map, Vector.length_toList]
    -- Consume the k-1 Wg.cons's against Cs.curry (k-1).
    rw [foldr_curry h_carries_len]
    by_cases hk1 : k = 1
    · -- k = 1 case: carries = [], List.finRange 0 = [], only the base Cs.eq0.
      subst hk1
      have h_carries_nil : carries = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using h_carries_len)
      -- Show t_wg[0].eval = 0 from hsum.
      have h_t0_wg : (t_wg[0] : Expₑ p).eval = 0 := by
        have hsum1 : zmod_int_cast (2 ^ (2 * w + Nat.clog 2 1 + 3))
            (t_wg[0] : Expₑ p).eval = 0 := by
          have h := hsum
          rw [Fin.sum_univ_one] at h
          have h_pow : (2 ^ w : ℤ) ^ (0 : Fin 1).1 = 1 := by simp
          rw [h_pow, _root_.mul_one] at h
          exact h
        unfold zmod_int_cast at hsum1
        split_ifs at hsum1 with h_lt
        · have h_val : (t_wg[0] : Expₑ p).eval.val = 0 := by exact_mod_cast hsum1
          exact (ZMod.val_eq_zero _).mp h_val
        · have h_neg_int : ((-(t_wg[0] : Expₑ p).eval).val : ℤ) = 0 := by
            linarith [hsum1]
          have h_val : (-(t_wg[0] : Expₑ p).eval).val = 0 := by
            exact_mod_cast h_neg_int
          have h_neg_zero : -(t_wg[0] : Expₑ p).eval = 0 :=
            (ZMod.val_eq_zero _).mp h_val
          rw [neg_eq_zero] at h_neg_zero
          exact h_neg_zero
      have h_t0_cs : (t_cs[0] : Expₑ p).eval = 0 := (hval_eq 0).symm.trans h_t0_wg
      -- Reduce carries and finRange to empty.
      simp only [h_carries_nil, List.foldr_nil]
      -- Cs.curry 0 f = f #v[], and the if h : 1 = 1 reduces to .c 0.
      show (wrap wg (Cs.eq0 ((t_cs[0] : Expₑ p) + Exp.c 0) cs)).eval = _
      rw [wrap_eq0]
      show (if _ = _ then _ else _) = _
      have h_eval : ((t_cs[0] : Expₑ p) + Exp.c 0).eval = 0 := by
        show (t_cs[0] : Expₑ p).eval + 0 = 0
        rw [h_t0_cs, _root_.add_zero]
      rw [if_pos h_eval]
    · -- k ≥ 2: peel off each carry equation and num2bits pair.
      have h_k_ge_2 : 2 ≤ k := by omega
      -- Package honest carries as a Vector.
      set carries_vec : Vector (ZMod p) (k - 1) :=
        ⟨⟨carries⟩, h_carries_len⟩ with h_carries_vec
      -- Convert the wg foldr from list-indexed to Fin-indexed.
      have h_wg_convert :
          List.foldr (fun c rest => Num2Bits.num2bits_wg (w + Nat.clog 2 k + 2)
              (Exp.c (c + (2 ^ (w + 1) * (k : ZMod p)))) (fun _ => rest)) wg carries =
          List.foldr (fun (i : Fin (k - 1)) rest => Num2Bits.num2bits_wg (w + Nat.clog 2 k + 2)
              (Exp.c (carries_vec[i] + (2 ^ (w + 1) * (k : ZMod p)))) (fun _ => rest))
            wg (List.finRange (k - 1)) := by
        have h_toList : carries_vec.toList = carries := by
          simp [h_carries_vec, Vector.toList]
        rw [← h_toList]
        have h_v_eq : carries_vec = Vector.ofFn (fun i => carries_vec[i]) := by
          apply Vector.ext; intros i hi; simp
        conv_lhs =>
          rw [h_v_eq]
          rw [show (Vector.ofFn (fun i => carries_vec[i])).toList =
                List.ofFn (fun i => carries_vec[i]) from Vector.toList_ofFn]
          rw [List.ofFn_eq_map]
        rw [List.foldr_map]
      -- The honest carries satisfy carry equations, base equation, and range checks.
      have h_heq : ∀ i : Fin (k - 1),
          (if i.1 = 0 then (t_cs[i] : Expₑ p).eval
           else (t_cs[i] : Expₑ p).eval +
                carries_vec[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (k - 1))])
            = (2 ^ w : ZMod p) * carries_vec[i] := by
        intro i
        have h_i_lt_k : i.1 < k := by have := i.2; omega
        have h_i_lt_list : i.1 < (t_wg.toList.map Exp.eval).length := by
          rw [List.length_map, Vector.length_toList]; exact h_i_lt_k
        have h_bd : i.1 < (carry w (t_wg.toList.map Exp.eval) 0).length := by
          rw [carry_length, List.length_map, Vector.length_toList]; have := i.2; omega
        have h_get := carry_get_eq w (t_wg.toList.map Exp.eval) 0 i.1 h_bd
        -- `carries_vec[i] = (carry ...)[i.1]` definitionally
        have h_cv_eq : (carries_vec[i] : ZMod p) =
            (carry w (t_wg.toList.map Exp.eval) 0)[i.1]'h_bd := rfl
        -- `(t_wg.toList.map Exp.eval)[i.1] = Exp.eval t_wg[i]`
        have h_list_eq : (t_wg.toList.map Exp.eval)[i.1]'h_i_lt_list =
            (t_wg[i] : Expₑ p).eval := by
          simp [List.getElem_map, Vector.getElem_toList, Fin.getElem_fin]
        -- hval_eq: Exp.eval t_wg[i] = Exp.eval t_cs[i]
        have h_val : (t_wg[i] : Expₑ p).eval = (t_cs[i] : Expₑ p).eval := by
          have := hval_eq ⟨i.1, h_i_lt_k⟩
          exact this
        by_cases hi : i.1 = 0
        · -- i.1 = 0 case
          simp only [if_pos hi] at h_get
          rw [h_list_eq, h_val] at h_get
          -- h_get : 2^w * (carry ...)[i.1] = t_cs[i].eval + 0
          rw [_root_.add_zero] at h_get
          simp only [if_pos hi]
          -- goal: t_cs[i].eval = 2^w * carries_vec[i]
          rw [h_cv_eq]
          exact h_get.symm
        · -- i.1 ≠ 0 case
          simp only [if_neg hi] at h_get
          rw [h_list_eq, h_val] at h_get
          -- h_get : 2^w * (carry ...)[i.1] = t_cs[i].eval + (carry ...)[i.1 - 1]
          simp only [if_neg hi]
          -- goal: t_cs[i].eval + carries_vec[⟨i.1-1, ⋯⟩] = 2^w * carries_vec[i]
          rw [h_cv_eq]
          -- carries_vec[⟨i.1-1, ⋯⟩] = (carry ...)[i.1 - 1] definitionally
          have h_prev_eq : (carries_vec[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (k - 1))]
                : ZMod p) =
              (carry w (t_wg.toList.map Exp.eval) 0)[i.1 - 1]'(by
                rw [carry_length]; omega) := rfl
          rw [h_prev_eq]
          exact h_get.symm
      have h_hbase : (t_cs[(⟨k - 1, by omega⟩ : Fin k)] : Expₑ p).eval +
          (if h : k = 1 then (0 : ZMod p) else
            carries_vec[(⟨k - 2, by omega⟩ : Fin (k - 1))]) = 0 := by
        -- Define t_fn using Nat-index access to align with h_heq.
        set t_fn : Fin k → ZMod p :=
          fun i => (t_cs[i.val]'i.isLt : Expₑ p).eval with h_t_fn
        set c_fn : Fin (k - 1) → ZMod p := fun i => carries_vec[i] with h_c_fn
        have h_2w_pow_ne : (2 ^ w : ZMod p) ^ (k - 1) ≠ 0 :=
          pow_ne_zero _ (zmod_two_pow_ne_zero w)
        -- Cast hsum from ℤ to ZMod p, aligned with t_fn.
        have h_zmod_sum : ∑ i : Fin k, t_fn i * (2 ^ w : ZMod p) ^ i.1 = 0 := by
          have h_cast : ((∑ i : Fin k, zmod_int_cast (2 ^ (2 * w + Nat.clog 2 k + 3))
                    (Exp.eval t_wg[i]) * (2 ^ w : ℤ) ^ i.1 : ℤ) : ZMod p) = 0 := by
            rw [hsum]; push_cast; rfl
          push_cast at h_cast
          -- h_cast is now: ∑ ((zmod_int_cast … : ℤ) : ZMod p) * (2^w) ^ i.1 = 0
          -- Convert each term via zmod_int_cast_cast + hval_eq.
          rw [show ∑ i : Fin k, t_fn i * (2 ^ w : ZMod p) ^ i.1 =
              ∑ i : Fin k, ((zmod_int_cast (2 ^ (2 * w + Nat.clog 2 k + 3))
                (Exp.eval t_wg[i]) : ℤ) : ZMod p) * (2 ^ w : ZMod p) ^ i.1 from ?_]
          · exact h_cast
          apply Finset.sum_congr rfl
          intro i _
          simp only [h_t_fn]
          rw [zmod_int_cast_cast]
          have h_val := hval_eq i
          simp [Fin.getElem_fin] at h_val
          rw [← h_val]
          simp [Fin.getElem_fin]
        -- Reformulate heq in the required shape.
        have heq' : ∀ i : Fin (k - 1),
            (if i.1 = 0 then t_fn ⟨0, h_k_pos⟩
             else t_fn ⟨i.1, by have := i.2; omega⟩ +
                  c_fn ⟨i.1 - 1, by have := i.2; omega⟩)
              = (2 ^ w : ZMod p) * c_fn i := by
          intro i
          have h := h_heq i
          simp only [h_t_fn, h_c_fn]
          -- Convert t_cs[i] (i : Fin (k-1)) to t_cs[i.val]'proof
          have h_ti_eq : (t_cs[i] : Expₑ p) = t_cs[i.val]'(by have := i.2; omega) := by
            simp [Fin.getElem_fin]
          rw [h_ti_eq] at h
          by_cases hi : i.1 = 0
          · simp only [if_pos hi] at h ⊢
            -- goal: t_cs[0]'h_k_pos.eval = ...; h: t_cs[↑i]'proof.eval = ...
            -- ↑i = 0, so they're equal
            have h_idx_eq : (t_cs[(0 : ℕ)]'h_k_pos : Expₑ p) =
                t_cs[i.val]'(by have := i.2; omega) := by
              congr 1
              exact hi.symm
            rw [h_idx_eq]
            exact h
          · simp only [if_neg hi] at h ⊢
            exact h
        exact sum_and_carry_imp_hbase_zmod t_fn c_fn h_k_pos h_2w_pow_ne heq' h_zmod_sum
      have h_hrc : ∀ i : Fin (k - 1),
          (carries_vec[i] + (2 ^ (w + 1) * (k : ZMod p))).val <
            2 ^ (w + Nat.clog 2 k + 2) := fun i =>
        h_hrc_hyp i (by
          rw [carry_length, List.length_map, Vector.length_toList]
          have := i.2; omega)
      -- Now apply the peel helper.
      rw [h_wg_convert]
      exact check_carry_peel_wrap t_cs carries_vec wg cs h_k_pos h_heq h_hbase h_hrc
        (List.finRange (k - 1))

-- #check check_lt_wg
-- #check check_lt_circuit

omit inst inst' in
/-- Geometric sum bound: `∑_{i<k} c[i] * (2^w)^i < (2^w)^k` when each `c[i] < 2^w`. -/
private lemma tail_bd_geom {w k : ℕ} (h_w_pos : 0 < 2 ^ w) (f : ℕ → ℕ)
    (hf : ∀ i, i < k → f i < 2 ^ w) :
    ∑ i ∈ Finset.range k, f i * (2 ^ w) ^ i < (2 ^ w) ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h_ih : ∑ i ∈ Finset.range n, f i * (2 ^ w) ^ i < (2 ^ w) ^ n :=
      ih (fun i hi => hf i (by omega))
    have h_last : f n * (2 ^ w) ^ n ≤ (2 ^ w - 1) * (2 ^ w) ^ n :=
      Nat.mul_le_mul_right _ (by have := hf n (by omega); omega)
    have h_pow_n_pos : 1 ≤ (2 ^ w) ^ n := Nat.one_le_pow n _ h_w_pos
    have h_pow_succ : (2 ^ w) ^ (n + 1) = 2 ^ w * (2 ^ w) ^ n := by rw [pow_succ]; ring
    have h_sub : (2 ^ w - 1) * (2 ^ w) ^ n = (2 ^ w) * (2 ^ w) ^ n - (2 ^ w) ^ n := by
      rw [Nat.sub_mul, _root_.one_mul]
    have h_pow_2w_ge : (2 ^ w) ^ n ≤ (2 ^ w) * (2 ^ w) ^ n :=
      Nat.le_mul_of_pos_left _ h_w_pos
    omega


set_option maxHeartbeats 800000 in
/--
  Generalized completeness helper for `check_lt'`. Same invariant as
  `check_lt'_wrBisim` (either `isLt = 1`, or `isLt = 0 ∧ sum <`). With the
  `(1 - isLt)` gate on num2bits, no limbwise hypothesis is needed — once
  isLt = 1 the num2bits argument reduces to 0.
-/
private lemma check_lt'_wrap_succ {k w : ℕ}
    {isLt_wg isLt_cs : Expₑ p}
    {t t' p' : Vector (Expₑ p) k}
    {wg : Wg p} {cs : Csₑ p}
    (hp_bound : 2 ^ (w + 1) ≤ p)
    (hr_rc : ∀ i : Fin k, t[i].eval.val < 2 ^ w)
    (h_equiv : ∀ i : Fin k, t[i].eval = t'[i].eval)
    (hp_rc : ∀ i : Fin k, p'[i].eval.val < 2 ^ w)
    (h_isLt : isLt_wg.eval = isLt_cs.eval)
    (h_isLt_bool : isLt_wg.eval = 0 ∨ isLt_wg.eval = 1) :
    (isLt_wg.eval = 1 ∨
      (isLt_wg.eval = 0 ∧
        ∑ i : Fin k, t[i].eval.val * (2 ^ w) ^ i.1 <
          ∑ i : Fin k, p'[i].eval.val * (2 ^ w) ^ i.1)) →
    (wrap (check_lt_wg' w isLt_wg t p' wg)
          (check_lt_circuit' w isLt_cs t' p' cs)).eval = (wrap wg cs).eval := by
  induction k generalizing isLt_wg isLt_cs with
  | zero =>
    intro hcond
    unfold check_lt_wg' check_lt_circuit'
    rw [wrap_eq0]
    show (if (isLt_cs - 1).eval = 0 then _ else _) = _
    rcases hcond with h_isLt_1 | ⟨_, h_lt⟩
    · rw [if_pos]
      show (isLt_cs - 1).eval = 0
      simp only [Exp.eval_sub, Exp.eval_ofNat, Nat.cast_one]
      rw [← h_isLt, h_isLt_1]; ring
    · simp at h_lt
  | succ k ih =>
    intro hcond
    unfold check_lt_wg' check_lt_circuit'
    set a : ℕ := t[Fin.last k].eval.val with ha_def
    set b : ℕ := p'[Fin.last k].eval.val with hb_def
    have ha_rc : a < 2 ^ w := hr_rc (Fin.last k)
    have hb_rc : b < 2 ^ w := hp_rc (Fin.last k)
    have hp_gt_1 : 1 < p := by have := inst'.out; omega
    have h_pow_two_pos : (1 : ℕ) ≤ 2 ^ w := Nat.one_le_two_pow
    have h_2pw_lt_p : 2 ^ w < p := by
      have : 2 ^ w < 2 ^ (w + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have h_pow_cast : ((2 : ZMod p) ^ w) = ((2 ^ w : ℕ) : ZMod p) := by push_cast; ring
    have h_2pw_val : ((2 : ZMod p) ^ w).val = 2 ^ w := by
      rw [h_pow_cast, ZMod.val_natCast_of_lt h_2pw_lt_p]
    have h_one_val : (1 : ZMod p).val = 1 := ZMod.val_one p
    have h_2pw_sub_one_val : ((2 ^ w : ZMod p) - 1).val = 2 ^ w - 1 := by
      rw [ZMod.val_sub]
      · rw [h_2pw_val, h_one_val]
      · rw [h_2pw_val, h_one_val]; exact h_pow_two_pos
    -- MSB comparison when isLt = 0.
    have h_msb_le_of_isLt_zero : isLt_wg.eval = 0 → a ≤ b := by
      intro h_isLt_z
      rcases hcond with h_isLt_1 | ⟨_, h_lt⟩
      · rw [h_isLt_z] at h_isLt_1; exact absurd h_isLt_1 zero_ne_one
      · by_contra h_not_le
        push_neg at h_not_le
        have h_msb_lt : b + 1 ≤ a := h_not_le
        have h_2w_pos : 0 < 2 ^ w := Nat.pos_of_neZero _
        have h_tail_p'_bd : ∑ i : Fin k, p'[i.castSucc].eval.val * (2 ^ w) ^ i.1 <
            (2 ^ w) ^ k :=
          tail_lt_pow_of_range h_2w_pos (fun i => p'[i].eval.val) hp_rc
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at h_lt
        simp only [Fin.val_last, Fin.val_castSucc, ← ha_def, ← hb_def] at h_lt
        have h_msb_gap : a * (2^w)^k ≥ (b + 1) * (2^w)^k :=
          Nat.mul_le_mul_right _ h_msb_lt
        have h_expand : (b + 1) * (2^w)^k = b * (2^w)^k + (2^w)^k := by ring
        rw [h_expand] at h_msb_gap
        have h_tail_t_nn : 0 ≤ ∑ i : Fin k, t[i.castSucc].eval.val * (2 ^ w) ^ i.1 :=
          Nat.zero_le _
        omega
    -- Range bound on num2bits argument.
    have h_num_range : ((1 - isLt_wg) *
        (t[Fin.last k] - p'[Fin.last k] + Exp.c ((2 ^ w : ZMod p) - 1))).eval.val <
        2 ^ w := by
      rcases h_isLt_bool with h_isLt_z | h_isLt_o
      · have h_msb_le := h_msb_le_of_isLt_zero h_isLt_z
        have h_val_expand :
            ((1 - isLt_wg) *
              (t[Fin.last k] - p'[Fin.last k] +
                Exp.c ((2 ^ w : ZMod p) - 1))).eval =
            ((2 ^ w : ZMod p) - 1) - (p'[Fin.last k].eval - t[Fin.last k].eval) := by
          simp only [Exp.eval_mul, Exp.eval_sub, Exp.eval_add, Exp.eval, Exp.eval_ofNat,
                     Nat.cast_one]
          rw [h_isLt_z]; ring
        rw [h_val_expand]
        have h_p'_sub_t_val :
            (p'[Fin.last k].eval - t[Fin.last k].eval).val = b - a :=
          ZMod.val_sub h_msb_le
        have h_le : (p'[Fin.last k].eval - t[Fin.last k].eval).val ≤
            ((2 ^ w : ZMod p) - 1).val := by
          rw [h_p'_sub_t_val, h_2pw_sub_one_val]; omega
        rw [ZMod.val_sub h_le, h_2pw_sub_one_val, h_p'_sub_t_val]
        omega
      · have h_val_zero :
            ((1 - isLt_wg) *
              (t[Fin.last k] - p'[Fin.last k] +
                Exp.c ((2 ^ w : ZMod p) - 1))).eval = 0 := by
          simp only [Exp.eval_mul, Exp.eval_sub, Exp.eval, Exp.eval_ofNat, Nat.cast_one]
          rw [h_isLt_o]; ring
        rw [h_val_zero, ZMod.val_zero]
        exact Nat.pos_of_neZero _
    -- Equality of num2bits arguments (wg vs cs).
    have h_num_eq :
        ((1 - isLt_wg) *
          (t[Fin.last k] - p'[Fin.last k] +
            Exp.c ((2 ^ w : ZMod p) - 1))).eval =
        ((1 - isLt_cs) *
          (t'[Fin.last k] - p'[Fin.last k] +
            Exp.c ((2 ^ w : ZMod p) - 1))).eval := by
      simp only [Exp.eval_mul, Exp.eval_sub, Exp.eval_add, Exp.eval, Exp.eval_ofNat,
                 Nat.cast_one]
      rw [h_isLt, h_equiv (Fin.last k)]
    rw [num2bits_wrap_step h_num_range h_num_eq]
    -- Peel isZero.
    unfold IsZero.isZero_wg IsZero.isZero_circuit
    set e_wg_val : ZMod p := Exp.eval (t[Fin.last k] - p'[Fin.last k]) with he_wg_val
    set o_val : ZMod p := if e_wg_val = 0 then 1 else 0 with ho_val
    show (wrap (Wg.cons _ (Wg.cons _ _))
                (Cs.lam (fun inv => Cs.lam (fun o' => _)))).eval = _
    show (wrap _ (Cs.eq0 _ (Cs.eq0 _ _))).eval = _
    rw [wrap_eq0, wrap_eq0]
    show (if _ = 0 then (if _ = 0 then _ else _) else _) = _
    have h_iz1 :
        ((Exp.c 1 : Expₑ p) - Exp.v e_wg_val⁻¹ *
          (t'[Fin.last k] - p'[Fin.last k]) - Exp.v o_val).eval = 0 := by
      simp only [Exp.eval_sub, Exp.eval_mul, Exp.eval, Exp.eval_ofNat, Nat.cast_one]
      show (1 : ZMod p) - e_wg_val⁻¹ * ((t'[Fin.last k]).eval - (p'[Fin.last k]).eval) -
        o_val = 0
      have h_te : (t'[Fin.last k]).eval - (p'[Fin.last k]).eval = e_wg_val := by
        simp only [he_wg_val, Exp.eval_sub]
        rw [← h_equiv (Fin.last k)]
      rw [h_te]
      simp only [ho_val]
      split_ifs with h_e_zero
      · rw [h_e_zero]; simp
      · have h_inv : e_wg_val⁻¹ * e_wg_val = 1 :=
          ZMod.inv_mul_of_unit _ (isUnit_iff_ne_zero.mpr h_e_zero)
        rw [h_inv]; ring
    have h_iz2 :
        (Exp.v o_val * (t'[Fin.last k] - p'[Fin.last k])).eval = 0 := by
      simp only [Exp.eval_mul, Exp.eval_sub, Exp.eval]
      show o_val * ((t'[Fin.last k]).eval - (p'[Fin.last k]).eval) = 0
      have h_te : (t'[Fin.last k]).eval - (p'[Fin.last k]).eval = e_wg_val := by
        simp only [he_wg_val, Exp.eval_sub]
        rw [← h_equiv (Fin.last k)]
      rw [h_te]
      simp only [ho_val]
      split_ifs with h_e_zero
      · rw [h_e_zero]; ring
      · ring
    rw [if_pos h_iz1, if_pos h_iz2]
    -- Apply IH.
    have h_new_isLt_eq :
        (isLt_wg + ((1 : Expₑ p) - Exp.v o_val) -
          isLt_wg * ((1 : Expₑ p) - Exp.v o_val)).eval =
        (isLt_cs + ((1 : Expₑ p) - Exp.v o_val) -
          isLt_cs * ((1 : Expₑ p) - Exp.v o_val)).eval := by
      simp only [Exp.eval_add, Exp.eval_sub, Exp.eval_mul, Exp.eval, h_isLt]
    have h_new_isLt_bool :
        (isLt_wg + ((1 : Expₑ p) - Exp.v o_val) -
          isLt_wg * ((1 : Expₑ p) - Exp.v o_val)).eval = 0 ∨
        (isLt_wg + ((1 : Expₑ p) - Exp.v o_val) -
          isLt_wg * ((1 : Expₑ p) - Exp.v o_val)).eval = 1 := by
      simp only [Exp.eval_add, Exp.eval_sub, Exp.eval_mul, Exp.eval, Exp.eval_ofNat,
                 Nat.cast_one]
      rcases h_isLt_bool with h_isLt_z | h_isLt_o
      · rw [h_isLt_z]
        simp only [ho_val]
        split_ifs
        · left; ring
        · right; ring
      · rw [h_isLt_o]; right; ring
    -- Derive new invariant.
    have h_new_cond :
        (isLt_wg + ((1 : Expₑ p) - Exp.v o_val) -
          isLt_wg * ((1 : Expₑ p) - Exp.v o_val)).eval = 1 ∨
        ((isLt_wg + ((1 : Expₑ p) - Exp.v o_val) -
          isLt_wg * ((1 : Expₑ p) - Exp.v o_val)).eval = 0 ∧
          ∑ i : Fin k, (Vector.ofFn (fun j : Fin k ↦ t[j.castSucc]))[i].eval.val *
              (2 ^ w) ^ i.1 <
            ∑ i : Fin k, (Vector.ofFn (fun j : Fin k ↦ p'[j.castSucc]))[i].eval.val *
              (2 ^ w) ^ i.1) := by
      have h_lhs_t : ∀ i : Fin k,
          (Vector.ofFn (fun j : Fin k ↦ t[j.castSucc]))[i].eval.val =
            t[i.castSucc].eval.val := fun i => by simp
      have h_lhs_p' : ∀ i : Fin k,
          (Vector.ofFn (fun j : Fin k ↦ p'[j.castSucc]))[i].eval.val =
            p'[i.castSucc].eval.val := fun i => by simp
      rw [show ∑ i : Fin k, (Vector.ofFn (fun j : Fin k ↦ t[j.castSucc]))[i].eval.val *
              (2 ^ w) ^ i.1 =
              ∑ i : Fin k, t[i.castSucc].eval.val * (2 ^ w) ^ i.1 from
        Finset.sum_congr rfl (fun i _ => by rw [h_lhs_t])]
      rw [show ∑ i : Fin k, (Vector.ofFn (fun j : Fin k ↦ p'[j.castSucc]))[i].eval.val *
              (2 ^ w) ^ i.1 =
              ∑ i : Fin k, p'[i.castSucc].eval.val * (2 ^ w) ^ i.1 from
        Finset.sum_congr rfl (fun i _ => by rw [h_lhs_p'])]
      simp only [Exp.eval_add, Exp.eval_sub, Exp.eval_mul, Exp.eval, Exp.eval_ofNat,
                 Nat.cast_one]
      rcases hcond with h_isLt_1 | ⟨h_isLt_0, h_lt⟩
      · left; rw [h_isLt_1]; ring
      · rw [h_isLt_0]
        by_cases h_msb_eq_val : a = b
        · right
          have h_val_inj : t[Fin.last k].eval = p'[Fin.last k].eval :=
            ZMod.val_injective p h_msb_eq_val
          have h_e_zero : e_wg_val = 0 := by
            simp only [he_wg_val, Exp.eval_sub, h_val_inj]; ring
          have h_o_one : o_val = 1 := by simp [ho_val, h_e_zero]
          refine ⟨?_, ?_⟩
          · rw [h_o_one]; ring
          · rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at h_lt
            simp only [Fin.val_last, Fin.val_castSucc, ← ha_def, ← hb_def] at h_lt
            rw [h_msb_eq_val] at h_lt
            omega
        · left
          have h_msb_le := h_msb_le_of_isLt_zero h_isLt_0
          have h_a_lt : a < b := by omega
          have h_e_ne : e_wg_val ≠ 0 := by
            intro h_e_zero
            simp only [he_wg_val, Exp.eval_sub] at h_e_zero
            have h_val_eq : t[Fin.last k].eval.val = p'[Fin.last k].eval.val := by
              rw [sub_eq_zero] at h_e_zero
              rw [h_e_zero]
            omega
          have h_o_zero : o_val = 0 := by simp [ho_val, h_e_ne]
          rw [h_o_zero]; ring
    apply ih (isLt_wg := isLt_wg ||| (1 - Exp.v o_val))
      (isLt_cs := isLt_cs ||| (1 - Exp.v o_val))
      (t := Vector.ofFn (fun j : Fin k ↦ t[j.castSucc]))
      (t' := Vector.ofFn (fun j : Fin k ↦ t'[j.castSucc]))
      (p' := Vector.ofFn (fun j : Fin k ↦ p'[j.castSucc]))
      (fun i => by simp; exact hr_rc i.castSucc)
      (fun i => by simp; exact h_equiv i.castSucc)
      (fun i => by simp; exact hp_rc i.castSucc)
      h_new_isLt_eq h_new_isLt_bool h_new_cond

lemma check_lt_wrap_succ {k w : ℕ} {wg : Wg p} {cs : Csₑ p} {t t' p' :  Vector (Expₑ p) k}
    (hp_bound : 2 ^ (w + 1) ≤ p)
    (hr_rc : ∀ i : Fin k, t[i].eval.val < 2 ^ w)
    (h_equiv : ∀ i : Fin k, t[i].eval = t'[i].eval)
    (hp_rc : ∀ i : Fin k, p'[i].eval.val < 2 ^ w):
  (∑ i : Fin _, t[i].eval.val * (2 ^ w) ^ i.1 < ∑ i : Fin _, p'[i].eval.val * (2 ^ w) ^ i.1) →
    (wrap (check_lt_wg w t p' wg) (check_lt_circuit w t' p' cs)).eval = (wrap wg cs).eval := by
  intro h_lt
  unfold check_lt_wg check_lt_circuit
  apply check_lt'_wrap_succ hp_bound hr_rc h_equiv hp_rc rfl (Or.inl (by simp [Exp.eval]))
  right
  refine ⟨by simp [Exp.eval], h_lt⟩

/--
  Generalized failure helper for `check_lt'` when `p'` is identically zero.
  Given `isLt` starts at 0 and every `p'[i].eval = 0`, the recursion must
  eventually reject: either a num2bits check fails (when some `t[i]` is
  nonzero), or the terminal `.eq0 (isLt - 1)` fires (since isLt stays 0).
-/
private lemma check_lt'_wrap_fail_p_zero {k w : ℕ}
    {isLt_wg isLt_cs : Expₑ p}
    {t t' p' : Vector (Expₑ p) k}
    {wg : Wg p} {cs : Csₑ p}
    (hp_bound : 2 ^ (w + 1) ≤ p)
    (hr_rc : ∀ i : Fin k, t[i].eval.val < 2 ^ w)
    (h_equiv : ∀ i : Fin k, t[i].eval = t'[i].eval)
    (h_p_zero : ∀ i : Fin k, p'[i].eval = 0)
    (h_isLt_eq : isLt_wg.eval = isLt_cs.eval)
    (h_isLt_zero : isLt_wg.eval = 0) :
    (wrap (check_lt_wg' w isLt_wg t p' wg)
          (check_lt_circuit' w isLt_cs t' p' cs)).eval = .n := by
  induction k generalizing isLt_wg isLt_cs with
  | zero =>
    unfold check_lt_wg' check_lt_circuit'
    rw [wrap_eq0]
    show (if (isLt_cs - 1).eval = 0 then _ else _) = denotation.n
    rw [if_neg]
    show ¬ (isLt_cs - 1).eval = 0
    simp only [Exp.eval_sub, Exp.eval_ofNat, Nat.cast_one]
    rw [← h_isLt_eq, h_isLt_zero]
    intro h
    have : (0 : ZMod p) - 1 = -1 := by ring
    rw [this] at h
    have hp_gt : 1 < p := by have := inst'.out; omega
    have h_neg_one : (-1 : ZMod p) ≠ 0 := by
      intro h_eq
      have : (1 : ZMod p) = 0 := by linear_combination -h_eq
      have h_val_one : (1 : ZMod p).val = 1 := ZMod.val_one p
      rw [this] at h_val_one
      simp at h_val_one
    exact h_neg_one h
  | succ k ih =>
    unfold check_lt_wg' check_lt_circuit'
    have hp_gt_1 : 1 < p := by have := inst'.out; omega
    have h_2pw_lt_p : 2 ^ w < p := by
      have : 2 ^ w < 2 ^ (w + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have h_pow_cast : ((2 : ZMod p) ^ w) = ((2 ^ w : ℕ) : ZMod p) := by push_cast; ring
    have h_2pw_val : ((2 : ZMod p) ^ w).val = 2 ^ w := by
      rw [h_pow_cast, ZMod.val_natCast_of_lt h_2pw_lt_p]
    have h_one_val : (1 : ZMod p).val = 1 := ZMod.val_one p
    have h_2pw_sub_one_val : ((2 ^ w : ZMod p) - 1).val = 2 ^ w - 1 := by
      rw [ZMod.val_sub]
      · rw [h_2pw_val, h_one_val]
      · rw [h_2pw_val, h_one_val]; exact Nat.one_le_two_pow
    -- Compute both num2bits arguments' eval and val.
    have h_num_wg_eval :
        ((1 - isLt_wg) *
          (t[Fin.last k] - p'[Fin.last k] +
            Exp.c ((2 ^ w : ZMod p) - 1))).eval =
        (t[Fin.last k]).eval + ((2 ^ w : ZMod p) - 1) := by
      simp only [Exp.eval_mul, Exp.eval_sub, Exp.eval_add, Exp.eval, Exp.eval_ofNat,
                 Nat.cast_one]
      rw [h_isLt_zero, h_p_zero (Fin.last k)]
      ring
    have h_num_eq :
        ((1 - isLt_wg) *
          (t[Fin.last k] - p'[Fin.last k] +
            Exp.c ((2 ^ w : ZMod p) - 1))).eval =
        ((1 - isLt_cs) *
          (t'[Fin.last k] - p'[Fin.last k] +
            Exp.c ((2 ^ w : ZMod p) - 1))).eval := by
      simp only [Exp.eval_mul, Exp.eval_sub, Exp.eval_add, Exp.eval, Exp.eval_ofNat,
                 Nat.cast_one]
      rw [h_isLt_eq, h_equiv (Fin.last k)]
    -- Case-split on whether t[Fin.last k].eval = 0.
    by_cases h_t_zero : (t[Fin.last k] : Expₑ p).eval = 0
    · -- t[last] = 0: num2bits passes with value 2^w - 1. Then iz = 1, isLt' = 0.
      have h_val_lt : ((1 - isLt_wg) *
          (t[Fin.last k] - p'[Fin.last k] +
            Exp.c ((2 ^ w : ZMod p) - 1))).eval.val < 2 ^ w := by
        rw [h_num_wg_eval, h_t_zero, _root_.zero_add, h_2pw_sub_one_val]
        have h_pow_pos : 1 ≤ 2 ^ w := Nat.one_le_two_pow
        omega
      rw [num2bits_wrap_step h_val_lt h_num_eq]
      -- Peel isZero
      unfold IsZero.isZero_wg IsZero.isZero_circuit
      set e_wg_val : ZMod p := Exp.eval (t[Fin.last k] - p'[Fin.last k]) with he_wg_val
      have h_e_zero : e_wg_val = 0 := by
        simp only [he_wg_val, Exp.eval_sub, h_t_zero, h_p_zero (Fin.last k), sub_self]
      set o_val : ZMod p := if e_wg_val = 0 then 1 else 0 with ho_val
      show (wrap (Wg.cons _ (Wg.cons _ _))
                  (Cs.lam (fun inv => Cs.lam (fun o' => _)))).eval = _
      show (wrap _ (Cs.eq0 _ (Cs.eq0 _ _))).eval = _
      rw [wrap_eq0, wrap_eq0]
      show (if _ = 0 then (if _ = 0 then _ else _) else _) = _
      have h_iz1 :
          ((Exp.c 1 : Expₑ p) - Exp.v e_wg_val⁻¹ *
            (t'[Fin.last k] - p'[Fin.last k]) - Exp.v o_val).eval = 0 := by
        simp only [Exp.eval_sub, Exp.eval_mul, Exp.eval, Exp.eval_ofNat, Nat.cast_one]
        show (1 : ZMod p) - e_wg_val⁻¹ * ((t'[Fin.last k]).eval - (p'[Fin.last k]).eval) -
          o_val = 0
        have h_te : (t'[Fin.last k]).eval - (p'[Fin.last k]).eval = e_wg_val := by
          simp only [he_wg_val, Exp.eval_sub]
          rw [← h_equiv (Fin.last k)]
        rw [h_te]
        simp only [ho_val]
        rw [if_pos h_e_zero, h_e_zero]; simp
      have h_iz2 :
          (Exp.v o_val * (t'[Fin.last k] - p'[Fin.last k])).eval = 0 := by
        simp only [Exp.eval_mul, Exp.eval_sub, Exp.eval]
        show o_val * ((t'[Fin.last k]).eval - (p'[Fin.last k]).eval) = 0
        have h_te : (t'[Fin.last k]).eval - (p'[Fin.last k]).eval = e_wg_val := by
          simp only [he_wg_val, Exp.eval_sub]
          rw [← h_equiv (Fin.last k)]
        rw [h_te, h_e_zero]; ring
      rw [if_pos h_iz1, if_pos h_iz2]
      have h_o_one : o_val = 1 := by simp [ho_val, h_e_zero]
      -- Apply IH: isLt' = isLt ||| (1 - o_val) = 0 ||| 0 = 0.
      have h_new_isLt_eq :
          (isLt_wg + ((1 : Expₑ p) - Exp.v o_val) -
            isLt_wg * ((1 : Expₑ p) - Exp.v o_val)).eval =
          (isLt_cs + ((1 : Expₑ p) - Exp.v o_val) -
            isLt_cs * ((1 : Expₑ p) - Exp.v o_val)).eval := by
        simp only [Exp.eval_add, Exp.eval_sub, Exp.eval_mul, Exp.eval, h_isLt_eq]
      have h_new_isLt_zero :
          (isLt_wg + ((1 : Expₑ p) - Exp.v o_val) -
            isLt_wg * ((1 : Expₑ p) - Exp.v o_val)).eval = 0 := by
        simp only [Exp.eval_add, Exp.eval_sub, Exp.eval_mul, Exp.eval, Exp.eval_ofNat,
                   Nat.cast_one]
        rw [h_isLt_zero, h_o_one]; ring
      apply ih (isLt_wg := isLt_wg ||| (1 - Exp.v o_val))
        (isLt_cs := isLt_cs ||| (1 - Exp.v o_val))
        (t := Vector.ofFn (fun j : Fin k ↦ t[j.castSucc]))
        (t' := Vector.ofFn (fun j : Fin k ↦ t'[j.castSucc]))
        (p' := Vector.ofFn (fun j : Fin k ↦ p'[j.castSucc]))
        (fun i => by simp; exact hr_rc i.castSucc)
        (fun i => by simp; exact h_equiv i.castSucc)
        (fun i => by simp; exact h_p_zero i.castSucc)
        h_new_isLt_eq h_new_isLt_zero
    · -- t[last] ≠ 0: num2bits input ≥ 2^w, so num2bits fails.
      have h_val_ge : ¬ ((1 - isLt_wg) *
          (t[Fin.last k] - p'[Fin.last k] +
            Exp.c ((2 ^ w : ZMod p) - 1))).eval.val < 2 ^ w := by
        rw [h_num_wg_eval]
        -- (t[last].eval + (2^w - 1)).val ≥ 2^w since t[last].eval ≠ 0 and < 2^w
        have h_t_val : (t[Fin.last k]).eval.val ≥ 1 := by
          have h_ne : (t[Fin.last k]).eval.val ≠ 0 := fun h0 =>
            h_t_zero ((ZMod.val_eq_zero _).mp h0)
          omega
        have h_t_lt : (t[Fin.last k]).eval.val < 2 ^ w := hr_rc (Fin.last k)
        have h_sum_val :
            ((t[Fin.last k]).eval + ((2 ^ w : ZMod p) - 1)).val =
              (t[Fin.last k]).eval.val + 2 ^ w - 1 := by
          have h_bd : (t[Fin.last k]).eval.val + ((2 ^ w : ZMod p) - 1).val < p := by
            rw [h_2pw_sub_one_val]; omega
          have h_pow_pos : 1 ≤ 2 ^ w := Nat.one_le_two_pow
          rw [ZMod.val_add_of_lt h_bd, h_2pw_sub_one_val]
          omega
        rw [h_sum_val]
        omega
      exact num2bits_wrap_step_fail' h_num_eq h_val_ge

lemma check_lt_wrap_fail_p_zero {k w : ℕ} {wg : Wg p} {cs : Csₑ p}
    {t t' p' : Vector (Expₑ p) k}
    (hp_bound : 2 ^ (w + 1) ≤ p)
    (hr_rc : ∀ i : Fin k, t[i].eval.val < 2 ^ w)
    (h_equiv : ∀ i : Fin k, t[i].eval = t'[i].eval)
    (h_p_zero : ∀ i : Fin k, p'[i].eval = 0) :
    (wrap (check_lt_wg w t p' wg) (check_lt_circuit w t' p' cs)).eval = .n := by
  unfold check_lt_wg check_lt_circuit
  exact check_lt'_wrap_fail_p_zero hp_bound hr_rc h_equiv h_p_zero rfl
    (by simp [Exp.eval])

omit inst' in
lemma eq0_foldr_wrap_succ {α : Type} {ls : List α} {f : α → Expₑ p} {wg : Wg p} {cs : Csₑ p} :
    (∀ i ∈ ls, (f i).eval = 0) →
      (List.foldr (fun i ↦ Cs.eq0 (f i)) (wrap wg cs) ls).eval = (wrap wg cs).eval := by
  intros h
  induction ls with
  | nil => simp
  | cons l ls ih =>
    simp_all only
      [List.foldr_cons, Cs.eval, h l (by simp), ↓reduceIte, List.mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp]

omit inst inst' in
private lemma sum_bound_of_lt {k w : ℕ} (h_w_pos : 0 < 2 ^ w) (v : Fin k → ℕ)
    (hv : ∀ i : Fin k, v i < 2 ^ w) :
    ∑ i : Fin k, v i * (2 ^ w) ^ i.1 < (2 ^ w) ^ k := by
  let f : ℕ → ℕ := fun j => if h : j < k then v ⟨j, h⟩ else 0
  have h_conv :
      ∑ i : Fin k, v i * (2 ^ w) ^ i.1 = ∑ i ∈ Finset.range k, f i * (2 ^ w) ^ i := by
    trans (∑ i : Fin k, f i.val * (2 ^ w) ^ i.val)
    · apply Finset.sum_congr rfl
      intro i _
      have h_i_lt : i.val < k := i.2
      simp only [f, dif_pos h_i_lt]
    · exact Fin.sum_univ_eq_sum_range (fun i => f i * (2 ^ w) ^ i) k
  rw [h_conv]
  apply tail_bd_geom' h_w_pos f
  intro i hi
  show (if h : i < k then v ⟨i, h⟩ else 0) < 2 ^ w
  rw [dif_pos hi]; exact hv ⟨i, hi⟩

set_option maxHeartbeats 1000000000 in
/--
  Polynomial identity for the check_carry sum-to-zero constraint. Given honest
  witnesses `Q = nat2words (a*b / p)` and `R = nat2words (a*b % p)`, the CPolynomial
  `A*B - P*Q - R` evaluates coefficient-wise (through the signed integer window
  via `zmod_int_cast`) to give a sum of zero.

  Preconditions:
   - `p` is bounded: `2 ^ (2*w + Nat.clog 2 (2*k-1) + 4) ≤ p` (so the signed window is valid)
   - Each limb `< 2^w`
   - `0 < p_val` (needed to make `a*b = p*q + r` hold via `Nat.div_add_mod`)
   - `q_num < 2^(w*k)` (so `nat2words` faithfully represents q_num;
     follows from `a_val < p_val` in practice)
-/
private lemma carry_zero_sum_eq_zero {k w : ℕ}
    (_invariant : 2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 4) ≤ p)
    (a b p'_vec : Vector (Exp p (ZMod p)) k)
    (_h_a_rc : ∀ i : Fin k, a[i].eval.val < 2 ^ w)
    (_h_b_rc : ∀ i : Fin k, b[i].eval.val < 2 ^ w)
    (_h_p_rc : ∀ i : Fin k, p'_vec[i].eval.val < 2 ^ w)
    (_h_pval_pos : 0 < ∑ i : Fin k, p'_vec[i].eval.val * (2 ^ w) ^ i.1)
    (_h_q_lt : ((∑ i : Fin k, a[i].eval.val * (2 ^ w) ^ i.1) *
                (∑ i : Fin k, b[i].eval.val * (2 ^ w) ^ i.1)) /
              (∑ i : Fin k, p'_vec[i].eval.val * (2 ^ w) ^ i.1) < 2 ^ (w * k)) :
    ∑ i : Fin (2 * k - 1),
      zmod_int_cast (2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 3))
        (CPolynomial.coeff
          (toCompPoly (a.map Exp.eval) * toCompPoly (b.map Exp.eval)
             - toCompPoly (p'_vec.map Exp.eval) *
                 toCompPoly (Circuit.nat2words p w k
                   (((∑ x : Fin k, a[x].eval.val * (2 ^ w) ^ (x : ℕ)) *
                     (∑ x : Fin k, b[x].eval.val * (2 ^ w) ^ (x : ℕ))) /
                    ∑ x : Fin k, p'_vec[x].eval.val * (2 ^ w) ^ (x : ℕ)))
             - toCompPoly (Circuit.nat2words p w k
                 (((∑ x : Fin k, a[x].eval.val * (2 ^ w) ^ (x : ℕ)) *
                   (∑ x : Fin k, b[x].eval.val * (2 ^ w) ^ (x : ℕ))) %
                  ∑ x : Fin k, p'_vec[x].eval.val * (2 ^ w) ^ (x : ℕ))))
          i.1)
        * (2 ^ w : ℤ) ^ i.1 = 0 := by
  -- Follow the soundness proof structure but in reverse: start from
  -- `a_val * b_val = p_val * q_num + r_num` (via `Nat.div_add_mod`) and
  -- derive that the diff sum is zero.
  set a_val := ∑ i : Fin k, a[i].eval.val * (2 ^ w) ^ i.1 with ha_val
  set b_val := ∑ i : Fin k, b[i].eval.val * (2 ^ w) ^ i.1 with hb_val
  set p_val := ∑ i : Fin k, p'_vec[i].eval.val * (2 ^ w) ^ i.1 with hp_val
  set q_num := (a_val * b_val) / p_val with hq_num
  set r_num := (a_val * b_val) % p_val with hr_num
  set Q_vec : Vector (ZMod p) k := Circuit.nat2words p w k q_num with hQ_vec
  set R_vec : Vector (ZMod p) k := Circuit.nat2words p w k r_num with hR_vec
  set t_poly : CPolynomial (ZMod p) :=
    toCompPoly (a.map Exp.eval) * toCompPoly (b.map Exp.eval)
      - toCompPoly (p'_vec.map Exp.eval) * toCompPoly Q_vec
      - toCompPoly R_vec with ht_poly
  -- The `Nat.div_add_mod` identity is the core arithmetic fact.
  have h_div_mod : a_val * b_val = p_val * q_num + r_num :=
    (Nat.div_add_mod (a_val * b_val) p_val).symm
  -- 2^w < p (used later)
  have hp_gt : 2 ^ w < p := by
    refine lt_of_lt_of_le ?_ _invariant
    apply Nat.pow_lt_pow_right (by decide); omega
  -- Range check on Q_vec, R_vec via nat2words_spec (each digit < 2^w)
  have h_Q_rc : ∀ i : Fin k, Q_vec[i].val < 2 ^ w := fun i => by
    rw [hQ_vec, Circuit.nat2words_spec hp_gt i]
    exact Nat.mod_lt _ (Nat.two_pow_pos w)
  have h_R_rc : ∀ i : Fin k, R_vec[i].val < 2 ^ w := fun i => by
    rw [hR_vec, Circuit.nat2words_spec hp_gt i]
    exact Nat.mod_lt _ (Nat.two_pow_pos w)
  by_cases hk0 : k = 0
  · -- k = 0 case: sum is empty
    subst hk0
    simp
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  have h_2km1_pos : 0 < 2 * k - 1 := by omega
  -- Signed-window setup (mirrors the soundness proof).
  set t_off : ℕ := 2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 3) with ht_off
  have h_pow_succ : t_off ≤ 2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 4) := by
    rw [ht_off]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h_toff_le_p : t_off ≤ p := le_trans h_pow_succ _invariant
  have h_2toff_le_p : 2 * t_off ≤ p := by
    have h_eq : 2 * t_off = 2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 4) := by
      rw [ht_off]; ring
    rw [h_eq]; exact _invariant
  -- Integer lifts.
  let aint : ℕ → ℤ := fun j => if h : j < k then (a[j].eval.val : ℤ) else 0
  let bint : ℕ → ℤ := fun j => if h : j < k then (b[j].eval.val : ℤ) else 0
  let pint : ℕ → ℤ := fun j => if h : j < k then (p'_vec[j].eval.val : ℤ) else 0
  let qint : ℕ → ℤ := fun j => if h : j < k then (Q_vec[j].val : ℤ) else 0
  let rint : ℕ → ℤ := fun j => if h : j < k then (R_vec[j].val : ℤ) else 0
  let diff : ℕ → ℤ := fun n =>
    (∑ j ∈ Finset.range (n + 1), aint j * bint (n - j)) -
    (∑ j ∈ Finset.range (n + 1), pint j * qint (n - j)) -
    rint n
  -- Bounds on each integer lift (each is in [0, 2^w)).
  have h_aint_bound : ∀ j, 0 ≤ aint j ∧ aint j < (2 ^ w : ℤ) := fun j => by
    simp only [aint]; split_ifs with hj
    · exact ⟨Int.natCast_nonneg _, by exact_mod_cast _h_a_rc ⟨j, hj⟩⟩
    · exact ⟨le_refl 0, by positivity⟩
  have h_bint_bound : ∀ j, 0 ≤ bint j ∧ bint j < (2 ^ w : ℤ) := fun j => by
    simp only [bint]; split_ifs with hj
    · exact ⟨Int.natCast_nonneg _, by exact_mod_cast _h_b_rc ⟨j, hj⟩⟩
    · exact ⟨le_refl 0, by positivity⟩
  have h_pint_bound : ∀ j, 0 ≤ pint j ∧ pint j < (2 ^ w : ℤ) := fun j => by
    simp only [pint]; split_ifs with hj
    · exact ⟨Int.natCast_nonneg _, by exact_mod_cast _h_p_rc ⟨j, hj⟩⟩
    · exact ⟨le_refl 0, by positivity⟩
  have h_qint_bound : ∀ j, 0 ≤ qint j ∧ qint j < (2 ^ w : ℤ) := fun j => by
    simp only [qint]; split_ifs with hj
    · exact ⟨Int.natCast_nonneg _, by exact_mod_cast h_Q_rc ⟨j, hj⟩⟩
    · exact ⟨le_refl 0, by positivity⟩
  have h_rint_bound : ∀ j, 0 ≤ rint j ∧ rint j < (2 ^ w : ℤ) := fun j => by
    simp only [rint]; split_ifs with hj
    · exact ⟨Int.natCast_nonneg _, by exact_mod_cast h_R_rc ⟨j, hj⟩⟩
    · exact ⟨le_refl 0, by positivity⟩
  -- Signed-window bound on diff.
  have h_2w_pos : (0 : ℤ) < (2 ^ w : ℤ) := by positivity
  have h_2pw_pow : (2 ^ w : ℤ) * (2 ^ w : ℤ) = (2 ^ (2 * w) : ℤ) := by
    rw [← pow_add]; congr 1; ring
  have h_diff_bound : ∀ n : ℕ, n < 2 * k - 1 →
      -(t_off : ℤ) ≤ diff n ∧ diff n < (t_off : ℤ) := by
    intro n hn
    have h_term_ab : ∀ j, aint j * bint (n - j) ≤ (2 ^ w : ℤ) * (2 ^ w : ℤ) := fun j =>
      mul_le_mul (le_of_lt (h_aint_bound j).2) (le_of_lt (h_bint_bound (n - j)).2)
        (h_bint_bound (n - j)).1 (le_of_lt h_2w_pos)
    have h_term_pq : ∀ j, pint j * qint (n - j) ≤ (2 ^ w : ℤ) * (2 ^ w : ℤ) := fun j =>
      mul_le_mul (le_of_lt (h_pint_bound j).2) (le_of_lt (h_qint_bound (n - j)).2)
        (h_qint_bound (n - j)).1 (le_of_lt h_2w_pos)
    have h_term_ab_nn : ∀ j, 0 ≤ aint j * bint (n - j) := fun j =>
      mul_nonneg (h_aint_bound j).1 (h_bint_bound (n - j)).1
    have h_term_pq_nn : ∀ j, 0 ≤ pint j * qint (n - j) := fun j =>
      mul_nonneg (h_pint_bound j).1 (h_qint_bound (n - j)).1
    have h_ab_sum_nn : 0 ≤ ∑ j ∈ Finset.range (n + 1), aint j * bint (n - j) :=
      Finset.sum_nonneg (fun j _ => h_term_ab_nn j)
    have h_pq_sum_nn : 0 ≤ ∑ j ∈ Finset.range (n + 1), pint j * qint (n - j) :=
      Finset.sum_nonneg (fun j _ => h_term_pq_nn j)
    have h_ab_sum_le : ∑ j ∈ Finset.range (n + 1), aint j * bint (n - j) ≤
        ((n + 1 : ℕ) : ℤ) * ((2 ^ w : ℤ) * (2 ^ w : ℤ)) := by
      calc ∑ j ∈ Finset.range (n + 1), aint j * bint (n - j)
          ≤ ∑ _j ∈ Finset.range (n + 1), (2 ^ w : ℤ) * (2 ^ w : ℤ) :=
            Finset.sum_le_sum (fun j _ => h_term_ab j)
        _ = ((n + 1 : ℕ) : ℤ) * ((2 ^ w : ℤ) * (2 ^ w : ℤ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h_pq_sum_le : ∑ j ∈ Finset.range (n + 1), pint j * qint (n - j) ≤
        ((n + 1 : ℕ) : ℤ) * ((2 ^ w : ℤ) * (2 ^ w : ℤ)) := by
      calc ∑ j ∈ Finset.range (n + 1), pint j * qint (n - j)
          ≤ ∑ _j ∈ Finset.range (n + 1), (2 ^ w : ℤ) * (2 ^ w : ℤ) :=
            Finset.sum_le_sum (fun j _ => h_term_pq j)
        _ = ((n + 1 : ℕ) : ℤ) * ((2 ^ w : ℤ) * (2 ^ w : ℤ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h_rn := h_rint_bound n
    have h_2km1_le_pow : (2 * k - 1 : ℕ) ≤ 2 ^ Nat.clog 2 (2 * k - 1) :=
      Nat.le_pow_clog (b := 2) (by omega) _
    have h_n1_le_pow : (n + 1 : ℕ) ≤ 2 ^ Nat.clog 2 (2 * k - 1) := by omega
    have h_2w_le_22w : (2 ^ w : ℕ) ≤ 2 ^ (2 * w) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h_toff_unfold : (t_off : ℤ) = 8 * (2 ^ (2 * w) : ℤ) * (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) := by
      rw [ht_off]
      push_cast
      rw [show 2 * w + Nat.clog 2 (2 * k - 1) + 3 = 3 + 2 * w + Nat.clog 2 (2 * k - 1) from by ring,
          pow_add, pow_add]
      ring
    have h_n1_le_int : ((n + 1 : ℕ) : ℤ) ≤ (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) := by
      exact_mod_cast h_n1_le_pow
    have h_2w_le_int : (2 ^ w : ℤ) ≤ (2 ^ (2 * w) : ℤ) := by exact_mod_cast h_2w_le_22w
    have h_22w_pos : (0 : ℤ) < (2 ^ (2 * w) : ℤ) := by positivity
    have h_clog_pos : (1 : ℤ) ≤ (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) := by
      have := Nat.one_le_two_pow (n := Nat.clog 2 (2 * k - 1))
      exact_mod_cast this
    have h_prod_pos : (0 : ℤ) <
        (2 ^ (2 * w) : ℤ) * (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) := by
      exact mul_pos h_22w_pos (by linarith)
    have h_key : 2 * ((n + 1 : ℕ) : ℤ) * ((2 ^ w : ℤ) * (2 ^ w : ℤ)) + (2 ^ w : ℤ) <
        (t_off : ℤ) := by
      rw [h_2pw_pow, h_toff_unfold]
      calc 2 * ((n + 1 : ℕ) : ℤ) * (2 ^ (2 * w) : ℤ) + (2 ^ w : ℤ)
          ≤ 2 * (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) * (2 ^ (2 * w) : ℤ) + (2 ^ (2 * w) : ℤ) := by
            have h1 : 2 * ((n + 1 : ℕ) : ℤ) * (2 ^ (2 * w) : ℤ) ≤
                2 * (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) * (2 ^ (2 * w) : ℤ) := by
              have := mul_le_mul_of_nonneg_right h_n1_le_int (le_of_lt h_22w_pos)
              linarith
            linarith
        _ ≤ 2 * (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) * (2 ^ (2 * w) : ℤ) +
              (2 ^ (2 * w) : ℤ) * (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) := by
            have h1 : (2 ^ (2 * w) : ℤ) ≤ (2 ^ (2 * w) : ℤ) * (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) := by
              have := mul_le_mul_of_nonneg_left h_clog_pos (le_of_lt h_22w_pos)
              linarith
            linarith
        _ < 8 * (2 ^ (2 * w) : ℤ) * (2 ^ Nat.clog 2 (2 * k - 1) : ℤ) := by nlinarith [h_prod_pos]
    refine ⟨?_, ?_⟩
    · simp only [diff]
      linarith [h_ab_sum_nn, h_pq_sum_le, h_rn.2, h_rn.1, h_key]
    · simp only [diff]
      linarith [h_ab_sum_le, h_pq_sum_nn, h_rn.2, h_rn.1, h_key]
  -- Coefficient identity: ZMod cast of diff equals t_poly.coeff.
  have h_diff_cast : ∀ n : ℕ, ((diff n : ℤ) : ZMod p) = t_poly.coeff n := by
    intro n
    -- Coefficients of individual toCompPolys
    have h_a_coeff : ∀ j, (toCompPoly (a.map Exp.eval)).coeff j =
        if h : j < k then a[j].eval else 0 := by
      intro j; rw [coeff_toCompPoly]
      split_ifs with h
      · simp [Vector.getElem_map]
      · rfl
    have h_b_coeff : ∀ j, (toCompPoly (b.map Exp.eval)).coeff j =
        if h : j < k then b[j].eval else 0 := by
      intro j; rw [coeff_toCompPoly]
      split_ifs with h
      · simp [Vector.getElem_map]
      · rfl
    have h_p_coeff : ∀ j, (toCompPoly (p'_vec.map Exp.eval)).coeff j =
        if h : j < k then p'_vec[j].eval else 0 := by
      intro j; rw [coeff_toCompPoly]
      split_ifs with h
      · simp [Vector.getElem_map]
      · rfl
    have h_q_coeff : ∀ j, (toCompPoly Q_vec).coeff j =
        if h : j < k then (Q_vec[j] : ZMod p) else 0 := fun j => by
      rw [coeff_toCompPoly]
    have h_r_coeff : ∀ j, (toCompPoly R_vec).coeff j =
        if h : j < k then (R_vec[j] : ZMod p) else 0 := fun j => by
      rw [coeff_toCompPoly]
    -- Expand t_poly.coeff n via coeff_sub and coeff_mul
    have h_t_coeff : t_poly.coeff n =
        (toCompPoly (a.map Exp.eval) * toCompPoly (b.map Exp.eval)).coeff n -
        (toCompPoly (p'_vec.map Exp.eval) * toCompPoly Q_vec).coeff n -
        (toCompPoly R_vec).coeff n := by
      rw [ht_poly, CPolynomial.coeff_sub, CPolynomial.coeff_sub]
    rw [h_t_coeff]
    rw [CPolynomial.coeff_mul, CPolynomial.coeff_mul]
    simp_rw [h_a_coeff, h_b_coeff, h_p_coeff, h_q_coeff, h_r_coeff]
    simp only [diff]
    push_cast
    -- Casts of integer lifts
    have h_aint_cast : ∀ j : ℕ, ((aint j : ℤ) : ZMod p) =
        if h : j < k then a[j].eval else 0 := by
      intro j; simp only [aint]
      split_ifs with h
      · push_cast; rw [ZMod.natCast_zmod_val]
      · simp
    have h_bint_cast : ∀ j : ℕ, ((bint j : ℤ) : ZMod p) =
        if h : j < k then b[j].eval else 0 := by
      intro j; simp only [bint]
      split_ifs with h
      · push_cast; rw [ZMod.natCast_zmod_val]
      · simp
    have h_pint_cast : ∀ j : ℕ, ((pint j : ℤ) : ZMod p) =
        if h : j < k then p'_vec[j].eval else 0 := by
      intro j; simp only [pint]
      split_ifs with h
      · push_cast; rw [ZMod.natCast_zmod_val]
      · simp
    have h_qint_cast : ∀ j : ℕ, ((qint j : ℤ) : ZMod p) =
        if h : j < k then (Q_vec[j] : ZMod p) else 0 := by
      intro j; simp only [qint]
      split_ifs with h
      · push_cast; rw [ZMod.natCast_zmod_val]
      · simp
    have h_rint_cast : ((rint n : ℤ) : ZMod p) =
        if h : n < k then (R_vec[n] : ZMod p) else 0 := by
      simp only [rint]
      split_ifs with h
      · push_cast; rw [ZMod.natCast_zmod_val]
      · simp
    simp_rw [h_aint_cast, h_bint_cast, h_pint_cast, h_qint_cast]
    rw [h_rint_cast]
  -- Bridge zmod_int_cast: for each t_poly.coeff n we have zmod_int_cast = diff n.
  have h_zmod_int_eq : ∀ i : Fin (2 * k - 1),
      zmod_int_cast t_off (t_poly.coeff i.1) = diff i.1 := by
    intro i
    apply zmod_int_cast_eq_of_repr t_off (t_poly.coeff i.1) (diff i.1) h_toff_le_p
    · rw [show ((t_off : ℕ) : ℤ) + ((t_off : ℕ) : ℤ) = ((2 * t_off : ℕ) : ℤ) from by
        push_cast; ring]
      exact_mod_cast h_2toff_le_p
    · convert h_diff_cast i.1
    · exact (h_diff_bound i.1 i.2).1
    · exact (h_diff_bound i.1 i.2).2
  -- The goal reduces to the integer-diff sum being zero.
  have h_diff_sum_zero : ∑ i : Fin (2 * k - 1), diff i.1 * (2 ^ w : ℤ) ^ i.1 = 0 := by
    -- Extend integer sums from range k to range (2*k - 1) for convolution expansion.
    have h_aint_zero : ∀ j, k ≤ j → aint j = 0 := fun j hj => by
      simp only [aint]; rw [dif_neg (by omega)]
    have h_bint_zero : ∀ j, k ≤ j → bint j = 0 := fun j hj => by
      simp only [bint]; rw [dif_neg (by omega)]
    have h_pint_zero : ∀ j, k ≤ j → pint j = 0 := fun j hj => by
      simp only [pint]; rw [dif_neg (by omega)]
    have h_qint_zero : ∀ j, k ≤ j → qint j = 0 := fun j hj => by
      simp only [qint]; rw [dif_neg (by omega)]
    have h_rint_zero : ∀ j, k ≤ j → rint j = 0 := fun j hj => by
      simp only [rint]; rw [dif_neg (by omega)]
    -- Express a_val, b_val, p_val, q_val, r_val as integer sums.
    have h_aval_int : (a_val : ℤ) = ∑ j ∈ Finset.range k, aint j * (2 ^ w : ℤ) ^ j := by
      rw [ha_val]
      push_cast
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intros x _
      show ((a[x].eval.val * (2 ^ w) ^ (x : ℕ) : ℕ) : ℤ) = aint x.1 * (2 ^ w : ℤ) ^ x.1
      simp only [aint]; rw [dif_pos x.2]
      push_cast
      simp only [Fin.getElem_fin]
    have h_bval_int : (b_val : ℤ) = ∑ j ∈ Finset.range k, bint j * (2 ^ w : ℤ) ^ j := by
      rw [hb_val]
      push_cast
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intros x _
      show ((b[x].eval.val * (2 ^ w) ^ (x : ℕ) : ℕ) : ℤ) = bint x.1 * (2 ^ w : ℤ) ^ x.1
      simp only [bint]; rw [dif_pos x.2]
      push_cast
      simp only [Fin.getElem_fin]
    have h_pval_int : (p_val : ℤ) = ∑ j ∈ Finset.range k, pint j * (2 ^ w : ℤ) ^ j := by
      rw [hp_val]
      push_cast
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intros x _
      show ((p'_vec[x].eval.val * (2 ^ w) ^ (x : ℕ) : ℕ) : ℤ) = pint x.1 * (2 ^ w : ℤ) ^ x.1
      simp only [pint]; rw [dif_pos x.2]
      push_cast
      simp only [Fin.getElem_fin]
    have h_qval_int : (q_num : ℤ) = ∑ j ∈ Finset.range k, qint j * (2 ^ w : ℤ) ^ j := by
      -- q_num = ∑ Q_vec[j].val * (2^w)^j via nat2words_spec₁ if q_num < 2^(w*k)
      have h_nat_sum : q_num = ∑ i : Fin k, Q_vec[i].val * (2 ^ w) ^ i.1 := by
        rw [hQ_vec]
        rw [Circuit.nat2words_spec₁ hp_gt]
        rw [Nat.mod_eq_of_lt _h_q_lt]
      rw [h_nat_sum]
      push_cast
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intros x _
      show ((Q_vec[x].val * (2 ^ w) ^ (x : ℕ) : ℕ) : ℤ) = qint x.1 * (2 ^ w : ℤ) ^ x.1
      simp only [qint]; rw [dif_pos x.2]
      push_cast
      simp only [Fin.getElem_fin]
    have h_rval_int : (r_num : ℤ) = ∑ j ∈ Finset.range k, rint j * (2 ^ w : ℤ) ^ j := by
      -- r_num < p_val ≤ 2^(w*k) via nat2words_spec₁
      have h_r_lt : r_num < 2 ^ (w * k) := by
        rw [hr_num]
        refine lt_of_lt_of_le (Nat.mod_lt _ _h_pval_pos) ?_
        rw [hp_val, pow_mul]
        exact le_of_lt
          (sum_bound_of_lt (Nat.pos_of_neZero _) (fun i => p'_vec[i].eval.val) _h_p_rc)
      have h_nat_sum : r_num = ∑ i : Fin k, R_vec[i].val * (2 ^ w) ^ i.1 := by
        rw [hR_vec]
        rw [Circuit.nat2words_spec₁ hp_gt]
        rw [Nat.mod_eq_of_lt h_r_lt]
      rw [h_nat_sum]
      push_cast
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intros x _
      show ((R_vec[x].val * (2 ^ w) ^ (x : ℕ) : ℕ) : ℤ) = rint x.1 * (2 ^ w : ℤ) ^ x.1
      simp only [rint]; rw [dif_pos x.2]
      push_cast
      simp only [Fin.getElem_fin]
    -- Combinatorial expansion of a*b and p*q as convolution sums.
    have h_ab_prod : (a_val : ℤ) * b_val =
        ∑ n ∈ Finset.range (2 * k - 1),
          (∑ j ∈ Finset.range (n + 1), aint j * bint (n - j)) * (2 ^ w : ℤ) ^ n := by
      rw [h_aval_int, h_bval_int]
      exact sum_mul_sum_conv_eq k aint bint (2 ^ w : ℤ) h_aint_zero h_bint_zero hk1
    have h_pq_prod : (p_val : ℤ) * q_num =
        ∑ n ∈ Finset.range (2 * k - 1),
          (∑ j ∈ Finset.range (n + 1), pint j * qint (n - j)) * (2 ^ w : ℤ) ^ n := by
      rw [h_pval_int, h_qval_int]
      exact sum_mul_sum_conv_eq k pint qint (2 ^ w : ℤ) h_pint_zero h_qint_zero hk1
    have h_rval_ext : (r_num : ℤ) =
        ∑ n ∈ Finset.range (2 * k - 1), rint n * (2 ^ w : ℤ) ^ n := by
      rw [h_rval_int]
      apply Finset.sum_subset
      · intros j hj
        rw [Finset.mem_range] at hj ⊢; omega
      · intros j hj hj_not
        rw [Finset.mem_range] at hj hj_not
        push_neg at hj_not
        rw [h_rint_zero j hj_not]; ring
    -- Expand sum in terms of aint, bint, pint, qint, rint
    have h_sum_expand : ∑ i : Fin (2 * k - 1), diff i.1 * (2 ^ w : ℤ) ^ i.1 =
        ((a_val : ℤ) * b_val) - ((p_val : ℤ) * q_num) - (r_num : ℤ) := by
      rw [h_ab_prod, h_pq_prod, h_rval_ext]
      rw [Fin.sum_univ_eq_sum_range (fun i => diff i * (2 ^ w : ℤ) ^ i)]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intros n _
      simp only [diff]
      ring
    rw [h_sum_expand]
    -- Convert h_div_mod to ℤ: a_val*b_val = p_val*q_num + r_num
    have h_div_mod_int : (a_val : ℤ) * b_val = (p_val : ℤ) * q_num + r_num := by
      exact_mod_cast h_div_mod
    linarith
  -- Final: the goal's zmod_int_cast sum equals the diff sum (which is zero).
  calc ∑ i : Fin (2 * k - 1),
        zmod_int_cast t_off (t_poly.coeff i.1) * (2 ^ w : ℤ) ^ i.1
      = ∑ i : Fin (2 * k - 1), diff i.1 * (2 ^ w : ℤ) ^ i.1 := by
        apply Finset.sum_congr rfl
        intros i _
        rw [h_zmod_int_eq i]
    _ = 0 := h_diff_sum_zero

omit inst inst' in
/-- `(v.map Exp.v).map Exp.eval = v` since `Exp.eval ∘ Exp.v = id`. -/
private lemma map_v_map_eval_eq_self {n : ℕ} (v : Vector (ZMod p) n) :
    (v.map Exp.v).map Exp.eval = v := by
  apply Vector.ext
  intro i hi
  simp [Exp.eval]

omit inst inst' in
/-- Constructing a Vector from `f` over `List.range n` yields `f i` at index `i`. -/
private lemma getElem_vec_of_map_range {α : Type} {n : ℕ} (f : ℕ → α) (i : ℕ) (hi : i < n) :
    (Vector.mk (List.map f (List.range n)).toArray
        (by simp)
      : Vector α n)[i]'hi = f i := by
  show ((List.map f (List.range n)).toArray)[i]'(by simp; exact hi) = f i
  simp [List.getElem_map, List.getElem_range]

omit inst inst' in
/-- `(Vector.mk (List.map (Exp.v ∘ f) L).toArray _).map Exp.eval` reduces to
    `Vector.mk (List.map f L).toArray _`. -/
private lemma map_eval_of_map_v_comp {α : Type} (f : α → ZMod p) (L : List α) :
    (Vector.mk (List.map ((Exp.v : ZMod p → Exp p (ZMod p)) ∘ f) L).toArray (by simp)
      : Vector (Exp p (ZMod p)) L.length).map Exp.eval =
      (Vector.mk (List.map f L).toArray (by simp) : Vector (ZMod p) L.length) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  show Exp.eval ((List.map ((Exp.v : ZMod p → Exp p (ZMod p)) ∘ f) L).toArray[i]'
                  (by simpa using hi)) =
    (List.map f L).toArray[i]'(by simpa using hi)
  simp [List.getElem_map, Exp.eval]

omit inst' in
/-- `toCompPoly` reconstructs a polynomial from its first `n` coefficients
    if the polynomial's degree is `< n`. -/
private lemma toCompPoly_of_range_coeff {n : ℕ} (poly : CPolynomial (ZMod p))
    (h_deg : poly.degree < (n : WithBot ℕ)) :
    toCompPoly (Vector.mk (List.map poly.coeff (List.range n)).toArray (by simp)
                : Vector _ n) = poly := by
  apply CPolynomial.eq_iff_coeff.mpr
  intro i
  rw [coeff_toCompPoly]
  by_cases h_i : i < n
  · rw [dif_pos h_i]
    exact getElem_vec_of_map_range poly.coeff i h_i
  · rw [dif_neg h_i]
    push_neg at h_i
    symm
    exact (CPolynomial.degree_lt_iff_coeff_zero poly n).mp h_deg i h_i

set_option maxHeartbeats 1000000000 in
/--
  The polynomial identity `A*B - P*Q - R = 0` (evaluated at index `i`) that
  the wg's honest witnesses satisfy. Shared between the positive branch of
  `fpmul_completeness` and `p_zero_finish` — extracted to reduce compile time.
-/
private lemma fpmul_poly_identity_at {k w : ℕ}
    (a b p' : Vector (Exp p (ZMod p)) k) (i : ZMod p) :
    let A : CPolynomial (ZMod p) := toCompPoly (a.map Exp.eval)
    let B : CPolynomial (ZMod p) := toCompPoly (b.map Exp.eval)
    let P : CPolynomial (ZMod p) := toCompPoly (p'.map Exp.eval)
    let q_num : ℕ := (∑ x : Fin k, a[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) *
                     (∑ x : Fin k, b[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) /
                     ∑ x : Fin k, p'[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)
    let r_num : ℕ := (∑ x : Fin k, a[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) *
                     (∑ x : Fin k, b[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) %
                     ∑ x : Fin k, p'[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)
    let Q : CPolynomial (ZMod p) := toCompPoly (Circuit.nat2words p w k q_num)
    let R : CPolynomial (ZMod p) := toCompPoly (Circuit.nat2words p w k r_num)
    (eval_poly
        (Vector.mk (List.map (Exp.v ∘ (A * B - P * Q - R).coeff)
          (List.range (2 * k - 1))).toArray
          (by simp) : Vector (Expₑ p) (2 * k - 1)) i -
      (eval_poly
          (Vector.mk (List.map (Exp.v ∘ fun j : Fin (2 * k - 1) =>
              ((A * B).val)[j.1]?.getD 0)
            (List.finRange (2 * k - 1))).toArray
            (by simp) : Vector (Expₑ p) (2 * k - 1)) i -
        (eval_poly p' i *
            eval_poly (Vector.map Exp.v (Circuit.nat2words p w k q_num)) i +
          eval_poly (Vector.map Exp.v (Circuit.nat2words p w k r_num)) i))).eval = 0 := by
  set A : CPolynomial (ZMod p) := toCompPoly (a.map Exp.eval) with hA
  set B : CPolynomial (ZMod p) := toCompPoly (b.map Exp.eval) with hB
  set P : CPolynomial (ZMod p) := toCompPoly (p'.map Exp.eval) with hP
  set q_num : ℕ := (∑ x : Fin k, a[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) *
                   (∑ x : Fin k, b[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) /
                   ∑ x : Fin k, p'[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)
  set r_num : ℕ := (∑ x : Fin k, a[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) *
                   (∑ x : Fin k, b[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) %
                   ∑ x : Fin k, p'[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)
  set Q : CPolynomial (ZMod p) := toCompPoly (Circuit.nat2words p w k q_num) with hQ
  set R : CPolynomial (ZMod p) := toCompPoly (Circuit.nat2words p w k r_num) with hR
  simp only [Exp.eval_sub, Exp.eval_add, Exp.eval_mul, sub_eq_zero]
  rw [eval_poly_eval_eq, eval_poly_eval_eq, eval_poly_eval_eq,
      eval_poly_eval_eq, eval_poly_eval_eq]
  rw [map_v_map_eval_eq_self, map_v_map_eval_eq_self]
  have h_deg_R : R.degree < ((2 * k - 1 : ℕ) : WithBot ℕ) := by
    refine lt_of_lt_of_le (toCompPoly_degree_lt _) ?_
    norm_cast; omega
  have h_deg_AB : (A * B).degree < ((2 * k - 1 : ℕ) : WithBot ℕ) :=
    toCompPoly_mul_degree_lt (a.map Exp.eval) (b.map Exp.eval)
  have h_deg_PQ : (P * Q).degree < ((2 * k - 1 : ℕ) : WithBot ℕ) :=
    toCompPoly_mul_degree_lt (p'.map Exp.eval) (Circuit.nat2words p w k q_num)
  have h_deg_t : (A * B - P * Q - R).degree < ((2 * k - 1 : ℕ) : WithBot ℕ) := by
    rw [CPolynomial.degree_lt_iff_coeff_zero]
    intro j hj
    rw [CPolynomial.coeff_sub, CPolynomial.coeff_sub]
    rw [(CPolynomial.degree_lt_iff_coeff_zero _ _).mp h_deg_AB j hj]
    rw [(CPolynomial.degree_lt_iff_coeff_zero _ _).mp h_deg_PQ j hj]
    rw [(CPolynomial.degree_lt_iff_coeff_zero _ _).mp h_deg_R j hj]
    ring
  have h_t_eq :
      toCompPoly
          ((Vector.map Exp.eval
            (Vector.mk
              (List.map (Exp.v ∘ (A * B - P * Q - R).coeff)
                (List.range (2 * k - 1))).toArray
              (by simp) : Vector (Exp p (ZMod p)) (2 * k - 1)))
          : Vector (ZMod p) (2 * k - 1)) =
        (A * B - P * Q - R : CPolynomial (ZMod p)) := by
    apply CPolynomial.eq_iff_coeff.mpr
    intro j
    rw [coeff_toCompPoly]
    by_cases h_j : j < 2 * k - 1
    · rw [dif_pos h_j]
      simp only [Vector.getElem_map]
      show Exp.eval ((List.map (Exp.v ∘ (A * B - P * Q - R).coeff)
          (List.range (2 * k - 1))).toArray[j]'(by simp; exact h_j)) =
        (A * B - P * Q - R).coeff j
      rw [List.getElem_toArray, List.getElem_map, List.getElem_range]
      simp [Exp.eval]
    · rw [dif_neg h_j]
      push_neg at h_j
      symm
      exact (CPolynomial.degree_lt_iff_coeff_zero _ _).mp h_deg_t j h_j
  have h_ab_eq :
      toCompPoly
          ((Vector.map Exp.eval
            (Vector.mk
              (List.map (Exp.v ∘ fun j : Fin (2 * k - 1) =>
                  ((A * B).val)[j.1]?.getD 0)
                (List.finRange (2 * k - 1))).toArray
              (by simp) : Vector (Exp p (ZMod p)) (2 * k - 1)))
          : Vector (ZMod p) (2 * k - 1)) =
        (A * B : CPolynomial (ZMod p)) := by
    apply CPolynomial.eq_iff_coeff.mpr
    intro j
    rw [coeff_toCompPoly]
    by_cases h_j : j < 2 * k - 1
    · rw [dif_pos h_j]
      simp only [Vector.getElem_map]
      show Exp.eval ((List.map _ (List.finRange (2 * k - 1))).toArray[j]'
          (by simp; exact h_j)) = (A * B).coeff j
      rw [List.getElem_toArray, List.getElem_map, List.getElem_finRange]
      show ((A * B).val)[j]?.getD 0 = (A * B).coeff j
      rw [CPolynomial.coeff, CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?]
    · rw [dif_neg h_j]
      push_neg at h_j
      symm
      exact (CPolynomial.degree_lt_iff_coeff_zero _ (2 * k - 1)).mp h_deg_AB j h_j
  rw [h_t_eq, h_ab_eq]
  rw [cpoly_eval_sub, cpoly_eval_sub, cpoly_eval_mul, cpoly_eval_mul]
  rw [← hP, ← hQ, ← hR]
  ring

set_option maxHeartbeats 1000000000 in
/--
  The check_carry + check_lt tail of the p_val = 0 completeness sub-case.
  Case-splits on whether the check_carry_zero integer sum is zero:
  * Sum = 0: uses `check_carry_zero_wrap_succ` then `check_lt_wrap_fail_p_zero`.
  * Sum ≠ 0: uses `check_carry_zero_wrap_fail`.
-/
private lemma p_zero_finish {w k : ℕ} {a b p' : Vector (Exp p (ZMod p)) k}
    {c : Vector (ZMod p) k → Circuit p (ZMod p)}
    (h_bound : 2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 4) ≤ p)
    (hp_gt : 2 ^ w < p)
    (cond : ∀ (i : Fin k), p'[i].eval = 0) :
    denotation.n =
      (wrap
          (check_carry_zero_wg (k := 2 * k - 1) w
            (Vector.ofFn (n := 2 * k - 1) fun i =>
              Exp.c
                ((↑(toCompPoly (Vector.map Exp.eval a) * toCompPoly (Vector.map Exp.eval b) -
                            toCompPoly (Vector.map Exp.eval p') *
                              toCompPoly
                                (Circuit.nat2words p w k
                                  (((∑ x : Fin k, a[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) *
                                    ∑ x : Fin k, b[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) /
                                    ∑ x : Fin k, p'[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ))) -
                          toCompPoly
                            (Circuit.nat2words p w k
                              (((∑ x : Fin k, a[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) *
                                ∑ x : Fin k, b[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) %
                                ∑ x : Fin k, p'[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)))) :
                    Array (ZMod p))[i.1]?.getD 0))
            (check_lt_wg w
              (Vector.map Exp.c
                (Circuit.nat2words p w k
                  (((∑ x : Fin k, a[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) *
                    ∑ x : Fin k, b[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) %
                    ∑ x : Fin k, p'[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ))))
              p'
              (c
                  (Circuit.nat2words p w k
                    (((∑ x : Fin k, a[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) *
                      ∑ x : Fin k, b[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) %
                      ∑ x : Fin k, p'[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)))).toWg))
          (check_carry_zero_circuit w
            (Vector.mk (α := Expₑ p) (n := 2 * k - 1)
              (List.map
                  (Exp.v ∘
                    (toCompPoly (Vector.map Exp.eval a) * toCompPoly (Vector.map Exp.eval b) -
                          toCompPoly (Vector.map Exp.eval p') *
                            toCompPoly
                              (Circuit.nat2words p w k
                                (((∑ x : Fin k, a[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) *
                                  ∑ x : Fin k, b[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) /
                                  ∑ x : Fin k, p'[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ))) -
                        toCompPoly
                          (Circuit.nat2words p w k
                            (((∑ x : Fin k, a[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) *
                              ∑ x : Fin k, b[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) %
                              ∑ x : Fin k, p'[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)))).coeff)
                  (List.range (2 * k - 1))).toArray
              (by simp))
            (check_lt_circuit w
              (Vector.map Exp.v
                (Circuit.nat2words p w k
                  (((∑ x : Fin k, a[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) *
                    ∑ x : Fin k, b[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) %
                    ∑ x : Fin k, p'[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ))))
              p'
              (c
                  (Circuit.nat2words p w k
                    (((∑ x : Fin k, a[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) *
                      ∑ x : Fin k, b[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) %
                      ∑ x : Fin k, p'[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)))).toCs))).eval := by
  set t_poly : CPolynomial (ZMod p) :=
    toCompPoly (Vector.map Exp.eval a) * toCompPoly (Vector.map Exp.eval b) -
      toCompPoly (Vector.map Exp.eval p') *
        toCompPoly (Circuit.nat2words p w k
          (((∑ x : Fin k, a[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) *
            ∑ x : Fin k, b[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) /
            ∑ x : Fin k, p'[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ))) -
      toCompPoly (Circuit.nat2words p w k
        (((∑ x : Fin k, a[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) *
          ∑ x : Fin k, b[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ)) %
          ∑ x : Fin k, p'[(x : ℕ)].eval.val * (2 ^ w) ^ (x : ℕ))) with ht_poly
  set t_vec_cs : Vector (Expₑ p) (2 * k - 1) :=
    Vector.mk (List.map (Exp.v ∘ t_poly.coeff) (List.range (2 * k - 1))).toArray
      (by simp) with ht_vec_cs
  set t_vec_wg : Vector (Expₑ p) (2 * k - 1) :=
    Vector.ofFn (fun (i : Fin (2 * k - 1)) =>
      Exp.c ((↑t_poly : Array (ZMod p))[i.1]?.getD 0)) with ht_vec_wg
  -- t_vec_wg and t_vec_cs have equal evals.
  have h_wg_cs_eq : ∀ i : Fin (2 * k - 1),
      t_vec_wg[i].eval = t_vec_cs[i].eval := by
    intro i
    simp only [ht_vec_wg, Vector.getElem_ofFn, Fin.getElem_fin]
    show (Exp.c _).eval = (t_vec_cs[i]).eval
    have h_tvec_cs_eq : t_vec_cs[i] = Exp.v (t_poly.coeff i.1) := by
      simp only [ht_vec_cs, Fin.getElem_fin]
      simp
    rw [h_tvec_cs_eq]
    simp only [Exp.eval]
    rw [CPolynomial.coeff, CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?]
  by_cases h_sum :
      ∑ i : Fin (2 * k - 1),
        zmod_int_cast (2 ^ (2 * w + Nat.clog 2 (2 * k - 1) + 3))
          (t_vec_wg[i].eval) * (2 ^ w : ℤ) ^ i.1 = 0
  · -- Sum = 0: case-split on whether all carry range checks hold.
    by_cases h_hrc :
        ∀ (i : Fin (2 * k - 1 - 1))
          (h : i.1 < (carry w (t_vec_wg.toList.map Exp.eval) 0).length),
          ((carry w (t_vec_wg.toList.map Exp.eval) 0)[i.1]'h +
            2 ^ (w + 1) * ((2 * k - 1 : ℕ) : ZMod p)).val <
          2 ^ (w + Nat.clog 2 (2 * k - 1) + 2)
    · -- h_hrc holds: use check_carry_zero_wrap_succ then check_lt_wrap_fail_p_zero
      rw [check_carry_zero_wrap_succ h_bound h_wg_cs_eq h_sum h_hrc]
      symm
      apply check_lt_wrap_fail_p_zero
        (by refine le_trans ?_ h_bound; apply Nat.pow_le_pow_right (by decide); grind)
        (fun i ↦ by
          simp only [Vector.getElem_map, Exp.eval, Fin.getElem_fin]
          erw [Circuit.nat2words_spec hp_gt]
          exact Nat.mod_lt _ (Nat.two_pow_pos w))
        (by simp [Exp.eval])
        cond
    · -- h_hrc fails: use check_carry_zero_wrap_fail_hrc.
      push_neg at h_hrc
      obtain ⟨j, h_j_bd, h_j_fail⟩ := h_hrc
      symm
      exact check_carry_zero_wrap_fail_hrc h_bound h_wg_cs_eq
        ⟨j, h_j_bd, not_lt.mpr h_j_fail⟩
  · -- Sum ≠ 0: apply check_carry_zero_wrap_fail directly.
    symm
    exact check_carry_zero_wrap_fail h_bound h_wg_cs_eq h_sum

set_option maxHeartbeats 1000000000 in
/--
  Completeness of `Circuit.fpmul`, assuming canonical operand bounds
  (`a_val < p_val`, `b_val < p_val`). These are the standard operational
  preconditions for a well-formed FpMul, ensuring `q_num = a_val * b_val / p_val`
  fits into `k` limbs of `w` bits and that the honest carries stay in range.
-/
lemma fpmul_completeness {w k : ℕ} {a b p' : Vector (Exp p (ZMod p)) k} {c : Vector (ZMod p) k → Circuit p (ZMod p)}
      (ih : ∀ (a : Vector (ZMod p) k), circuitWF (c a) → (c a).eval = (wrap (c a).toWg (c a).toCs).eval)
      (h_a_lt : (∑ i : Fin k, a[i].eval.val * (2 ^ w) ^ i.1) <
                 ∑ i : Fin k, p'[i].eval.val * (2 ^ w) ^ i.1)
      (h_b_lt : (∑ i : Fin k, b[i].eval.val * (2 ^ w) ^ i.1) <
                 ∑ i : Fin k, p'[i].eval.val * (2 ^ w) ^ i.1) :
    circuitWF (Circuit.fpmul w k a b p' c) →
      (Circuit.fpmul w k a b p' c).eval = (wrap (Circuit.fpmul w k a b p' c).toWg (Circuit.fpmul w k a b p' c).toCs).eval := by
  intros h
  unfold circuitWF at h
  have hp_gt : 2 ^ w < p := by
    refine lt_of_lt_of_le ?_ h.1
    apply Nat.pow_lt_pow_right (by decide)
    grind
  unfold Circuit.eval Circuit.toWg Circuit.toCs
  split_ifs with cond
  · simp only [fpMul_circuit, fpMul_wg]
    rw [range_check_vec_completeness_succ cond.1 (by simp)]
    rw [range_check_vec_completeness_succ cond.2.1 (by simp)]
    rw [range_check_vec_completeness_succ cond.2.2.1 (by simp)]
    rw [← List.foldr_map]
    rw [foldr_curry (by simp)]
    rw [← List.foldr_map]
    rw [assert_poly_eq_prod_wrap]
    rw [foldr_curry_v]
    rw [assert_poly_eq_prod_eval_succ (fun i ↦ by simp [Vector.get, Exp.eval])]
    rw [range_check_vec_completeness_succ (nat2words_map_c_val_lt _) (by simp [Exp.eval])]
    rw [foldr_curry_v]
    rw [range_check_vec_completeness_succ (nat2words_map_c_val_lt _) (by simp [Exp.eval])]
    rw [foldr_curry (by simp)]
    simp only [Fin.getElem_fin, Array.getD_eq_getD_getElem?, Vector.map_mk, List.map_toArray,
      List.map_map, List.pure_def, List.bind_eq_flatMap]
    rw [foldr_eq0_wrap, eq0_foldr_wrap_succ (by
      intro i _
      exact fpmul_poly_identity_at a b p' i)]
    rw [check_carry_zero_wrap_succ h.1 (by simp [Exp.eval])
      (by
        have h_help := carry_zero_sum_eq_zero h.1 a b p' cond.1 cond.2.1 cond.2.2.1
          cond.2.2.2 (by
            -- q_num = (a_val * b_val) / p_val < p_val ≤ 2^(w*k),
            -- using h_a_lt, h_b_lt, and the geometric-sum bound on p_val.
            have h_p_pos := cond.2.2.2
            have h_ab_lt : (∑ i : Fin k, a[i].eval.val * (2 ^ w) ^ i.1) *
                (∑ i : Fin k, b[i].eval.val * (2 ^ w) ^ i.1) <
                (∑ i : Fin k, p'[i].eval.val * (2 ^ w) ^ i.1) *
                  (∑ i : Fin k, p'[i].eval.val * (2 ^ w) ^ i.1) := by
              exact Nat.mul_lt_mul_of_lt_of_le h_a_lt (Nat.le_of_lt h_b_lt) h_p_pos
            have h_q_lt_p : ((∑ i : Fin k, a[i].eval.val * (2 ^ w) ^ i.1) *
                (∑ i : Fin k, b[i].eval.val * (2 ^ w) ^ i.1)) /
                (∑ i : Fin k, p'[i].eval.val * (2 ^ w) ^ i.1) <
                (∑ i : Fin k, p'[i].eval.val * (2 ^ w) ^ i.1) := by
              rw [Nat.div_lt_iff_lt_mul h_p_pos]
              exact h_ab_lt
            have h_p_lt : (∑ i : Fin k, p'[i].eval.val * (2 ^ w) ^ i.1) < 2 ^ (w * k) := by
              rw [pow_mul]
              exact sum_bound_of_lt (Nat.pos_of_neZero _) (fun i => p'[i].eval.val) cond.2.2.1
            omega)
        refine Eq.trans ?_ h_help
        apply Finset.sum_congr rfl
        intro j _
        simp only [Fin.getElem_fin, Vector.getElem_ofFn]
        congr 2
        show (Exp.c _).eval = CPolynomial.coeff _ _
        rw [CPolynomial.coeff, CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?]
        rfl)
      (fun i h => by
        by_cases hk : 2 * k - 1 - 1 = 0
        · exfalso; have := i.2; omega
        · sorry)]
    rw [check_lt_wrap_succ
        (by refine le_trans ?_ h.1; apply Nat.pow_le_pow_right (by decide); grind)
        (fun i ↦ by
          simp only [Vector.getElem_map, Exp.eval, Fin.getElem_fin]
          erw [Circuit.nat2words_spec hp_gt]
          exact Nat.mod_lt _ (Nat.two_pow_pos w)
        )
        (by simp [Exp.eval])
        cond.2.2.1
        (by
          set a_val : ℕ := ∑ i : Fin k, a[i].eval.val * (2 ^ w) ^ i.1 with ha_val
          set b_val : ℕ := ∑ i : Fin k, b[i].eval.val * (2 ^ w) ^ i.1 with hb_val
          set p_val : ℕ := ∑ i : Fin k, p'[i].eval.val * (2 ^ w) ^ i.1 with hp_val
          have h_2w_pos : 0 < 2 ^ w := Nat.pos_of_neZero _
          have h_lhs_eq :
              (∑ i : Fin k,
                (Exp.eval ((Vector.map Exp.c
                  (Circuit.nat2words p w k ((a_val * b_val) % p_val)))[i])).val
                  * (2 ^ w) ^ i.1)
              = ((a_val * b_val) % p_val) % 2 ^ (w * k) := by
            rw [← Circuit.nat2words_spec₁ (n := (a_val * b_val) % p_val) hp_gt]
            apply Finset.sum_congr rfl
            intro i _
            congr 1
            show (Exp.c _).eval.val = _
            simp [Exp.eval]
          have hp_val_ub : p_val < 2 ^ (w * k) := by
            rw [hp_val, pow_mul]
            exact sum_bound_of_lt h_2w_pos (fun i => p'[i].eval.val) cond.2.2.1
          have hp_val_pos : 0 < p_val := by
            rw [hp_val] at cond ⊢
            exact cond.2.2.2
          have h_mod_lt : (a_val * b_val) % p_val < p_val := Nat.mod_lt _ hp_val_pos
          have h_bound : ((a_val * b_val) % p_val) % 2 ^ (w * k) < p_val := by
            rw [Nat.mod_eq_of_lt (lt_of_lt_of_le h_mod_lt hp_val_ub.le)]
            exact h_mod_lt
          exact h_lhs_eq ▸ h_bound)
      ]
    rw [ih _ (h.2 _)]
  · simp only [fpMul_circuit, fpMul_wg]
    simp only [Fin.getElem_fin, Classical.not_and_iff_not_or_not] at cond
    rcases cond with cond | cond | cond | cond
    · rw [range_check_vec_completeness_fail cond]
    · by_cases h : ¬∀ (i : Fin k), a[i].eval.val < 2 ^ w
      · rw [range_check_vec_completeness_fail h]
      · rw [not_not] at h
        rw [range_check_vec_completeness_succ h (by simp)]
        rw [range_check_vec_completeness_fail cond]
    · by_cases h : ¬∀ (i : Fin k), a[i].eval.val < 2 ^ w
      · rw [range_check_vec_completeness_fail h]
      · rw [not_not] at h
        rw [range_check_vec_completeness_succ h (by simp)]
        by_cases h' : ¬∀ (i : Fin k), b[i].eval.val < 2 ^ w
        · rw [range_check_vec_completeness_fail h']
        · rw [not_not] at h'
          rw [range_check_vec_completeness_succ h' (by simp)]
          rw [range_check_vec_completeness_fail cond]
    · -- Positivity fails: p_val = 0 (all p'[i] evaluate to 0).
      simp only [not_lt, nonpos_iff_eq_zero, Finset.sum_eq_zero_iff, Finset.mem_univ, mul_eq_zero,
        ZMod.val_eq_zero, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, false_and, or_false,
        forall_const] at cond
      -- The range checks on a and b may or may not hold; case split.
      by_cases h_a : ¬∀ (i : Fin k), a[i].eval.val < 2 ^ w
      · rw [range_check_vec_completeness_fail h_a]
      rw [not_not] at h_a
      rw [range_check_vec_completeness_succ h_a (by simp)]
      by_cases h_b : ¬∀ (i : Fin k), b[i].eval.val < 2 ^ w
      · rw [range_check_vec_completeness_fail h_b]
      rw [not_not] at h_b
      rw [range_check_vec_completeness_succ h_b (by simp)]
      -- p' range check succeeds trivially since each p'[i].eval = 0.
      have h_p_rc : ∀ (i : Fin k), p'[i].eval.val < 2 ^ w := fun i => by
        simp only [Fin.getElem_fin]
        rw [show p'[i.1].eval = 0 from cond i]
        rw [ZMod.val_zero]
        exact Nat.two_pow_pos w
      rw [range_check_vec_completeness_succ h_p_rc (by simp)]
      -- Walk the same rewrites as the positive case through the polynomial
      -- identity check.
      rw [← List.foldr_map]
      rw [foldr_curry (by simp)]
      rw [← List.foldr_map]
      rw [assert_poly_eq_prod_wrap]
      rw [foldr_curry_v]
      rw [assert_poly_eq_prod_eval_succ (fun i ↦ by simp [Vector.get, Exp.eval])]
      rw [range_check_vec_completeness_succ (nat2words_map_c_val_lt _) (by simp [Exp.eval])]
      rw [foldr_curry_v]
      rw [range_check_vec_completeness_succ (nat2words_map_c_val_lt _) (by simp [Exp.eval])]
      rw [foldr_curry (by simp)]
      simp only [Fin.getElem_fin, Array.getD_eq_getD_getElem?, Vector.map_mk, List.map_toArray,
        List.map_map, List.pure_def, List.bind_eq_flatMap]
      -- Peel the polynomial identity foldr (same proof as positive case).
      rw [foldr_eq0_wrap, eq0_foldr_wrap_succ (by
        intro i _
        exact fpmul_poly_identity_at a b p' i)]
      exact p_zero_finish h.1 hp_gt cond



end Clap.FpMul
