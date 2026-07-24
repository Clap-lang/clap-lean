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

omit inst' in
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

set_option maxHeartbeats 400000 in
/--
  Generalized auxiliary lemma for `check_lt'`. The recursion accumulates the
  `isLt` flag, so the spec is parametrized over the current value of `isLt`.

  The invariant `(isLt.eval = 1 ∧ multi-prec_≤) ∨ multi-prec_<` says: the
  continuation should be entered if either (a) we have already determined a
  strict inequality at some more-significant position (tracked in `isLt`) AND
  the current `(r_pol, p')` is multi-prec_≤ (which the recursion will enforce
  limb-wise), OR (b) the current `(r_pol, p')` is itself multi-prec_<.
-/
private lemma check_lt'_wrBisim {k w : ℕ}
    {isLt : Expₑ p}
    {r_pol : Vector (ZMod p) k}
    {p' : Vector (Expₑ p) k}
    {cont : Csₑ p}
    {d : denotation (ZMod p)}
    (hp_bound : 2 ^ (w + 1) ≤ p)
    (hr_rc : ∀ i : Fin k, r_pol[i].val < 2 ^ w)
    (hp_rc : ∀ i : Fin k, p'[i].eval.val < 2 ^ w) :
    (((isLt.eval = 1 ∧
          ∑ i : Fin k, r_pol[i].val * (2 ^ w) ^ i.1 ≤
            ∑ i : Fin k, p'[i].eval.val * (2 ^ w) ^ i.1) ∨
        ∑ i : Fin k, r_pol[i].val * (2 ^ w) ^ i.1 <
          ∑ i : Fin k, p'[i].eval.val * (2 ^ w) ^ i.1) →
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
      refine ⟨?_, ?_⟩
      · have := sub_eq_zero.mp h
        simpa using this
      · simp
    · exact wrBisim.none
  | succ k ih =>
    intro hbisim
    unfold check_lt_circuit'
    apply num2bits_wrBisim_cont
    intro h_nb
    set a : ℕ := r_pol[Fin.last k].val with ha_def
    set b : ℕ := p'[Fin.last k].eval.val with hb_def
    have ha_rc : a < 2 ^ w := hr_rc (Fin.last k)
    have hb_rc : b < 2 ^ w := hp_rc (Fin.last k)
    have h_msb_le : a ≤ b := by
      by_contra h_not_le
      push Not at h_not_le
      have h_eval : ((Vector.map Exp.v r_pol)[Fin.last k] - p'[Fin.last k] +
          Exp.c (2 ^ w - 1)).eval = r_pol[Fin.last k] - p'[Fin.last k].eval +
          ((2 ^ w - 1 : ZMod p)) := by
        simp [Exp.eval, Vector.getElem_map]
      rw [h_eval] at h_nb
      have hp_gt_1 : 1 < p := by have := inst'.out; omega
      haveI : Fact (1 < p) := ⟨hp_gt_1⟩
      have h_pow_two_pos : (1 : ℕ) ≤ 2 ^ w := Nat.one_le_two_pow
      have h_2pw_lt_p : 2 ^ w < p := by
        have : 2 ^ w < 2 ^ (w + 1) := by
          apply Nat.pow_lt_pow_right (by norm_num); omega
        omega
      have h_pow_cast : ((2 : ZMod p) ^ w) = ((2 ^ w : ℕ) : ZMod p) := by push_cast; ring
      have h_2pw_val : ((2 : ZMod p) ^ w).val = 2 ^ w := by
        rw [h_pow_cast, ZMod.val_natCast_of_lt h_2pw_lt_p]
      have h_one_val : (1 : ZMod p).val = 1 := ZMod.val_one p
      have h_2pw_sub_one_val : ((2 ^ w : ZMod p) - 1).val = 2 ^ w - 1 := by
        rw [ZMod.val_sub]
        · rw [h_2pw_val, h_one_val]
        · rw [h_2pw_val, h_one_val]; exact h_pow_two_pos
      have h_pp_le_r : p'[Fin.last k].eval.val ≤ r_pol[Fin.last k].val :=
        Nat.le_of_lt h_not_le
      have h_sub_val :
          (r_pol[Fin.last k] - p'[Fin.last k].eval).val =
            r_pol[Fin.last k].val - p'[Fin.last k].eval.val :=
        ZMod.val_sub h_pp_le_r
      have h_sum_lt_p :
          (r_pol[Fin.last k] - p'[Fin.last k].eval).val + ((2 ^ w : ZMod p) - 1).val < p := by
        rw [h_sub_val, h_2pw_sub_one_val, ← ha_def, ← hb_def]
        have : 2 * (2 ^ w - 1) < 2 ^ (w + 1) := by
          rw [two_mul, pow_succ]; omega
        omega
      have h_total_val :
          (r_pol[Fin.last k] - p'[Fin.last k].eval + ((2 ^ w : ZMod p) - 1)).val =
            (r_pol[Fin.last k].val - p'[Fin.last k].eval.val) + (2 ^ w - 1) := by
        rw [ZMod.val_add_of_lt h_sum_lt_p, h_sub_val, h_2pw_sub_one_val]
      rw [h_total_val, ← ha_def, ← hb_def] at h_nb
      omega
    unfold IsZero.isZero_circuit
    apply wrBisim.right
    intro inv
    simp only [Cs.eval]
    apply wrBisim.right
    intro o
    split_ifs with h_iz1 h_iz2
    · have h_o_or_eq :
          o = 0 ∨ r_pol[Fin.last k] = p'[Fin.last k].eval := by
        have h := h_iz2
        simp only [Vector.getElem_map, Exp.eval,
          Fin.getElem_fin, Fin.val_last] at h
        rcases mul_eq_zero.mp h with ho | he
        · exact Or.inl ho
        · right
          have he' : r_pol[Fin.last k] - p'[Fin.last k].eval = 0 := by
            aesop
          exact sub_eq_zero.mp he'
      have h_map_ofFn :
          Vector.ofFn (fun i : Fin k ↦ (Vector.map Exp.v r_pol)[i.castSucc]) =
            Vector.map (Exp.v (p := p) (var := ZMod p))
              (Vector.ofFn (fun i : Fin k ↦ r_pol[i.castSucc])) := by
        ext i hi
        simp [Vector.getElem_ofFn, Vector.getElem_map]
      rw [h_map_ofFn]
      refine ih
        (isLt := isLt ||| (1 - Exp.v o))
        (r_pol := Vector.ofFn (fun i ↦ r_pol[i.castSucc]))
        (p' := Vector.ofFn (fun i ↦ p'[i.castSucc]))
        (fun i => by simp [Vector.getElem_ofFn]; exact hr_rc i.castSucc)
        (fun i => by simp [Vector.getElem_ofFn]; exact hp_rc i.castSucc)
        ?_
      rintro (⟨h_isLt', h_le'⟩ | h_lt')
      · have h_le'' :
            ∑ x : Fin k, r_pol[x.castSucc].val * (2 ^ w) ^ x.val ≤
              ∑ x : Fin k, p'[x.castSucc].eval.val * (2 ^ w) ^ x.val := by
          simpa using h_le'
        have h_unfold_or : isLt.eval + (1 - o) - isLt.eval * (1 - o) = 1 := by
          have h := h_isLt'
          change (isLt + (1 - Exp.v o) - isLt * (1 - Exp.v o)).eval = 1 at h
          simpa [Exp.eval] using h
        have h_or_zero : o * (isLt.eval - 1) = 0 := by linear_combination h_unfold_or
        rcases mul_eq_zero.mp h_or_zero with ho | hisLt
        · apply hbisim
          right
          have h_a_lt : a < b := by
            rcases lt_or_eq_of_le h_msb_le with h | h_a_eq
            · exact h
            · exfalso
              have h_val_eq : r_pol[Fin.last k].val = p'[Fin.last k].eval.val := by
                rw [← ha_def, ← hb_def]; exact h_a_eq
              have h_e_eq : r_pol[Fin.last k] = p'[Fin.last k].eval :=
                ZMod.val_injective p h_val_eq
              have h_simp : (1 : ZMod p) - inv * (r_pol[Fin.last k] - p'[Fin.last k].eval) - o = 0 := by
                have := h_iz1
                rw [Exp.eval_sub, Exp.eval_sub, Exp.eval_mul, Exp.eval_sub] at this
                simp [Vector.getElem_map, Fin.getElem_fin, Fin.val_last, Exp.eval] at this
                simpa
              rw [h_e_eq, sub_self, MulZeroClass.mul_zero, sub_zero] at h_simp
              have h_o_one : o = 1 := (sub_eq_zero.mp h_simp).symm
              rw [ho] at h_o_one
              exact zero_ne_one h_o_one
          rw [Fin.sum_univ_castSucc (n := k), Fin.sum_univ_castSucc (n := k)]
          simp only [Fin.val_last, Fin.val_castSucc, ← ha_def, ← hb_def]
          have h_pow_pos : (0 : ℕ) < (2 ^ w) ^ k := by
            exact Nat.pos_of_neZero ((2 ^ w) ^ k)
          have h_msb_mul_strict : a * (2 ^ w) ^ k < b * (2 ^ w) ^ k := by
            have : (a + 1) * (2 ^ w) ^ k ≤ b * (2 ^ w) ^ k := Nat.mul_le_mul_right _ h_a_lt
            linarith [this, Nat.add_mul a 1 ((2 ^ w) ^ k), h_pow_pos]
          exact Nat.add_lt_add_of_le_of_lt h_le'' h_msb_mul_strict
        · have h_isLt_eq : isLt.eval = 1 := by linear_combination hisLt
          apply hbisim
          left
          refine ⟨h_isLt_eq, ?_⟩
          rw [Fin.sum_univ_castSucc (n := k), Fin.sum_univ_castSucc (n := k)]
          simp only [Fin.val_last, Fin.val_castSucc, ← ha_def, ← hb_def]
          have h_msb_mul : a * (2 ^ w) ^ k ≤ b * (2 ^ w) ^ k :=
            Nat.mul_le_mul_right ((2 ^ w) ^ k) h_msb_le
          linarith [h_le'', h_msb_mul]
      · apply hbisim
        right
        have h_lt'' :
            ∑ x : Fin k, r_pol[x.castSucc].val * (2 ^ w) ^ x.val <
              ∑ x : Fin k, p'[x.castSucc].eval.val * (2 ^ w) ^ x.val := by
          simpa using h_lt'
        rw [Fin.sum_univ_castSucc (n := k), Fin.sum_univ_castSucc (n := k)]
        simp only [Fin.val_last, Fin.val_castSucc, ← ha_def, ← hb_def]
        have h_msb_mul : a * (2 ^ w) ^ k ≤ b * (2 ^ w) ^ k :=
          Nat.mul_le_mul_right ((2 ^ w) ^ k) h_msb_le
        linarith [h_lt'', h_msb_mul]
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
  apply check_lt'_wrBisim hp_bound hr_rc hp_rc
  rintro (⟨h, _⟩ | h)
  · -- `(0 : Expₑ p).eval = 1` is impossible (since `p > 2`), so this case is vacuous.
    exfalso
    simp [Exp.eval] at h
  · exact hbisim h

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
    rcases cond with h | h | h
    · exfalso
      apply h
      exact a_rc
    · exfalso
      apply h
      exact b_rc
    · exfalso
      apply h
      exact p'_rc

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

lemma check_carry_zero_wrap_succ {k w : ℕ} {t_wg t_cs : Vector (Expₑ p) k}
    {wg : Wg p} {cs : Csₑ p} :
  2 ^ (2 * w + Nat.clog 2 k + 4) ≤ p →
  (∀ i : Fin k, t_wg[i].eval = t_cs[i].eval) →
  ∑ i : Fin k, zmod_int_cast (2 ^ (2 * w + Nat.clog 2 k + 3)) t_wg[i].eval * (2 ^ w : ℤ) ^ i.1 = 0 →
    (wrap (check_carry_zero_wg w t_wg wg) (check_carry_zero_circuit w t_cs cs)).eval =
      (wrap wg cs).eval := by
  intros hp_bound hval_eq hsum
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
    -- Remaining: peel off each Cs.eq0 carry-equation and each num2bits pair
    -- (honest carries satisfy all constraints under hp_bound + hsum), then the
    -- final base Cs.eq0. Analog of `check_carry_zero_circuit_wrBisim`'s ~500 lines.
    sorry

-- #check check_lt_wg
-- #check check_lt_circuit

lemma check_lt_wrap_succ {k w : ℕ} {wg : Wg p} {cs : Csₑ p} {t t' p' :  Vector (Expₑ p) k}
    (hp_bound : 2 ^ (w + 1) ≤ p)
    (hr_rc : ∀ i : Fin k, t[i].eval.val < 2 ^ w)
    (h_equiv : ∀ i : Fin k, t[i].eval = t'[i].eval)
    (hp_rc : ∀ i : Fin k, p'[i].eval.val < 2 ^ w) :
  (∑ i : Fin _, t[i].eval.val * (2 ^ w) ^ i.1 < ∑ i : Fin _, p'[i].eval.val * (2 ^ w) ^ i.1) → (wrap (check_lt_wg w t p' wg) (check_lt_circuit w t' p' cs)).eval = (wrap wg cs).eval := by sorry

omit inst' in
lemma eq0_foldr_wrap_succ {α : Type} {ls : List α} {f : α → Expₑ p} {wg : Wg p} {cs : Csₑ p} :
    (∀ i ∈ ls, (f i).eval = 0) →
      (List.foldr (fun i ↦ Cs.eq0 (f i)) (wrap wg cs) ls).eval = (wrap wg cs).eval := by
  intros h
  induction ls with
  | nil => simp
  | cons l ls ih =>
    simp_all only [List.foldr_cons, Cs.eval, h l (by simp), ↓reduceIte, List.mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp]

lemma fpmul_completeness {w k : ℕ} {a b p' : Vector (Exp p (ZMod p)) k} {c : Vector (ZMod p) k → Circuit p (ZMod p)}
      (ih : ∀ (a : Vector (ZMod p) k), circuitWF (c a) → (c a).eval = (wrap (c a).toWg (c a).toCs).eval) :
    circuitWF (Circuit.fpmul w k a b p' c) →
      (Circuit.fpmul w k a b p' c).eval = (wrap (Circuit.fpmul w k a b p' c).toWg (Circuit.fpmul w k a b p' c).toCs).eval := by
  intros h
  unfold circuitWF at h
  unfold Circuit.eval Circuit.toWg Circuit.toCs
  split_ifs with cond
  · simp only [fpMul_circuit, fpMul_wg]
    rw [range_check_vec_completeness_succ cond.1 (by simp)]
    rw [range_check_vec_completeness_succ cond.2.1 (by simp)]
    rw [range_check_vec_completeness_succ cond.2.2 (by simp)]
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
    rw [foldr_eq0_wrap, eq0_foldr_wrap_succ (by sorry)]
    rw [check_carry_zero_wrap_succ h.1 (by simp [Exp.eval]) (by simp [Exp.eval]; sorry)]
    rw [check_lt_wrap_succ (by sorry) sorry sorry sorry sorry]
    rw [ih _ (h.2 _)]
  · simp only [fpMul_circuit, fpMul_wg]
    simp only [Fin.getElem_fin, Classical.not_and_iff_not_or_not] at cond
    rcases cond with cond | cond | cond
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


end Clap.FpMul
