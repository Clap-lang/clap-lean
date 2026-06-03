import Mathlib.LinearAlgebra.Lagrange

import CompPoly.Univariate.Basic
import CompPoly.Univariate.ToPoly.Equiv
import CompPoly.Univariate.ToPoly.Degree

import Clap.Compiler.Back.Compilation
import Clap.Compiler.Back.Correctness.Basic
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
      unfold Exp.eval at h'
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
      simp only [Exp.eval, eval_poly_eval_eq] at h'
      rw [cpoly_eval_sub, cpoly_eval_sub, cpoly_eval_mul]
      linear_combination h'
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
        wrBisim d cont.eval)
    (lst : List (Fin (n - 1)))
    (hverified : ∀ i : Fin (n - 1), i ∉ lst →
        (if i.1 = 0 then t_pol[(⟨0, h_n_pos⟩ : Fin n)]
         else t_pol[(⟨i.1, by have := i.2; omega⟩ : Fin n)] +
              carry[(⟨i.1 - 1, by have := i.2; omega⟩ : Fin (n - 1))])
          = (2 ^ w : ZMod p) * carry[i]) :
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
    apply hbisim _ h_base'
    intro i
    apply hverified
    simp
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
    intro _h_rc
    apply ih
    intro i hi
    by_cases hieq : i = head
    · subst hieq; exact h_cons'
    · apply hverified
      simp [hieq, hi, List.mem_cons]

/--
  Generalized version of `check_carry_spec` over any vector length `n`.
-/
private lemma check_carry_zero_circuit_wrBisim {n w : ℕ}
    {t_pol : Vector (ZMod p) n} {cont : Csₑ p} {d : denotation (ZMod p)}
    (hbisim : ∑ i : Fin n, t_pol[i] * (2 ^ w : ZMod p) ^ i.1 = 0 → wrBisim d cont.eval) :
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
    apply check_carry_foldr_wrBisim t_pol carry cont d h_n_pos
      (lst := List.finRange (n - 1))
    · intro heq hbase
      apply hbisim
      exact carry_eqs_imp_sum_zero (fun i => t_pol[i]) (fun i => carry[i]) h_n_pos heq hbase
    · intro i hi
      exact absurd (List.mem_finRange i) hi

lemma check_carry_spec {k w : ℕ} {t_pol : Vector (ZMod p) (2 * k - 1)} {cont : Csₑ p} {d : denotation (ZMod p)} :
  4 * 2 ^ (2 * w + Nat.clog 2 k) < p →
  (∑ i : Fin (2 * k - 1), t_pol[i] * (2 ^ w : ZMod p) ^ i.1 = 0 → wrBisim d cont.eval) →
    wrBisim d (check_carry_zero_circuit w (Vector.map Exp.v t_pol) cont).eval := by
  intro _hp hbisim
  exact check_carry_zero_circuit_wrBisim hbisim

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
    wrBisim d (check_lt' w isLt (Vector.map Exp.v r_pol) p' cont).eval := by
  induction k generalizing isLt with
  | zero =>
    intro hbisim
    unfold check_lt'
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
    unfold check_lt'
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
            simpa using he
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
                simp only [Vector.getElem_map,
                  Fin.getElem_fin, Fin.val_last, Exp.eval] at this
                convert this using 2
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
    wrBisim d ((check_lt w (Vector.map Exp.v r_pol) p' cont).eval) := by
  intro hbisim
  unfold check_lt
  apply check_lt'_wrBisim hp_bound hr_rc hp_rc
  rintro (⟨h, _⟩ | h)
  · -- `(0 : Expₑ p).eval = 1` is impossible (since `p > 2`), so this case is vacuous.
    exfalso
    simp [Exp.eval] at h
  · exact hbisim h

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
      have : k ≤ 2 ^ Nat.clog 2 k := Nat.le_pow_clog (b := 2) (by omega) k
      have : 4 * k ≤ 4 * 2 ^ (2 * w + Nat.clog 2 k) := by
        calc 4 * k ≤ 4 * 2 ^ Nat.clog 2 k := by omega
        _ ≤ 4 * 2 ^ (2 * w + Nat.clog 2 k) := by apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_right <;> omega
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
        -- `2 ^ (w + 1) ≤ p` from `invariant : 4 * 2 ^ (2 * w + Nat.clog 2 k) < p`
        have h1 : (2 : ℕ) ^ (w + 1) ≤ 4 * 2 ^ (2 * w + Nat.clog 2 k) := by
          have h2 : (4 : ℕ) = 2 ^ 2 := by norm_num
          rw [h2, ← pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        omega)
      (fun i => by simpa using r_rc i)
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

        sorry
      rw [r_eq, p'_eq] at r_lt_p'
      rw [this, Nat.mod_eq_of_lt r_lt_p']
      rw [←r_eq]
      apply Circuit.nat2words_of_sum
      · -- `2 ^ w < p` from `invariant : 4 * 2 ^ (2 * w + Nat.clog 2 k) < p`
        have h1 : (2 : ℕ) ^ w ≤ 4 * 2 ^ (2 * w + Nat.clog 2 k) := by
          have : (2 : ℕ) ^ w ≤ 2 ^ (2 * w + Nat.clog 2 k) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        omega
      · intro i
        have := r_rc i
        simpa using this
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

lemma fpmul_completeness {w k : ℕ} {a b p' : Vector (Exp p (ZMod p)) k} {c : Vector (ZMod p) k → Circuit p (ZMod p)}
      (ih : ∀ (a : Vector (ZMod p) k), circuitWF (c a) → (c a).eval = (wrap (c a).toWg (c a).toCs).eval) :
    circuitWF (Circuit.fpmul w k a b p' c) →
      (Circuit.fpmul w k a b p' c).eval = (wrap (Circuit.fpmul w k a b p' c).toWg (Circuit.fpmul w k a b p' c).toCs).eval := by
  intros h
  sorry

end Clap.FpMul
