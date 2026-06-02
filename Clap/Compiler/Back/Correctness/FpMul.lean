import Clap.Compiler.Back.Compilation
import Clap.Compiler.Back.Correctness.WF
import Clap.Compiler.Back.IsZero
import Clap.Compiler.Back.Num2Bits
import Clap.Compiler.Back.Simulation

variable {p : ℕ}  [inst : Fact (Nat.Prime p)] [inst' : Fact (p > 2)]

instance : NeZero p where
  out := by grind [inst'.out]

open Clap Simulation

namespace Clap.FpMul

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

lemma assert_poly_eq_prod_spec {k : ℕ} {a b : Vector (Expₑ p) k}
  {c : Vector (ZMod p) (2 * k - 1)} {rest : Csₑ p} {d : denotation (ZMod p)} :
    (toCompPoly c = toCompPoly (Vector.map Exp.eval a) * toCompPoly (Vector.map Exp.eval b) → wrBisim d rest.eval) →
      wrBisim d (assert_poly_eq_prod a b (c.map .v) rest).eval := by sorry

lemma eq_check_spec {k : ℕ} {t ab : Vector (Expₑ p) (2*k - 1)} {q r p' : Vector (Expₑ p) k} {cont : Csₑ p} {d : denotation (ZMod p)}  :
  (toCompPoly (t.map Exp.eval) = toCompPoly (ab.map Exp.eval) + (toCompPoly (p'.map Exp.eval)) * (toCompPoly (q.map Exp.eval)) + toCompPoly (r.map Exp.eval) → wrBisim d cont.eval) →
    wrBisim d
      (List.foldr
        (fun i ↦ Cs.eq0 (eval_poly t i - (eval_poly ab i - ((eval_poly p' i) * (eval_poly q i) + eval_poly r i))))
        cont
        (List.range (2*k - 1))
      ).eval := sorry

lemma check_carry_spec {k w : ℕ} {t_pol : Vector (ZMod p) (2 * k - 1)} {cont : Csₑ p} {d : denotation (ZMod p)} :
  4 * 2 ^ (2 * w + Nat.clog 2 k) < p →
  (∑ i : Fin (2 * k - 1), t_pol[i].val * 2 ^ i.1 = 0 → wrBisim d cont.eval) →
    wrBisim d (check_carry_zero_circuit w (Vector.map Exp.v t_pol) cont).eval := by sorry

/--
  Generalized auxiliary lemma for `check_lt'`. The recursion accumulates the
  `isLt` flag, so the spec is parametrized over the current value of `isLt`.

  The invariant `(isLt.eval = 1 ∧ multi-prec_≤) ∨ multi-prec_<` says: the
  continuation should be entered if either (a) we have already determined a
  strict inequality at some more-significant position (tracked in `isLt`) AND
  the current `(r_pol, p')` is multi-prec_≤ (which the recursion will enforce
  limb-wise), OR (b) the current `(r_pol, p')` is itself multi-prec_<.

  Tracking multi-prec_≤ in the `isLt = 1` case is essential: in the inductive
  step, the case where `isLt' = 1` originates from `o = 0` at the current MSB
  (so we have MSB strict-`<`) needs lower-limb `≤` info to derive multi-prec_<
  on the full vectors — and that info arrives via the `≤` component of the
  inductive call's hypothesis.
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
          ∑ i : Fin k, r_pol[i].val * 2 ^ i.1 ≤ ∑ i : Fin k, p'[i].eval.val * 2 ^ i.1) ∨
        ∑ i : Fin k, r_pol[i].val * 2 ^ i.1 < ∑ i : Fin k, p'[i].eval.val * 2 ^ i.1) →
      wrBisim d cont.eval) →
    wrBisim d (check_lt' w isLt (Vector.map Exp.v r_pol) p' cont).eval := by
  induction k generalizing isLt with
  | zero =>
    intro hbisim
    -- `check_lt'` reduces to `.eq0 (isLt - 1) cont`.
    unfold check_lt'
    simp only [Cs.eval, Exp.eval_sub, Exp.eval_ofNat]
    split_ifs with h
    · -- The constraint `isLt - 1 = 0` is satisfied, so we enter the continuation.
      apply hbisim
      left
      refine ⟨?_, ?_⟩
      · -- From `isLt.eval - 1 = 0` deduce `isLt.eval = 1`.
        have := sub_eq_zero.mp h
        simpa using this
      · -- Empty sums are equal.
        simp
    · -- The constraint fails, so `.eval` is `.n`.
      exact wrBisim.none
  | succ k ih =>
    -- The recursive case: process the MSB (index `Fin.last k`) via num2bits + isZero,
    -- then recurse on the first `k` elements (which drops the MSB via `i.castSucc`).
    intro hbisim
    unfold check_lt'
    -- Step 1: absorb the num2bits gadget. After this, we have `h_nb` saying the
    -- num2bits witness exists, i.e., `(r_pol[last] - p'[last] + (2^w - 1)).val < 2^w`.
    apply num2bits_wrBisim_cont
    intro h_nb
    -- Set up abbreviations for the MSB values.
    set a : ℕ := r_pol[Fin.last k].val with ha_def
    set b : ℕ := p'[Fin.last k].eval.val with hb_def
    have ha_rc : a < 2 ^ w := hr_rc (Fin.last k)
    have hb_rc : b < 2 ^ w := hp_rc (Fin.last k)
    -- KEY ALGEBRAIC FACT: the num2bits witness forces the MSB inequality `a ≤ b`.
    -- (Proof: in `ZMod p` with `2^(w+1) ≤ p`, no wraparound; suppose `a > b` and
    -- derive `.val ≥ 2^w`, contradicting `h_nb`.)
    have h_msb_le : a ≤ b := by
      by_contra h_not_le
      push Not at h_not_le  -- h_not_le : b < a
      -- Unfold `h_nb` to a clean expression in `ZMod p`.
      have h_eval : ((Vector.map Exp.v r_pol)[Fin.last k] - p'[Fin.last k] +
          Exp.c (2 ^ w - 1)).eval = r_pol[Fin.last k] - p'[Fin.last k].eval +
          ((2 ^ w - 1 : ZMod p)) := by
        simp [Exp.eval, Vector.getElem_map]
      rw [h_eval] at h_nb
      -- The value `r - pp + (2^w - 1)` in `ZMod p`, where `r.val = a`, `pp.val = b`.
      -- With `b < a` and both `< 2^w`, `r - pp` has `.val = a - b`. Adding `(2^w - 1)`
      -- (which has `.val = 2^w - 1` since `2^w - 1 < p`) gives `.val = a - b + 2^w - 1`
      -- (since the sum is `< 2^(w+1) - 1 ≤ p - 1 < p`, no wrap). But `a > b` gives
      -- `a - b ≥ 1`, so this `.val ≥ 2^w`, contradicting `h_nb`.
      have hp_gt_1 : 1 < p := by have := inst'.out; omega
      haveI : Fact (1 < p) := ⟨hp_gt_1⟩
      have h_pow_two_pos : (1 : ℕ) ≤ 2 ^ w := Nat.one_le_two_pow
      have h_2pw_lt_p : 2 ^ w < p := by
        have : 2 ^ w < 2 ^ (w + 1) := by
          apply Nat.pow_lt_pow_right (by norm_num); omega
        omega
      -- `((2 : ZMod p) ^ w).val = 2 ^ w`.
      have h_pow_cast : ((2 : ZMod p) ^ w) = ((2 ^ w : ℕ) : ZMod p) := by push_cast; ring
      have h_2pw_val : ((2 : ZMod p) ^ w).val = 2 ^ w := by
        rw [h_pow_cast, ZMod.val_natCast_of_lt h_2pw_lt_p]
      have h_one_val : (1 : ZMod p).val = 1 := ZMod.val_one p
      -- `((2 ^ w : ZMod p) - 1).val = 2 ^ w - 1`.
      have h_2pw_sub_one_val : ((2 ^ w : ZMod p) - 1).val = 2 ^ w - 1 := by
        rw [ZMod.val_sub]
        · rw [h_2pw_val, h_one_val]
        · rw [h_2pw_val, h_one_val]; exact h_pow_two_pos
      -- `(r_pol[Fin.last k] - p'[Fin.last k].eval).val = a - b` (since `b < a`).
      have h_pp_le_r : p'[Fin.last k].eval.val ≤ r_pol[Fin.last k].val :=
        Nat.le_of_lt h_not_le
      have h_sub_val :
          (r_pol[Fin.last k] - p'[Fin.last k].eval).val =
            r_pol[Fin.last k].val - p'[Fin.last k].eval.val :=
        ZMod.val_sub h_pp_le_r
      -- The sum stays `< p`, so the additive `.val` is just the integer sum.
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
      -- `h_nb : (a - b) + (2 ^ w - 1) < 2 ^ w` with `b < a`. Contradiction.
      omega
    -- Step 2: unfold the isZero gadget. It is `.lam fun inv => .lam fun o => ...`
    unfold IsZero.isZero_circuit
    apply wrBisim.right
    intro inv
    simp only [Cs.eval]
    apply wrBisim.right
    intro o
    -- Now we have the two `.eq0` constraints from isZero.
    split_ifs with h_iz1 h_iz2
    · -- Both isZero constraints satisfied.
      -- From `h_iz2 : (o * e_msb).eval = 0` and ZMod p being a field, either
      -- `o = 0` or `e_msb.eval = 0` (i.e. `r_pol[last] = p'[last].eval`).
      have h_o_or_eq :
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
      -- Apply `ih` to the recursive `check_lt'` call. `hp_bound` is shared with
      -- the outer goal and isn't part of `ih`. Bridge `Vector.ofFn ∘ Vector.map`
      -- to `Vector.map ∘ Vector.ofFn` so the call matches `ih`'s shape.
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
      · -- `isLt' = isLt ||| (1 - .v o)` and `h_isLt' : isLt'.eval = 1`.
        -- Reshape `h_le'` so its index form matches the decomposed full sums.
        have h_le'' :
            ∑ x : Fin k, r_pol[x.castSucc].val * 2 ^ x.val ≤
              ∑ x : Fin k, p'[x.castSucc].eval.val * 2 ^ x.val := by
          simpa using h_le'
        -- Algebra: `(e₀ ||| e₁).eval = e₀.eval + e₁.eval - e₀.eval * e₁.eval`.
        -- From `isLt'.eval = 1` and unfolding `|||`, factor to `o * (isLt.eval - 1) = 0`.
        have h_unfold_or : isLt.eval + (1 - o) - isLt.eval * (1 - o) = 1 := by
          have h := h_isLt'
          change (isLt + (1 - Exp.v o) - isLt * (1 - Exp.v o)).eval = 1 at h
          simpa [Exp.eval] using h
        have h_or_zero : o * (isLt.eval - 1) = 0 := by linear_combination h_unfold_or
        rcases mul_eq_zero.mp h_or_zero with ho | hisLt
        · -- `o = 0`: from `h_iz1`, this forces `r_pol[last] ≠ p'[last].eval`, hence
          -- `a < b`. Combined with `h_le''` (lower bits ≤), derive multi-prec_<(full).
          apply hbisim
          right
          -- Show `a < b` at the MSB.
          have h_a_lt : a < b := by
            -- Suppose `a = b`; then in `ZMod p` (since `.val < 2^w < p` for both),
            -- `r_pol[last] = p'[last].eval`. Then by `h_iz1`, `o = 1`, contradicting `ho`.
            rcases lt_or_eq_of_le h_msb_le with h | h_a_eq
            · exact h
            · exfalso
              have h_val_eq : r_pol[Fin.last k].val = p'[Fin.last k].eval.val := by
                rw [← ha_def, ← hb_def]; exact h_a_eq
              have h_e_eq : r_pol[Fin.last k] = p'[Fin.last k].eval :=
                ZMod.val_injective p h_val_eq
              -- From `h_iz1`: `1 - inv * (r - p) - o = 0`. Substituting `r = p`: `1 - o = 0`.
              have h_simp : (1 : ZMod p) - inv * (r_pol[Fin.last k] - p'[Fin.last k].eval) - o = 0 := by
                have := h_iz1
                simp only [Vector.getElem_map,
                  Fin.getElem_fin, Fin.val_last, Exp.eval] at this
                convert this using 2
              rw [h_e_eq, sub_self, mul_zero, sub_zero] at h_simp
              -- h_simp : 1 - o = 0
              have h_o_one : o = 1 := (sub_eq_zero.mp h_simp).symm
              rw [ho] at h_o_one
              exact zero_ne_one h_o_one
          rw [Fin.sum_univ_castSucc (n := k), Fin.sum_univ_castSucc (n := k)]
          simp only [Fin.val_last, Fin.val_castSucc, ← ha_def, ← hb_def]
          have h_pow_pos : (0 : ℕ) < 2 ^ k := Nat.two_pow_pos k
          have h_msb_mul_strict : a * 2 ^ k < b * 2 ^ k := by
            have : (a + 1) * 2 ^ k ≤ b * 2 ^ k := Nat.mul_le_mul_right _ h_a_lt
            linarith [this, Nat.add_mul a 1 (2 ^ k), h_pow_pos]
          exact Nat.add_lt_add_of_le_of_lt h_le'' h_msb_mul_strict
        · -- `isLt.eval - 1 = 0`, i.e., `isLt.eval = 1`. Take left disjunct of outer.
          have h_isLt_eq : isLt.eval = 1 := by linear_combination hisLt
          apply hbisim
          left
          refine ⟨h_isLt_eq, ?_⟩
          -- multi-prec_≤(full) from `h_le''` + `h_msb_le`.
          rw [Fin.sum_univ_castSucc (n := k), Fin.sum_univ_castSucc (n := k)]
          simp only [Fin.val_last, Fin.val_castSucc, ← ha_def, ← hb_def]
          have h_msb_mul : a * 2 ^ k ≤ b * 2 ^ k :=
            Nat.mul_le_mul_right (2 ^ k) h_msb_le
          linarith [h_le'', h_msb_mul]
      · -- `multi-prec_<` on the truncated vectors. Use `Fin.sum_univ_castSucc` to
        -- decompose; combined with `h_msb_le`, derive multi-prec_< on the full vectors.
        apply hbisim
        right
        -- Reshape `h_lt'` so its index form matches the post-`Fin.sum_univ_castSucc` goal.
        have h_lt'' :
            ∑ x : Fin k, r_pol[x.castSucc].val * 2 ^ x.val <
              ∑ x : Fin k, p'[x.castSucc].eval.val * 2 ^ x.val := by
          simpa using h_lt'
        rw [Fin.sum_univ_castSucc (n := k), Fin.sum_univ_castSucc (n := k)]
        simp only [Fin.val_last, Fin.val_castSucc, ← ha_def, ← hb_def]
        have h_msb_mul : a * 2 ^ k ≤ b * 2 ^ k :=
          Nat.mul_le_mul_right (2 ^ k) h_msb_le
        linarith [h_lt'', h_msb_mul]
    · exact wrBisim.none
    · exact wrBisim.none

lemma check_lt_spec {k w : ℕ} {r_pol : Vector (ZMod p) k} {p' : Vector (Expₑ p) k}
    {cont : Csₑ p} {d : denotation (ZMod p)}
    (hp_bound : 2 ^ (w + 1) ≤ p)
    (hr_rc : ∀ i : Fin k, r_pol[i].val < 2 ^ w)
    (hp_rc : ∀ i : Fin k, p'[i].eval.val < 2 ^ w) :
  (∑ i : Fin _, r_pol[i].val * 2 ^ i.1 < ∑ i : Fin _, p'[i].eval.val * 2 ^ i.1 → wrBisim d cont.eval) →
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
  unfold Circuit.eval -- Clap/Compiler/Back/Correctness/FpMul.lean
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
    apply assert_poly_eq_prod_spec
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
    apply eq_check_spec
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

      sorry
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
