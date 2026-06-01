import Clap.Compiler.Back.Compilation
import Clap.Compiler.Back.Correctness.WF
import Clap.Compiler.Back.IsZero
import Clap.Compiler.Back.Num2Bits
import Clap.Compiler.Back.Simulation

variable {p : ℕ}  [inst : Fact (Nat.Prime p)] [inst' : Fact (p > 2)] [NeZero p]

open Clap Simulation

namespace Clap.FpMul

lemma range_check_vec_circuit_success  {k : ℕ} {w : ℕ} {vec : Vector (Expₑ p) k} {cont : Csₑ p} {d : denotation (ZMod p)} :
    (∀ i : Fin k, vec[i].eval.val < 2 ^ w) →
      wrBisim d cont.eval → wrBisim d (range_check_vec_circuit w vec cont).eval := by
  sorry

lemma range_check_vec_circuit_fail {k : ℕ} {w : ℕ} {vec : Vector (Expₑ p) k} {cont : Csₑ p} {d : denotation (ZMod p)} :
    ¬ (∀ i : Fin k, vec[i].eval.val < 2 ^ w) →
      wrBisim d (range_check_vec_circuit w vec cont).eval := by sorry

lemma assert_poly_eq_prod_success {k : ℕ} {a b : Vector (Expₑ p) k}
  {c : Vector (ZMod p) (2 * k - 1)} {rest : Csₑ p} {d : denotation (ZMod p)} :
     toCompPoly c = toCompPoly (Vector.map Exp.eval a) * toCompPoly (Vector.map Exp.eval b) →
    wrBisim d rest.eval → wrBisim d (assert_poly_eq_prod a b (c.map .v) rest).eval := by sorry

lemma assert_poly_eq_prod_failure {k : ℕ} {a b : Vector (Expₑ p) k}
  {c : Vector (ZMod p) (2 * k - 1)} {rest : Csₑ p} {d : denotation (ZMod p)} :
     toCompPoly c ≠ toCompPoly (Vector.map Exp.eval a) * toCompPoly (Vector.map Exp.eval b) →
    wrBisim d (assert_poly_eq_prod a b (c.map .v) rest).eval := by sorry

lemma eq_check_success {k : ℕ} {t ab : Vector (Expₑ p) (2*k - 1)} {q r p' : Vector (Expₑ p) k} {cont : Csₑ p} {d : denotation (ZMod p)}  :
  toCompPoly (t.map Exp.eval) = toCompPoly (ab.map Exp.eval) + (toCompPoly (p'.map Exp.eval)) * (toCompPoly (q.map Exp.eval)) + toCompPoly (r.map Exp.eval) →
  wrBisim d cont.eval →
  wrBisim d
    (List.foldr
      (fun i ↦ Cs.eq0 (eval_poly t i - (eval_poly ab i - ((eval_poly p' i) * (eval_poly q i) + eval_poly r i))))
      cont
      (List.range (2*k - 1))
    ).eval := sorry

lemma eq_check_fail {k : ℕ} {t ab : Vector (Expₑ p) (2*k - 1)} {q r p' : Vector (Expₑ p) k} {cont : Csₑ p} {d : denotation (ZMod p)}  :
  toCompPoly (t.map Exp.eval) ≠ toCompPoly (ab.map Exp.eval) + (toCompPoly (p'.map Exp.eval)) * (toCompPoly (q.map Exp.eval)) + toCompPoly (r.map Exp.eval) →
  wrBisim d
    (List.foldr
      (fun i ↦ Cs.eq0 (eval_poly t i - (eval_poly ab i - ((eval_poly p' i) * (eval_poly q i) + eval_poly r i))))
      cont
      (List.range (2*k - 1))
    ).eval := sorry

lemma check_carry_success {k w : ℕ} {t_pol : Vector (ZMod p) (2 * k - 1)} {cont : Csₑ p} {d : denotation (ZMod p)} :
  4 * 2 ^ (2 * w + Nat.clog 2 k) < p →
  ∑ i : Fin (2 * k - 1), t_pol[i].val * 2 ^ i.1 = 0 →
    wrBisim d cont.eval →
    wrBisim d (check_carry_zero_circuit w (Vector.map Exp.v t_pol) cont).eval := by sorry

lemma check_carry_fail {k w : ℕ} {t_pol : Vector (ZMod p) (2 * k - 1)} {cont : Csₑ p} {d : denotation (ZMod p)} :
  4 * 2 ^ (2 * w + Nat.clog 2 k) < p →
  ∑ i : Fin (2 * k - 1), t_pol[i].val * 2 ^ i.1 ≠ 0 →
    wrBisim d (check_carry_zero_circuit w (Vector.map Exp.v t_pol) cont).eval := by sorry

lemma check_lt_success {k w : ℕ} {r_pol : Vector (ZMod p) k} {p' : Vector (Expₑ p) k} {cont : Csₑ p} {d : denotation (ZMod p)} :
  ∑ i : Fin _, r_pol[i].val * 2 ^ i.1 < ∑ i : Fin _, p'[i].eval.val * 2 ^ i.1 →
  wrBisim d cont.eval → wrBisim d ((check_lt w (Vector.map Exp.v r_pol) p' cont).eval) := by sorry

lemma check_lt_fail {k w : ℕ} {r_pol : Vector (ZMod p) k} {p' : Vector (Expₑ p) k} {cont : Csₑ p} {d : denotation (ZMod p)} :
  ∑ i : Fin _, r_pol[i].val * 2 ^ i.1 ≥ ∑ i : Fin _, p'[i].eval.val * 2 ^ i.1 →
  wrBisim d ((check_lt w (Vector.map Exp.v r_pol) p' cont).eval) := by sorry

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
    apply range_check_vec_circuit_success cond.1
    apply range_check_vec_circuit_success cond.2.1
    apply range_check_vec_circuit_success cond.2.2
    apply rw_bisim_uncurry
    intros ab_pol
    by_cases ab_honest : (toCompPoly ab_pol) = (toCompPoly (a.map Exp.eval)) * (toCompPoly (b.map Exp.eval))
    · apply assert_poly_eq_prod_success ab_honest
      apply rw_bisim_uncurry
      intros q_pol
      by_cases q_honest : (∀ i : Fin k, (Exp.eval (.v q_pol[i])).val < 2 ^ w)
      · apply range_check_vec_circuit_success (by simpa using q_honest)
        apply rw_bisim_uncurry
        intro r_pol
        by_cases r_honest : (∀ i : Fin k, (Exp.eval (.v r_pol[i])).val < 2 ^ w)
        · apply range_check_vec_circuit_success (by simpa using r_honest)
          apply rw_bisim_uncurry
          intro t_pol
          have :  Exp.eval ∘ (Exp.v : ZMod p → Expₑ p) = id := by
            ext x; simp [Function.comp_apply, Exp.eval]
          by_cases t_eq : toCompPoly t_pol = toCompPoly ab_pol + (toCompPoly (p'.map Exp.eval)) * (toCompPoly q_pol) + toCompPoly r_pol
          · apply eq_check_success (by simpa [this] using t_eq)
            by_cases carry_honest : ∑ i : Fin (2 * k - 1), t_pol[i].val * 2 ^ i.1 = 0
            · apply check_carry_success invariant carry_honest
              by_cases r_lt_p' : ∑ i : Fin _, r_pol[i].val * 2 ^ i.1 < ∑ i : Fin _, p'[i].eval.val * 2 ^ i.1
              · apply check_lt_success r_lt_p'
                simp only [Fin.getElem_fin]
                have :
                  Circuit.nat2words p w k
                    (((∑ x : Fin k, a[x].eval.val * (2 ^ w) ^ x.1) * ∑ x : Fin k, b[↑x].eval.val * (2 ^ w) ^ x.1) %
                      ∑ x : Fin k, p'[x].eval.val * (2 ^ w) ^ x.1) = r_pol := by

                  sorry
                simp at this
                rw [this]
                exact (ih r_pol ∘ fun a => h r_pol) p
              · apply check_lt_fail (by simpa using r_lt_p')
            · apply check_carry_fail invariant carry_honest
          · apply eq_check_fail (by simpa [this] using t_eq)
        · apply range_check_vec_circuit_fail (by simpa using r_honest)
      · apply range_check_vec_circuit_fail (by simpa using q_honest)
    · apply assert_poly_eq_prod_failure ab_honest
  · simp only [Fin.getElem_fin, Classical.not_and_iff_not_or_not] at cond
    unfold Circuit.toCs FpMul.fpMul_circuit
    rcases cond with cond | cond | cond
    · apply range_check_vec_circuit_fail cond
    · by_cases cond' :  ¬∀ (i : Fin k), a[i].eval.val < 2 ^ w
      · apply range_check_vec_circuit_fail cond'
      · apply range_check_vec_circuit_success (by simpa using cond')
        apply range_check_vec_circuit_fail cond
    · by_cases cond' :  ¬∀ (i : Fin k), a[i].eval.val < 2 ^ w
      · apply range_check_vec_circuit_fail cond'
      · by_cases cond'' :  ¬∀ (i : Fin k), b[i].eval.val < 2 ^ w
        · apply range_check_vec_circuit_success (by simpa using cond')
          apply range_check_vec_circuit_fail cond''
        · apply range_check_vec_circuit_success (by simpa using cond')
          apply range_check_vec_circuit_success (by simpa using cond'')
          apply range_check_vec_circuit_fail cond

lemma fpmul_completeness {w k : ℕ} {a b p' : Vector (Exp p (ZMod p)) k} {c : Vector (ZMod p) k → Circuit p (ZMod p)}
      (ih : ∀ (a : Vector (ZMod p) k), circuitWF (c a) → (c a).eval = (wrap (c a).toWg (c a).toCs).eval) :
    circuitWF (Circuit.fpmul w k a b p' c) →
      (Circuit.fpmul w k a b p' c).eval = (wrap (Circuit.fpmul w k a b p' c).toWg (Circuit.fpmul w k a b p' c).toCs).eval := by
  intros h
  sorry

end Clap.FpMul
