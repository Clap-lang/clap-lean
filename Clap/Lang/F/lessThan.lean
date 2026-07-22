import Clap.Lang.F.F
import Clap.Lang.F.num2bits
import Clap.Lang.FB.FB
import Clap.Lang.FB.not

namespace Clap.Edsl.Lang.F

variable {p : ℕ} [p.AtLeastTwo]

def lessThan (w : ℕ) (a b : F p) : Edsl.CircuitStateM p (FB p) := do
  let d := a - b + ofZMod p (2 ^ w : ZMod p)
  let bits ← num2bits (w + 1) d
  return FB.not (bits[w]'(by omega))

def lessEqThan (w : ℕ) (a b : F p) : Edsl.CircuitStateM p (FB p) :=
  lessThan w a (b + 1)

def greaterThan (w : ℕ) (a b : F p) : Edsl.CircuitStateM p (FB p) :=
  lessThan w b a

def greaterEqThan (w : ℕ) (a b : F p) : Edsl.CircuitStateM p (FB p) :=
  lessThan w b (a + 1)

namespace lessThan

/-- like `F.eq`'s `matchesBinaryBooleanFunctionWithSideEffects`, but also
    threading the range/prime-bound hypotheses the comparison needs
TODO: build a generic withSideEffects matches* functions? -/
def matchesBinaryComparisonFunction
  (p : ℕ) [p.AtLeastTwo] (w : ℕ)
  (spec_function : ℕ → ℕ → Bool)
  (function : F p → F p → Edsl.CircuitStateM p (FB p))
  (allocatesN : ℕ)
: Prop :=
  ∀ (a b : F p) (varStorePre : VarStore p) (numAllocPre : ℕ),
    (ha : a.isValid varStorePre) → (hb : b.isValid varStorePre) →
      letI aVal := (a.toZMod varStorePre).get ha
      letI bVal := (b.toZMod varStorePre).get hb
      (haRange : aVal.val < 2 ^ w) → (hbRange : bVal.val < 2 ^ w) → (hw : 2 ^ (w + 1) < p) →
        let ⟨result, circuit⟩ := CircuitStateM.runAndEval (function a b) numAllocPre varStorePre
        circuit.constraints ∧
        circuit.numAlloc = numAllocPre + allocatesN ∧
        (∀ n < numAllocPre, circuit.varStore[n]? = varStorePre[n]?) ∧
        Convert.toIdeal circuit.varStore result = .some (spec_function aVal.val bVal.val)

def spec (p : ℕ) [p.AtLeastTwo] (w : ℕ) : Prop :=
  matchesBinaryComparisonFunction p w (· < ·) (lessThan w) (allocatesN := w + 1)

lemma equiv (p : ℕ) [p.AtLeastTwo] (w : ℕ) : spec p w := by
  unfold spec matchesBinaryComparisonFunction lessThan
  intro a b varStorePre numAllocPre ha hb haRange hbRange hw
  set aVal := (a.toZMod varStorePre).get ha with haVal_def
  set bVal := (b.toZMod varStorePre).get hb with hbVal_def
  have hAVal : a.toZMod varStorePre = some aVal := (Option.some_get ha).symm
  have hBVal : b.toZMod varStorePre = some bVal := (Option.some_get hb).symm
  set d : F p := a - b + ofZMod p (2 ^ w : ZMod p) with hd_def
  have hDVal : [varStorePre|d] = .some (aVal - bVal + (2 : ZMod p) ^ w) := by
    rw [hd_def]
    exact FixedExp.eval_add_some (FixedExp.eval_sub_some hAVal hBVal) F.eval_ofZMod
  set dVal : ZMod p := aVal - bVal + (2 : ZMod p) ^ w with hdVal_def
  -- numeric core, mirroring `Clap.Lang.Spec.F.lessThan_equiv` (`Clap/Lang.lean:251-296`)
  have h2w_lt_p : 2 ^ w < p :=
    lt_trans (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self w)) hw
  have h2w_val : ((2 : ZMod p) ^ w).val = 2 ^ w := by
    have hc : ((2 : ZMod p) ^ w) = ((2 ^ w : ℕ) : ZMod p) := by push_cast; ring
    rw [hc]; exact ZMod.val_cast_of_lt h2w_lt_p
  have h_a_plus_2w : (aVal + (2 : ZMod p) ^ w).val = aVal.val + 2 ^ w := by
    have h := ZMod.val_add_of_lt (a := aVal) (b := (2 : ZMod p) ^ w) (by rw [h2w_val]; omega)
    rwa [h2w_val] at h
  have hdVal_val : dVal.val = aVal.val + 2 ^ w - bVal.val := by
    rw [hdVal_def]
    have heq : aVal - bVal + (2 : ZMod p) ^ w = aVal + (2 : ZMod p) ^ w - bVal := by ring
    rw [heq, ZMod.val_sub (by rw [h_a_plus_2w]; omega), h_a_plus_2w]
  have hdVal_lt : dVal.val < 2 ^ (w + 1) := by
    rw [hdVal_val]
    have h2 : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by ring
    omega
  have hDIsValid : d.isValid varStorePre := Option.isSome_iff_exists.mpr ⟨dVal, hDVal⟩
  -- the bit at index `w`: false (top bit unset) iff `a < b`
  have htestBit : dVal.val.testBit w = decide (¬ aVal.val < bVal.val) := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    by_cases hab : aVal.val < bVal.val
    · have hdiv0 : dVal.val / 2 ^ w = 0 := Nat.div_eq_of_lt (by rw [hdVal_val]; omega)
      simp [hdiv0, hab]
    · have hdiv1 : dVal.val / 2 ^ w = 1 := by
        apply Nat.div_eq_of_lt_le
        · rw [hdVal_val]; omega
        · rw [hdVal_val]
          have h2 : 2 * 2 ^ w = 2 ^ (w + 1) := by ring
          omega
      simp [hdiv1, hab]
  -- split the do-block: `num2bits (w+1) d` then the pure `return`
  have hwf : (num2bits (w + 1) d).wellFormed := Edsl.num2bits_wellFormed (w + 1) d
  have hpure_run : ∀ {α : Type} (x : α) (n : ℕ) (vs : VarStore p),
      (pure x : Edsl.CircuitStateM p α).runAndEval n vs = ⟨x, unconstrained[n][vs]⟩ :=
    fun _ _ _ => rfl
  simp only [CircuitState.runAndEval_bind hwf, hpure_run, CircuitResult.addConstraint_unconstrained]
  -- bring in `num2bits.equiv` for constraints/numAlloc/frame, and the new single-bit
  -- companion lemma `num2bits.toIdeal_getElem` for the value conjunct
  have hnum2 := num2bits.equiv p (w + 1)
  unfold num2bits.spec matchesUnaryMonadFunctionPost at hnum2
  have hnum2' := hnum2 d varStorePre numAllocPre hDIsValid
  have hc1 : ((num2bits (w + 1) d).runAndEval numAllocPre varStorePre).2.constraints = True :=
    hnum2'.1
  have hc2 : ((num2bits (w + 1) d).runAndEval numAllocPre varStorePre).2.numAlloc
      = numAllocPre + (w + 1) :=
    hnum2'.2.1
  have hc3 : ∀ n < numAllocPre,
      ((num2bits (w + 1) d).runAndEval numAllocPre varStorePre).2.varStore[n]? = varStorePre[n]? :=
    hnum2'.2.2.1
  have hbit := num2bits.toIdeal_getElem hDVal numAllocPre (w + 1) w (by omega)
  simp only [CircuitStateM.runAndEval_eq] at hc1 hc2 hc3 hbit ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc1]; trivial
  · exact hc2
  · exact hc3
  · rw [FB.toIdeal_not hbit, htestBit]
    by_cases hab : aVal.val < bVal.val <;> simp [hab]

end lessThan

namespace lessEqThan

def spec (p : ℕ) [p.AtLeastTwo] (w : ℕ) : Prop :=
  lessThan.matchesBinaryComparisonFunction p w (· ≤ ·) (lessEqThan w) (allocatesN := w + 1)

lemma equiv (p : ℕ) [p.AtLeastTwo] (w : ℕ) : spec p w := by sorry

end lessEqThan

namespace greaterThan

def spec (p : ℕ) [p.AtLeastTwo] (w : ℕ) : Prop :=
  lessThan.matchesBinaryComparisonFunction p w (· > ·) (greaterThan w) (allocatesN := w + 1)

lemma equiv (p : ℕ) [p.AtLeastTwo] (w : ℕ) : spec p w := by sorry

end greaterThan

namespace greaterEqThan

def spec (p : ℕ) [p.AtLeastTwo] (w : ℕ) : Prop :=
  lessThan.matchesBinaryComparisonFunction p w (· ≥ ·) (greaterEqThan w) (allocatesN := w + 1)

lemma equiv (p : ℕ) [p.AtLeastTwo] (w : ℕ) : spec p w := by sorry

end greaterEqThan

end Clap.Edsl.Lang.F
