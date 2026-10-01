import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.F.mkF
import Clap.Lang.Data.FArray.OneHotRaw
import Clap.Lang.Data.FArray.xor
import Clap.Lang.Data.FArray.xorScan
import Clap.Lang.Core.FB.and
import Clap.Lang.Core.FB.assert
import Clap.Lang.Core.FUnit.assert_range
import Clap.Lang.Core.FB.ofBool
import Clap.Lang.Data.FArray.assert_eq
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.WitnessGenerator.toWg
namespace Clap.Lang

variable {p : ℕ}

section arraySelector

/-- The body of `arraySelector` without its two index range checks: 1s at `[startIdx, endIdx)`,
0s elsewhere, saturating at `len`. A difference-array / toggle construction: XOR the two one-hot
masks, then take the inclusive prefix-XOR scan

Both comparisons (`startIdx < endIdx` and `startIdx < len`) are folded into a single `assert`,
and each `lessThan` range-checks its own offset, so this emits three constraints. It never
range-checks the indices, so `convertsM_unchecked` states them for arbitrary indices. -/
def arraySelectorCore [p.AtLeastTwo] (len : ℕ) (startIdx endIdx : F p) : ClapM p (FArray p len) := do
  let lt1 ← lessThan (minBits' len) startIdx endIdx
  let lenF ← mkF (len : ZMod p)
  let lt2 ← lessThan (minBits' len) startIdx lenF
  let combined ← FB.and lt1 lt2
  assert combined
  let startMask ← oneHotRaw len startIdx
  -- No need for `singleEndArray` (Circom's `SingleNegOneArray`): its sum check cannot fail for
  -- `len < p`, so it is functionally `oneHotRaw` (Andrei Burdusa, PR #74).
  let endMask ← oneHotRaw len endIdx
  let diffMask ← FArray.xor startMask endMask
  let false' ← FB.ofBool false
  diffMask.xorScan false'

/-- Bit array with 1s at `[startIdx, endIdx)`, 0s elsewhere, saturating at `len` when
`endIdx ≥ len`. Satisfiable exactly when both indices fit in `minBits' len` bits,
`startIdx < len` and `startIdx < endIdx`.

Circom's `ArraySelector` range-checks both indices, `Num2Bits(B)` with `B = min_num_bits(LEN)`,
before comparing them, and so does this. Without those checks the comparisons are meaningless on
out-of-range indices, so `convertsM` needs no range hypotheses. -/
def arraySelector [p.AtLeastTwo] (len : ℕ) (startIdx endIdx : F p) : ClapM p (FArray p len) := do
  assert_range (minBits' len) startIdx
  assert_range (minBits' len) endIdx
  arraySelectorCore len startIdx endIdx

namespace arraySelectorCore

private lemma scanAuxPure_getElem
  {len a b : ℕ}
  (j : ℕ) (hj : j ≤ len) (m : ℕ) (hm : m ≤ j)
:
  (scanAuxPure (Vector.ofFn (fun t : Fin len => (t.val == a) ^^ (t.val == b))) false j hj)[m]'(by omega)
    = (decide (a < m) ^^ decide (b < m))
:= by
  induction j generalizing m with
  | zero =>
    have hm0 : m = 0 := by omega
    subst hm0
    unfold scanAuxPure
    simp
  | succ j ih =>
    unfold scanAuxPure
    by_cases hmj : m ≤ j
    . rw [Vector.getElem_push_lt]
      exact ih (by omega) m hmj
    . have hmj' : m = j + 1 := by omega
      subst hmj'
      rw [Vector.getElem_push_eq]
      have h_rest_j := ih (by omega) j (le_refl j)
      have h_vals_j : (Vector.ofFn (fun t : Fin len => (t.val == a) ^^ (t.val == b)))[j]'(by omega)
          = ((j == a) ^^ (j == b)) := by
        simp
      simp only [h_rest_j]
      have hlt_a : (a < j + 1) ↔ (a < j ∨ a = j) := by omega
      have hlt_b : (b < j + 1) ↔ (b < j ∨ b = j) := by omega
      simp only [hlt_a, hlt_b, Bool.decide_or]
      by_cases ha : a < j <;> by_cases ha2 : a = j <;>
        by_cases hb : b < j <;> by_cases hb2 : b = j <;>
        simp [ha, ha2, hb, hb2] <;> omega

/-- `arraySelectorCore` on arbitrary indices -/
lemma convertsM_unchecked
  [p.AtLeastTwo]
  {len : ℕ}
  {startIdx endIdx : F p}
  {state : ClapMState p}
  {startIdx_val endIdx_val : ZMod p}
  (h_startIdx : Converts F.conversion state startIdx startIdx_val)
  (h_endIdx : Converts F.conversion state endIdx endIdx_val)
  (h_len : len < p)
:
  ConvertsM FArray.conversion (arraySelectorCore len startIdx endIdx) state
    (Vector.ofFn (fun i : Fin len =>
      decide (startIdx_val.val ≤ i.val) ^^ decide (endIdx_val.val ≤ i.val)))
    (lessThan.lessThanOk (minBits' len) startIdx_val endIdx_val ∧
     lessThan.lessThanOk (minBits' len) startIdx_val (len : ZMod p) ∧
     (lessThan.lessThanRaw (minBits' len) startIdx_val endIdx_val &&
       lessThan.lessThanRaw (minBits' len) startIdx_val (len : ZMod p)) = true)
:= by
  unfold arraySelectorCore
  -- Three steps assert. Each comparison is sequenced with `convertsM_bind_and`, reframing by hand
  -- what `step` would have reframed; `step` takes the rest, with the `assert` as its only one.
  have h_lt1 := lessThan.convertsM_unchecked (w := minBits' len) h_startIdx h_endIdx
  have h_s1 := converts_skip h_lt1 h_startIdx
  have h_e1 := converts_skip h_lt1 h_endIdx
  have h_lt1r := h_lt1.result
  clear h_startIdx h_endIdx
  apply convertsM_bind_and h_lt1
  step mkF.convertsM as lenF
  simp only [true_implies]
  have h_lt2 := lessThan.convertsM_unchecked (w := minBits' len) h_s1 h_lenF
  have h_s2 := converts_skip h_lt2 h_s1
  have h_e2 := converts_skip h_lt2 h_e1
  have h_lt1r' := converts_skip h_lt2 h_lt1r
  have h_lt2r := h_lt2.result
  clear h_s1 h_e1 h_lt1r h_lenF
  apply convertsM_bind_and h_lt2
  step FB.and.convertsM h_lt1r' h_lt2r as combined
  step assert.convertsM h_combined as assertStep
  step oneHotRaw.convertsM h_s2 h_len as startMask
  step oneHotRaw.convertsM h_e2 h_len as endMask
  step FArray.xor.convertsM h_startMask h_endMask as diffMask
  step (FB.ofBool.convertsM (state := diffMask_state) (b := false)) as false'
  apply convertsM_of_convertsM (FArray.xorScan.convertsM h_false' h_diffMask)
  . have hdiff_eq :
        (Vector.ofFn (fun i : Fin len => (Vector.ofFn (fun x : Fin len => x.val == startIdx_val.val))[i]
          ^^ (Vector.ofFn (fun x : Fin len => x.val == endIdx_val.val))[i]))
        = Vector.ofFn (fun t : Fin len => (t.val == startIdx_val.val) ^^ (t.val == endIdx_val.val)) := by
      ext i hi
      simp
    have htail :
        ∀ (j : ℕ) (hj : j < len),
          (scanAuxPure (Vector.ofFn (fun i : Fin len => (Vector.ofFn (fun x : Fin len => x.val == startIdx_val.val))[i]
            ^^ (Vector.ofFn (fun x : Fin len => x.val == endIdx_val.val))[i])) false len (le_refl len)).tail[j]'(by omega)
          = (scanAuxPure (Vector.ofFn (fun t : Fin len => (t.val == startIdx_val.val) ^^ (t.val == endIdx_val.val)))
              false len (le_refl len))[j + 1]'(by omega) := by
      intro j hj
      rw [hdiff_eq]
      simp [Nat.add_comm]
    ext i hi
    simp only [Vector.getElem_cast]
    rw [htail i hi]
    have hi' := scanAuxPure_getElem (len := len) (a := startIdx_val.val) (b := endIdx_val.val)
      len (le_refl len) (i + 1) (by omega)
    simp only [Nat.lt_succ_iff] at hi'
    simp only [Vector.getElem_ofFn]
    exact hi'
  -- the `assert` is the only asserting `step`, so both constraint goals are that `assert`
  . simp
  . simp

end arraySelectorCore

namespace arraySelector

/-- The value is the XOR form of the two masks, which reads as `[startIdx, endIdx)` once
`startIdx < endIdx` (see `convertsM'`) -/
lemma convertsM
  [p.AtLeastTwo]
  {len : ℕ}
  {startIdx endIdx : F p}
  {state : ClapMState p}
  {startIdx_val endIdx_val : ZMod p}
  (h_startIdx : Converts F.conversion state startIdx startIdx_val)
  (h_endIdx : Converts F.conversion state endIdx endIdx_val)
  (h_len : len < p)
  (hw : 2 ^ (minBits' len + 1) < p)
:
  ConvertsM FArray.conversion (arraySelector len startIdx endIdx) state
    (Vector.ofFn (fun i : Fin len =>
      decide (startIdx_val.val ≤ i.val) ^^ decide (endIdx_val.val ≤ i.val)))
    (startIdx_val.val < 2 ^ minBits' len ∧ endIdx_val.val < 2 ^ minBits' len ∧
      startIdx_val.val < len ∧ startIdx_val.val < endIdx_val.val)
:= by
  unfold arraySelector
  -- Group the two range checks, so that one action establishes both bounds.
  rw [← bind_assoc]
  have hA := assert_range.convertsM (w := minBits' len) h_startIdx
  have hAB := convertsM_bind_and (function := fun _ => assert_range (minBits' len) endIdx) hA
    (assert_range.convertsM (w := minBits' len) (converts_skip hA h_endIdx))
  have hCore := arraySelectorCore.convertsM_unchecked
    (converts_skip hAB h_startIdx) (converts_skip hAB h_endIdx) h_len
  refine convertsM_of_convertsM (convertsM_bind_guard hAB hCore ?_) rfl and_assoc
  -- Under the range checks, the raw comparisons are the real ones and their offsets fit.
  rintro ⟨ha, hb⟩
  have h_lenF_val : (len : ZMod p).val < 2 ^ minBits' len := by
    rw [ZMod.val_natCast_of_lt h_len]
    exact lt_two_pow_minBits' len
  rw [lessThan.lessThanRaw_eq ha hb hw, lessThan.lessThanRaw_eq ha h_lenF_val hw,
    ZMod.val_natCast_of_lt h_len]
  simp only [lessThan.lessThanOk_of ha hb hw, lessThan.lessThanOk_of ha h_lenF_val hw,
    true_and, Bool.and_eq_true, decide_eq_true_eq]
  exact And.comm

/-- `convertsM` with the value read as the interval `[startIdx, endIdx)`, for `startIdx < endIdx`. -/
lemma convertsM'
  [p.AtLeastTwo]
  {len : ℕ}
  {startIdx endIdx : F p}
  {state : ClapMState p}
  {startIdx_val endIdx_val : ZMod p}
  (h_startIdx : Converts F.conversion state startIdx startIdx_val)
  (h_endIdx : Converts F.conversion state endIdx endIdx_val)
  (h_len : len < p)
  (hw : 2 ^ (minBits' len + 1) < p)
  (h_idx : startIdx_val.val < endIdx_val.val)
:
  ConvertsM FArray.conversion (arraySelector len startIdx endIdx) state
    (Vector.ofFn (fun i : Fin len =>
      (startIdx_val.val ≤ i.val) && (i.val < endIdx_val.val)))
    (startIdx_val.val < 2 ^ minBits' len ∧ endIdx_val.val < 2 ^ minBits' len ∧
      startIdx_val.val < len ∧ startIdx_val.val < endIdx_val.val)
:= by
  apply convertsM_of_convertsM (convertsM h_startIdx h_endIdx h_len hw)
  . ext i hi
    simp only [Vector.getElem_ofFn]
    by_cases hai : startIdx_val.val ≤ i <;> by_cases hib : i < endIdx_val.val <;>
      simp [hai, hib] <;> omega
  . exact Iff.rfl
end arraySelector

end arraySelector


section examples

private abbrev q : ℕ := 47

local instance instFactPrimeArraySelectorQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def runSat (c : ClapM q Unit) : Bool :=
  let circ  := c.getCircuit 0 (HashConsSt.empty q)
  let cache := c.getHashConsState 0 (HashConsSt.empty q)
  (circ.toCs cache 0).run ((circ.toWg cache 0).run #v[])

private def checkBits {n} (g : ClapM q (FArray q n)) (e : Vector Bool n) : ClapM q Unit := do
  let r ← g
  let e' ← e.mapM FB.ofBool
  FArray.assert_eq r e'

private def sel (len : ℕ) (s e : ZMod q) (out : Vector Bool len) : Bool :=
  runSat (checkBits (do arraySelector len (← mkF s) (← mkF e)) out)

private def selCore (len : ℕ) (s e : ZMod q) (out : Vector Bool len) : Bool :=
  runSat (checkBits (do arraySelectorCore len (← mkF s) (← mkF e)) out)

example : sel 4 0 1 #v[true, false, false, false] = true := by native_decide
example : sel 4 1 3 #v[false, true, true, false] = true := by native_decide
example : sel 4 3 4 #v[false, false, false, true] = true := by native_decide
example : sel 4 0 4 #v[true, true, true, true] = true := by native_decide
example : sel 4 1 2 #v[false, true, false, false] = true := by native_decide
-- `endIdx ≥ len` saturates, as long as it fits in `minBits' 4 = 3` bits
example : sel 4 2 7 #v[false, false, true, true] = true := by native_decide
example : sel 4 3 3 #v[false, false, false, false] = false := by native_decide
example : sel 4 0 0 #v[false, false, false, false] = false := by native_decide
-- the range checks: the core alone accepts an out-of-range start, `arraySelector` does not
example : selCore 4 (-1) 2 #v[false, false, true, true] = true := by native_decide
example : sel 4 (-1) 2 #v[false, false, true, true] = false := by native_decide
example : sel 4 2 8 #v[false, false, true, true] = false := by native_decide

end examples

end Clap.Lang
