import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.F.mkF
import Clap.Lang.Data.FArray.OneHotRaw
import Clap.Lang.Data.FArray.xor
import Clap.Lang.Data.FArray.xorScan
import Clap.Lang.Core.FB.and
import Clap.Lang.Core.FB.assert
namespace Clap.Lang

variable {p : ℕ}

section arraySelector

/-- Bit array with 1s at `[startIdx, endIdx)`, 0s elsewhere, saturating at `len` when
`endIdx ≥ len`. Only satisfiable when `startIdx < len ∧ startIdx < endIdx`. Simplified from the
old OR/AND left-to-right scan (`old/Clap/Array.lean:31-41`) to a difference-array / toggle
construction: XOR the two one-hot masks, then take the inclusive prefix-XOR scan.

Both range checks (`startIdx < endIdx` and `startIdx < len`) are folded into a single `assert`
so the gadget emits exactly one real assertion — chaining two separate asserts through the
`ConvertsM` bind machinery does not compose the way a single one does. -/
def arraySelector [p.AtLeastTwo] (len : ℕ) (startIdx endIdx : F p) : ClapM p (FArray p len) := do
  let lt1 ← lessThan (minBits' len) startIdx endIdx
  let lenF ← mkF (len : ZMod p)
  -- Instead of calling, `singleOneArray` as in the original circuit,
  -- we enforce startIdx < len here and call just `oneHotRaw`. See docs above.
  let lt2 ← lessThan (minBits' len) startIdx lenF
  let combined ← FB.and lt1 lt2
  assert combined
  let startMask ← oneHotRaw len startIdx
  -- No need to use `singleEndArray`. In our case it's functionally the same as `oneHotRaw`
  let endMask ← oneHotRaw len endIdx
  let diffMask ← FArray.xor startMask endMask
  let false' ← FB.ofBool false
  diffMask.xorScan false'

namespace arraySelector

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

lemma convertsM
  [p.AtLeastTwo]
  {len : ℕ}
  {startIdx endIdx : F p}
  {state : ClapMState p}
  {startIdx_val endIdx_val : ZMod p}
  (h_startIdx : Converts F.conversion state startIdx startIdx_val)
  (h_endIdx : Converts F.conversion state endIdx endIdx_val)
  (h_len : len < p)
  (ha : startIdx_val.val < 2 ^ minBits' len) (hb : endIdx_val.val < 2 ^ minBits' len)
  (hw : 2 ^ (minBits' len + 1) < p)
:
  ConvertsM FArray.conversion (arraySelector len startIdx endIdx) state
    (Vector.ofFn (fun i : Fin len =>
      decide (startIdx_val.val ≤ i.val) ^^ decide (endIdx_val.val ≤ i.val)))
    (startIdx_val.val < len ∧ startIdx_val.val < endIdx_val.val)
:= by
  unfold arraySelector
  step lessThan.convertsM h_startIdx h_endIdx ha hb hw as lt1
  step mkF.convertsM as lenF
  have h_lenF_val : (len : ZMod p).val < 2 ^ minBits' len := by
    rw [ZMod.val_natCast_of_lt h_len]
    exact lt_two_pow_minBits' len
  step lessThan.convertsM h_startIdx h_lenF ha h_lenF_val hw as lt2
  step FB.and.convertsM h_lt1 h_lt2 as combined
  step assert.convertsM h_combined as assertStep
  step oneHotRaw.convertsM h_startIdx h_len as startMask
  step oneHotRaw.convertsM h_endIdx h_len as endMask
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
  . simp only [true_iff, true_implies]
    rw [Bool.and_eq_true_iff, decide_eq_true_eq, decide_eq_true_eq, ZMod.val_natCast_of_lt h_len]
    rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩
  . simp only [true_implies]
    rw [Bool.and_eq_true_iff, decide_eq_true_eq, decide_eq_true_eq, ZMod.val_natCast_of_lt h_len]
    rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩

lemma convertsM'
  [p.AtLeastTwo]
  {len : ℕ}
  {startIdx endIdx : F p}
  {state : ClapMState p}
  {startIdx_val endIdx_val : ZMod p}
  (h_startIdx : Converts F.conversion state startIdx startIdx_val)
  (h_endIdx : Converts F.conversion state endIdx endIdx_val)
  (h_len : len < p)
  (ha : startIdx_val.val < 2 ^ minBits' len) (hb : endIdx_val.val < 2 ^ minBits' len)
  (hw : 2 ^ (minBits' len + 1) < p)
  (h_idx : startIdx_val.val < endIdx_val.val)
:
  ConvertsM FArray.conversion (arraySelector len startIdx endIdx) state
    (Vector.ofFn (fun i : Fin len =>
      (startIdx_val.val ≤ i.val) && (i.val < endIdx_val.val))
    )
    (startIdx_val.val < len ∧ startIdx_val.val < endIdx_val.val)
:= by
  apply convertsM_of_convertsM (convertsM h_startIdx h_endIdx h_len ha hb hw)
  . ext i hi
    simp only [Vector.getElem_ofFn]
    by_cases hai : startIdx_val.val ≤ i <;> by_cases hib : i < endIdx_val.val <;>
      simp [hai, hib] <;> omega
  . exact Iff.rfl

end arraySelector

end arraySelector

end Clap.Lang
