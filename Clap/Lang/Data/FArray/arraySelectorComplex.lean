import Clap.Lang.Core.F.mkF
import Clap.Lang.Data.FArray.rightArraySelector
import Clap.Lang.Data.FArray.leftArraySelector
import Clap.Lang.Data.FArray.and
import Clap.Lang.Core.FB.and
import Clap.Lang.Core.FB.assert
import Clap.Lang.Core.FB.not

namespace Clap.Lang

variable {p : ℕ}


/-- Combines `rightArraySelector`/`leftArraySelector`/`FArray.and` via `convertsM_bind_and`, kept
as a standalone lemma (rather than inlined into `arraySelectorComplex.convertsM`) specifically so
its own elaboration doesn't have to carry the accumulated context of the `isZero`/`not`/`assert`/
`mkF`/`mkSub` steps that precede it there — combining `convertsM_bind_and` with the (recursively
defined) `rightArraySelector` inline behind that much prior `step`-context caused a severe
elaboration blowup (didn't finish even at 4,000,000 heartbeats); isolated like this it's fast. -/
private lemma rightArraySelector_and_leftArraySelector
  [p.AtLeastTwo]
  {len : ℕ}
  {idx endIdx : F p}
  {state : ClapMState p}
  {idx_val endIdx_val : ZMod p}
  (h_idx : Converts F.conversion state idx idx_val)
  (h_endIdx : Converts F.conversion state endIdx endIdx_val)
  (h_len : len < p)
:
  ConvertsM FArray.conversion
    (rightArraySelector len idx >>= fun rightBits =>
      leftArraySelector len endIdx >>= fun leftBits => rightBits.and leftBits)
    state
    (Vector.ofFn (fun i : Fin len => idx_val.val < i.val && i.val < endIdx_val.val))
    (idx_val.val < len ∧ endIdx_val.val < len)
:= by
  have h_right := rightArraySelector.convertsM h_idx h_len
  apply convertsM_bind_and h_right
  set right_state := (rightArraySelector len idx).getState state
  set right_result := (rightArraySelector len idx).getResult state.numAlloc state.σ
  have h_rightBits : Converts FArray.conversion right_state right_result
      (Vector.ofFn (fun i : Fin len => idx_val.val < i.val)) := h_right.result
  have h_endIdx' : Converts F.conversion right_state endIdx endIdx_val :=
    converts_skip h_right h_endIdx
  clear_value right_state right_result
  clear h_idx h_endIdx
  step leftArraySelector.convertsM h_endIdx' h_len as leftBits
  simp only [imp_self]
  apply convertsM_of_convertsM (FArray.and.convertsM h_rightBits h_leftBits)
  . ext i hi
    simp [Vector.getElem_ofFn]
  . rfl

def arraySelectorComplex [p.AtLeastTwo] (len : ℕ) (startIdx endIdx : F p) :
  ClapM p (FArray p len)
:= do
  assert (←not (←isZero startIdx))
  /- The author of the original circom circuit was not sure whether requiring
  (startIdx ≠ 0) is necessary beside for being able to decrement it.
  -/
  let one ← mkF 1
  let rightBits ← rightArraySelector len (←(startIdx - one))
  let leftBits ← leftArraySelector len endIdx
  rightBits.and leftBits

namespace arraySelectorComplex

lemma convertsM
  [p.AtLeastTwo]
  {len : ℕ}
  {startIdx endIdx : F p}
  {state : ClapMState p}
  {startIdx_val endIdx_val : ZMod p}
  (h_startIdx : Converts F.conversion state startIdx startIdx_val)
  (h_endIdx : Converts F.conversion state endIdx endIdx_val)
  (h_len : len < p)
  (h_idx : startIdx_val.val ≠ 0)
:
  ConvertsM FArray.conversion (arraySelectorComplex len startIdx endIdx) state
    (Vector.ofFn (fun i : Fin len =>
      (startIdx_val.val ≤ i.val) && (i.val < endIdx_val.val))
    )
    (0 < startIdx_val.val ∧ startIdx_val.val <= len ∧ endIdx_val.val < len)
:= by
  have h_val_sub : (startIdx_val - 1).val = startIdx_val.val - 1 := by
    have h1 : (1 : ZMod p).val = 1 := by
      haveI : Fact (1 < p) := ⟨Nat.AtLeastTwo.one_lt⟩
      exact ZMod.val_one p
    rw [ZMod.val_sub (by rw [h1]; omega), h1]
  unfold arraySelectorComplex
  step isZero.convertsM h_startIdx as isZeroStep
  clear_value isZeroStep isZeroStep_result isZeroStep_state
  step not.convertsM h_isZeroStep as notStep
  step assert.convertsM (by assumption) as bob
  · step mkF.convertsM as one
    step mkSub.convertsM h_startIdx h_one as sub
    simp only [true_implies]
    apply convertsM_of_convertsM (rightArraySelector_and_leftArraySelector h_sub h_endIdx h_len)
    . ext i hi
      simp only [Vector.getElem_ofFn]
      rw [h_val_sub]
      congr 1
      simp only [decide_eq_decide]
      omega
    . rw [h_val_sub]
      have hne : startIdx_val ≠ 0 := by
        intro h
        apply h_idx
        rw [h]
        simp
      constructor
      . rintro ⟨h1, h2⟩ _
        exact ⟨by omega, by omega, h2⟩
      . intro h
        have hassert : (!startIdx_val == 0) = true := by simp [hne]
        obtain ⟨_, h2, h3⟩ := h hassert
        exact ⟨by omega, h3⟩
  · simp
    intro start_ne_zero start_le_len end_lt_len
    assumption


end arraySelectorComplex

end Clap.Lang
