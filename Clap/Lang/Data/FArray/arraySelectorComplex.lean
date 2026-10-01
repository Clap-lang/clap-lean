import Clap.Lang.Core.F.mkF
import Clap.Lang.Data.FArray.rightArraySelector
import Clap.Lang.Data.FArray.leftArraySelector
import Clap.Lang.Data.FArray.and
import Clap.Lang.Core.FB.and
import Clap.Lang.Core.FB.assert
import Clap.Lang.Core.FB.not
import Clap.Lang.Data.FArray.assert_eq
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.WitnessGenerator.toWg

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

/-- Everything after the `startIdx ≠ 0` assertion. -/
def arraySelectorComplex.tail [p.AtLeastTwo] (len : ℕ) (startIdx endIdx : F p) :
  ClapM p (FArray p len)
:= do
  let one ← mkF 1
  let rightBits ← rightArraySelector len (←(startIdx - one))
  let leftBits ← leftArraySelector len endIdx
  rightBits.and leftBits

/-- Bit array with 1s at `[startIdx, endIdx)`, all 0s when `endIdx ≤ startIdx`. Circom's
`ArraySelectorComplex`: `RightArraySelector(startIdx - 1)` and `LeftArraySelector(endIdx)`, after
asserting `startIdx ≠ 0`. -/
def arraySelectorComplex [p.AtLeastTwo] (len : ℕ) (startIdx endIdx : F p) :
  ClapM p (FArray p len)
:= do
  assert (←not (←isZero startIdx))
  /- The author of the original circom circuit was not sure whether requiring
  (startIdx ≠ 0) is necessary beside for being able to decrement it.
  -/
  arraySelectorComplex.tail len startIdx endIdx

namespace arraySelectorComplex

lemma tail_convertsM
  [p.AtLeastTwo]
  {len : ℕ}
  {startIdx endIdx : F p}
  {state : ClapMState p}
  {startIdx_val endIdx_val : ZMod p}
  (h_startIdx : Converts F.conversion state startIdx startIdx_val)
  (h_endIdx : Converts F.conversion state endIdx endIdx_val)
  (h_len : len < p)
:
  ConvertsM FArray.conversion (tail len startIdx endIdx) state
    (Vector.ofFn (fun i : Fin len =>
      (startIdx_val - 1).val < i.val && i.val < endIdx_val.val))
    ((startIdx_val - 1).val < len ∧ endIdx_val.val < len)
:= by
  unfold tail
  step mkF.convertsM as one
  step mkSub.convertsM h_startIdx h_one as sub
  simp only [true_implies]
  exact rightArraySelector_and_leftArraySelector h_sub h_endIdx h_len

/-- The value holds for every input. At `startIdx = 0` the decrement wraps to `p - 1`, the right
mask is all zero, and so is the output; slot 5 rules that input out, as the circuit asserts
`startIdx ≠ 0`. -/
lemma convertsM
  [p.AtLeastTwo]
  {len : ℕ}
  {startIdx endIdx : F p}
  {state : ClapMState p}
  {startIdx_val endIdx_val : ZMod p}
  (h_startIdx : Converts F.conversion state startIdx startIdx_val)
  (h_endIdx : Converts F.conversion state endIdx endIdx_val)
  (h_len : len < p)
:
  ConvertsM FArray.conversion (arraySelectorComplex len startIdx endIdx) state
    (Vector.ofFn (fun i : Fin len =>
      decide (0 < startIdx_val.val ∧ startIdx_val.val ≤ i.val) && (i.val < endIdx_val.val)))
    (0 < startIdx_val.val ∧ startIdx_val.val <= len ∧ endIdx_val.val < len)
:= by
  haveI : Fact (1 < p) := ⟨Nat.AtLeastTwo.one_lt⟩
  have h1 : (1 : ZMod p).val = 1 := ZMod.val_one p
  -- `(s - 1).val`: `s.val - 1` when `s ≠ 0`, `p - 1` when `s = 0`
  have h_dec : (startIdx_val - 1).val = if startIdx_val = 0 then p - 1 else startIdx_val.val - 1 := by
    split
    · rename_i h0
      subst h0
      rw [zero_sub, ZMod.neg_val, if_neg one_ne_zero, h1]
    · rename_i h0
      have hpos : 0 < startIdx_val.val := by
        rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]; exact h0
      rw [ZMod.val_sub (by rw [h1]; omega), h1]
  unfold arraySelectorComplex
  step isZero.convertsM h_startIdx as isZeroStep
  step not.convertsM h_isZeroStep as notStep
  -- The assertion and the selectors both constrain, so `convertsM_bind_and`, not `step`.
  have hA := assert.convertsM h_notStep
  have hT := tail_convertsM (converts_skip hA h_startIdx) (converts_skip hA h_endIdx) h_len
  apply convertsM_of_convertsM
    (convertsM_bind_and (function := fun _ ↦ tail len startIdx endIdx) hA hT)
  · ext i hi
    simp only [Vector.getElem_ofFn, h_dec]
    by_cases h0 : startIdx_val = 0
    · subst h0
      simp only [if_true, ZMod.val_zero, lt_self_iff_false, false_and, decide_false,
        Bool.false_and]
      simp only [decide_eq_false_iff_not, not_lt, Bool.and_eq_false_iff]
      left
      omega
    · have hpos : 0 < startIdx_val.val := by
        rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]; exact h0
      simp only [h0, if_false]
      congr 1
      simp only [decide_eq_decide]
      omega
  · simp only [true_implies, h_dec, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
    by_cases h0 : startIdx_val = 0
    · subst h0
      simp
    · have hpos : 0 < startIdx_val.val := by
        rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]; exact h0
      simp only [h0, if_false, not_false_eq_true, true_and]
      constructor
      · rintro ⟨h2, h3⟩
        exact ⟨hpos, by omega, h3⟩
      · rintro ⟨-, h2, h3⟩
        exact ⟨by omega, h3⟩

end arraySelectorComplex

section examples

/-! The old model's vectors (`old/Clap/Array.lean`), run end to end. -/

private abbrev q : ℕ := 47

local instance instFactPrimeArraySelectorComplexQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def runSat (c : ClapM q Unit) : Bool :=
  let circ  := c.getCircuit 0 (HashConsSt.empty q)
  let cache := c.getHashConsState 0 (HashConsSt.empty q)
  (circ.toCs cache 0).run ((circ.toWg cache 0).run #v[])

private def checkBits {n} (g : ClapM q (FArray q n)) (e : Vector Bool n) : ClapM q Unit := do
  let r ← g
  let e' ← e.mapM FB.ofBool
  FArray.assert_eq r e'

private def csel (len : ℕ) (s e : ZMod q) (out : Vector Bool len) : Bool :=
  runSat (checkBits (do arraySelectorComplex len (← mkF s) (← mkF e)) out)

example : csel 4 1 2 #v[false, true, false, false] = true := by native_decide
example : csel 4 2 3 #v[false, false, true, false] = true := by native_decide
example : csel 4 1 3 #v[false, true, true, false] = true := by native_decide
example : csel 4 2 1 #v[false, false, false, false] = true := by native_decide
example : csel 4 1 3 #v[false, true, false, false] = false := by native_decide
example : csel 4 0 2 #v[false, false, false, false] = false := by native_decide
example : csel 4 0 2 #v[true, true, false, false] = false := by native_decide
example : csel 4 1 4 #v[false, true, true, true] = false := by native_decide

end examples

end Clap.Lang
