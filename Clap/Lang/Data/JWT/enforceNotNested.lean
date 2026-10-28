import Clap.Lang.Core.F.dotProduct
import Clap.Lang.Data.FArray.arraySelector
import Clap.Lang.Data.JWT.Scaffold.enforceNotNested

namespace Clap.Lang

variable {p : ℕ}

/-- Given `bracketsDepthMap`, the nested-brackets depth at every index of the original JWT, and
a `startIndex`/`fieldLen` pair demarking a parsed field, enforce that no index of that field sits
inside nested brackets. -/
def enforceNotNested [p.AtLeastTwo]
  {len : ℕ}
  (startIndex fieldLen : F p)
  (bracketsDepthMap : FVec p len) :
  ClapM p Unit
:= do
  let endIndex ← startIndex + fieldLen
  let bracketsSelector : FVec p len ← arraySelector len startIndex endIndex
  let o ← dotProduct bracketsDepthMap bracketsSelector
  eq0 o

namespace enforceNotNested

lemma convertsM
  [p.AtLeastTwo]
  {len : ℕ}
  {state : ClapMState p}
  {startIdx fieldLen : F p}
  {startIdx_val fieldLen_val : ZMod p}
  {a : FVec p len}
  {a_vals : Vector (ZMod p) len}
  (h_startIdx : Converts F.conversion state startIdx startIdx_val)
  (h_fieldLen : Converts F.conversion state fieldLen fieldLen_val)
  (h_a : Converts FVec.conversion state a a_vals)
  (h_len : len < p)
  (hw : 2 ^ (minBits' len + 1) < p)
:
  ConvertsM FUnit.conversion
    (enforceNotNested startIdx fieldLen a)
    state
    ()
    ( (startIdx_val + fieldLen_val).val < 2 ^ minBits' len ∧
      startIdx_val.val < len ∧
      startIdx_val.val < (startIdx_val + fieldLen_val).val ∧
      (a_vals.extract startIdx_val.val (startIdx_val + fieldLen_val).val).sum = 0
    )
:= by
  unfold enforceNotNested
  step mkAdd.convertsM h_startIdx h_fieldLen as endIndex
  have h_as := arraySelector.convertsM h_startIdx h_endIndex h_len hw
  have h_bind := arraySelector_tail_convertsM h_as h_a
  apply convertsM_of_convertsM h_bind
  · rfl
  · have h_eq : startIdx_val.val ≤ (startIdx_val + fieldLen_val).val →
      (a_vals.zip ((Vector.ofFn (fun i : Fin len =>
          decide (startIdx_val.val ≤ i.val) ^^ decide ((startIdx_val + fieldLen_val).val ≤ i.val))).map
            (fun b => if b then (1 : ZMod p) else 0))).foldl (fun acc xy => acc + xy.1 * xy.2) 0
        = (a_vals.extract startIdx_val.val (startIdx_val + fieldLen_val).val).sum := by
      intro h_idx
      rw [dotProduct.foldl_eq_sum, zero_add, extract_sum_eq_window_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_map]
      exact xor_mask_mul_eq_window_ite h_idx a_vals i
    simp only [true_implies]
    grind

end enforceNotNested

end Clap.Lang
