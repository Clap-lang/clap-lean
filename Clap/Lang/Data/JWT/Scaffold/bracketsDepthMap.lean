import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkSub
import Clap.Lang.Core.F.conditionalSwap
import Clap.Lang.Core.FB.eq
import Clap.Lang.Gate.isZero

namespace Clap.Lang

variable {p : ℕ}

namespace bracketsDepthMap

/-- The prefix-sum scan's entry `i` is exactly `depth`'s `(v.take i).sum`. -/
lemma scanl_eq_take_sum {n} (v : Vector (ZMod p) n) (i : ℕ) (hi : i < n) :
    (Vector.scanl (· + ·) (0 : ZMod p) v)[i] = (v.take i).sum := by
  rw [Vector.getElem_scanl, ← List.sum_eq_foldl, ← Vector.toList_take, Vector.sum_toList]

lemma depthStep_convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {bs : F p × F p}
  {c_val s_val : ZMod p}
  (h_bs : Converts FPair.conversion state bs (c_val, s_val))
:
  ConvertsM F.conversion
    (do
      let negOne ← mkF (-1)
      let isClose ← eq bs.1 negOne
      let one ← mkF 1
      let sMinus1 ← mkSub bs.2 one
      conditionalSwap isClose sMinus1 bs.2)
    state
    (if c_val == -1 then s_val - 1 else s_val)
    True
:= by
  have h_c := FPair.converts_fst h_bs
  have h_s := FPair.converts_snd h_bs
  step mkF.convertsM as negOne
  step eq.convertsM h_c h_negOne as isClose
  step mkF.convertsM as one
  step mkSub.convertsM h_s h_one as sMinus1
  apply convertsM_of_convertsM (conditionalSwap.convertsM h_isClose h_sMinus1 h_s)
  · simp
  · simp

lemma ignoreOutermost_step_convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {d : F p}
  {d_val : ZMod p}
  (h_d : Converts F.conversion state d d_val)
:
  ConvertsM F.conversion
    (do
      let isZ ← isZero d
      let one ← mkF 1
      let dMinus1 ← mkSub d one
      let zeroF ← mkF 0
      conditionalSwap isZ zeroF dMinus1)
    state
    (if d_val == 0 then 0 else d_val - 1)
    True
:= by
  step isZero.convertsM h_d as isZ
  step mkF.convertsM as one
  step mkSub.convertsM h_d h_one as dMinus1
  step mkF.convertsM as zeroF
  apply convertsM_of_convertsM (conditionalSwap.convertsM h_isZ h_zeroF h_dMinus1)
  · simp
  · simp

end bracketsDepthMap

end Clap.Lang
