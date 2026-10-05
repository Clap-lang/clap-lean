import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkSub
import Clap.Lang.Core.F.conditionalSwap
import Clap.Lang.Core.FB.eq
import Clap.Lang.Gate.isZero
import Clap.Lang.Core.Combinators.scanlM
import Clap.Lang.Core.Combinators.mapM
namespace Clap.Lang

variable {p : ℕ}

/--
  Given an input array `input` of length `w` containing `1`s corresponding to open
  brackets `{`, `-1`s corresponding to closed brackets `}`, and 0s everywhere else, outputs an array
  containing a positive integer in each index between nested brackets which indicates the depth
  of the brackets nesting at that index, and 0 everywhere else. The outermost open and
  closed bracket are both ignored. The open and closed brackets are not considered to be inside
  their bracketed area. It is assumed that the input will contain an equal
  number of closed and open brackets, and that a closed bracket will not appear while there are no unclosed open brackets

  Example input/output for the entire subcircuit
  To preserve alignment, we use * to represent -1:
  str:           a{aaa{a{aaa}aa}aaaa}
  input:         01000101000*00*0000*
  out:           00000011222111000000   correctly represents open brackets as being outside of bracket nesting

-/

def bracketsDepthMap [p.AtLeastTwo] {w} (input : FVec p w) : ClapM p (FVec p w) := do
  let start ← mkF 0
  let sums ← Vector.scanlM (fun acc x ↦ mkAdd acc x) start input
  let depths ← (input.zip sums).mapM (fun bs ↦ do
    let negOne ← mkF (-1)
    let isClose ← eq bs.1 negOne
    let one ← mkF 1
    let sMinus1 ← mkSub bs.2 one
    conditionalSwap isClose sMinus1 bs.2)
  depths.mapM (fun d ↦ do
    let isZ ← isZero d
    let one ← mkF 1
    let dMinus1 ← mkSub d one
    let zeroF ← mkF 0
    conditionalSwap isZ zeroF dMinus1)

namespace bracketsDepthMap

/-- Depth at index `i`. -/
private def depth {n} (v : Vector (ZMod p) n) (i : Fin n) : ZMod p :=
  let s := (v.take i).sum
  if v[i] == -1 then s - 1 else s

/-- Depth at index `i` ignoring outermost brackets . -/
private def depthIgnoringOutermostBrackets {n}
  (v : Vector (ZMod p) n)
  (i : Fin n) :
  ZMod p
:=
  let d := depth v i
  if d == 0 then 0 else d - 1

/-- The prefix-sum scan's entry `i` is exactly `depth`'s `(v.take i).sum`. -/
private lemma scanl_eq_take_sum {n} (v : Vector (ZMod p) n) (i : ℕ) (hi : i < n) :
    (Vector.scanl (· + ·) (0 : ZMod p) v)[i] = (v.take i).sum := by
  rw [Vector.getElem_scanl, ← List.sum_eq_foldl, ← Vector.toList_take, Vector.sum_toList]

private lemma depthStep_convertsM
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

private lemma ignoreOutermost_step_convertsM
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

lemma convertsM
  [p.AtLeastTwo]
  {k}
  {state : ClapMState p}
  {a : FVec p k}
  {a_val : Vector (ZMod p) k}
  (h_a : Converts FVec.conversion state a a_val)
:
  ConvertsM FVec.conversion (bracketsDepthMap a) state
    (Vector.ofFn fun i ↦ depthIgnoringOutermostBrackets a_val i)
    True
:= by
  unfold bracketsDepthMap
  step mkF.convertsM as start
  step (convertsM_scanlM (FVec.converts_iff_F_converts.mp h_a) h_start
          (fun h_acc h_x ↦ mkAdd.convertsM h_acc h_x)) as sums
  step (convertsM_mapM (C_elem := FPair.conversion)
          (f_spec := fun bs ↦ if bs.1 == (-1 : ZMod p) then bs.2 - 1 else bs.2)
          (fun i ↦ FVec.converts_zip h_a h_sums i.isLt)
          (fun h_bs ↦ depthStep_convertsM h_bs)) as depths
  apply convertsM_of_convertsM
    (convertsM_mapM (C_elem := F.conversion)
      (f_spec := fun d ↦ if d == (0 : ZMod p) then 0 else d - 1)
      (FVec.converts_iff_F_converts.mp h_depths)
      (fun h_d ↦ ignoreOutermost_step_convertsM h_d))
  · apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_zip, Vector.getElem_ofFn]
    rw [scanl_eq_take_sum a_val i hi]
    simp [depthIgnoringOutermostBrackets, depth]
  · trivial

end bracketsDepthMap

end Clap.Lang
