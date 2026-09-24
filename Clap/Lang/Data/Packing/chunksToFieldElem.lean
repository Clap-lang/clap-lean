import Clap.Lang.Core.Combinators.foldlM
import Clap.Lang.Core.F.mkAdd
import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkMul
import Clap.Lang.Core.FUnit.assert_eq
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.WitnessGenerator.toWg

namespace Clap.Lang.Packing

variable {p : ℕ}

section chunksToFieldElem

/-- The field element that little-endian chunks of `bitsPerChunk` bits denote,
`vals[0] + 2^bitsPerChunk * vals[1] + …`, in Horner form. The ideal value of
`chunksToFieldElem`, named so the specifications built on it stay readable. -/
def chunksToNum {w : ℕ} (bitsPerChunk : ℕ) (vals : Vector (ZMod p) w) : ZMod p :=
  vals.reverse.foldl (fun acc x ↦ x + 2 ^ bitsPerChunk * acc) 0

/-- Pack `w` chunks of `bitsPerChunk` bits into one field element, chunk `0` least significant. -/
def chunksToFieldElem {w : ℕ} (bitsPerChunk : ℕ) (chunks : FVec p w) : ClapM p (F p) := do
  let acc0 ← mkF 0
  chunks.reverse.foldlM (fun acc x ↦ do
    let base ← mkF (2 ^ bitsPerChunk)
    let shifted ← base * acc
    x + shifted) acc0

namespace chunksToFieldElem

private lemma step_convertsM
  {bitsPerChunk : ℕ}
  {state : ClapMState p}
  {acc x : F p}
  {acc_val x_val : ZMod p}
  (h_acc : Converts F.conversion state acc acc_val)
  (h_x : Converts F.conversion state x x_val)
:
  ConvertsM F.conversion
    (do
      let base ← mkF (2 ^ bitsPerChunk)
      let shifted ← base * acc
      x + shifted)
    state (x_val + 2 ^ bitsPerChunk * acc_val) True
:= by
  step mkF.convertsM as base
  step mkMul.convertsM h_base h_acc as shifted
  apply convertsM_of_convertsM (mkAdd.convertsM h_x h_shifted)
  . rfl
  . trivial

lemma convertsM
  {w bitsPerChunk : ℕ}
  {state : ClapMState p}
  {chunks : FVec p w}
  {vals : Vector (ZMod p) w}
  (h_chunks : Converts FVec.conversion state chunks vals)
:
  ConvertsM F.conversion (chunksToFieldElem bitsPerChunk chunks) state
    (chunksToNum bitsPerChunk vals) True
:= by
  unfold chunksToFieldElem

  step mkF.convertsM as acc0

  have h_elems : ∀ i : Fin w,
      Converts F.conversion acc0_state chunks.reverse[i] vals.reverse[i] :=
    fun i ↦ FVec.converts_getElem (FVec.converts_reverse h_chunks) i.isLt

  apply convertsM_of_convertsM
    (convertsM_foldlM
      (f_spec := fun (acc x : ZMod p) ↦ x + 2 ^ bitsPerChunk * acc)
      h_elems h_acc0 step_convertsM)
  . rfl
  . trivial

end chunksToFieldElem

end chunksToFieldElem

section examples

private abbrev q : ℕ := 1031

local instance instFactPrimeChunksToFieldElemQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def check {w : ℕ} (b : ℕ) (chunks : Vector (ZMod q) w) (expected : ZMod q) :
    ClapM q Unit := do
  let cs ← chunks.mapM mkF
  let r ← chunksToFieldElem b cs
  assert_eq r (← mkF expected)

private def sat {w : ℕ} (b : ℕ) (chunks : Vector (ZMod q) w) (expected : ZMod q) : Bool :=
  let c := check b chunks expected
  let circ  := c.getCircuit 0 (HashConsSt.empty q)
  let cache := c.getHashConsState 0 (HashConsSt.empty q)
  (circ.toCs cache 0).run ((circ.toWg cache 0).run #v[])

example : sat 2 #v[] 0 = true := by native_decide
-- `[00₂, 11₂, 10₂] ↦ 101100₂`
example : sat 2 #v[0, 3, 2] 44 = true := by native_decide
example : sat 2 #v[0, 3, 2] 45 = false := by native_decide

end examples

end Clap.Lang.Packing
