import Clap.Lang.Combinators.foldlM
import Clap.Lang.F.mkAdd
import Clap.Lang.F.mkF
import Clap.Lang.F.mkMul

namespace Clap.Lang.FArray

variable {p : ℕ}

section bits2num

/--
The field element a `Bool` vector denotes, LSB first.

This is exactly the ideal value of `bits2num` below, named so that the specifications built on
top of it (`FBitVec.binSum`, `F32.add`) stay readable.
-/
def toNum {w : ℕ} (bits : Vector Bool w) : ZMod p :=
  bits.reverse.foldl (fun acc b ↦ (if b then (1 : ZMod p) else 0) + 2 * acc) 0

/--
The field element a bit vector denotes, LSB first.
-/
def bits2num {w : ℕ} (bits : FArray p w) : ClapM p (F p) := do
  let acc0 ← mkF 0
  bits.reverse.foldlM (fun acc b ↦ do mkAdd b (←mkMul (←mkF 2) acc)) acc0

namespace bits2num

private lemma step_convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {acc : F p}
  {acc_val : ZMod p}
  {b : FB p}
  {b_val : Bool}
  (h_acc : Converts F.conversion state acc acc_val)
  (h_b : Converts FB.conversion state b b_val)
:
  ConvertsM F.conversion (do mkAdd b (←mkMul (←mkF 2) acc)) state
    ((if b_val then (1 : ZMod p) else 0) + 2 * acc_val) True
:= by
  have h_b_f := F.converts_of_FB_converts h_b
  step mkF.convertsM as two
  step mkMul.convertsM h_two h_acc as prod
  apply convertsM_of_convertsM (mkAdd.convertsM h_b_f h_prod)
  . rfl
  . trivial

lemma convertsM
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {bits : FArray p w}
  {bits_val : Vector Bool w}
  (h_bits : Converts FArray.conversion state bits bits_val)
:
  ConvertsM F.conversion (bits2num bits) state (toNum bits_val) True
:= by
  unfold bits2num

  step mkF.convertsM as acc0

  have h_elems : ∀ i : Fin w,
      Converts FB.conversion acc0_state bits.reverse[i] bits_val.reverse[i] :=
    fun i ↦ FArray.converts_getElem (FArray.converts_reverse h_bits) i.isLt

  apply convertsM_of_convertsM
    (convertsM_foldlM
      (f_spec := fun (acc : ZMod p) (b : Bool) ↦ (if b then (1 : ZMod p) else 0) + 2 * acc)
      h_elems h_acc0 step_convertsM)
  . rfl
  . trivial

end bits2num
end bits2num

end Clap.Lang.FArray
