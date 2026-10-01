import Clap.Lang.Core.F.mkAdd
import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkMul
import Clap.Lang.Core.Combinators.foldlM

namespace Clap.Lang.FBitVec

variable {p : ℕ}

section bits2numV

/-- The field element a bit vector denotes, LSB first — same convention as `FArray.bits2num`,
computed with a right fold over the vector instead of a left fold over its reverse. -/
def bits2numV {w} (bits : FBitVec p w) : ClapM p (F p) := do
  let zeroF ← mkF 0
  bits.foldrM go zeroF
 where
  go (b : FB p) (acc : F p) : ClapM p (F p) := do
    let two ← mkF 2
    let accTwice ← two * acc
    b + accTwice

namespace bits2numV

/-- `(BitVec.ofBoolListLE l).toFin`, cast into `ZMod p`, is the same little-endian weighted sum
that `bits2numV`'s per-step `go` builds up. -/
private lemma toFin_ofBoolListLE_eq (l : List Bool) :
    ((BitVec.ofBoolListLE l).toFin.val : ZMod p) =
      l.foldr (fun b acc ↦ (if b then (1 : ZMod p) else 0) + 2 * acc) 0
:= by
  induction l with
  | nil => simp [BitVec.ofBoolListLE]
  | cons b bs ih =>
    simp only [BitVec.ofBoolListLE, BitVec.val_toFin, BitVec.toNat_concat, List.foldr_cons]
    push_cast
    rw [← ih]
    cases b <;> simp [Bool.toNat] <;> ring

lemma convertsM
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {bits : FBitVec p w}
  {bits_vals : Vector Bool w}
  (h_bits : Converts FArray.conversion state bits bits_vals)
:
  ConvertsM F.conversion (bits2numV bits) state
    (BitVec.ofBoolListLE bits_vals.toList).toFin
    True
:= by
  unfold bits2numV

  step mkF.convertsM as zeroF

  rw [show bits.foldrM go zeroF_result = bits.reverse.foldlM (fun acc b ↦ go b acc) zeroF_result
      from (Vector.foldlM_reverse (f := fun acc b ↦ go b acc)).symm]

  have h_elems : ∀ i : Fin w,
      Converts FB.conversion zeroF_state bits.reverse[i] bits_vals.reverse[i] :=
    fun i ↦ FArray.converts_getElem (FArray.converts_reverse h_bits) i.isLt

  apply convertsM_of_convertsM
    (convertsM_foldlM
      (f_spec := fun (acc : ZMod p) (b : Bool) ↦ (if b then (1 : ZMod p) else 0) + 2 * acc)
      h_elems h_zeroF
      (fun {state' acc acc_val x x_val} h_acc h_x ↦ by
        clear h_bits h_zeroF
        unfold go
        have h_x_f := F.converts_of_FB_converts h_x
        step mkF.convertsM as two
        step mkMul.convertsM h_two h_acc as prod
        apply convertsM_of_convertsM (mkAdd.convertsM h_x_f h_prod)
        . rfl
        . trivial))
  . have h_fold : bits_vals.foldr (fun (b : Bool) (acc : ZMod p) ↦ (if b then (1 : ZMod p) else 0) + 2 * acc) 0
                = bits_vals.reverse.foldl (fun acc b ↦ (if b then (1 : ZMod p) else 0) + 2 * acc) 0 :=
      Vector.foldr_eq_foldl_reverse (f := fun (b : Bool) (acc : ZMod p) ↦ (if b then (1 : ZMod p) else 0) + 2 * acc)
    rw [toFin_ofBoolListLE_eq, ← h_fold, Vector.foldr_toList]
  . trivial

end bits2numV

end bits2numV

end Clap.Lang.FBitVec
