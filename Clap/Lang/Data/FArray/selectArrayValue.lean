import Clap.Lang.Core.F.dotProduct
import Clap.Lang.Data.FArray.singleOneArray

namespace Clap.Lang

variable {p : ℕ}

/-- Returns the element of `arr` at index `idx`. Fails when `idx ≥ len`. -/
def selectArrayValue [p.AtLeastTwo] (len : ℕ)
  (arr : FVec p len)
  (idx : F p) :
  ClapM p (F p)
:= do
  let hot ← singleOneArray len idx
  dotProduct hot arr

namespace selectArrayValue

/-- The dot product of a one-hot vector against `a_val` picks out `a_val` at the hot position,
defaulting to `0` out of range. True unconditionally: out of range, every position of the
one-hot vector is `0` and `Vector.getD` also returns its default `0`. -/
private lemma sum_ofFn_ite_mul_eq_getD
  {len : ℕ} (idx : ℕ) (a_val : Vector (ZMod p) len)
:
  ((Vector.ofFn (fun x : Fin len => if (x.val == idx : Bool) then (1:ZMod p) else 0)).zip a_val).foldl
    (fun acc xy ↦ acc + xy.1 * xy.2) 0
  = a_val.getD idx 0
:= by
  have h1 :
    ((Vector.ofFn (fun x : Fin len => if (x.val == idx:Bool) then (1:ZMod p) else 0)).zip a_val).foldl
      (fun acc xy ↦ acc + xy.1 * xy.2) 0
    = ((Vector.ofFn (fun x : Fin len => if (x.val == idx:Bool) then (1:ZMod p) else 0)).zipWith (· * ·) a_val).sum := by
    rw [Vector.sum_eq_foldl, Vector.zipWith_foldl_eq_zip_foldl]
  rw [h1]
  have h1' : (Vector.ofFn (fun x : Fin len => if (x.val == idx:Bool) then (1:ZMod p) else 0)).zipWith (· * ·) a_val
      = Vector.ofFn (fun x : Fin len => (if (x.val == idx:Bool) then (1:ZMod p) else 0) * a_val[x]) := by
    ext i hi
    simp
  rw [h1']
  by_cases h : idx < len
  · have h2 : (fun x : Fin len => (if (x.val == idx:Bool) then (1:ZMod p) else 0) * a_val[x])
         = (fun x : Fin len => if x = (⟨idx, h⟩ : Fin len) then a_val[x] else 0) := by
      funext x
      by_cases hx : x = (⟨idx,h⟩ : Fin len)
      · simp [hx]
      · have hxv : x.val ≠ idx := by
          intro hh; apply hx; exact Fin.ext hh
        simp [hxv, hx]
    rw [h2, ←Vector.sum_toList, Vector.toList_ofFn, List.sum_ofFn, Fintype.sum_ite_eq']
    simp [Vector.getD, h]
  · have h2 : (fun x : Fin len => (if (x.val == idx:Bool) then (1:ZMod p) else 0) * a_val[x])
         = (fun _ : Fin len => (0:ZMod p)) := by
      funext x
      have hxv : x.val ≠ idx := by have := x.isLt; omega
      simp [hxv]
    rw [h2, ←Vector.sum_toList, Vector.toList_ofFn, List.sum_ofFn]
    have hgetD : a_val.getD idx 0 = 0 := by simp [Vector.getD, h]
    rw [hgetD]
    exact Finset.sum_const_zero

lemma convertsM [p.AtLeastTwo] {len : ℕ}
  {a : FVec p len}
  {idx : F p}
  {a_val : Vector (ZMod p) len}
  {idx_val : ZMod p}
  {state}
  (h_idx : Converts F.conversion state idx idx_val)
  (h_a : Converts FVec.conversion state a a_val)
  (h_len : len < p)
:
  ConvertsM F.conversion (selectArrayValue len a idx) state
    (a_val.getD idx_val.val 0)
    (idx_val.val < len)
:= by
  unfold selectArrayValue
  step singleOneArray.convertsM h_idx h_len as hot
  have h_hot_fvec := FVec.converts_of_FArray_converts h_hot
  rw [Vector.map_ofFn] at h_hot_fvec
  apply convertsM_of_convertsM (dotProduct.convertsM h_hot_fvec h_a)
  . exact sum_ofFn_ite_mul_eq_getD idx_val.val a_val
  . exact ⟨fun _ h => h, fun _ => trivial⟩

end selectArrayValue
