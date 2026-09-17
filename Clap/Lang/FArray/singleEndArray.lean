import Clap.Lang.FArray.OneHotRaw
import Clap.Lang.FArray.singleOneArray
import Clap.Lang.FArray.sum
import Clap.Lang.F.mkMul
import Clap.Lang.FUnit.assert_eq

namespace Clap.Lang

variable {p : ℕ}

section singleEndArray

/-- One-hot mask at `idx`, but never fails: returns all-zeros when `idx ≥ len` instead of being
unsatisfiable (unlike `singleOneArray`). Ports `SingleNegOneArray` (`Clap/Array.lean:22-27`). -/
def singleEndArray [p.AtLeastTwo] (len : ℕ) (idx : F p) : ClapM p (FArray p len) := do
  let out ← oneHotRaw len idx
  let s : F p ← out.sum
  let sSq ← mkMul s s
  assert_eq s sSq
  return out

namespace singleEndArray

lemma sum_ofFn_ite_mem_zero_one
  {k n : ℕ}
:
  (Vector.ofFn (fun x : Fin k => if x.val = n then (1 : ZMod p) else 0)).sum = 0 ∨
  (Vector.ofFn (fun x : Fin k => if x.val = n then (1 : ZMod p) else 0)).sum = 1
:= by
  induction k with
  | zero =>
    left
    have : (Vector.ofFn (fun x : Fin 0 => if x.val = n then (1 : ZMod p) else 0)) = #v[] := by
      ext i hi
      omega
    simp [this]
  | succ k ih =>
    rw [Vector.ofFn_succ, Vector.sum_push]
    by_cases h : n = k
    . right
      have hcast :
          (Vector.ofFn (fun i : Fin k => if i.castSucc.val = n then (1 : ZMod p) else 0))
            = Vector.ofFn (fun _ : Fin k => (0 : ZMod p)) := by
        ext i hi
        simp only [Vector.getElem_ofFn]
        have : ¬ (i = n) := by omega
        simp [this]
      have hzero : (Vector.ofFn (fun _ : Fin k => (0 : ZMod p))).sum = 0 :=
        singleOneArray.Vector.sum_ofFn_eq_zero_of_eq_zero (fun _ => rfl)
      have hpos : (k = n) := by omega
      rw [hcast, hzero, if_pos hpos]
      ring
    . rcases ih with ih | ih
      . left
        have hcast :
            (Vector.ofFn (fun i : Fin k => if i.castSucc.val = n then (1 : ZMod p) else 0))
              = Vector.ofFn (fun i : Fin k => if i.val = n then (1 : ZMod p) else 0) := by
          ext i hi
          simp
        have hneg : ¬ (k = n) := by omega
        rw [hcast, ih, if_neg hneg]
        ring
      . right
        have hcast :
            (Vector.ofFn (fun i : Fin k => if i.castSucc.val = n then (1 : ZMod p) else 0))
              = Vector.ofFn (fun i : Fin k => if i.val = n then (1 : ZMod p) else 0) := by
          ext i hi
          simp
        have hneg : ¬ (k = n) := by omega
        rw [hcast, ih, if_neg hneg]
        ring

lemma sum_ofFn_beq_mem_zero_one
  {k n : ℕ}
:
  (Vector.map (fun x => if x = true then (1 : ZMod p) else 0)
    (Vector.ofFn fun x : Fin k => x.val == n)).sum = 0 ∨
  (Vector.map (fun x => if x = true then (1 : ZMod p) else 0)
    (Vector.ofFn fun x : Fin k => x.val == n)).sum = 1
:= by
  have heq :
      (Vector.map (fun x => if x = true then (1 : ZMod p) else 0)
        (Vector.ofFn fun x : Fin k => x.val == n))
        = Vector.ofFn (fun x : Fin k => if x.val = n then (1 : ZMod p) else 0) := by
    ext i hi
    simp [Function.comp, beq_iff_eq]
  rw [heq]
  exact sum_ofFn_ite_mem_zero_one

lemma convertsM
  [p.AtLeastTwo]
  {len : ℕ}
  {idx : F p}
  {state}
  {idx_val : ZMod p}
  (h_idx : Converts F.conversion state idx idx_val)
  (h_len : len < p)
:
  ConvertsM FArray.conversion (singleEndArray len idx) state
    (Vector.ofFn (λ x => x.val == idx_val.val)) True
:= by
  unfold singleEndArray

  step oneHotRaw.convertsM h_idx h_len as oneHot
  step FArray.sum.convertsM h_oneHot as sum
  step mkMul.convertsM h_sum h_sum as sSq
  step assert_eq.convertsM h_sum h_sSq as assert_eq
  apply convertsM_pure
  . exact h_oneHot
  . simp
  . simp only [true_implies]
    rcases sum_ofFn_beq_mem_zero_one (n := idx_val.val) (k := len) with h | h <;>
      rw [h] <;> ring

end singleEndArray

end singleEndArray

end Clap.Lang
