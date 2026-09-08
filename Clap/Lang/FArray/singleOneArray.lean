import Clap.Lang.FArray.OneHotRaw
import Clap.Lang.FArray.sum
import Clap.Lang.FUnit.assert_eq
import Clap.Lang.F.mkF

namespace Clap.Lang

variable {p : ℕ}

section singleOneArray

/-- Returns a one-hot bit mask of length `len` with a 1 at index `idx` and 0s elsewhere. Only satisfiable when `0 ≤ idx < len`. -/
def singleOneArray [p.AtLeastTwo] (len : ℕ) (idx : F) : ClapM p (FArray len) := do
  let out ← oneHotRaw len idx
  let s : F ← out.sum
  assert_eq s (←mkF 1)
  return out

namespace singleOneArray

lemma Vector.sum_ofFn_eq_zero_of_eq_zero
  {k}
  {f : Fin k → ZMod p}
  (h : ∀ x : Fin k, f x = 0)
:
  (Vector.ofFn f).sum = 0
:= by
  rw [
    ←Vector.sum_toList,
    Vector.toList_ofFn,
    List.sum_eq_zero
  ]
  grind

lemma convertsM
  [p.AtLeastTwo]
  {len : ℕ}
  {idx : F}
  {state}
  {idx_val : ZMod p}
  (h_idx : Converts F.conversion state idx idx_val)
  (h_len : len < p)
:
  ConvertsM FArray.conversion (singleOneArray len idx) state (Vector.ofFn (λ x => x.val == idx_val.val)) (idx_val.val < len)
:= by
  unfold singleOneArray

  step oneHotRaw.convertsM h_idx h_len as oneHot
  step FArray.sum.convertsM h_oneHot as sum
  step mkF.convertsM as one
  step assert_eq.convertsM h_sum h_one as assert_eq
  apply convertsM_pure
  . exact h_oneHot
  . simp
    intro h_sum
    by_contra h_idx_val
    rewrite [Vector.sum_ofFn_eq_zero_of_eq_zero] at h_sum
    . simp at h_sum
    . grind
  . simp
    intro h_idx_val
    clear *-h_len h_idx_val
    induction' len with len ih
    . grind
    . specialize ih (by grind)
      rewrite [Vector.ofFn_succ]
      by_cases h: idx_val.val = len
      . simp [h]
        clear ih
        have (i : Fin len) : (i.val = len) = false := by grind
        simp [this]
        clear *-len
        unfold Vector.ofFn
        simp
        induction' len with len ih'
        . set x := Array.ofFn _
          have : x = #[] := rfl
          grind
        . rewrite [Array.ofFn_succ]
          grind
      . specialize ih (by grind)
        simp
        rewrite [ite_cond_eq_false]
        . simp
          convert ih
          grind
        . grind
  . exact λ _ ↦ True.intro
  . exact λ _ ↦ True.intro
  . exact λ _ ↦ True.intro

end singleOneArray

end singleOneArray

end Clap.Lang
