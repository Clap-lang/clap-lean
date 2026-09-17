import Clap.eDSLState.Convert.Specialised

/-!
# A reusable `ConvertsM` lemma for `Vector.ofFnM`

Building a vector of field elements position by position. The per-position hypothesis is
quantified over *every* state, which is what makes this usable: it holds for any position whose
action is a constant (`mkF`, `ofChar`, …), which is the case for every constant-vector gadget.
-/

namespace Clap.Lang

variable {p : ℕ}

section ofFnM

lemma convertsM_ofFnM
  {k}
  {f : Fin k → ClapM p (F p)}
  {vals : Vector (ZMod p) k}
  {state : ClapMState p}
  (h_f : ∀ (i : Fin k) (state' : ClapMState p),
          ConvertsM F.conversion (f i) state' vals[i] True)
:
  ConvertsM FVec.conversion (Vector.ofFnM f) state vals True
:= by
  induction' k with k h_k
  . rw [Vector.ofFnM_zero]
    apply convertsM_pure
    . have h : vals = #v[] := by grind
      rw [h]
      exact FVec.converts_empty
    . trivial
  . rw [Vector.ofFnM_succ]
    set vals_base := Vector.cast (m := k) (by trivial) vals.pop with h_vals_base_def

    have h_eq : ∀ (j : ℕ) (hj : j < k), vals_base[j]'hj = vals[j]'(by omega) := by
      intro j hj
      simp [vals_base]

    have h_vals : vals = vals_base.push vals[k] := by
      ext
      rewrite [Vector.getElem_push]
      split
      . simp [vals_base]
      . grind

    have h_ih := h_k (f := fun i ↦ f i.castSucc) (vals := vals_base)
      (by
        intro i state'
        have := h_f i.castSucc state'
        simp only [Fin.getElem_fin, Fin.val_castSucc] at this ⊢
        rwa [h_eq i.val i.isLt])

    step h_ih as base
    step (h_f (Fin.last k) base_state) as last

    apply convertsM_pure
    . have h_push := FVec.converts_push h_base h_last
      simpa [← h_vals] using h_push
    . trivial

end ofFnM

end Clap.Lang
