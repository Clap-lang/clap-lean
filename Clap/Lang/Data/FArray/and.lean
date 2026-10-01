import Clap.Lang.Core.FB.and

namespace Clap.Lang

variable {p : ℕ}

section and

/-- Elementwise `FB.and` of two same-length bit arrays. -/
def FArray.and {k} (a b : FArray p k) : ClapM p (FArray p k) :=
  Vector.ofFnM (fun i => FB.and a[i] b[i])

namespace FArray.and

lemma convertsM
  [p.AtLeastTwo]
  {k}
  {state : ClapMState p}
  {a b : FArray p k}
  {a_val b_val : Vector Bool k}
  (h_a : Converts FArray.conversion state a a_val)
  (h_b : Converts FArray.conversion state b b_val)
:
  ConvertsM FArray.conversion (FArray.and a b) state
    (Vector.ofFn (fun i ↦ a_val[i] && b_val[i])) True
:= by
  unfold FArray.and
  induction' k with k h_k
  . rw [Vector.ofFnM_zero]
    apply convertsM_pure
    . have ha0 : a_val = #v[] := by grind
      have hb0 : b_val = #v[] := by grind
      rw [ha0, hb0]
      exact FArray.converts_empty
    . trivial
  . rw [Vector.ofFnM_succ]
    have h_a_base :
        Converts FArray.conversion state
          ((a.pop.cast (by omega) : Vector (FB p) k)) ((a_val.pop.cast (by omega) : Vector Bool k)) :=
      FArray.converts_vector_cast (FArray.converts_pop h_a) (by omega)
    have h_b_base :
        Converts FArray.conversion state
          ((b.pop.cast (by omega) : Vector (FB p) k)) ((b_val.pop.cast (by omega) : Vector Bool k)) :=
      FArray.converts_vector_cast (FArray.converts_pop h_b) (by omega)
    have h_ih := h_k h_a_base h_b_base

    have h_action_eq :
        (fun i : Fin k => FB.and a[i.castSucc] b[i.castSucc]) =
        (fun i : Fin k => FB.and (a.pop.cast (by omega) : Vector (FB p) k)[i]
          (b.pop.cast (by omega) : Vector (FB p) k)[i]) := by
      funext i
      simp

    rw [h_action_eq]
    step h_ih as base
    step FB.and.convertsM (FArray.converts_getElem h_a (i := k) (by omega))
      (FArray.converts_getElem h_b (i := k) (by omega)) as last

    have h_vals :
        Vector.ofFn (fun i ↦ a_val[i] && b_val[i]) =
        (Vector.ofFn (fun i : Fin k ↦
          (a_val.pop.cast (by omega) : Vector Bool k)[i] && (b_val.pop.cast (by omega) : Vector Bool k)[i]
        )).push (a_val[k] && b_val[k]) := by
      ext i hi
      rw [Vector.getElem_push]
      split
      . simp
      . grind

    apply convertsM_pure
    . rw [h_vals]
      exact FArray.converts_push h_base h_last
    . trivial

end FArray.and

end and

end Clap.Lang
