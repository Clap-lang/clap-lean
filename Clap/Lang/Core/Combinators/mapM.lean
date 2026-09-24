import Clap.Model.Convert.Vector
import Clap.Util.Containers

/-!
# Reusable `ConvertsM` lemmas for `Vector.mapM`

`convertsM_mapM` is the common case: a field-valued gadget that asserts nothing, giving an
`FVec`. `convertsM_mapM_constraints` is the general one: any result conversion `C_out`, with steps
that may assert. Its result is a `C_out.vector k` (`Clap/Model/Convert/Vector.lean`), and its
constraint is the conjunction of the per-element ones. Like `convertsM_foldlM_constraints`, it
does not use `step`, which cannot sequence two real assertions.
-/

namespace Clap.Lang

variable {p : ℕ}

section mapM

lemma convertsM_mapM
  {k} {γ}
  {C_elem : Conversion p γ}
  {f : γ → ClapM p (F p)}
  {f_spec : C_elem.IdealT → ZMod p}
  {state : ClapMState p}
  {v : Vector γ k}
  {vals : Vector C_elem.IdealT k}
  (h_v : ∀ i : Fin k, Converts C_elem state v[i] vals[i])
  (h_f : ∀ {state' : ClapMState p} {x x_val},
          Converts C_elem state' x x_val →
          ConvertsM F.conversion (f x) state' (f_spec x_val) True)
:
  ConvertsM FVec.conversion (v.mapM f) state (vals.map f_spec) True
:= by
  induction' k with k h_k generalizing state
  . have hv : v = #v[] := by grind
    have hvals : vals = #v[] := by grind
    subst hv hvals
    simp
    apply convertsM_pure
    . exact FVec.converts_empty
    . trivial
  . rw [Vector.mapM_succ]
    set v_base := Vector.cast (m := k) (by trivial) v.pop
    set vals_base := Vector.cast (m := k) (by trivial) vals.pop
    have h_vb : ∀ i : Fin k, Converts C_elem state v_base[i] vals_base[i] := by
      intro ⟨i, h_i⟩
      have h1 : v_base[i]'h_i = v[i]'(by omega) := by simp [v_base]
      have h2 : vals_base[i]'h_i = vals[i]'(by omega) := by simp [vals_base]
      simp only [Fin.getElem_fin]
      rw [h1, h2]
      exact h_v ⟨i, by omega⟩
    have h_ih := h_k h_vb
    have h_pop : v.pop = v_base := rfl
    rw [h_pop]
    step h_ih as base
    -- Only now: `step` re-frames every `Converts` in context through the new state, and would
    -- fail on one already stated at `base_state`.
    have h_last : Converts C_elem base_state v[k] vals[k] :=
      converts_skip h_ih (h_v ⟨k, Nat.lt_succ_self k⟩)
    step (h_f h_last) as last
    have h_vals : vals.map f_spec = (vals_base.map f_spec).push (f_spec vals[k]) := by
      ext i hi
      rw [Vector.getElem_push]
      split
      . simp [vals_base]
      . have : i = k := by omega
        subst this; simp
    rw [h_vals]
    exact FVec.converts_push h_base h_last

/-- `Vector.mapM` of a gadget with any result conversion, where each step asserts
`step_constraints` about its element. The map's constraint is the conjunction of the
per-element ones. -/
lemma convertsM_mapM_constraints
  {k} {γ β}
  {C_elem : Conversion p γ}
  {C_out : Conversion p β}
  {f : γ → ClapM p β}
  {f_spec : C_elem.IdealT → C_out.IdealT}
  {step_constraints : C_elem.IdealT → Prop}
  {state : ClapMState p}
  {v : Vector γ k}
  {vals : Vector C_elem.IdealT k}
  (h_v : ∀ i : Fin k, Converts C_elem state v[i] vals[i])
  (h_f : ∀ {state' : ClapMState p} {x x_val},
          Converts C_elem state' x x_val →
          ConvertsM C_out (f x) state' (f_spec x_val) (step_constraints x_val))
:
  ConvertsM (C_out.vector k) (v.mapM f) state (vals.map f_spec)
    (∀ i : Fin k, step_constraints vals[i])
:= by
  induction' k with k h_k generalizing state
  . have hv : v = #v[] := by grind
    have hvals : vals = #v[] := by grind
    subst hv hvals
    simp
    apply convertsM_pure
    . exact Conversion.vector.converts_empty
    . trivial
  . rw [Vector.mapM_succ]
    set v_base := Vector.cast (m := k) (by trivial) v.pop
    set vals_base := Vector.cast (m := k) (by trivial) vals.pop
    have h_vb : ∀ i : Fin k, Converts C_elem state v_base[i] vals_base[i] := by
      intro ⟨i, h_i⟩
      have h1 : v_base[i]'h_i = v[i]'(by omega) := by simp [v_base]
      have h2 : vals_base[i]'h_i = vals[i]'(by omega) := by simp [vals_base]
      simp only [Fin.getElem_fin]
      rw [h1, h2]
      exact h_v ⟨i, by omega⟩
    have h_ih := h_k h_vb
    have h_pop : v.pop = v_base := rfl
    rw [h_pop]
    have h_last := h_f (converts_skip h_ih (h_v ⟨k, Nat.lt_succ_self k⟩))
    -- Both halves assert, so `convertsM_bind_and`, reframing the prefix by hand.
    apply convertsM_of_convertsM
      (convertsM_bind_and h_ih
        (convertsM_map h_last
          (Conversion.vector.converts_push (converts_skip h_last h_ih.result) h_last.result)
          Iff.rfl))
    . ext i hi
      rw [Vector.getElem_push]
      split
      . simp [vals_base]
      . have : i = k := by omega
        subst this; simp
    . simp only [Fin.getElem_fin]
      simp [Fin.forall_fin_succ', vals_base]

end mapM

end Clap.Lang
