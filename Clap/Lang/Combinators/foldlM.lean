import Clap.eDSLState.Convert.Specialised

/-!
# Reusable `ConvertsM` lemmas for `Vector.foldlM`

Every iterating gadget in `Clap/Lang/` previously repeated the induction scaffolding of
`Clap/Lang/FArray/OneHotRaw.lean` by hand. These two lemmas do it once.

`convertsM_foldlM` covers a fold whose step emits no assertion (slot 5 `True`);
`convertsM_foldlM_constraints` covers a fold whose step asserts something, accumulating the
per-element conditions into a `∀ i`.

Both are generic in the *element* conversion `C_elem`, so the same lemma serves a fold over a
bit vector (`FB.conversion`), over a vector of field elements (`F.conversion`) and over a
zipped pair of vectors (`FPair.conversion`, via `FVec.converts_zip`) — the last being the shape
`dotProduct`, `FArray.eq` and `FArray.assert_eq` all need.

The element hypothesis is an explicit `∀ i`, rather than a bundled `Converts`, precisely so that
it can be reframed through each intermediate state by mapping `converts_skip` over it. Note that
these proofs do **not** use the `step` tactic: `step` goes through `convertsM_bind`, which cannot
sequence two real assertions (see `convertsM_bind_and`).
-/

namespace Clap.Lang

variable {p : ℕ}

section foldlM

/-- `Vector.foldlM` where each step is unconditionally satisfiable. -/
lemma convertsM_foldlM
  {k} {α γ}
  {C_acc : Conversion p α}
  {C_elem : Conversion p γ}
  {f : α → γ → ClapM p α}
  {f_spec : C_acc.IdealT → C_elem.IdealT → C_acc.IdealT}
  {state : ClapMState p}
  {v : Vector γ k}
  {vals : Vector C_elem.IdealT k}
  {init : α}
  {init_val : C_acc.IdealT}
  (h_v : ∀ i : Fin k, Converts C_elem state v[i] vals[i])
  (h_init : Converts C_acc state init init_val)
  (h_f : ∀ {state' : ClapMState p} {acc acc_val x x_val},
          Converts C_acc state' acc acc_val →
          Converts C_elem state' x x_val →
          ConvertsM C_acc (f acc x) state' (f_spec acc_val x_val) True)
:
  ConvertsM C_acc (v.foldlM f init) state (vals.foldl f_spec init_val) True
:= by
  induction' k with k h_k
  . have h_empty : Vector.foldlM (m := ClapM p) f init v = pure init := by
      convert Vector.foldlM_empty
      obtain ⟨⟨_⟩, _⟩ := v
      grind
    simp [h_empty]
    apply convertsM_pure <;> [skip; exact True.intro]
    have : vals = #v[] := by grind
    simp [this]
    assumption
  . set v_base := Vector.cast (m := k) (by trivial) v.pop with h_v_base_def
    set vals_base := Vector.cast (m := k) (by trivial) vals.pop with h_vals_base_def

    have h_v_base : ∀ i : Fin k, Converts C_elem state v_base[i] vals_base[i] := by
      intro ⟨i, h_i⟩
      have h1 : v_base[i]'h_i = v[i]'(by omega) := by simp [v_base]
      have h2 : vals_base[i]'h_i = vals[i]'(by omega) := by simp [vals_base]
      simp only [Fin.getElem_fin]
      rw [h1, h2]
      exact h_v ⟨i, by omega⟩

    have h_vals : vals = vals_base.push vals[k] := by
      ext
      rewrite [Vector.getElem_push]
      split
      . simp [vals_base]
      . grind

    have h_push : v = v_base.push v[k] := by
      ext
      rewrite [Vector.getElem_push]
      split
      . simp [v_base]
      . grind

    have h_last := h_v ⟨k, Nat.lt_succ_self k⟩
    have h_ih := h_k h_v_base

    rewrite [h_push]
    simp only [Vector.foldlM_push]

    apply convertsM_of_convertsM
      (convertsM_bind_and h_ih (h_f h_ih.result (converts_skip h_ih h_last)))
    . conv_rhs => rewrite [h_vals]
      simp
    . simp

/-- `Vector.foldlM` where each step asserts `step_constraints` about its element. The fold's own
constraint is the conjunction of the per-element ones. -/
lemma convertsM_foldlM_constraints
  {k} {α γ}
  {C_acc : Conversion p α}
  {C_elem : Conversion p γ}
  {f : α → γ → ClapM p α}
  {f_spec : C_acc.IdealT → C_elem.IdealT → C_acc.IdealT}
  {step_constraints : C_elem.IdealT → Prop}
  {state : ClapMState p}
  {v : Vector γ k}
  {vals : Vector C_elem.IdealT k}
  {init : α}
  {init_val : C_acc.IdealT}
  (h_v : ∀ i : Fin k, Converts C_elem state v[i] vals[i])
  (h_init : Converts C_acc state init init_val)
  (h_f : ∀ {state' : ClapMState p} {acc acc_val x x_val},
          Converts C_acc state' acc acc_val →
          Converts C_elem state' x x_val →
          ConvertsM C_acc (f acc x) state' (f_spec acc_val x_val) (step_constraints x_val))
:
  ConvertsM C_acc (v.foldlM f init) state (vals.foldl f_spec init_val)
    (∀ i : Fin k, step_constraints vals[i])
:= by
  induction' k with k h_k
  . have h_empty : Vector.foldlM (m := ClapM p) f init v = pure init := by
      convert Vector.foldlM_empty
      obtain ⟨⟨_⟩, _⟩ := v
      grind
    simp [h_empty]
    apply convertsM_pure
    . have : vals = #v[] := by grind
      simp [this]
      assumption
    . trivial
  . set v_base := Vector.cast (m := k) (by trivial) v.pop with h_v_base_def
    set vals_base := Vector.cast (m := k) (by trivial) vals.pop with h_vals_base_def

    have h_eq : ∀ (j : ℕ) (hj : j < k), vals_base[j]'hj = vals[j]'(by omega) := by
      intro j hj
      simp [vals_base]

    have h_v_base : ∀ i : Fin k, Converts C_elem state v_base[i] vals_base[i] := by
      intro ⟨i, h_i⟩
      have h1 : v_base[i]'h_i = v[i]'(by omega) := by simp [v_base]
      simp only [Fin.getElem_fin]
      rw [h1, h_eq i h_i]
      exact h_v ⟨i, by omega⟩

    have h_vals : vals = vals_base.push vals[k] := by
      ext
      rewrite [Vector.getElem_push]
      split
      . simp [vals_base]
      . grind

    have h_push : v = v_base.push v[k] := by
      ext
      rewrite [Vector.getElem_push]
      split
      . simp [v_base]
      . grind

    have h_last := h_v ⟨k, Nat.lt_succ_self k⟩
    have h_ih := h_k h_v_base

    rewrite [h_push]
    simp only [Vector.foldlM_push]

    -- `convertsM_bind`, and so `step`, cannot sequence two real assertions; use the
    -- conjunction form instead.
    apply convertsM_of_convertsM
      (convertsM_bind_and h_ih (h_f h_ih.result (converts_skip h_ih h_last)))
    . conv_rhs => rewrite [h_vals]
      simp
    . constructor
      . rintro ⟨h_prefix, h_elem⟩ ⟨i, h_i⟩
        by_cases h : i = k
        . subst h
          exact h_elem
        . have h_lt : i < k := by grind
          have h1 := h_prefix ⟨i, h_lt⟩
          simp only [Fin.getElem_fin] at h1
          rwa [h_eq i h_lt] at h1
      . intro h
        refine ⟨fun ⟨i, h_i⟩ ↦ ?_, h ⟨k, Nat.lt_succ_self k⟩⟩
        have h1 := h ⟨i, by grind⟩
        simp only [Fin.getElem_fin] at h1 ⊢
        rwa [← h_eq i h_i] at h1

end foldlM

end Clap.Lang
