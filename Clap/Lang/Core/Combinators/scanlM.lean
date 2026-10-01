import Clap.Model.Convert.Specialised

/-!
# Reusable `ConvertsM` lemma for `Vector.scanlM`

`Vector.scanlM` (`Clap/Util/Wheels.lean`) is an exclusive-prefix monadic scan: position `i` of the
output folds elements `[0, i)` of the input, dropping the final accumulator so the output has the
same length as the input. Circom writes this shape as a signal array filled by a loop
(`out[i] <== out[i-1] + bits[i-1]`, `challenge_powers[i] <== challenge_powers[i-1] * α`).

`convertsM_scanlM` covers a field-valued accumulator whose step asserts nothing, with elements
under any conversion. It follows the same head/tail induction as `Vector.scanlM_succ` itself. As
with `convertsM_foldlM`, the step hypothesis is quantified over every state, so anything the step
reads besides the accumulator must ride in the elements (`Vector.replicate n α`, or a `zip`).

`Vector.scanlM` applies the step to every element, the last included, and drops that last result.
So a step that emits gates emits one set more than the outputs need.
-/

namespace Clap.Lang

variable {p : ℕ}

section scanlM

private lemma FVec.converts_cons
  {k} {state : ClapMState p}
  {expr : F p} {val : ZMod p}
  {exprs : FVec p k} {vals : Vector (ZMod p) k}
  (h_expr : Converts F.conversion state expr val)
  (h_exprs : Converts FVec.conversion state exprs vals)
:
  Converts FVec.conversion state (⟨⟨expr :: exprs.toList⟩, by simp⟩ : Vector (F p) (k + 1))
    (⟨⟨val :: vals.toList⟩, by simp⟩ : Vector (ZMod p) (k + 1))
:= by
  rewrite [FVec.converts_iff_F_converts] at h_exprs ⊢
  intro ⟨i, h_i⟩
  match i, h_i with
  | 0, h_i => simpa using h_expr
  | i + 1, h_i =>
    have h := h_exprs ⟨i, by omega⟩
    simpa using h

lemma convertsM_scanlM
  {k} {γ}
  {C_elem : Conversion p γ}
  {f : F p → γ → ClapM p (F p)}
  {f_spec : ZMod p → C_elem.IdealT → ZMod p}
  {state : ClapMState p}
  {v : Vector γ k}
  {vals : Vector C_elem.IdealT k}
  {init : F p}
  {init_val : ZMod p}
  (h_v : ∀ i : Fin k, Converts C_elem state v[i] vals[i])
  (h_init : Converts F.conversion state init init_val)
  (h_f : ∀ {state' : ClapMState p} {acc acc_val x x_val},
          Converts F.conversion state' acc acc_val →
          Converts C_elem state' x x_val →
          ConvertsM F.conversion (f acc x) state' (f_spec acc_val x_val) True)
:
  ConvertsM FVec.conversion (Vector.scanlM f init v) state (Vector.scanl f_spec init_val vals) True
:= by
  induction k generalizing state init init_val with
  | zero =>
    have h_v_eq : v = #v[] := by grind
    have h_vals_eq : vals = #v[] := by grind
    subst h_v_eq
    subst h_vals_eq
    rw [Vector.scanlM_zero, Vector.scanl_zero]
    apply convertsM_pure
    . exact FVec.converts_empty
    . trivial
  | succ k ih =>
    have h_head : Converts C_elem state v[0] vals[0] := h_v ⟨0, by omega⟩
    have h_tail : ∀ i : Fin k, Converts C_elem state (v.tail.cast (by omega) : Vector γ k)[i]
        (vals.tail.cast (by omega) : Vector C_elem.IdealT k)[i] := by
      intro ⟨i, h_i⟩
      simpa [Nat.add_comm] using h_v ⟨i + 1, by omega⟩
    have hA := h_f h_init h_head
    -- the tail's elements, carried past the first step by hand: `step` only reframes `Converts`
    have h_tail' := fun i : Fin k ↦ converts_skip hA (h_tail i)
    clear h_tail h_v
    rw [Vector.eq_cons v, Vector.scanlM_succ]
    step hA as acc
    step (ih h_tail' h_acc) as rest
    apply convertsM_pure
    . rw [Vector.eq_cons vals, Vector.scanl_succ]
      exact FVec.converts_cons h_init h_rest
    . trivial

end scanlM

end Clap.Lang
