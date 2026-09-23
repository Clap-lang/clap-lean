import Clap.Lang.Core.FB.or

/-!
# Reusable `ConvertsM` lemma for `Vector.scanlM`

`Vector.scanlM` (`Clap/Util/Wheels.lean`) is an exclusive-prefix monadic scan: position `i` of the
output folds elements `[0, i)` of the input, dropping the final accumulator so the output has the
same length as the input. This lemma covers `Vector.scanlM` specialised to `FB.or`/`Bool.or` — the
shape needed by `rightArraySelector` — following the same head/tail induction as
`Vector.scanlM_succ` itself.
-/

namespace Clap.Lang

variable {p : ℕ}

section scanlM

private lemma FArray.converts_cons
  {k} {state : ClapMState p}
  {expr : FB p} {val : Bool}
  {exprs : FArray p k} {vals : Vector Bool k}
  (h_expr : Converts FB.conversion state expr val)
  (h_exprs : Converts FArray.conversion state exprs vals)
:
  Converts FArray.conversion state (⟨⟨expr :: exprs.toList⟩, by simp⟩ : Vector (FB p) (k + 1))
    (⟨⟨val :: vals.toList⟩, by simp⟩ : Vector Bool (k + 1))
:= by
  rewrite [FArray.converts_iff_FB_converts] at h_exprs ⊢
  intro ⟨i, h_i⟩
  match i, h_i with
  | 0, h_i => simpa using h_expr
  | i + 1, h_i =>
    have h := h_exprs ⟨i, by omega⟩
    simpa using h

namespace Vector.scanlM

lemma convertsM
  [p.AtLeastTwo]
  {n} {state : ClapMState p}
  {vals : FArray p n} {vals_val : Vector Bool n}
  (h_vals : Converts FArray.conversion state vals vals_val)
  {init : FB p} {init_val : Bool}
  (h_init : Converts FB.conversion state init init_val)
:
  ConvertsM FArray.conversion (Vector.scanlM FB.or init vals) state
    (Vector.scanl (· || ·) init_val vals_val) True
:= by
  induction n generalizing state init init_val with
  | zero =>
    have h_vals_eq : vals = (#v[] : FArray p 0) := by grind
    have h_vals_val_eq : vals_val = (#v[] : Vector Bool 0) := by grind
    subst h_vals_eq
    subst h_vals_val_eq
    rw [Vector.scanlM_zero, Vector.scanl_zero]
    apply convertsM_pure
    . exact FArray.converts_empty
    . trivial
  | succ n ih =>
    have h_head : Converts FB.conversion state vals[0] vals_val[0] :=
      FArray.converts_getElem h_vals (by omega)
    have h_tail :
        Converts FArray.conversion state
          ((vals.tail.cast (by omega) : Vector (FB p) n))
          ((vals_val.tail.cast (by omega) : Vector Bool n)) :=
      FArray.converts_vector_cast (FArray.converts_tail h_vals) (by omega)
    rw [Vector.eq_cons vals, Vector.scanlM_succ]
    step FB.or.convertsM h_init h_head as acc
    step (ih h_tail h_acc) as rest
    apply convertsM_pure
    . rw [Vector.eq_cons vals_val, Vector.scanl_succ]
      exact FArray.converts_cons h_init h_rest
    . trivial

end Vector.scanlM

end scanlM

end Clap.Lang
