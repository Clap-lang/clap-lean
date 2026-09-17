import Clap.Lang.FB.xor

namespace Clap.Lang

variable {p : ℕ}

section xor

/-- Elementwise `FB.xor` of two same-length bit arrays. -/
def FArray.xor {k} (a b : FArray p k) : ClapM p (FArray p k) :=
  Vector.ofFnM (fun i => FB.xor a[i] b[i])

namespace FArray.xor

lemma convertsM
  [p.AtLeastTwo]
  {k}
  {state : ClapMState p}
  {a b : FArray p k}
  {a_val b_val : Vector Bool k}
  (h_a : Converts FArray.conversion state a a_val)
  (h_b : Converts FArray.conversion state b b_val)
:
  ConvertsM FArray.conversion (FArray.xor a b) state
    (Vector.ofFn (fun i ↦ a_val[i] ^^ b_val[i])) True
:= by
  unfold FArray.xor

  induction' k with k h_k
  . simp only [Vector.ofFnM_zero]
    apply convertsM_pure <;> [skip; exact True.intro]
    have hav0 : a_val = #v[] := by grind
    have hbv0 : b_val = #v[] := by grind
    have hempty : (Vector.ofFn (fun i : Fin 0 => a_val[i] ^^ b_val[i])) = #v[] := by
      ext i hi
      omega
    rw [hempty]
    exact FArray.converts_empty
  . have hA := (FArray.converts_vector_cast (k2 := k) (FArray.converts_pop h_a) (by trivial))
    have hB := (FArray.converts_vector_cast (k2 := k) (FArray.converts_pop h_b) (by trivial))
    set a_base := Vector.cast (m := k) (by trivial) a.pop
    set b_base := Vector.cast (m := k) (by trivial) b.pop
    set aval_base := Vector.cast (m := k) (by trivial) a_val.pop
    set bval_base := Vector.cast (m := k) (by trivial) b_val.pop

    have h_push_a : a = a_base.push a[k] := by
      ext
      rewrite [Vector.getElem_push]
      split
      . simp [a_base]
      . grind
    have h_push_b : b = b_base.push b[k] := by
      ext
      rewrite [Vector.getElem_push]
      split
      . simp [b_base]
      . grind

    have hfun :
        (fun i : Fin k => FB.xor a[i.castSucc] b[i.castSucc])
          = (fun i : Fin k => FB.xor a_base[i] b_base[i]) := by
      funext i
      have ha : a[(i.castSucc : Fin (k + 1))] = a_base[i.val] := by
        conv_lhs => rw [h_push_a]
        simp
      have hb : b[(i.castSucc : Fin (k + 1))] = b_base[i.val] := by
        conv_lhs => rw [h_push_b]
        simp
      rw [ha, hb]
      rfl

    rw [Vector.ofFnM_succ, hfun]

    step @h_k a_base b_base aval_base bval_base hA hB as mapM

    have h_a_k := FArray.converts_getElem h_a (Nat.lt_succ_self k)
    have h_b_k := FArray.converts_getElem h_b (Nat.lt_succ_self k)
    step FB.xor.convertsM h_a_k h_b_k as last

    have hav_push : a_val = aval_base.push a_val[k] := by
      ext
      rewrite [Vector.getElem_push]
      split
      . simp [aval_base]
      . grind
    have hbv_push : b_val = bval_base.push b_val[k] := by
      ext
      rewrite [Vector.getElem_push]
      split
      . simp [bval_base]
      . grind

    have hval :
        (Vector.ofFn (fun i : Fin (k + 1) => a_val[i] ^^ b_val[i]))
          = (Vector.ofFn (fun i : Fin k => aval_base[i] ^^ bval_base[i])).push (a_val[k] ^^ b_val[k])
    := by
      rw [Vector.ofFn_succ]
      congr 1
      apply congrArg
      funext i
      have hav : a_val[(i.castSucc : Fin (k + 1))] = aval_base[i.val] := by
        conv_lhs => rw [hav_push]
        simp
      have hbv : b_val[(i.castSucc : Fin (k + 1))] = bval_base[i.val] := by
        conv_lhs => rw [hbv_push]
        simp
      rw [hav, hbv]
      rfl

    apply convertsM_pure
    . rw [hval]
      exact FArray.converts_push h_mapM h_last
    . trivial

end FArray.xor

end xor

end Clap.Lang
