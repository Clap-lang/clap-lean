import Clap.Lang.F.mkAdd
import Clap.Lang.F.mkF

namespace Clap.Lang

variable {p : ℕ}

section sum

open HashConsM in
def FArray.sum' {k} (init : F) (vals : FArray k) : ClapM p F := do
  vals.foldlM mkAdd init

namespace FArray.sum'

lemma convertsM
  {k}
  {state : ClapMState p}
  {f_vals : FArray k}
  {vals : Vector Bool k}
  {init : F}
  (h_vals : Converts FArray.conversion state f_vals vals)
  (h_init : Converts F.conversion state init 0)
:
  ConvertsM F.conversion (f_vals.sum' init) state (vals.map (λ x => if x then (1: ZMod p) else 0)).sum True
:= by
  unfold sum'

  induction' k with k h_k
  . have (init : ExprRef) : Vector.foldlM (m := ClapM p) mkAdd init f_vals = pure init := by
      convert Vector.foldlM_empty
      obtain ⟨⟨_⟩, _⟩ := f_vals
      grind
    simp [this]

    apply convertsM_pure <;> [skip; exact True.intro]

    have : vals = #v[] := by grind
    simp [this]
    assumption
  . have := (FArray.converts_vector_cast (k2 := k) (FArray.converts_pop h_vals) (by trivial))
    set fvals_base := Vector.cast (m := k) (by trivial) f_vals.pop
    set vals_base := Vector.cast (m := k) (by trivial) vals.pop

    have h_push : f_vals = fvals_base.push f_vals[k] := by
      ext
      rewrite [Vector.getElem_push]
      split
      . simp [fvals_base]
      . grind
    rewrite [h_push]
    simp [Vector.foldlM_push]

    step @h_k fvals_base vals_base this as mapM

    have h_fvals_k := F.converts_of_FB_converts (FArray.converts_getElem h_vals (Nat.lt_succ_self k))
    apply convertsM_of_convertsM (mkAdd.convertsM h_mapM h_fvals_k)
    . have : vals = vals_base.push vals[k] := by
        ext
        rewrite [Vector.getElem_push]
        split
        . simp [vals_base]
        . grind
      rewrite [this]
      simp
    . trivial

end FArray.sum'



open HashConsM in
def FArray.sum {k} (vals : FArray k) : ClapM p F := do
  vals.foldlM mkAdd (←mkF 0)

namespace FArray.sum

lemma convertsM
  {k}
  {state : ClapMState p}
  {f_vals : FArray k}
  {vals : Vector Bool k}
  (h_vals : Converts FArray.conversion state f_vals vals)
:
  ConvertsM F.conversion (f_vals.sum) state (vals.map (λ x => if x then (1: ZMod p) else 0)).sum True
:= by
  unfold sum
  simp [←sum'.eq_def]

  step mkF.convertsM as zero

  apply convertsM_of_convertsM (sum'.convertsM h_vals h_zero)
  . rfl
  . trivial

end FArray.sum
end sum

end Clap.Lang
