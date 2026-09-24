import Clap.Model.Convert.Specialised

/-!
# Vectors of convertible values

`Conversion.vector C k` converts a `Vector β k` whose elements each convert under `C`, laid out
one after another. It is the nested conversion that `FArray.conversion` cannot express on its
own, such as a vector of bytes held as bits. Its ideal value is the vector of the elements' ideal
values. Up to flattening singleton lists, it is the layout `FVec.conversion` (a vector of `F`) and
`FArray.conversion` (a vector of `FB`) already use.

`convertsM_mapM_constraints` in `Clap/Lang/Core/Combinators/mapM.lean` produces it, and
`FArray.converts_flatten` turns a vector of bit vectors back into one bit vector. There is no
element-projection lemma yet.
-/

namespace Clap

variable {p : ℕ}

/-- `Converts` for a layout that is two others laid end to end. -/
lemma converts_append_of_eq
  {α₁ α₂ α₃ : Type}
  {C₁ : Conversion p α₁}
  {C₂ : Conversion p α₂}
  {C₃ : Conversion p α₃}
  {state : ClapMState p}
  {x₁ : α₁} {x₂ : α₂} {x₃ : α₃}
  {v₁ : C₁.IdealT} {v₂ : C₂.IdealT} {v₃ : C₃.IdealT}
  (h₁ : Converts C₁ state x₁ v₁)
  (h₂ : Converts C₂ state x₂ v₂)
  (h_ptr : C₃.toExprs x₃ = C₁.toExprs x₁ ++ C₂.toExprs x₂)
  (h_val : C₃.conversion v₃ = C₁.conversion v₁ ++ C₂.conversion v₂)
:
  Converts C₃ state x₃ v₃
:= by
  obtain ⟨len₁, varSet₁, wf₁, val₁⟩ := h₁
  obtain ⟨len₂, varSet₂, wf₂, val₂⟩ := h₂
  constructor
  · intro ⟨i, h_i⟩
    simp only [Fin.getElem_fin, h_ptr, List.getElem_append]
    split
    · exact varSet₁ ⟨i, by grind⟩
    · exact varSet₂ ⟨i - (C₁.toExprs x₁).length, by grind⟩
  · intro ⟨i, h_i⟩
    simp only [Fin.getElem_fin, h_ptr, List.getElem_append]
    split
    · exact wf₁ ⟨i, by grind⟩
    · exact wf₂ ⟨i - (C₁.toExprs x₁).length, by grind⟩
  · intro ⟨i, h_i⟩
    simp only [Fin.getElem_fin, h_ptr, h_val, List.getElem_append]
    split
    · rw [dif_pos (by grind)]
      exact val₁ ⟨i, by grind⟩
    · rw [dif_neg (by grind)]
      simp only [len₁]
      exact val₂ ⟨i - (C₁.toExprs x₁).length, by grind⟩
  · grind

/-- A vector of values that each convert under `C`, laid out one after another. -/
abbrev Conversion.vector {β : Type} (C : Conversion p β) (k : ℕ) : Conversion p (Vector β k) where
  IdealT := Vector C.IdealT k
  toExprs xs := (xs.toList.map C.toExprs).flatten
  conversion vs := (vs.toList.map C.conversion).flatten

namespace Conversion.vector

variable {β : Type} {C : Conversion p β} {state : ClapMState p}

@[simp]
lemma converts_empty : Converts (C.vector 0) state #v[] #v[] := by
  constructor <;> simp

lemma converts_push
  {k}
  {xs : Vector β k}
  {x : β}
  {vs : Vector C.IdealT k}
  {v : C.IdealT}
  (h_xs : Converts (C.vector k) state xs vs)
  (h_x : Converts C state x v)
:
  Converts (C.vector (k + 1)) state (xs.push x) (vs.push v)
:= converts_append_of_eq h_xs h_x (by simp [Vector.toList_push]) (by simp [Vector.toList_push])

end Conversion.vector

end Clap

namespace Clap.Lang.FArray

variable {p : ℕ}

/-- A vector of bit vectors converts, flattened, to its bits flattened. -/
lemma converts_flatten
  {k w}
  {state : ClapMState p}
  {exprs : Vector (FArray p w) k}
  {vals : Vector (Vector Bool w) k}
  (h : Converts (Conversion.vector FArray.conversion k) state exprs vals)
:
  Converts FArray.conversion state exprs.flatten vals.flatten
:= converts_cast h
    (by simp [Vector.flatten, Vector.toList, Function.comp_def])
    (by simp [Vector.flatten, Vector.toList, Function.comp_def])

end Clap.Lang.FArray
