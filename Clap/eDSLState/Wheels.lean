import Lean

import Mathlib.Data.ZMod.Basic

@[simp]
theorem Vector.range_one : Vector.range 1 = #v[0] := rfl

namespace Clap

initialize Lean.registerTraceClass `Clap.Preprocessor

initialize Lean.registerTraceClass `Clap.Preprocessor.addLambdas (inherited := true)

register_simp_attr Clap.monads

-- TODO move out of Clap namespace?
@[simp, grind .]
lemma ZMod.zero_ne_one
  {p : ℕ}
  [p_ge_2 : p.AtLeastTwo]
:
  (0: ZMod p) ≠ (1 : ZMod p)
:= by
  obtain ⟨p_ge_2⟩ := p_ge_2
  symm
  simp only [ne_eq, ZMod.one_eq_zero_iff]
  omega

@[simp, grind .]
lemma ZMod.one_ne_zero
  {p : ℕ}
  [p_ge_2 : p.AtLeastTwo]
:
  (1: ZMod p) ≠ (0 : ZMod p)
:= by
  symm
  simp

@[simp, grind =]
lemma Std.ExtTreeMap.insertMany_single
  (α)
  (β)
  (cmp)
  [Std.TransCmp cmp]
  (x: Std.ExtTreeMap α β cmp)
  (y)
  (z)
: x.insertMany #v[(y, z)] = x.insert y z
:= by rfl

@[grind =]
lemma _root_.Id.pure_eq {α : Type} {x : α} : pure (f := Id) x = x := by rfl

end Clap

namespace Array

@[simp, grind =]
lemma foldl_empty_collection
  (α β)
  (f : β → α → β)
  (init)
: Array.foldl f init ∅ = init
:= by rfl

@[simp, grind =]
lemma getElem_idxOf {α : Type} {a : Array α} {x : α} [BEq α] [LawfulBEq α] (h : a.idxOf x < a.size) :
  a[a.idxOf x]'h = x := by
  rcases a with ⟨a⟩
  simp

@[simp, grind ←]
lemma isPrefixOf_rfl {α : Type} [BEq α] [LawfulBEq α] {a : Array α} : a.isPrefixOf a := by
  rcases a
  simp

@[simp, grind →]
lemma isPrefixOf_trans {α : Type} [BEq α] [LawfulBEq α] {a b c : Array α}
  (h₁ : a.isPrefixOf b) (h₂ : b.isPrefixOf c) : a.isPrefixOf c := by
  grind [cases Array]

@[grind =>]
lemma IsPrefix.length_le {α} {l₁ l₂ : Array α} [BEq α] [LawfulBEq α]
  (h : l₁.isPrefixOf l₂) : l₁.size ≤ l₂.size := by
  rcases h₁ : l₁ with ⟨l₁⟩
  rcases h₂ : l₂ with ⟨l₂⟩
  grind

end Array

@[simp, grind =]
lemma Std.ExtTreeMap.mem_insertMany_vector.{u, v}
  {α : Type u}
  {β : Type v}
  {cmp : α → α → Ordering}
  {t : Std.ExtTreeMap α β cmp}
  [Std.TransCmp cmp] [BEq α] [Std.LawfulBEqCmp cmp]
  {len : ℕ}
  {v : Vector (α × β) len}
  {k : α}
:
  k ∈ t.insertMany v ↔ k ∈ t ∨ (v.map Prod.fst).contains k = true
:= by
  obtain ⟨⟨manyList⟩, h_manyList⟩ := v
  have := (@Std.ExtTreeMap.mem_insertMany_list _ _ _ t _ _ _ manyList k).mpr
  simp [Std.ExtTreeMap.insertMany, Std.ExtDTreeMap.Const.insertMany] at ⊢ this
  subst h_manyList
  apply Iff.intro
  · intro a
    simp_all only [implies_true]
    convert Std.ExtTreeMap.mem_insertMany_list.mp _ using 1
    . aesop
    . assumption
    . simpa [Std.ExtTreeMap.insertMany, Std.ExtDTreeMap.Const.insertMany]
  · intro a
    simp_all only [forall_const]

@[grind .]
lemma Std.ExtTreeMap.mem_insertMany_of_mem
  {α β}
  {cmp}
  [BEq α] [Std.TransCmp cmp] [Std.LawfulBEqCmp cmp]
  {k : α}
  {manyLen : ℕ}
  {many : Vector (α × β) manyLen}
  {map : Std.ExtTreeMap α β cmp}
  (h_mem : k ∈ map)
:
  k ∈ map.insertMany many
:= by
  obtain ⟨⟨manyList⟩, h_manyList⟩ := many
  have := (@Std.ExtTreeMap.mem_insertMany_list _ _ _ map _ _ _ manyList k).mpr
  simp [Std.ExtTreeMap.insertMany, Std.ExtDTreeMap.Const.insertMany] at ⊢ this
  apply this
  left
  assumption
