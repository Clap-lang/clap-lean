import Lean

import Mathlib.Data.ZMod.Basic

@[simp]
theorem Vector.range_one : Vector.range 1 = #v[0] := rfl

namespace Clap

initialize Lean.registerTraceClass `Clap.Preprocessor

initialize Lean.registerTraceClass `Clap.Preprocessor.addLambdas (inherited := true)

register_simp_attr Clap.monads

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

theorem Vector.forIn_eq_forIn_toList
  {α : Type*} {m : Type* → Type*} [Monad m] {γ} {n}
  (v : Vector α n) (init : γ) (step : α → γ → m (ForInStep γ))
: ForIn.forIn v init step = ForIn.forIn v.toList init step
:= by
  obtain ⟨arr, harr⟩ := v
  rw [Vector.forIn_mk, show (Vector.mk arr harr).toList = arr.toList from rfl,
    Array.forIn_toList]

theorem Std.ExtTreeMap.insertMany_vector_eq_insertMany_toList
  {α β : Type*} {cmp} [Std.TransCmp cmp]
  (t : Std.ExtTreeMap α β cmp) {n} (v : Vector (α × β) n)
: t.insertMany v = t.insertMany v.toList
:= by
  unfold Std.ExtTreeMap.insertMany Std.ExtDTreeMap.Const.insertMany
  simp only [Vector.forIn_eq_forIn_toList]

private lemma range_map_add_eq_range'_gen (s numAlloc k : ℕ) :
    (List.range' s k).map (·+numAlloc) = List.range' (s+numAlloc) k := by
  induction k generalizing s with
  | zero => simp
  | succ k ih => simp [List.range'_succ, ih, Nat.add_right_comm]

theorem range_map_add_eq_range' (numAlloc k : ℕ) :
    (List.range k).map (·+numAlloc) = List.range' numAlloc k := by
  rw [List.range_eq_range']
  simpa using range_map_add_eq_range'_gen 0 numAlloc k

@[simp, grind =]
lemma Array.foldl_empty_collection
  (α β)
  (f : β → α → β)
  (init)
: Array.foldl f init ∅ = init
:= by rfl

end Clap
