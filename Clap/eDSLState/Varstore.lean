import Mathlib.Data.ZMod.Basic
import Std.Data.ExtTreeMap
import Clap.eDSLState.Wheels

namespace Clap

def VarStore (p : ℕ) := Std.ExtTreeMap ℕ (ZMod p) (cmp := compare)
deriving Inhabited

instance {p : ℕ} : EmptyCollection (VarStore p) := inferInstanceAs (EmptyCollection (Std.ExtTreeMap ℕ (ZMod p)))

instance {p : ℕ} : GetElem? (VarStore p) ℕ (ZMod p) (λ Γ x ↦ Γ.contains x) where
  getElem  Γ x h := Γ.get x h
  getElem? Γ x   := Γ.get? x

@[simp, grind =]
lemma VarStore.getElem?_insert_self {p : ℕ} {Γ : VarStore p} {k : ℕ} {v : ZMod p} :
  (Γ.insert k v)[k]? = some v
:= Std.ExtTreeMap.getElem?_insert_self

@[simp, grind =]
lemma VarStore.get?_insert_self {p : ℕ} {Γ : VarStore p} {k : ℕ} {v : ZMod p} :
  (Γ.insert k v).get? k = some v
:= Std.ExtTreeMap.getElem?_insert_self

/-- Inserting at indices `≥ len_start`, for any keys/values, never disturbs an index below `len_start` -/
private lemma VarStore.getElem?_insertMany_list_range'_zip_frame {p : ℕ}
    (Γ : VarStore p) (start len n : ℕ) (vals : List (ZMod p)) (hn : n < start) :
    (Γ.insertMany ((List.range' start len).zip vals))[n]? = Γ[n]? := by
  apply Std.ExtTreeMap.getElem?_insertMany_list_of_contains_eq_false
  simp only [List.contains_eq_mem, decide_eq_false_iff_not, List.mem_map]
  rintro ⟨⟨a, b⟩, hmem, rfl⟩
  have ha := (List.of_mem_zip hmem).1
  rw [List.mem_range'_1] at ha
  omega

/-- Inserting `k` fresh values at indices `numAlloc, numAlloc+1, ..., numAlloc+k-1` never disturbs
    any index below `numAlloc` -/
theorem VarStore.getElem?_insertMany_alloc_of_lt {p k numAlloc n : ℕ} {vals : Vector (ZMod p) k}
    (Γ : VarStore p) (hn : n < numAlloc) :
    (Γ.insertMany ((Vector.range k).map (·+numAlloc) |>.zip vals))[n]? = Γ[n]? := by
  rw [Std.ExtTreeMap.insertMany_vector_eq_insertMany_toList]
  simp only [Vector.toList_zip, Vector.toList_map, Vector.toList_range, range_map_add_eq_range']
  exact VarStore.getElem?_insertMany_list_range'_zip_frame Γ numAlloc k n vals.toList hn

/-- The `i`-th of `k` fresh values inserted starting at `start` lands at index `start+i` -/
private theorem VarStore.getElem?_insertMany_range'_zip {p : ℕ} :
    ∀ (Γ : VarStore p) (start : ℕ) (vals : List (ZMod p)) {i : ℕ} (hi : i < vals.length),
      (Γ.insertMany ((List.range' start vals.length).zip vals))[start + i]? = some vals[i]
  | _Γ, _start, [], _i, hi => absurd hi (by simp)
  | Γ, start, v :: vs, 0, _ => by
      simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, Nat.add_zero]
      rw [Std.ExtTreeMap.insertMany_cons,
        VarStore.getElem?_insertMany_list_range'_zip_frame (Γ.insert start v) (start + 1) vs.length
          start vs (by omega)]
      exact Std.ExtTreeMap.getElem?_insert_self
  | Γ, start, v :: vs, i+1, hi => by
      simp only [List.length_cons, List.range'_succ, List.zip_cons_cons]
      rw [Std.ExtTreeMap.insertMany_cons]
      have hi' : i < vs.length := by simpa using hi
      have key := VarStore.getElem?_insertMany_range'_zip (Γ.insert start v) (start + 1) vs
        (i := i) hi'
      have heq : start + (i + 1) = start + 1 + i := by omega
      rw [heq, key]
      rfl

/-- `CircuitResult.alloc`'s decode fact: the `i`-th of `k` freshly-allocated values (at indices
    `numAlloc, ..., numAlloc+k-1`) is retrievable at index `numAlloc+i`. -/
theorem VarStore.getElem?_insertMany_alloc_of_lt' {p k numAlloc i : ℕ} {vals : Vector (ZMod p) k}
    (Γ : VarStore p) (hi : i < k) :
    (Γ.insertMany ((Vector.range k).map (·+numAlloc) |>.zip vals))[numAlloc+i]? = some vals[i] := by
  rw [Std.ExtTreeMap.insertMany_vector_eq_insertMany_toList]
  simp only [Vector.toList_zip, Vector.toList_map, Vector.toList_range, range_map_add_eq_range']
  have hlen : vals.toList.length = k := Vector.length_toList
  have hi' : i < vals.toList.length := by rw [hlen]; exact hi
  have key := VarStore.getElem?_insertMany_range'_zip Γ numAlloc vals.toList (i := i) hi'
  rw [hlen] at key
  rw [key]
  simp [Vector.getElem_toList]

end Clap
