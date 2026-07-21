import Clap.Lang.F.F

namespace Clap.Edsl.Lang.F

def dotProduct {p : ℕ} [Fact (p ≥ 2)] {w : ℕ} (a b : Vector (F p) w) : F p :=
  (a.zipWith (· * ·) b).foldl (· + ·) 0

namespace dotProduct

/-- When every entry evaluates, `toIdeal` of a vector is the pointwise-decoded vector. -/
lemma toIdeal_vec {p : ℕ} {w : ℕ} {vs : VarStore p} (a : Vector (F p) w)
    (h : ∀ x ∈ a, ([vs|x]).isSome) :
    Convert.toIdeal vs a = some (a.map (fun x => ([vs|x]).getD 0)) := by
  unfold_projs
  simp only [F.toZMod_def]
  have hmap : a.map (fun x => [vs|x]) = (a.map (fun x => ([vs|x]).getD 0)).map some := by
    rw [Vector.map_map]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Function.comp_apply]
    have hi' := h a[i] (Vector.getElem_mem hi)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hi'
    simp [hv]
  rw [hmap, Vector.map_map]
  rw [Vector.mapM_map]
  exact Vector.mapM_pure (m := Option) _

/-- Evaluating the syntactic left-fold `l.foldl (·+·) init`, when every summand is valid,
    equals `some` of the running sum over the decoded values. -/
lemma eval_foldl_add_valid {p : ℕ} {vs : VarStore p} (l : List (F p)) :
    ∀ (init : F p) (z : ZMod p), [vs|init] = some z → (∀ x ∈ l, ([vs|x]).isSome) →
    [vs | l.foldl (· + ·) init] = some (z + (l.map (fun x => ([vs|x]).getD 0)).sum) := by
  induction l with
  | nil => intro init z hinit _; simpa using hinit
  | cons x xs ih =>
    intro init z hinit hvalid
    have hx : ([vs|x]).isSome := hvalid x (by simp)
    obtain ⟨xv, hxv⟩ := Option.isSome_iff_exists.mp hx
    have hinit' : [vs | init + x] = some (z + xv) := by
      rw [FixedExp.add_def, FixedExp.eval_add, hinit, hxv]; rfl
    have hrest : ∀ y ∈ xs, ([vs|y]).isSome := fun y hy => hvalid y (by simp [hy])
    rw [List.foldl_cons, ih (init + x) (z + xv) hinit' hrest]
    simp only [List.map_cons, List.sum_cons, hxv, Option.getD_some]
    ring_nf

/-- The sum of a vector's `toList` is the `Finset` sum over its indices. -/
lemma sum_toList {p : ℕ} {w : ℕ} (V : Vector (ZMod p) w) :
    V.toList.sum = ∑ i : Fin w, V[i] := by
  rw [← Fin.sum_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

/-- `eval` of the dot-product circuit is `some` of the ideal dot product. -/
lemma eval_dotProduct {p : ℕ} [Fact (p ≥ 2)] {w : ℕ} {vs : VarStore p} (a b : Vector (F p) w)
    (ha : ∀ x ∈ a, ([vs|x]).isSome)
    (hb : ∀ x ∈ b, ([vs|x]).isSome) :
    [vs | dotProduct a b] = some (∑ i : Fin w, ([vs|a[i]]).getD 0 * ([vs|b[i]]).getD 0) := by
  unfold dotProduct
  rw [← Vector.foldl_toList]
  have hvalid : ∀ y ∈ (a.zipWith (· * ·) b).toList, ([vs|y]).isSome := by
    intro y hy
    rw [List.mem_iff_getElem] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    have hiw : i < w := by simpa using hi
    have hai := ha a[i] (Vector.getElem_mem hiw)
    have hbi := hb b[i] (Vector.getElem_mem hiw)
    obtain ⟨av, hav⟩ := Option.isSome_iff_exists.mp hai
    obtain ⟨bv, hbv⟩ := Option.isSome_iff_exists.mp hbi
    simp only [Vector.getElem_toList, Vector.getElem_zipWith, FixedExp.mul_def,
      FixedExp.eval_mul, hav, hbv]
    rfl
  rw [eval_foldl_add_valid _ 0 0 (by simp) hvalid, zero_add]
  congr 1
  rw [← Vector.toList_map, sum_toList]
  apply Finset.sum_congr rfl
  intro i _
  have hai := ha a[i.val] (Vector.getElem_mem i.isLt)
  have hbi := hb b[i.val] (Vector.getElem_mem i.isLt)
  obtain ⟨av, hav⟩ := Option.isSome_iff_exists.mp hai
  obtain ⟨bv, hbv⟩ := Option.isSome_iff_exists.mp hbi
  simp [FixedExp.mul_def, FixedExp.eval_mul, hav, hbv]

/-- `∑ i, a[i] * b[i]`. -/
def spec (p : ℕ) [Fact (p ≥ 2)] (w : ℕ) : Prop :=
  matchesBinaryFunction p (fun (a b : Vector (ZMod p) w) ↦ ∑ i : Fin w, a[i] * b[i]) (dotProduct (p := p) (w := w))

lemma equiv (p : ℕ) [Fact (p ≥ 2)] (w : ℕ) : spec p w := by
  unfold spec matchesBinaryFunction
  intro a b vs h₁ h₂
  have ha : ∀ x ∈ a, ([vs|x]).isSome := by
    intro x hx; have h := h₁; unfold_projs at h; exact h x hx
  have hb : ∀ x ∈ b, ([vs|x]).isSome := by
    intro x hx; have h := h₂; unfold_projs at h; exact h x hx
  rw [Convert.toIdeal_toRepresents, F.toIdeal_def]
  rw [eval_dotProduct a b ha hb]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [toIdeal_vec a ha, toIdeal_vec b hb]

end dotProduct

end Clap.Edsl.Lang.F
