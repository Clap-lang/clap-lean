import Clap.Lang.Core.F.dotProduct
import Clap.Lang.Data.FArray.arraySelector

namespace Clap.Lang

variable {p : ℕ}

namespace enforceNotNested

/-- A vector's sum is the `Fin`-indexed sum of its entries. -/
private lemma vector_sum_eq_fin_sum {len : ℕ} (v : Vector (ZMod p) len) :
    v.sum = ∑ i : Fin len, v[i] := by
  rw [← Vector.sum_toList, ← List.sum_ofFn]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- Extracting `[s, e)` out of a vector and summing it is the same as summing over every index,
counting only those inside the window. -/
lemma extract_sum_eq_window_sum {len : ℕ} (v : Vector (ZMod p) len) (s e : ℕ) :
    (v.extract s e).sum = ∑ i : Fin len, if s ≤ i.val ∧ i.val < e then v[i] else 0 := by
  rw [vector_sum_eq_fin_sum, ← Finset.sum_filter]
  apply Finset.sum_bij'
    (i := fun (a : Fin (min e len - s)) _ => (⟨s + a.val, by omega⟩ : Fin len))
    (j := fun (b : Fin len) (hb : b ∈ Finset.univ.filter fun i : Fin len => s ≤ i.val ∧ i.val < e) =>
      (⟨b.val - s, by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb; omega⟩ :
        Fin (min e len - s)))
  case hi =>
    intro a _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  case hj =>
    intro a _
    exact Finset.mem_univ _
  case left_neg =>
    intro a _
    apply Fin.ext
    simp
  case right_neg =>
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    apply Fin.ext
    simp
    omega
  case h =>
    intro a _
    simp [Fin.getElem_fin, Vector.getElem_extract]

/-- Pointwise, multiplying by the XOR-of-two-masks indicator (as computed by `arraySelector`)
is the same as the clean `[s, e)` window indicator, given `s ≤ e`. -/
lemma xor_mask_mul_eq_window_ite {len : ℕ} {s e : ℕ} (h_idx : s ≤ e)
    (v : Vector (ZMod p) len) (i : Fin len) :
    v[i] * (if (decide (s ≤ i.val) ^^ decide (e ≤ i.val)) then (1 : ZMod p) else 0)
      = if s ≤ i.val ∧ i.val < e then v[i] else 0 := by
  rcases lt_or_ge i.val s with h | h
  · have h1 : ¬ (s ≤ i.val) := by omega
    have h2 : ¬ (e ≤ i.val) := by omega
    simp [h1, h2]
  · rcases lt_or_ge i.val e with h' | h'
    · have h2 : ¬ (e ≤ i.val) := by omega
      simp [h, h2, h']
    · have h1 : s ≤ i.val := by omega
      simp [h1, h']

lemma dotProduct_eq0_convertsM
  [p.AtLeastTwo]
  {len : ℕ}
  {state : ClapMState p}
  {a : FVec p len}
  {a_vals : Vector (ZMod p) len}
  {mask : FArray p len}
  {mask_vals : Vector Bool len}
  (h_a : Converts FVec.conversion state a a_vals)
  (h_mask : Converts FArray.conversion state mask mask_vals)
:
  ConvertsM FUnit.conversion
    (dotProduct a mask >>= fun o => eq0 o)
    state
    ()
    ((a_vals.zip (mask_vals.map (fun b => if b then (1 : ZMod p) else 0))).foldl
      (fun acc xy => acc + xy.1 * xy.2) 0 = 0)
:= by
  have h_mask_f := FVec.converts_of_FArray_converts h_mask
  step dotProduct.convertsM h_a h_mask_f as o
  apply convertsM_of_convertsM (eq0.convertsM h_o)
  · rfl
  · simp

/-- `arraySelector`'s own constraint and `dotProduct`+`eq0`'s assertion can both fail, so this is
assembled with `convertsM_bind_and` rather than `step`. Stated over an abstract preceding
`action` (rather than inlining `arraySelector len startIdx endIndex`) so that instantiating it at
the end is a cheap substitution instead of a `whnf`-unfolding unification — see
docs/proving-circuits.md's failure-modes table, "state the bind over an abstract action". -/
lemma arraySelector_tail_convertsM
  [p.AtLeastTwo]
  {len : ℕ}
  {state : ClapMState p}
  {action : ClapM p (FArray p len)}
  {mask_val : Vector Bool len}
  {constraints1 : Prop}
  {a : FVec p len}
  {a_vals : Vector (ZMod p) len}
  (h_action : ConvertsM FArray.conversion action state mask_val constraints1)
  (h_a : Converts FVec.conversion state a a_vals)
:
  ConvertsM FUnit.conversion
    (action >>= fun bracketsSelector => dotProduct a bracketsSelector >>= fun o => eq0 o)
    state
    ()
    (constraints1 ∧
      (a_vals.zip (mask_val.map (fun b => if b then (1 : ZMod p) else 0))).foldl
        (fun acc xy => acc + xy.1 * xy.2) 0 = 0)
:=
  convertsM_bind_and h_action
    (dotProduct_eq0_convertsM (converts_skip h_action h_a) h_action.result)

end enforceNotNested

end Clap.Lang
