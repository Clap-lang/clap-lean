import Clap.RandomOracle.HashFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Probability.Distributions.Uniform

/-!
# The random oracle

The standard idealisation is to prove security bounds for a hash family `H` drawn uniformly
at random from all functions on the queries the circuit can make, and to read those bounds for
the real Poseidon. Security lemmas are stated for `H := Query.toHashFn f` with `f ← randomOracle`.
Circuit lemmas are stated for any `H` with `Lang.Poseidon.Computes H`. The real Poseidon is one such `H`; treating
it as if it had been sampled is the heuristic, stated here in words because it cannot be stated in
Lean.

## Fiat–Shamir challenges

A challenge is the answer at a query that is itself built from hashes. So the query depends on
`f`, and `randomOracle_eval`, which is about a fixed query, does not apply. `randomOracle_fresh_le` applies, since
, while the challenge query is outside the queries its own inputs read, its answer is
uniform. The chance that it is not outside them is a collision term, bounded per gadget
(`Clap/Lang/Data/HashToField/transcript.lean`).

Every bound here is over the same `f ← randomOracle`. So several Fiat–Shamir checks in one circuit
compose by `measure_union_le` on one measure, with no product of distributions. They are bounds for
a fixed instance, chosen before `f`. An adaptive prover that picks the instance after querying `f`
needs a query budget and a binding argument on top, which is not formalised here.

## Scope

The random oracle hides algebraic attacks on Poseidon (CICO-style finding inputs on which a low-degree check vanishes).
Use it for Fiat–Shamir challenges (Schwartz–Zippel needs a uniformly random evaluation point). -/

open scoped ENNReal Polynomial

namespace Clap.RandomOracle

open Primes

/-- The random oracle. A uniformly random function on queries. -/
noncomputable def randomOracle : PMF (Query → ZMod Primes.bn254) := PMF.uniformOfFintype _

section uniform

private lemma card_fiber_eval {Q F : Type} [Fintype Q] [DecidableEq Q] [Fintype F]
    [DecidableEq F] (q : Q) (y : F) :
    (Finset.univ.filter (fun H : Q → F ↦ H q = y)).card = Fintype.card F ^ (Fintype.card Q - 1)
:= by
  rw [← Fintype.card_subtype]
  have e : {H : Q → F // H q = y} ≃ ({i // i ≠ q} → F) :=
    { toFun := fun H i ↦ H.1 i.1
      invFun := fun g ↦ ⟨fun i ↦ if h : i = q then y else g ⟨i, h⟩, by simp⟩
      left_inv := fun H ↦ by
        ext i; by_cases h : i = q
        · subst h; simp [H.2]
        · simp [h]
      right_inv := fun g ↦ by ext ⟨i, hi⟩; simp [hi] }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]

/-- Evaluating a uniformly random function at a fixed point gives a uniformly random value. -/
theorem uniform_map_eval {Q F : Type} [Fintype Q] [DecidableEq Q] [Fintype F] [Nonempty F]
    [DecidableEq F] (q : Q) :
    (PMF.uniformOfFintype (Q → F)).map (fun H ↦ H q) = PMF.uniformOfFintype F
:= by
  ext y
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hfilt : (Finset.univ.filter (fun H : Q → F ↦ y = H q)) =
      (Finset.univ.filter (fun H : Q → F ↦ H q = y)) := by
    ext H; simp [eq_comm]
  rw [hfilt, card_fiber_eval, Fintype.card_fun]
  have hQ : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨q⟩
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card Q = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hQ).symm⟩
  rw [hm, Nat.add_sub_cancel, pow_succ]
  push_cast
  rw [ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp)]
  simp

/-- Each answer of the random oracle is uniformly distributed -/
theorem randomOracle_eval (q : Query) :
    randomOracle.map (fun H ↦ H q) = PMF.uniformOfFintype (ZMod Primes.bn254)
:= uniform_map_eval q

end uniform

section bounds

/-- Schwartz–Zippel, univariate: a uniformly random field element is a root of a fixed nonzero
polynomial with probability at most `natDegree P / |F|`. -/
lemma uniform_isRoot_le {p : ℕ} [Fact (Nat.Prime p)] [NeZero p] (P : (ZMod p)[X]) (hP : P ≠ 0) :
    (PMF.uniformOfFintype (ZMod p)).toOuterMeasure {α | P.eval α = 0} ≤ (P.natDegree : ℝ≥0∞) / (Fintype.card (ZMod p))
:= by
  classical
  have hrootsEq : {α : ZMod p | P.eval α = 0} = ↑P.roots.toFinset := by
    ext x; simp [Polynomial.mem_roots hP]
  rw [hrootsEq, PMF.toOuterMeasure_uniformOfFintype_apply]
  gcongr
  norm_cast
  rw [Fintype.card_coe]
  exact le_trans (Multiset.toFinset_card_le P.roots) (Polynomial.card_roots' P)

/-- Union bound over two draws: if each event is unlikely under its own distribution, their
disjunction is unlikely under the joint draw. Needs no independence, subadditivity suffices,
which is why several Fiat–Shamir checks in one circuit compose. -/
lemma union_bound_pair {α β : Type} (μ : PMF α) (ν : PMF β)
    (E₁ : α → Prop) (E₂ : β → Prop) (ε₁ ε₂ : ℝ≥0∞)
    (h₁ : μ.toOuterMeasure {a | E₁ a} ≤ ε₁) (h₂ : ν.toOuterMeasure {b | E₂ b} ≤ ε₂) :
    (μ.bind fun a ↦ ν.map fun b ↦ (a, b)).toOuterMeasure {x | E₁ x.1 ∨ E₂ x.2} ≤ ε₁ + ε₂
:= by
  set P := μ.bind fun a ↦ ν.map fun b ↦ (a, b) with hP
  have hFst : P.map Prod.fst = μ := by
    simp only [hP, PMF.map_bind, PMF.map_comp]
    have : ∀ a : α, ν.map (Prod.fst ∘ fun b ↦ (a, b)) = PMF.pure a := fun a ↦ by
      have heq : (Prod.fst ∘ fun b : β ↦ (a, b)) = Function.const _ a := by ext; simp
      rw [heq, PMF.map_const]
    simp_rw [this, PMF.bind_pure]
  have hSnd : P.map Prod.snd = ν := by
    simp only [hP, PMF.map_bind, PMF.map_comp]
    have : ∀ a : α, ν.map (Prod.snd ∘ fun b ↦ (a, b)) = ν := fun a ↦ by
      have heq : (Prod.snd ∘ fun b : β ↦ (a, b)) = id := by ext; simp
      rw [heq, PMF.map_id]
    simp_rw [this, PMF.bind_const]
  calc P.toOuterMeasure {x | E₁ x.1 ∨ E₂ x.2}
      ≤ P.toOuterMeasure (Prod.fst ⁻¹' {a | E₁ a} ∪ Prod.snd ⁻¹' {b | E₂ b}) :=
          MeasureTheory.measure_mono (fun _ h ↦ h)
    _ ≤ P.toOuterMeasure (Prod.fst ⁻¹' {a | E₁ a}) + P.toOuterMeasure (Prod.snd ⁻¹' {b | E₂ b}) :=
          MeasureTheory.measure_union_le _ _
    _ = μ.toOuterMeasure {a | E₁ a} + ν.toOuterMeasure {b | E₂ b} := by
          simp only [← PMF.toOuterMeasure_map_apply, hFst, hSnd]
    _ ≤ ε₁ + ε₂ := add_le_add h₁ h₂

end bounds

section fresh

/-- **A fresh query answers uniformly.** Let `g f` be a query computed from the random function
`f` (a Fiat–Shamir challenge query, whose inputs are themselves hashes), `T f` the queries its
computation reads, and `E f` a set of at most `K` bad answers. If `g`, `T` and `E` are
determined by `f` on `T f`, then the answer at `g f` is bad, while `g f` is outside `T f`, with
probability at most `K / |F|`.

The proof resamples `f` at `g f`. That changes nothing `g`, `T` or `E` read, so
`(f', z) ↦ (update f' (g f') z, f' (g f'))` injects the bad functions times `F` into the pairs
`(f, y)` with `y` bad for `f`, of which there are at most `|Q → F| · K`. -/
theorem uniform_fresh_le {Q F : Type} [Fintype Q] [DecidableEq Q] [Fintype F] [DecidableEq F]
    [Nonempty F]
    (g : (Q → F) → Q) (T : (Q → F) → Set Q) (E : (Q → F) → F → Prop)
    [∀ f, DecidablePred (E f)] (K : ℕ)
    (h_det : ∀ f f', (∀ q ∈ T f, f q = f' q) → g f = g f' ∧ T f = T f' ∧ E f = E f')
    (h_K : ∀ f, (Finset.univ.filter (E f)).card ≤ K) :
    (PMF.uniformOfFintype (Q → F)).toOuterMeasure {f | g f ∉ T f ∧ E f (f (g f))}
      ≤ K / Fintype.card F := by
  classical
  set B := Finset.univ.filter (fun f : Q → F ↦ g f ∉ T f ∧ E f (f (g f))) with hB
  set S := Finset.univ.filter (fun fy : (Q → F) × F ↦ E fy.1 fy.2) with hS
  -- resampling `f'` at its fresh query is an injection of `B × F` into `S`
  have h_upd : ∀ f', g f' ∉ T f' → ∀ z,
      g (Function.update f' (g f') z) = g f' ∧ T (Function.update f' (g f') z) = T f' ∧
        E (Function.update f' (g f') z) = E f' := by
    intro f' hf' z
    have := h_det f' (Function.update f' (g f') z) (fun q hq ↦ by
      rw [Function.update_of_ne (show q ≠ g f' from fun h ↦ hf' (by rw [← h]; exact hq))])
    exact ⟨this.1.symm, this.2.1.symm, this.2.2.symm⟩
  have h_card : (B ×ˢ (Finset.univ : Finset F)).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn
      (fun fz : (Q → F) × F ↦ (Function.update fz.1 (g fz.1) fz.2, fz.1 (g fz.1)))
    · intro ⟨f', z⟩ h
      simp only [hB, Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_univ,
        true_and, Set.mem_setOf_eq, Finset.coe_univ, Set.mem_univ, and_true] at h
      simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [(h_upd f' h.1 z).2.2]
      exact h.2
    · intro ⟨f₁, z₁⟩ h₁ ⟨f₂, z₂⟩ h₂ heq
      simp only [hB, Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_univ,
        true_and, Set.mem_setOf_eq, Finset.coe_univ, Set.mem_univ, and_true] at h₁ h₂
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hf, hy⟩ := heq
      have hg : g f₁ = g f₂ := by
        rw [← (h_upd f₁ h₁.1 z₁).1, ← (h_upd f₂ h₂.1 z₂).1, hf]
      have hf₁ : f₁ = Function.update (Function.update f₁ (g f₁) z₁) (g f₁) (f₁ (g f₁)) := by
        simp
      have hf₂ : f₂ = Function.update (Function.update f₂ (g f₂) z₂) (g f₂) (f₂ (g f₂)) := by
        simp
      have hff : f₁ = f₂ := by rw [hf₁, hf₂, hf, hy, hg]
      subst hff
      refine Prod.ext rfl ?_
      have := congrFun hf (g f₁)
      simpa using this
  have h_S : S.card ≤ Fintype.card (Q → F) * K := by
    rw [hS, Finset.card_filter, Fintype.sum_prod_type]
    calc ∑ f : Q → F, ∑ y : F, (if E f y then 1 else 0)
        = ∑ f : Q → F, (Finset.univ.filter (E f)).card := by
          congr 1; ext f; rw [Finset.card_filter]
      _ ≤ ∑ _f : Q → F, K := Finset.sum_le_sum fun f _ ↦ h_K f
      _ = Fintype.card (Q → F) * K := by simp
  have h_B : B.card * Fintype.card F ≤ K * Fintype.card (Q → F) := by
    have := h_card.trans h_S
    rw [Finset.card_product, Finset.card_univ] at this
    linarith
  have h_set : {f | g f ∉ T f ∧ E f (f (g f))} = (B : Set (Q → F)) := by
    ext f; simp [hB]
  rw [h_set, PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [Finset.coe_sort_coe, Fintype.card_coe]
  have hF : (Fintype.card F : ℝ≥0∞) ≠ 0 := by simp
  have hN : (Fintype.card (Q → F) : ℝ≥0∞) ≠ 0 := by simp
  calc (B.card : ℝ≥0∞) / Fintype.card (Q → F)
      = (B.card * Fintype.card F) / (Fintype.card (Q → F) * Fintype.card F) := by
        rw [ENNReal.mul_div_mul_right _ _ hF (by simp)]
    _ ≤ (K * Fintype.card (Q → F)) / (Fintype.card (Q → F) * Fintype.card F) := by
        exact ENNReal.div_le_div_right (by exact_mod_cast h_B) _
    _ = K / Fintype.card F := by
        rw [mul_comm (Fintype.card (Q → F) : ℝ≥0∞), ENNReal.mul_div_mul_right _ _ hN (by simp)]

/-- `uniform_fresh_le` for the random oracle. -/
theorem randomOracle_fresh_le
    (g : (Query → ZMod Primes.bn254) → Query) (T : (Query → ZMod Primes.bn254) → Set Query)
    (E : (Query → ZMod Primes.bn254) → ZMod Primes.bn254 → Prop) [∀ f, DecidablePred (E f)]
    (K : ℕ)
    (h_det : ∀ f f', (∀ q ∈ T f, f q = f' q) → g f = g f' ∧ T f = T f' ∧ E f = E f')
    (h_K : ∀ f, (Finset.univ.filter (E f)).card ≤ K) :
    randomOracle.toOuterMeasure {f | g f ∉ T f ∧ E f (f (g f))} ≤ K / Primes.bn254 := by
  have := uniform_fresh_le g T E K h_det h_K
  rwa [ZMod.card] at this

/-- The answer at a fixed query hits a value determined elsewhere with probability `1 / p`. -/
theorem randomOracle_eval_eq_le (q : Query) (κ : (Query → ZMod Primes.bn254) → ZMod Primes.bn254)
    (S : Set Query) (h_q : q ∉ S) (h_κ : ∀ f f', (∀ q' ∈ S, f q' = f' q') → κ f = κ f') :
    randomOracle.toOuterMeasure {f | f q = κ f} ≤ 1 / Primes.bn254 := by
  classical
  have := randomOracle_fresh_le (fun _ ↦ q) (fun _ ↦ S) (fun f y ↦ y = κ f) 1
    (fun f f' h ↦ ⟨rfl, rfl, by rw [h_κ f f' h]⟩)
    (fun f ↦ by simp [Finset.card_le_one])
  refine le_trans (MeasureTheory.measure_mono fun f hf ↦ ?_) (by simpa using this)
  exact ⟨h_q, hf⟩

end fresh

end Clap.RandomOracle
