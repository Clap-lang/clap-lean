import Clap.Poseidon.Computes
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Probability.Distributions.Uniform

/-!
# Poseidon as a random oracle

The standard idealisation, adopted here, is to prove security bounds for a hash family `H` drawn uniformly
at random from all functions on the queries the circuit can make, and to read those bounds for
the real Poseidon. Security lemmas are stated for `H := Query.toHashFn f` with `f ← randomOracle`.
Circuit lemmas are stated for any `H` with `Computes H`. -/

open scoped ENNReal Polynomial

namespace Clap.Poseidon

/-- `bn254 ≠ 0` -/
instance instNeZeroBn254 : NeZero Primes.bn254 := ⟨by decide⟩

/-- One call to Poseidon is denoted as query. A query is a pair `⟨n, v⟩`:
* `n` is how many inputs are hashed (the *arity*);
* `v : Fin n → ZMod Primes.bn254` is the list of those `n` inputs, `v 0` up to `v (n - 1)`.

For example, hashing the three field elements `a, b, c` is the query `⟨3, ![a, b, c]⟩`.

The random oracle gives back one field element for each query. Since `n` is part of the query,
hashing 3 inputs and hashing 4 inputs are unrelated.

`n` ranges over `Fin 17`. `16` is the largest number of inputs circomlib's Poseidon accepts, and so the largest `Computes`
covers. -/
abbrev Query := Σ n : Fin 17, (Fin n → ZMod Primes.bn254)

/-- The random oracle. A uniformly random function on queries. -/
noncomputable def randomOracle : PMF (Query → ZMod Primes.bn254) := PMF.uniformOfFintype _

/-- Read a function on queries as a hash family -/
def Query.toHashFn (f : Query → ZMod Primes.bn254) : HashFn :=
  fun {n} v ↦ if h : n < 17 then f ⟨⟨n, h⟩, fun i ↦ v[i]⟩ else 0

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

end Clap.Poseidon
