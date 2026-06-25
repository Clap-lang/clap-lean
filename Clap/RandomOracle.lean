import Clap.Lang
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Probability.Distributions.Uniform

open Clap.Lang
open scoped Polynomial

/-!
# Random-Oracle Model for Fiat–Shamir Circuits

This file provides the abstract random-oracle (RO) infrastructure used to state and compose
soundness lemmas for every Fiat–Shamir (FS) circuit in this library.

## Background

Circuits such as `isSubstringFS` and `assertIsConcatenation` use the Fiat–Shamir heuristic:
a Poseidon hash of the circuit inputs serves as a "random" challenge `α`. In Lean we model Poseidon
as an abstract random oracle (`ROModel`) whose output for any query is uniformly distributed over
`ZMod q`. This gives:

- **Soundness**: false-accept probability bounded by `degree / |F|` via Schwartz–Zippel (`uniform_isRoot_le`).
- **Composability**: multiple FS calls in one circuit compose via union bound (`ro_union_bound`) —
  no independence of the challenges is needed, subadditivity of outer measure suffices.

## The Four-Layer Proof Stack

```
Layer 4  _sound_RO           ROModel (Poseidon abstraction)
              │  ro.uniform query
Layer 3  _aux_sound_prob     PMF.uniformOfFintype  (concrete uniform distribution)
              │  uniform_isRoot_le
Layer 2  uniform_isRoot_le   Schwartz–Zippel  (generic, proved once here)
              │  Polynomial.card_roots'
Layer 1  _aux_sound_card     Deterministic root count
```

**Layer 2 — `uniform_isRoot_le`** (this file): for a nonzero polynomial `p` of degree `D`, a
uniform random `α` over `ZMod q` is a root with probability `≤ D / |F|`.

**Layer 4 — `_sound_RO`** (per-circuit, in `FString.lean`): takes `(ro : ROModel bn254)`. Rewrites
`ro.chal query` to `PMF.uniformOfFintype` via `ro.uniform`, then calls Layer 3. When the sorries
are filled, this proof is a one-liner:
```lean
lemma myCircuit_sound_RO (ro : ROModel bn254) ... :
    (ro.chal (myCircuitQuery ...)).toOuterMeasure {...}
      ≤ ((D - 1 : ℕ) : ENNReal) / |F| := by
  rw [ro.uniform]
  exact myCircuit_aux_sound_prob ...
``` -/

namespace Spec.FString

open Primes

/-- Abstract random-oracle model over `ZMod q`: `chal query` is the (modelled-uniform) Poseidon
    output for a given input list; `uniform` asserts every answer is uniform.
    A complete model would also record independence of distinct-query answers -/
structure ROModel (q : ℕ) [NeZero q] where
  chal    : List (ZMod q) → PMF (ZMod q)
  uniform : ∀ query, chal query = PMF.uniformOfFintype (ZMod q)

/-- **(Schwartz–Zippel)** A uniformly random field element is a root of a fixed nonzero polynomial
    with probability at most `deg p / |F|`. -/
lemma uniform_isRoot_le {q : ℕ} [Fact (Nat.Prime q)] [NeZero q] (p : (ZMod q)[X]) (hp : p ≠ 0) :
    (PMF.uniformOfFintype (ZMod q)).toOuterMeasure {α | p.eval α = 0}
      ≤ (p.natDegree : ENNReal) / (Fintype.card (ZMod q)) := by
  classical
  have hrootsEq : {α : ZMod q | p.eval α = 0} = ↑p.roots.toFinset := by
    ext x; simp [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
  rw [hrootsEq, PMF.toOuterMeasure_uniformOfFintype_apply]
  gcongr
  norm_cast
  rw [Fintype.card_coe]
  exact le_trans (Multiset.toFinset_card_le p.roots) (Polynomial.card_roots' p)

/-- **Union bound** over two RO queries.

    `E₁`, `E₂` are the false-accept events for two FS calls; the joint distribution is the product
    `(ro.chal q₁) ⊗ (ro.chal q₂)`. By outer-measure subadditivity:
    `P(E₁(α₁) ∨ E₂(α₂)) ≤ P(E₁(α₁)) + P(E₂(α₂)) ≤ ε₁ + ε₂`.

    No independence of `q₁` and `q₂` is assumed (TODO: do we need it?). -/
lemma ro_union_bound (ro : ROModel bn254)
    (q₁ q₂ : List (ZMod bn254))
    (E₁ E₂ : ZMod bn254 → Prop)
    (ε₁ ε₂ : ENNReal)
    (h₁ : (ro.chal q₁).toOuterMeasure {α | E₁ α} ≤ ε₁)
    (h₂ : (ro.chal q₂).toOuterMeasure {α | E₂ α} ≤ ε₂) :
    ((ro.chal q₁).bind fun α₁ => (ro.chal q₂).map fun α₂ => (α₁, α₂)).toOuterMeasure
        {p | E₁ p.1 ∨ E₂ p.2}
      ≤ ε₁ + ε₂ := by
  -- joint distribution P := (ro.chal q₁) ⊗ (ro.chal q₂)
  set P := (ro.chal q₁).bind fun α₁ => (ro.chal q₂).map fun α₂ => (α₁, α₂) with hP
  -- first marginal: fst-projection recovers ro.chal q₁
  have hFst : P.map Prod.fst = ro.chal q₁ := by
    simp only [hP, PMF.map_bind, PMF.map_comp]
    have : ∀ α₁ : ZMod bn254,
        (ro.chal q₂).map (Prod.fst ∘ fun α₂ => (α₁, α₂)) = PMF.pure α₁ := fun α₁ => by
      have heq : (Prod.fst ∘ fun α₂ : ZMod bn254 => (α₁, α₂)) = Function.const _ α₁ := by
        ext; simp
      rw [heq, PMF.map_const]
    simp_rw [this, PMF.bind_pure]
  -- second marginal: snd-projection recovers ro.chal q₂
  have hSnd : P.map Prod.snd = ro.chal q₂ := by
    simp only [hP, PMF.map_bind, PMF.map_comp]
    have : ∀ α₁ : ZMod bn254,
        (ro.chal q₂).map (Prod.snd ∘ fun α₂ => (α₁, α₂)) = ro.chal q₂ := fun α₁ => by
      have heq : (Prod.snd ∘ fun α₂ : ZMod bn254 => (α₁, α₂)) = id := by ext; simp
      rw [heq, PMF.map_id]
    simp_rw [this, PMF.bind_const]
  -- union bound via outer-measure subadditivity + marginal equalities
  calc P.toOuterMeasure {p | E₁ p.1 ∨ E₂ p.2}
      ≤ P.toOuterMeasure (Prod.fst ⁻¹' {α | E₁ α} ∪ Prod.snd ⁻¹' {α | E₂ α}) :=
          MeasureTheory.measure_mono (fun _ h => h)
    _ ≤ P.toOuterMeasure (Prod.fst ⁻¹' {α | E₁ α}) +
        P.toOuterMeasure (Prod.snd ⁻¹' {α | E₂ α}) :=
          MeasureTheory.measure_union_le _ _
    _ = (ro.chal q₁).toOuterMeasure {α | E₁ α} +
        (ro.chal q₂).toOuterMeasure {α | E₂ α} := by
          simp only [← PMF.toOuterMeasure_map_apply, hFst, hSnd]
    _ ≤ ε₁ + ε₂ := add_le_add h₁ h₂

end Spec.FString
