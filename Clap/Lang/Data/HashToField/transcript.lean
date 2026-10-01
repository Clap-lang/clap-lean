import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.RandomOracle.RandomOracle

/-!
# The Poseidon calls `hashElemsToFieldSpec` makes, under the random oracle

`hashElemsToFieldSpec H v` hashes a vector `v = [v₀, …, vₙ₋₁]` of `n ≤ 64` field elements with
Poseidon calls of at most 16 inputs each. With `H = Query.toHashFn f`, each call is a `Query`
(`hashQ u` is the call on the inputs `u`), and its result is `f (hashQ u)`.

- **`n ≤ 16`: one call**, on all of `v`: `hashQ v`, of arity `n`. The hash is `f (hashQ v)`.
- **`17 ≤ n ≤ 64`: `k + 1` calls**, with `k = ⌈n / 16⌉` between 2 and 4.
  - **Chunk calls.** `v` is cut into `k` chunks of 16, the last one shorter when `16 ∤ n`:
    `cᵢ = v.extract (16 * i) (16 * i + 16)`. Each is hashed, `hashQ cᵢ`, giving the chunk digest
    `dᵢ = f (hashQ cᵢ)`.
  - **Final call.** The digests are hashed together, `hashQ #v[d₀, …, dₖ₋₁]`, of arity `k`. The
    hash is `f (hashQ #v[d₀, …, dₖ₋₁])`.

For example, `n = 40` makes the calls `hashQ (v.extract 0 16)`, `hashQ (v.extract 16 32)`,
`hashQ (v.extract 32 48)` (8 elements) and `hashQ #v[d₀, d₁, d₂]`. Through `hashBytesToField`
(31 bytes per element, then the length), `n ≤ 16` is up to 465 bytes, and `n ≤ 64` up to 1953.

The call `hashQ v` and the chunk calls depend on `v` only. The final call depends on `f`, through
the digests `dᵢ`. The definitions below name them:

- `firstQueries v`: the calls on elements of `v`, `{hashQ v}` or `{hashQ c₀, …, hashQ cₖ₋₁}`.
- `leaves v`: the chunk calls `{hashQ c₀, …, hashQ cₖ₋₁}`, empty when `n ≤ 16`.
- `lastQuery f v`: the call whose result is the hash, `hashQ v` or `hashQ #v[d₀, …, dₖ₋₁]`.
- `transcript f v`: all of them, 1 call when `n ≤ 16` and at most `k + 1 ≤ 5` otherwise. `f` on
  these calls determines the hash (`congr`).

A Fiat–Shamir challenge is `f` at a challenge query that takes such a hash as one of its inputs,
e.g. `hashQ #v[H(left), H(right), H(full), ℓL]` in `assertIsConcatenation`. By
`randomOracle_fresh_le` it is uniform as long as the challenge query is not in `transcript f v`:
if it were, its result would be `dᵢ` or the hash itself, already used to build the challenge
query. `challenge_mem_transcript_le` bounds the chance that it is in the transcript by `25 / p`
per hashed vector. That bound is crude, `5 / p` for each of the up to 5 calls whatever its
arity, but it only has to be negligible.
-/

namespace Clap.Lang.HashToField

open Poseidon RandomOracle Primes

variable {n : ℕ}

/-- The calls on elements of `v`, which depend on `v` only:
- `n ≤ 16`: `{hashQ v}`;
- `n > 16`: the chunk calls `{hashQ (v.extract 0 16), hashQ (v.extract 16 32), …}`, 2 to 4 of
  them. -/
def firstQueries (v : Vector (ZMod bn254) n) : Finset Query :=
  if n ≤ 16 then {hashQ v}
  else if n ≤ 32 then {hashQ (v.extract 0 16), hashQ (v.extract 16 32)}
  else if n ≤ 48 then {hashQ (v.extract 0 16), hashQ (v.extract 16 32), hashQ (v.extract 32 48)}
  else {hashQ (v.extract 0 16), hashQ (v.extract 16 32), hashQ (v.extract 32 48),
    hashQ (v.extract 48 64)}

/-- The chunk calls `hashQ (v.extract (16 * i) (16 * i + 16))`, whose results `dᵢ` are the inputs
of the final call. Empty when `n ≤ 16`, where `hashQ v` is the only call and nothing feeds it. -/
def leaves (v : Vector (ZMod bn254) n) : Finset Query :=
  if n ≤ 16 then ∅ else firstQueries v

/-- The call whose result is `hashElemsToFieldSpec (Query.toHashFn f) v`
(`hashElemsToFieldSpec_toHashFn`):
- `n ≤ 16`: `hashQ v`;
- `n > 16`: the final call `hashQ #v[d₀, …, dₖ₋₁]`, with `dᵢ = f (hashQ cᵢ)` the `i`-th chunk
  digest and `cᵢ = v.extract (16 * i) (16 * i + 16)`. It depends on `f`, through the `dᵢ`. -/
def lastQuery (f : Query → ZMod bn254) (v : Vector (ZMod bn254) n) : Query :=
  if n ≤ 16 then hashQ v
  else if n ≤ 32 then hashQ #v[f (hashQ (v.extract 0 16)), f (hashQ (v.extract 16 32))]
  else if n ≤ 48 then hashQ #v[f (hashQ (v.extract 0 16)), f (hashQ (v.extract 16 32)),
    f (hashQ (v.extract 32 48))]
  else hashQ #v[f (hashQ (v.extract 0 16)), f (hashQ (v.extract 16 32)),
    f (hashQ (v.extract 32 48)), f (hashQ (v.extract 48 64))]

/-- Every call `hashElemsToFieldSpec (Query.toHashFn f) v` makes: `{hashQ v}` when `n ≤ 16`, and
the `k` chunk calls plus the final call `hashQ #v[d₀, …, dₖ₋₁]` otherwise (3 to 5 calls). -/
def transcript (f : Query → ZMod bn254) (v : Vector (ZMod bn254) n) : Finset Query :=
  insert (lastQuery f v) (firstQueries v)

lemma hashElemsToFieldSpec_toHashFn (f : Query → ZMod bn254) (v : Vector (ZMod bn254) n) :
    hashElemsToFieldSpec (Query.toHashFn f) v = f (lastQuery f v) := by
  unfold hashElemsToFieldSpec lastQuery
  split_ifs <;> simp (disch := omega) only [toHashFn_apply f]

lemma card_firstQueries_le (v : Vector (ZMod bn254) n) : (firstQueries v).card ≤ 4 := by
  unfold firstQueries
  split_ifs
  · simp
  · exact (Finset.card_insert_le _ _).trans (by simp)
  · exact (Finset.card_insert_le _ _).trans ((Nat.succ_le_succ (Finset.card_insert_le _ _)).trans
      (by simp))
  · refine (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ?_)
    refine (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ?_)
    exact (Finset.card_insert_le _ _).trans (by simp)

lemma leaves_subset (v : Vector (ZMod bn254) n) : leaves v ⊆ firstQueries v := by
  unfold leaves; split_ifs <;> simp

/-- Two functions that agree on the chunk calls give the same final call: its inputs are the
chunk digests `dᵢ`. -/
lemma lastQuery_congr {f f' : Query → ZMod bn254} (v : Vector (ZMod bn254) n)
    (h : ∀ q ∈ leaves v, f q = f' q) : lastQuery f v = lastQuery f' v := by
  unfold leaves firstQueries at h
  unfold lastQuery
  split_ifs at h ⊢ <;> simp_all

/-- Two functions that agree on every call in `transcript f v` give the same hash and the same
calls. -/
lemma congr {f f' : Query → ZMod bn254} (v : Vector (ZMod bn254) n)
    (h : ∀ q ∈ transcript f v, f q = f' q) :
    hashElemsToFieldSpec (Query.toHashFn f) v = hashElemsToFieldSpec (Query.toHashFn f') v ∧
      transcript f v = transcript f' v := by
  have h_last := lastQuery_congr v (fun q hq ↦ h q (Finset.mem_insert_of_mem (leaves_subset v hq)))
  refine ⟨?_, by rw [transcript, transcript, h_last]⟩
  rw [hashElemsToFieldSpec_toHashFn, hashElemsToFieldSpec_toHashFn, ← h_last]
  exact h _ (Finset.mem_insert_self _ _)

/-- When `n ≤ 16` the call whose result is the hash is `hashQ v`, which depends on `v` only. -/
lemma lastQuery_mem_firstQueries_of_le {f : Query → ZMod bn254} (v : Vector (ZMod bn254) n)
    (h : n ≤ 16) : lastQuery f v ∈ firstQueries v := by
  simp [lastQuery, firstQueries, h]

/-- When `n > 16`, input `0` of the final call is the first chunk digest,
`d₀ = f (hashQ (v.extract 0 16))`. -/
lemma coord_lastQuery_zero {f : Query → ZMod bn254} (v : Vector (ZMod bn254) n) (h : 16 < n) :
    (lastQuery f v).coord 0 = f (hashQ (v.extract 0 16)) := by
  unfold lastQuery
  split_ifs <;> first | omega | simp [coord_hashQ]

/-- The hash of `v` equals `κ f` with probability at most `5 / p`, for any `κ` that depends on `f`
only through the chunk digests `dᵢ`.
- `n ≤ 16`: the hash is `f (hashQ v)`, and `κ` is a constant: `1 / p`.
- `n > 16`: the hash is `f` at the final call `hashQ #v[d₀, …, dₖ₋₁]`. If the final call is none
  of the chunk calls, `f` there is uniform given the `dᵢ`: `1 / p`. It is chunk call
  `hashQ cᵢ` only if `d₀ = (hashQ cᵢ).coord 0 = v[16 * i]`, and `d₀` is uniform: `1 / p` for
  each of the at most 4 chunk calls. -/
theorem prob_hash_eq_le (v : Vector (ZMod bn254) n)
    (κ : (Query → ZMod bn254) → ZMod bn254)
    (h_κ : ∀ f f', (∀ q ∈ leaves v, f q = f' q) → κ f = κ f') :
    randomOracle.toOuterMeasure {f | hashElemsToFieldSpec (Query.toHashFn f) v = κ f}
      ≤ 5 / bn254 := by
  classical
  simp only [hashElemsToFieldSpec_toHashFn]
  by_cases hn : n ≤ 16
  · -- a single fixed query, and `κ` reads nothing
    have h_leaves : leaves v = ∅ := by simp [leaves, hn]
    have h := randomOracle_eval_eq_le (hashQ v) κ ∅ (by simp)
      (fun f f' _ ↦ h_κ f f' (by simp [h_leaves]))
    simp only [lastQuery, hn, if_true]
    exact h.trans (ENNReal.div_le_div_right (by norm_num) _)
  · -- the root: fresh, or equal to a leaf
    have h_fresh := randomOracle_fresh_le (fun f ↦ lastQuery f v) (fun _ ↦ ↑(leaves v))
      (fun f y ↦ y = κ f) 1
      (fun f f' h ↦ ⟨lastQuery_congr v h, rfl, by rw [h_κ f f' h]⟩)
      (fun f ↦ by simp [Finset.card_le_one])
    have h_coll : randomOracle.toOuterMeasure {f | lastQuery f v ∈ leaves v} ≤ 4 / bn254 := by
      have h_sub : {f | lastQuery f v ∈ leaves v} ⊆
          ⋃ l ∈ leaves v, {f | f (hashQ (v.extract 0 16)) = l.coord 0} := by
        intro f hf
        simp only [Set.mem_setOf_eq] at hf
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        exact ⟨_, hf, by rw [← coord_lastQuery_zero (f := f) v (by omega)]⟩
      refine (MeasureTheory.measure_mono h_sub).trans ?_
      refine (MeasureTheory.measure_biUnion_finset_le _ _).trans ?_
      calc ∑ l ∈ leaves v,
            randomOracle.toOuterMeasure {f | f (hashQ (v.extract 0 16)) = l.coord 0}
          ≤ ∑ _l ∈ leaves v, (1 / bn254 : ENNReal) :=
            Finset.sum_le_sum fun l _ ↦
              randomOracle_eval_eq_le _ (fun _ ↦ l.coord 0) ∅ (by simp) (fun _ _ _ ↦ rfl)
        _ = (leaves v).card * (1 / bn254 : ENNReal) := by simp
        _ ≤ 4 * (1 / bn254 : ENNReal) := by
            gcongr
            exact_mod_cast (Finset.card_le_card (leaves_subset v)).trans (card_firstQueries_le v)
        _ = 4 / bn254 := by rw [mul_one_div]
    calc randomOracle.toOuterMeasure {f | f (lastQuery f v) = κ f}
        ≤ randomOracle.toOuterMeasure
            ({f | lastQuery f v ∉ (leaves v : Set Query) ∧ f (lastQuery f v) = κ f} ∪
              {f | lastQuery f v ∈ leaves v}) := by
          apply MeasureTheory.measure_mono
          intro f hf
          by_cases h : lastQuery f v ∈ leaves v
          · exact Or.inr h
          · exact Or.inl ⟨by simpa using h, hf⟩
      _ ≤ 1 / bn254 + 4 / bn254 := (MeasureTheory.measure_union_le _ _).trans (add_le_add
            (by simpa using h_fresh) h_coll)
      _ = 5 / bn254 := by rw [ENNReal.div_add_div_same]; norm_num

/-- **The challenge query is one of the calls hashing `v` makes** with probability at most
`25 / p`, when input `j` of the challenge query `c f` is the hash of `v`.

Equal calls have equal inputs, so `c f = t` forces the hash of `v` to equal input `j` of `t`,
`t.coord j`. For `hashQ v` and the chunk calls, `t.coord j` is fixed by `v`: an element of `v`,
or `0` past the call's arity. For the final call it is the chunk digest `dⱼ`, or `0` past `k`.
Either way `prob_hash_eq_le` gives `5 / p`, and there are at most 5 calls: `5 · 5 / p`. -/
theorem challenge_mem_transcript_le (v : Vector (ZMod bn254) n) (j : ℕ)
    (c : (Query → ZMod bn254) → Query)
    (h_c : ∀ f, (c f).coord j = hashElemsToFieldSpec (Query.toHashFn f) v) :
    randomOracle.toOuterMeasure {f | c f ∈ transcript f v} ≤ 25 / bn254 := by
  classical
  have h_sub : {f | c f ∈ transcript f v} ⊆
      {f | hashElemsToFieldSpec (Query.toHashFn f) v = (lastQuery f v).coord j} ∪
        ⋃ t ∈ firstQueries v, {f | hashElemsToFieldSpec (Query.toHashFn f) v = t.coord j} := by
    intro f hf
    simp only [Set.mem_setOf_eq, transcript, Finset.mem_insert] at hf
    rcases hf with h | h
    · left
      simp only [Set.mem_setOf_eq]
      rw [← h, h_c f]
    · right
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨c f, h, (h_c f).symm⟩
  have h_last : randomOracle.toOuterMeasure
      {f | hashElemsToFieldSpec (Query.toHashFn f) v = (lastQuery f v).coord j} ≤ 5 / bn254 :=
    prob_hash_eq_le v _ (fun f f' h ↦ by rw [lastQuery_congr v h])
  have h_first : ∀ t ∈ firstQueries v, randomOracle.toOuterMeasure
      {f | hashElemsToFieldSpec (Query.toHashFn f) v = t.coord j} ≤ 5 / bn254 :=
    fun t _ ↦ prob_hash_eq_le v (fun _ ↦ t.coord j) (fun _ _ _ ↦ rfl)
  refine (MeasureTheory.measure_mono h_sub).trans ((MeasureTheory.measure_union_le _ _).trans ?_)
  calc randomOracle.toOuterMeasure
          {f | hashElemsToFieldSpec (Query.toHashFn f) v = (lastQuery f v).coord j} +
        randomOracle.toOuterMeasure
          (⋃ t ∈ firstQueries v, {f | hashElemsToFieldSpec (Query.toHashFn f) v = t.coord j})
      ≤ 5 / bn254 + ∑ _t ∈ firstQueries v, (5 / bn254 : ENNReal) :=
        add_le_add h_last ((MeasureTheory.measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum h_first))
    _ ≤ 5 / bn254 + 4 * (5 / bn254 : ENNReal) := by
        gcongr
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast card_firstQueries_le v
    _ = 25 / bn254 := by
        rw [← mul_div_assoc, ENNReal.div_add_div_same]
        norm_num

end Clap.Lang.HashToField
