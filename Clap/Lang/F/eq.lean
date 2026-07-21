import Clap.Lang.F.F
import Clap.Lang.FB.FB

namespace Clap.Edsl.Lang.F

def eq {p : ℕ} [p.AtLeastTwo] (a b : F p) : Edsl.CircuitStateM p (FB p) := do
  Edsl.isZero (a - b)

namespace eq

lemma wellFormed {p : ℕ} [p.AtLeastTwo] (a b : F p):
  (eq a b).wellFormed
:= by
  simp [eq]

-- TODO represents
def matchesBinaryBooleanFunctionWithSideEffects
  (p : ℕ)
  [p.AtLeastTwo]
  (spec_function : (ZMod p) → (ZMod p) → Bool)
  (function : (F p) → (F p) → Edsl.CircuitStateM p (FB p))
  (allocates : ℕ)
: Prop :=
  ∀ (a b: F p) varStorePre numAlloc,
  a.isValid varStorePre →
  b.isValid varStorePre →
  let a_eval := (a.eval varStorePre).getD 0
  let b_eval := (b.eval varStorePre).getD 0
  let ⟨⟨result, circuit⟩, numAllocPostRun⟩ := ((function a b).run numAlloc)
    let ⟨numAllocPostEval, varStorePost, constraints⟩ := Edsl.CircuitState.eval
      circuit
      varStorePre
      numAlloc
    result.eval varStorePost = (FB.ofBool p (spec_function a_eval b_eval)).eval varStorePost ∧
    constraints = True ∧
    numAllocPostRun = numAlloc + allocates ∧
    numAllocPostRun = numAllocPostEval ∧
    ∀ i < numAlloc, varStorePost.get? i = varStorePre.get? i ∧
    let e := a-b
    varStorePost.get? numAlloc = .some (if (e.eval varStorePre) = .some 0 then 1 else 0)

def spec (p : ℕ) [p.AtLeastTwo]: Prop := matchesBinaryBooleanFunctionWithSideEffects
  p
  (· == ·)
  F.eq
  (allocates := 1)

lemma equiv (p : ℕ) [p.AtLeastTwo] :
  spec p
:= by
  intro a b varStorePre numAlloc h_a_isValid h_b_isValid
  obtain ⟨a_eval, h_a_eval⟩ := Option.isSome_iff_exists.mp h_a_isValid
  obtain ⟨b_eval, h_b_eval⟩ := Option.isSome_iff_exists.mp h_b_isValid
  have hsub : [varStorePre|a - b] = some (a_eval - b_eval) :=
    FixedExp.eval_sub_some h_a_eval h_b_eval
  -- Pivot: the circuit stores `1` iff `a` and `b` evaluate equal.
  have hzero : ([varStorePre|a - b] = some 0) = (a_eval = b_eval) := by
    rw [hsub]; simp [sub_eq_zero]
  -- Reduce `(F.eq a b).run` and the evaluation of its single `isZero` command to concrete form.
  simp only [F.eq, isZero, Clap.monads, CircuitStateM.alloc_eq,
    CircuitState.mul_eq_append, CircuitState.one_eq_nil, List.append_nil,
    CircuitState.eval_singleton, CircuitResult.step_isZero]
  -- The post-run store is `varStorePre` with `numAlloc ↦ (if a_eval = b_eval then 1 else 0)`;
  -- `simp` folds the singleton `insertMany` to `insert` and discharges the two numeric conjuncts.
  simp
  refine ⟨?_, ?_, ?_⟩
  · -- value correctness: the fresh variable reads back the stored `if a_eval = b_eval …`,
    -- which matches `FB.ofBool p (a_eval == b_eval)`.
    simp only [hzero, h_a_eval, h_b_eval, Option.getD_some, FB.eval_true, FB.eval_false,
      GetElem?.getElem?]
    grind
  · -- constraint: `a - b` is allocated because it evaluates.
    simp [Membership.mem, CircuitResult.get?_unconstrained, hsub]
  · -- frame rule: keys `i < numAlloc` are untouched by inserting at `numAlloc`.
    intro i hi
    simp only [hzero]
    grind [Std.ExtTreeMap.getElem?_insert]


end eq

end Clap.Edsl.Lang.F
