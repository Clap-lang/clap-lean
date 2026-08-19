import Clap.Lang.F.F
import Clap.Lang.FB.FB

namespace Clap.Lang.F

open HashConsM in
def eq {p : ℕ} [p.AtLeastTwo] (a b : F p) : ClapM p (FB p) := do
  let x ← mkSub a b
  isZero x

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
  (function : (F p) → (F p) → Edsl.CircuitM p (FB p))
  (allocates : ℕ)
: Prop :=
  ∀ (a b: F p) varStorePre numAlloc,
  a.isValid varStorePre →
  b.isValid varStorePre →
  let a_eval := (a.eval varStorePre).getD 0
  let b_eval := (b.eval varStorePre).getD 0
  let ⟨⟨result, circuit⟩, numAllocPostRun⟩ := ((function a b).run numAlloc)
    let ⟨numAllocPostEval, varStorePost, constraints⟩ := Edsl.Circuit.eval
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
  sorry
  -- intro a b varStorePre numAlloc h_a_isValid h_b_isValid
  -- obtain ⟨a_eval, h_a_eval⟩ := Option.isSome_iff_exists.mp h_a_isValid
  -- obtain ⟨b_eval, h_b_eval⟩ := Option.isSome_iff_exists.mp h_b_isValid
  -- aesop (add simp [
  --   Clap.monads,
  --   F.eq,
  --   isZero,
  --   FB.ofBool.equiv,
  -- ]) (add safe (by grind))


end eq

end Clap.Edsl.Lang.F
