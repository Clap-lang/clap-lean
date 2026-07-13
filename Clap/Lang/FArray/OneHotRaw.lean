import Clap.Lang.F.eq

namespace Clap.Edsl.Lang.FArray

variable {p : ℕ}

def oneHotRaw [Fact (p ≥ 2)] (len : ℕ) (idx : F p) : Edsl.CircuitStateM p (Vector (FB p) len) :=
  (Vector.range len).mapM (fun (i:ℕ) ↦ F.eq idx i)

namespace oneHotRaw

def runAndEval
  {p : ℕ} {ResultT : Type} (cmd : CircuitStateM p ResultT) (numAlloc : ℕ) (varStore : Std.ExtTreeMap ℕ (ZMod p))
:
  ResultT × CircuitResult p
:=
  let ⟨⟨result, circuit⟩, _numAlloc⟩ := (cmd.run numAlloc)
  ⟨result, Edsl.CircuitState.eval circuit varStore numAlloc⟩


-- def matchesUnaryBitVecFunctionWithSideEffects
--   {length: ℕ}
--   (p : ℕ)
--   [Fact (p ≥ 2)]
--   (spec_function : (ZMod p) → Vector Bool length)
--   (function : (F p) → Edsl.CircuitStateM p (Vector (FB p) length))
--   (allocates : ℕ)
-- : Prop :=
--   ∀ (a : F p) varStorePre numAllocPre,
--   a.isValid (varStorePre.get?) →
--   let a_eval := (a.eval varStorePre.get?).getD 0
--   let ⟨result, numAllocPost, varStorePost, constraints⟩ := runAndEval (function a) numAllocPre varStorePre
--   result.map (FB.toBool · varStorePost.get?) = spec_function a_eval ∧
--   constraints = True ∧
--   numAllocPost = numAllocPre + allocates ∧
--   ∀ i < numAllocPre, varStorePost.get? i = varStorePre.get? i ∧
--   ∀ (i: Fin length),
--     varStorePost.get? (numAllocPost - i) =
--     .some (((spec_function a_eval).get ⟨length - 1 - i, by {
--       omega
--     }⟩).toNat)

def specFunction (n : ℕ) : Fin n → Vector Bool n := fun i ↦
  Vector.ofFn λ (idx : Fin n) => idx.val == i

def isValidRange (x : F p) (varStore : ℕ → Option (ZMod p)) : Prop :=
  let x.eval varStore

instance {k p} [Fact (k ≤ p)] : FB.Convert p (F p) (Fin k) where
  isValid varStore x := _
  size := _
  toLinear := _
  toIdeal := _
  toRepresents := _
  someOfIsValid := _
  toIdealtoRepresents := _
  toRepresentstoIdeal := _

def spec (p : ℕ) (length : ℕ) [Fact (p ≥ 2)] : Prop :=
  Clap.Edsl.Lang.FB.matchesUnaryMonadFunction
  p
  (specFunction length)
  (oneHotRaw length)
  length

lemma equiv (p : ℕ) (length : ℕ) [Fact (p ≥ 2)] :
  spec p length
:= by
  unfold spec
  intro a varStorePre numAllocPre h_a_isValid
  obtain ⟨a_eval, h_a_eval⟩ := Option.isSome_iff_exists.mp h_a_isValid
  aesop (add simp [
    Clap.monads,
    oneHotRaw,
    F.eq.equiv
  ]) (add safe (by grind))

end oneHotRaw

end Clap.Edsl.Lang.FArray
