import Clap.Lang.FB.FB
import Clap.Lang.FB.not

import Clap.eDSLState.Writer
import Clap.eDSLState.Wheels

namespace Clap.Lang.FB

def assert {p : ℕ} [Fact (p ≥ 2)] (a : FB p) : Edsl.CircuitStateM p Unit := do
  Edsl.eq0 (not a)

namespace assert

-- TODO do we need a relation between varStore and numAlloc
-- perhaps that varStore is full up to numAlloc?
def matchesUnaryPredicatePure
  (p : ℕ)
  (spec_function : Bool → Prop)
  (function : FB p → Edsl.CircuitStateM p Unit)
: Prop :=
  ∀ (a : FB p) varStore numAlloc, a.isValid (varStore.get?) →
    let ⟨numAllocPost, varStorePost, constraints⟩ := Edsl.CircuitState.eval
      ((function a).run numAlloc).1.2
      varStore
      numAlloc
    constraints = spec_function (a.toBool varStore.get?) ∧
    numAllocPost = numAlloc ∧
    varStorePost = varStore

def spec (p : ℕ) [Fact (p ≥ 2)] : Prop := matchesUnaryPredicatePure p (·) FB.assert

lemma equiv {p : ℕ} [Fact (p ≥ 2)] :
  spec p
:= by
  intro a varStore numAlloc h_isValid
  simp [Clap.monads, FB.assert]
  done

end assert

end Clap.Lang.FB
