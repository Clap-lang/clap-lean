import Clap.Lang.FB.FB
import Clap.Lang.FB.not

namespace Clap.Edsl.Lang.FB

def assert {p : ℕ} [p.AtLeastTwo] (a : FB p) : Edsl.CircuitStateM p Unit := do
  Edsl.eq0 (not a)

namespace assert

-- TODO do we need a relation between varStore and numAlloc
-- perhaps that varStore is full up to numAlloc?
def matchesUnaryPredicatePure
  (p : ℕ)
  (spec_function : Bool → Prop)
  (function : FB p → Edsl.CircuitStateM p Unit)
: Prop :=
  ∀ (a : FB p) varStore numAlloc, a.isValid (varStore) →
    let ⟨numAllocPost, varStorePost, constraints⟩ := Edsl.CircuitState.eval
      ((function a).getCircuit numAlloc)
      varStore
      numAlloc
    constraints = spec_function (a.toBool varStore) ∧
    numAllocPost = numAlloc ∧
    varStorePost = varStore

def spec (p : ℕ) [p.AtLeastTwo] : Prop := matchesUnaryPredicatePure p (·) FB.assert

lemma aux
  {p : ℕ}
  {varStore : VarStore p}
  [p.AtLeastTwo]
  {a : FB p}
:
  [varStore|a] = [varStore|false p] →
  [varStore|a.not] = [varStore|FB.ofBool p ((λ x => !x) (FB.toBool (false p) varStore))]
:= by
  simp
  have := FB.not.equiv (p := p)
  have :=

  intro h_a_false
  specialize this a varStore (by simp [h_a_false, IsValid.isValid, FB.isValid, eval_false])
  simp at this
  have :
    [varStore|a.not] = [varStore|Convert.toRepresents p (Convert.toIdeal varStore a.not).get (Convert.someOfIsValid)]

lemma equiv (p : ℕ) [p.AtLeastTwo] :
  spec p
:= by
  intro a varStore numAlloc h_isValid
  have := FB.not.equiv (p := p)
  simp [FB.assert]
  have :
    unconstrained[numAlloc][varStore][a.not]? =
    unconstrained[numAlloc][varStore][FB.ofBool p ((fun x => !x) (a.toBool varStore))]?
  := by
    unfold matchesUnaryFunction at this
    specialize this a varStore h_isValid
    simp [Convert.toIdeal, FB.toBool] at this
    simp [getElem?, FB.toBool]
    apply isValid_iff_eval_eq_eval_false_or_eval_true.mp at h_isValid
    grind
    obtain h_val | h_val := h_isValid
    -- have : [varStore|a.not] = [varStore|a]
    <;> simp [h_val, this]

  have getElem?_unconstrained (e : FixedExp p):
    unconstrained[numAlloc][varStore][e]? =
    [varStore|e]
  := rfl
  simp [this, getElem?_unconstrained]

end assert

end Clap.Edsl.Lang.FB
