import Clap.Lang.FB.FB
import Clap.Lang.FB.not
import Clap.Lang.FB.and

namespace Clap.Edsl.Lang.FB

def assert {p : ℕ} [Fact (p ≥ 2)] (a : FB p) : Edsl.CircuitStateM p Unit := do
  Edsl.eq0 (not a)

def assertBool {p : ℕ} [Fact (p ≥ 2)] (a : FB p) : Edsl.CircuitStateM p Unit := do
  Edsl.eq0 (and a a.not)

def conditionallyAssert {p : ℕ} [Fact (p ≥ 2)] (antecedent consequent : FB p) :
  Edsl.CircuitStateM p Unit
:= do
  -- a → c ≡ ¬(a ∧ ¬c)
  Edsl.eq0 (and antecedent consequent.not)

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

def matchesBinaryPredicatePure
  (p : ℕ)
  (spec_function : Bool → Bool → Prop)
  (function : FB p → FB p → Edsl.CircuitStateM p Unit)
: Prop :=
  ∀ (a b : FB p) varStore numAlloc,
    a.isValid (varStore.get?) →
    b.isValid (varStore.get?) →
    let ⟨numAllocPost, varStorePost, constraints⟩ := Edsl.CircuitState.eval
      ((function a b).run numAlloc).1.2
      varStore
      numAlloc
    constraints = spec_function (a.toBool varStore.get?) (b.toBool varStore.get?) ∧
    numAllocPost = numAlloc ∧
    varStorePost = varStore


def assert_spec (p : ℕ) [Fact (p ≥ 2)] : Prop := matchesUnaryPredicatePure p (·) FB.assert

lemma assert_equiv (p : ℕ) [Fact (p ≥ 2)] :
  assert_spec p
:= by
  intro a varStore numAlloc h_isValid
  simp [
    Clap.monads,
    FB.assert,
    h_isValid,
    not.equiv a,
    ofBool.equiv]

def assertBool_spec (p : ℕ) [Fact (p ≥ 2)] : Prop :=
  matchesUnaryPredicatePure p (Function.const Bool True) FB.assertBool

lemma assertBool_equiv (p : ℕ) [Fact (p ≥ 2)] :
  assertBool_spec p
:= by
  intro a varStore numAlloc h_isValid
  simp [
    Clap.monads,
    FB.assertBool,
    and.equiv a a.not _ h_isValid (not.not_isValid h_isValid)
  ]
  simp_all [toBool, not.equiv a, ofBool.equiv]

def conditionallyAssert_spec (p : ℕ) [Fact (p ≥ 2)] : Prop :=
  matchesBinaryPredicatePure p (fun a c ↦ !(a && !c)) FB.conditionallyAssert

lemma conditionallyAssert_equiv (p : ℕ) [Fact (p ≥ 2)] :
  conditionallyAssert_spec p
:= by
  intro a c varStore numAlloc h_isValid_a h_isValid_c
  simp [
    Clap.monads,
    FB.conditionallyAssert,
    and.equiv a c.not _ h_isValid_a (not.not_isValid h_isValid_c),
    ofBool.equiv,
    ]
  by_cases h₁ : a.toBool varStore.get? <;>
  by_cases h₂ : c.toBool varStore.get? <;>
  simp [h₁, h₂, not.not_toBool h_isValid_c]

end assert

end Clap.Edsl.Lang.FB
