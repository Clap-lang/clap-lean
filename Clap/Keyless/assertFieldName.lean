import Clap.Model.Convert.PaddedVector
import Clap.Lang.Data.FString.isPaddedOf
import Clap.Lang.Core.FB.conditionallyAssert

open Clap Lang FString Primes

/-- Assert that the field name (without the padding) matches the `expected` ASCII values.
    We expect `guard = 1` to be the default value, but can't enforce it.
-/
def assertFieldName {n : ℕ}
  (name : FString bn254 n)
  (expected : String)
  (guard : FB bn254 /- := 1 -/) : -- `mkF 1` can't be assigned as a default value
  ClapM bn254 Unit
:= do
  let isEq ← name.isPaddedOf expected
  FB.conditionallyAssert guard isEq

namespace assertFieldName

lemma convertsM {n : ℕ}
  {state : ClapMState bn254}
  {name : FString bn254 n}
  {expected : String}
  {guard : FB bn254}
  -- Ideal values
  {name_val : String}
  {guard_val : Bool}
  -- Conversion hypotheses
  (h_name : Converts FString.conversion state name name_val)
  (h_guard : Converts FB.conversion state guard guard_val)
  :
  let isPaddedOfSpec : Bool :=
    encodeV (p := bn254) n name_val == encodeV n expected &&
      (name_val.length : ZMod bn254) == (expected.length : ZMod bn254)
  ConvertsM FUnit.conversion (assertFieldName name expected guard) state ()
    (guard_val → isPaddedOfSpec)
:= by
  intro isEq
  unfold assertFieldName
  step isPaddedOf.convertsM h_name as eq
  apply convertsM_of_convertsM (FB.conditionallyAssert.convertsM h_guard h_eq)
  · rfl
  · simp [isEq]

lemma convertsM_string {n : ℕ}
  {state : ClapMState bn254}
  {name : FString bn254 n}
  {expected : String}
  {guard : FB bn254}
  -- Ideal values
  {name_val : String}
  {guard_val : Bool}
  -- Conversion hypotheses
  (h_name : Converts FString.conversion state name name_val)
  (h_guard : Converts FB.conversion state guard guard_val)
  -- Required
  (h_name_len : name_val.length < n)
  (h_expected_len : expected.length < n)
  (h_name_chars : ∀ c ∈ name_val.toList, c.toNat < 256)
  (h_expected_chars : ∀ c ∈ expected.toList, c.toNat < 256)
  (h_n : n < bn254)
  :
  let isPaddedOfSpec : Bool := name_val == expected
  ConvertsM FUnit.conversion (assertFieldName name expected guard) state ()
    (guard_val → isPaddedOfSpec)
:= by
  intro isEq
  unfold assertFieldName
  have h256 : 256 < bn254 := by decide
  step (isPaddedOf.convertsM_string h_name h_name_len h_expected_len h_name_chars
    h_expected_chars h256 h_n) as eq
  apply convertsM_of_convertsM (FB.conditionallyAssert.convertsM h_guard h_eq)
  · rfl
  · simp [isEq]

end assertFieldName
