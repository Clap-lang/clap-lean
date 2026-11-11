import Clap.Model.Monad
import Clap.Model.Convert.PaddedVector
import Clap.Lang.Data.FString.isPaddedOf
import Clap.Lang.Core.Combinators.ofFnM
import Clap.Lang.Core.FB.conditionallyAssert

open Clap Lang FString FArray Primes

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



end assertFieldName
