import Clap.RandomOracle.HashFn
import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkSub
import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.F.conditionalSwap
import Clap.Lang.Core.FB.eq
import Clap.Lang.Core.FB.not
import Clap.Lang.Gate.isZero
import Clap.Lang.Core.Combinators.scanlM
import Clap.Lang.Core.Combinators.mapM
import Clap.Model.Convert.PaddedVector
import Clap.Lang.Core.FUnit.guardedEq0
import Clap.Util.Primes
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Lang.Data.FString.isSubstring
import Clap.Lang.Data.FArray.selectArrayValue
import Clap.Lang.Core.FUnit.guardedAssertEq

namespace Clap.Lang

open Primes

def parseJWTFieldSharedLogic
    {maxKVPairLen maxNameLen maxValueLen : ℕ}
    (h_name_len  : maxNameLen  ≤ maxKVPairLen)
    (h_value_len : maxValueLen ≤ maxKVPairLen)
    (field       : FString bn254 maxKVPairLen)
    (name        : FString bn254 maxNameLen)
    (value       : FString bn254 maxValueLen)
    (colon_index : F bn254)
    (value_index : F bn254)
    (skipChecks  : FB bn254 /- := 0 -/) -- `mkF 0` can't be assigned as a default value
    : ClapM bn254 Unit
:= do
  let perform : FB bn254 ← not skipChecks
  -- Check 0: name_len < colon_index
  -- w = 20 bits suffices for comparisons: 2^20 = 1_048_576 > any realistic JWT field length.
  -- Hardcoded in https://github.com/aptos-labs/keyless-zk-proofs/blob/main/circuit/templates/helpers/jwt/ParseJWTFieldSharedLogic.circom
  let w := 20
  guardedEq0 perform (← not (← lessThan w name.len colon_index))
  -- Check 1: colon_index < value_index
  guardedEq0 perform (← not (← lessThan w colon_index value_index))
  -- Check 2: field_len > name_len + value_len
  guardedEq0 perform (← not (← greaterThan w field.len (← name.len + value.len)))
  -- Pre-compute hash of field for Fiat-Shamir substring checks
  let fieldHash ← HashToField.hashBytesToField field
  -- Check 3: field[0] == '"' (ASCII 34)
  let firstChar ← selectArrayValue maxKVPairLen field.data (← mkF 0)
  guardedAssertEq perform firstChar (← mkF '\"'.toNat)
  -- Check 4: name is a substring of field starting at index 1
  let nameOk ← FString.isSubstring h_name_len field.data fieldHash name (← mkF 1)
  guardedEq0 perform (← not nameOk)
  -- Check 5: field[name_len + 1] == '"' (ASCII 34)
  let nameClosingQuote ← selectArrayValue maxKVPairLen field.data (← name.len + (← mkF 1))
  guardedAssertEq perform nameClosingQuote (← mkF '\"'.toNat)
  -- Check 6: field[colon_index] == ':' (ASCII 58)
  let colonChar ← selectArrayValue maxKVPairLen field.data colon_index
  guardedAssertEq perform colonChar (← mkF ':'.toNat)
  -- Check 7: value is a substring of field starting at value_index
  let valueOk ← FString.isSubstring h_value_len field.data fieldHash value value_index
  guardedEq0 perform (← not valueOk)
  -- Check 8: field[field_len - 1] == ',' (44) or '}' (125)
  let lastChar ← selectArrayValue maxKVPairLen field.data (← field.len - (← mkF 1))
  -- Enforce (lastChar - 44) * (lastChar - 125) == 0
  guardedEq0 perform (← (← lastChar - (← mkF ','.toNat)) * (← lastChar - (← mkF '}'.toNat)))

namespace parseJWTFieldSharedLogic

open Poseidon RandomOracle Primes FiatShamir

open FString

def parses (H : HashFn) {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (field_vals : Vector (ZMod bn254) maxKVPairLen)
  (field_len : ZMod bn254)
  (name_vals : Vector (ZMod bn254) maxNameLen)
  (name_len : ZMod bn254)
  (value_vals : Vector (ZMod bn254) maxValueLen)
  (value_len : ZMod bn254)
  (colon_index_val value_index_val : ZMod bn254)
  (skipChecks_val  : Bool) :
  Prop
:=
  let fieldHash := HashToField.hashBytesToFieldSpec H field_vals field_len
  ¬skipChecks_val →
    name_len.val < colon_index_val.val ∧
    colon_index_val.val < value_index_val.val ∧
    field_len.val > (name_len + value_len).val ∧
    field_vals.getD 0 0 = 34 ∧
    isSubstring.accepts H field_vals fieldHash name_vals name_len 1 = true ∧
    field_vals.getD (name_len + 1).val 0 = 34 ∧
    field_vals.getD colon_index_val.val 0 = 58 ∧
    isSubstring.accepts H field_vals fieldHash value_vals value_len value_index_val = true ∧
    (field_vals.getD (field_len - 1).val 0 = 44 ∨ field_vals.getD (field_len - 1).val 0 = 125)

lemma convertsM
  {H : HashFn}
  (h_H : Computes H)
  {state : ClapMState bn254}
  -- Circuit arguments
  {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (h_name_len_lt  : maxNameLen  ≤ maxKVPairLen)
  (h_value_len_lt : maxValueLen ≤ maxKVPairLen)
  -- Needed by `hashBytesToField.convertsM` (`numBytes ≤ 1953`) and, via `h_name_len_lt` /
  -- `h_value_len_lt` and `maxKVPairLen ≤ 1953 ≪ bn254`, by `isSubstring.convertsM`'s
  -- `m ≤ 1953`, `n < bn254` and `2 ^ (minBits' n + 1) < bn254` for both substring checks.
  (h_len_bound    : maxKVPairLen ≤ 1953)
  {field       : FString bn254 maxKVPairLen}
  {name        : FString bn254 maxNameLen}
  {value       : FString bn254 maxValueLen}
  {colon_index : F bn254}
  {value_index : F bn254}
  {skipChecks  : FB bn254}
  -- Ideal values
  {field_vals : Vector (ZMod bn254) maxKVPairLen}
  {field_len : ZMod bn254}
  {name_vals : Vector (ZMod bn254) maxNameLen}
  {name_len : ZMod bn254}
  {value_vals : Vector (ZMod bn254) maxValueLen}
  {value_len : ZMod bn254}
  {colon_index_val value_index_val : ZMod bn254}
  {skipChecks_val  : Bool}
  -- Conversion hypotheses
  (h_field_val : Converts FVec.conversion state field.data field_vals)
  (h_field_len : Converts F.conversion state field.len field_len)
  (h_name_val : Converts FVec.conversion state name.data name_vals)
  (h_name_len : Converts F.conversion state name.len name_len)
  (h_value_val : Converts FVec.conversion state value.data value_vals)
  (h_value_len : Converts F.conversion state value.len value_len)
  (h_ci : Converts F.conversion state colon_index colon_index_val)
  (h_vi : Converts F.conversion state value_index value_index_val)
  (h_sk : Converts FB.conversion state skipChecks skipChecks_val)
  -- Range bounds (`w := 20` is hard-coded in the body)
  (h_name_len_w : name_len.val < 2 ^ 20)
  (h_colon_index_w : colon_index_val.val < 2 ^ 20)
  (h_value_index_w : value_index_val.val < 2 ^ 20)
  (h_field_len_w : field_len.val < 2 ^ 20)
  (h_sum_len_w : (name_len + value_len).val < 2 ^ 20)
  :
  ConvertsM FUnit.conversion
    (parseJWTFieldSharedLogic h_name_len_lt h_value_len_lt field name value
      colon_index
      value_index
      skipChecks
    )
    state
    ()
    ( (∀ i : Fin maxKVPairLen, field_vals[i].val < 2^8) ∧
      (∀ i : Fin maxNameLen, name_vals[i].val < 2^8) ∧
      (∀ i : Fin maxValueLen, value_vals[i].val < 2^8) ∧

      name_len.val + 1 < maxKVPairLen ∧
      -- /- redundant -/ 0 < maxKVPairLen ∧
      colon_index_val.val < maxKVPairLen ∧
      (field_len - 1).val < maxKVPairLen ∧

      -- /- redundant -/ 1 < 2 ^ minBits' maxKVPairLen ∧
      -- /- redundant -/ (1 + name_len).val < 2 ^ minBits' maxKVPairLen ∧
      -- /- redundant -/ 1 < maxKVPairLen ∧
      -- 1 < (1 + name_len).val ∧ /- equivalent -/
      0 < name_len.val ∧

      -- /- redundant -/ value_index_val.val < 2 ^ minBits' maxKVPairLen ∧
      (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen ∧
      value_index_val.val < maxKVPairLen ∧
      0 < value_len.val ∧

      parses H field_vals field_len name_vals name_len value_vals value_len
        colon_index_val
        value_index_val
        skipChecks_val
    )
:= sorry


end parseJWTFieldSharedLogic
