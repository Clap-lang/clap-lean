import Clap.RandomOracle.HashFn
import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkSub
import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.F.conditionalSwap
import Clap.Lang.Core.FB.eq
import Clap.Lang.Core.FB.not
import Clap.Lang.Core.FB.or
import Clap.Lang.Data.F8.isWhitespace
import Clap.Lang.Gate.isZero
import Clap.Lang.Core.Combinators.scanlM
import Clap.Lang.Core.Combinators.mapM
import Clap.Model.Convert.PaddedVector
import Clap.Lang.Core.FUnit.guardedEq0
import Clap.Util.Primes
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Lang.Data.FString.isSubstring
import Clap.Lang.Data.FArray.selectArrayValue
import Clap.Lang.Data.FArray.arraySelectorComplex
import Clap.Lang.Core.FUnit.guardedAssertEq
import Clap.Lang.Data.JWT.parseJWTFieldSharedLogic
import Mathlib.Data.List.GetD

namespace Clap.Lang

open Primes

def parseEmailVerifiedField
  {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (h_name_len  : maxNameLen  ≤ maxKVPairLen)
  (h_value_len : maxValueLen ≤ maxKVPairLen)
  (field       : FString bn254 maxKVPairLen)
  (name        : FString bn254 maxNameLen)
  (value       : FString bn254 maxValueLen)
  (colonIndex : F bn254)
  (valueIndex : F bn254)
  : ClapM bn254 Unit
:= do
  -- Delegate shared structural checks
  let f ← FB.ofBool false
  parseJWTFieldSharedLogic (skipChecks := f) h_name_len h_value_len field name
    value
    colonIndex
    valueIndex
  -- Char before value
  let charBeforeValue ← selectArrayValue maxKVPairLen field.data (← valueIndex - (← mkF 1))
  let beforeIsQuote      : FB bn254 ← eq charBeforeValue (← mkF '\"'.toNat)
  let beforeIsWhitespace : FB bn254 ← F8.isWhitespace charBeforeValue
  let beforeIsWsOrQuote ← FB.or beforeIsQuote beforeIsWhitespace
  -- Check: char before value is quote/whitespace, OR it is the colon (valueIndex - 1 == colonIndex)
  let one ← mkF 1
  let two ← mkF 2
  eq0 (← FB.and (← one - beforeIsWsOrQuote) (← (← valueIndex - one) - colonIndex))
  -- Char after value
  let charAfterValue ← selectArrayValue maxKVPairLen field.data (← valueIndex + value.len)
  let afterIsQuote      : FB bn254 ← eq charAfterValue (← mkF '\"'.toNat)
  let afterIsWhitespace : FB bn254 ← F8.isWhitespace charAfterValue
  let afterIsWsOrQuote ← FB.or afterIsQuote afterIsWhitespace
  -- Check: char after value is quote/whitespace, OR it is the field delimiter (fieldLen - 1 == valueIndex + valueLen)
  eq0 (← FB.and (← one - afterIsWsOrQuote) (← (← (← field.len - one) - valueIndex) - value.len))

  -- -- No mismatched quotes: ¬(before=quote ∧ after=whitespace) ∧ ¬(before=whitespace ∧ after=quote)
  -- let mismatch1 ← beforeIsQuote.and afterIsWhitespace
  -- let mismatch2 ←  beforeIsWhitespace.and afterIsQuote
  -- eq0 (← mismatch1 + mismatch2)

  -- No mismatched quotes
  assert_eq beforeIsQuote afterIsQuote

  -- Whitespace zones
  -- Zone A: [nameLen + 2, colonIndex)  — between closing name-quote and colon
  -- Zone B: [colonIndex + 1, valueIndex - 1)  — between colon and char before value (could be quote)
  -- Zone C: [valueIndex + valueLen + 1, fieldLen - 1)  — after char after value, before terminator
  let zoneA ← arraySelectorComplex maxKVPairLen (← name.len + two) colonIndex
  let zoneB ← arraySelectorComplex maxKVPairLen (← colonIndex + one) (← valueIndex - one)
  let zoneC ← arraySelectorComplex maxKVPairLen (← (← valueIndex + value.len) + one) (← field.len - one)
  let inZoneAB ← zoneA.zipWithM FB.or zoneB
  let inZone ← inZoneAB.zipWithM FB.or zoneC
  -- For each position in a whitespace zone, the character must be whitespace
  (inZone.zip field.data).foldlM (b := ()) fun _ (z, c) ↦ do
    let ws ← F8.isWhitespace c
    eq0 (← z.and (← not ws))

namespace parseEmailVerifiedField

open Poseidon RandomOracle Primes FiatShamir

open FString

def parses (H : HashFn) {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (field_vals : Vector (ZMod bn254) maxKVPairLen)
  (field_len : ZMod bn254)
  (name_vals : Vector (ZMod bn254) maxNameLen)
  (name_len : ZMod bn254)
  (value_vals : Vector (ZMod bn254) maxValueLen)
  (value_len : ZMod bn254)
  (colon_index_val value_index_val : ZMod bn254) :
  Prop
:=
  let charBeforeValue := field_vals.getD (value_index_val - 1).val 0 |>.val
  let charAfterValue := field_vals.getD (value_index_val + value_len).val 0 |>.val
  parseJWTFieldSharedLogic.parses H field_vals field_len name_vals name_len
    value_vals
    value_len
    colon_index_val
    value_index_val
    false
  ∧
  (charBeforeValue = /- quotes -/ 34 ∨ isWs charBeforeValue ∨
    value_index_val = colon_index_val + 1
  ) ∧
  (charAfterValue = /- quotes -/ 34 ∨ isWs charAfterValue ∨
    field_len = value_index_val + value_len + 1
  ) ∧
  ((charBeforeValue == 34) = (charAfterValue == 34)) ∧
  ∀ i : Fin maxKVPairLen,
    ((name_len + 2).val ≤ i.val ∧ i.val < colon_index_val.val) ∨
    (colon_index_val.val + 1 ≤ i.val ∧ i.val < (value_index_val - 1).val) ∨
    ((value_index_val + value_len).val + 1 ≤ i.val ∧ i.val < (field_len - 1).val) →
    isWs field_vals[i].val
 where
  isWs c := c > 8 && c < 14 || c = 32

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
  -- Ideal values
  {field_vals : Vector (ZMod bn254) maxKVPairLen}
  {field_len : ZMod bn254}
  {name_vals : Vector (ZMod bn254) maxNameLen}
  {name_len : ZMod bn254}
  {value_vals : Vector (ZMod bn254) maxValueLen}
  {value_len : ZMod bn254}
  {colon_index_val value_index_val : ZMod bn254}
  -- Conversion hypotheses
  (h_field_val : Converts FVec.conversion state field.data field_vals)
  (h_field_len : Converts F.conversion state field.len field_len)
  (h_name_val : Converts FVec.conversion state name.data name_vals)
  (h_name_len : Converts F.conversion state name.len name_len)
  (h_value_val : Converts FVec.conversion state value.data value_vals)
  (h_value_len : Converts F.conversion state value.len value_len)
  (h_ci : Converts F.conversion state colon_index colon_index_val)
  (h_vi : Converts F.conversion state value_index value_index_val)
  -- Range bounds (`w := 20` is hard-coded in the body)
  (h_name_len_w : name_len.val < 2 ^ 20)
  (h_colon_index_w : colon_index_val.val < 2 ^ 20)
  (h_value_index_w : value_index_val.val < 2 ^ 20)
  (h_field_len_w : field_len.val < 2 ^ 20)
  (h_sum_len_w : (name_len + value_len).val < 2 ^ 20)
  :
  ConvertsM FUnit.conversion
    (parseEmailVerifiedField h_name_len_lt h_value_len_lt field name value
      colon_index
      value_index
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
      (value_index_val + value_len).val < maxKVPairLen ∧
      -- /- redundant -/ value_index_val.val < maxKVPairLen ∧
      value_index_val.val < (value_index_val + value_len).val ∧
      0 < value_len.val ∧

      parses H field_vals field_len name_vals name_len value_vals value_len
        colon_index_val
        value_index_val
    )
:= by
  sorry

end parseEmailVerifiedField

end Clap.Lang
