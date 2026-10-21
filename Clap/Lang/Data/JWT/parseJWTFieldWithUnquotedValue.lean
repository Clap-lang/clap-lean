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
import Clap.Lang.Data.JWT.Basic
import Clap.Lang.Data.FString.isSubstring
import Mathlib.Data.List.GetD

namespace Clap.Lang

open Primes

/-- JWT field with an unquoted value (iat). -/
structure UnquotedFieldInput (maxPairLen maxNameLen maxValueLen : ℕ) where
  field      : FString bn254 maxPairLen
  name       : FString bn254 maxNameLen
  value      : FString bn254 maxValueLen
  nameIndex  : F bn254
  colonIndex : F bn254
  valueIndex : F bn254

/-- Every position in the three "gap" zones (between name/colon, colon/value, value/terminator)
must be whitespace, guarded by `perform` so `skipChecks` can bypass it. -/
private def checkWhitespaceZones {maxKVPairLen : ℕ}
    (field_data : FVec bn254 maxKVPairLen) (perform : FB bn254)
    (nameLen colonIndex valueIndex valueLen fieldLen : F bn254) : ClapM bn254 Unit := do
  -- Zone A: [name_len + 2, colonIndex)  — between closing name-quote and colon
  -- Zone B: [colonIndex + 1, valueIndex)  — between colon and value (no quote around value)
  -- Zone C: [valueIndex + value_len, field_len - 1)  — after value, before terminator
  let one ← mkF 1
  let two ← mkF 2
  let zoneA ← arraySelectorComplex maxKVPairLen (← nameLen + two) colonIndex
  let zoneB ← arraySelectorComplex maxKVPairLen (← colonIndex + one) valueIndex
  let zoneC ← arraySelectorComplex maxKVPairLen (← valueIndex + valueLen) (← fieldLen - one)
  -- Merge zones: inZone[i] = zoneA[i] ∨ zoneB[i] ∨ zoneC[i]
  let inZoneAB ← zoneA.zipWithM FB.or zoneB
  let inZone ← inZoneAB.zipWithM FB.or zoneC
  -- For each position in a whitespace zone, the character must be whitespace
  (inZone.zip field_data).toList.forM fun (z, c) ↦ do
    let ws ← F8.isWhitespace c
    guardedEq0 perform (← z.and (← not ws))

def parseJWTFieldWithUnquotedValue
  {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (fi : UnquotedFieldInput maxKVPairLen maxNameLen maxValueLen)
  (h_name  : maxNameLen  ≤ maxKVPairLen)
  (h_value : maxValueLen ≤ maxKVPairLen)
  (skipChecks  : FB bn254) :
  ClapM bn254 Unit
:= do
  -- Delegate shared structural checks
  parseJWTFieldSharedLogic h_name h_value fi.field fi.name fi.value fi.colonIndex fi.valueIndex skipChecks
  let perform : FB bn254 ← not skipChecks
  -- Check 1: whitespace in three zones
  checkWhitespaceZones fi.field.data perform fi.name.len fi.colonIndex fi.valueIndex fi.value.len fi.field.len
  -- Check 2: value must not contain ',', '}', or '"'
  -- valueSelector: 1s at [valueIndex, valueIndex + value_len)
  let valueSel ← arraySelector maxKVPairLen fi.valueIndex (← fi.valueIndex + fi.value.len)
  (valueSel.zip fi.field.data).toList.forM fun (sel, c) ↦ do
    let isForbidden ←
      FB.or
        (← FB.or (← eq c (← mkF ','.toNat)) (← eq c (← mkF '}'.toNat)))
        (← eq c (← mkF '\"'.toNat))
    -- If in value range, character must not be forbidden
    guardedEq0 perform (← sel.and isForbidden)

namespace parseJWTFieldWithUnquotedValue

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
  ¬skipChecks_val →
    parseJWTFieldSharedLogic.parses H field_vals field_len name_vals name_len
      value_vals
      value_len
      colon_index_val
      value_index_val
      false
    ∧
    (∀ i : Fin maxKVPairLen,
      ((name_len + 2).val ≤ i.val ∧ i.val < colon_index_val.val) ∨
      (colon_index_val.val + 1 ≤ i.val ∧ i.val < value_index_val.val) ∨
      ((value_index_val + value_len).val ≤ i.val ∧ i.val < (field_len - 1).val) →
      isWs field_vals[i].val
    ) ∧
    ∀ i : Fin maxKVPairLen,
      value_index_val.val ≤ i.val ∧ i.val < (value_index_val + value_len).val →
        field_vals[i].val ∉ [44, 125, 34] -- [',', '}', '"']

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
  {unquoted :     UnquotedFieldInput maxKVPairLen maxNameLen maxValueLen}
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
  (h_field_val : Converts FVec.conversion state unquoted.field.data field_vals)
  (h_field_len : Converts F.conversion state unquoted.field.len field_len)
  (h_name_val : Converts FVec.conversion state unquoted.name.data name_vals)
  (h_name_len : Converts F.conversion state unquoted.name.len name_len)
  (h_value_val : Converts FVec.conversion state unquoted.value.data value_vals)
  (h_value_len : Converts F.conversion state unquoted.value.len value_len)
  (h_ci : Converts F.conversion state unquoted.colonIndex colon_index_val)
  (h_vi : Converts F.conversion state unquoted.valueIndex value_index_val)
  (h_sk : Converts FB.conversion state skipChecks skipChecks_val)
  -- Range bounds (`w := 20` is hard-coded in the body)
  (h_name_len_w : name_len.val < 2 ^ 20)
  (h_colon_index_w : colon_index_val.val < 2 ^ 20)
  (h_value_index_w : value_index_val.val < 2 ^ 20)
  (h_field_len_w : field_len.val < 2 ^ 20)
  (h_sum_len_w : (name_len + value_len).val < 2 ^ 20)
  :
  ConvertsM FUnit.conversion
    (parseJWTFieldWithUnquotedValue unquoted h_name_len_lt h_value_len_lt
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
      -- NOT redundant, unlike the name case: `name_len.val + 1 < maxKVPairLen` above is a bound
      -- on `name_len.val` itself, so `0 < name_len.val` alone is enough to rebuild this window's
      -- `1 < (1 + name_len).val` (no wraparound, since `name_len.val` is already known small).
      -- Here `(value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen` only bounds the
      -- *wrapped* sum, not `value_len.val` itself, so `0 < value_len.val` is not enough to rule
      -- out `value_len.val` being adversarially close to `bn254` (wrapping the sum back down);
      -- keep the window fact itself.
      value_index_val.val < (value_index_val + value_len).val ∧
      0 < value_len.val ∧

      parses H field_vals field_len name_vals name_len value_vals value_len
        colon_index_val
        value_index_val
        skipChecks_val
    )
:= by
  sorry

end parseJWTFieldWithUnquotedValue
