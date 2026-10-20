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
  -- Zone A: [name_len + 2, colonIndex)  — between closing name-quote and colon
  -- Zone B: [colonIndex + 1, valueIndex)  — between colon and value (no quote around value)
  -- Zone C: [valueIndex + value_len, field_len - 1)  — after value, before terminator
  let one ← mkF 1
  let two ← mkF 2
  let zoneA ←
    arraySelectorComplex maxKVPairLen (← fi.name.len + two) fi.colonIndex
  let zoneB ←
    arraySelectorComplex maxKVPairLen (← fi.colonIndex + one) fi.valueIndex
  let zoneC ←
    arraySelectorComplex maxKVPairLen (← fi.valueIndex + fi.value.len) (← fi.field.len - one)
  -- Merge zones: inZone[i] = zoneA[i] ∨ zoneB[i] ∨ zoneC[i]
  let inZoneAB ← zoneA.zipWithM FB.or zoneB
  let inZone ← inZoneAB.zipWithM FB.or zoneC

  -- For each position in a whitespace zone, the character must be whitespace
  (inZone.zip fi.field.data).toList.forM fun (z, c) ↦ do
    let ws ← F8.isWhitespace c
    guardedEq0 perform (← z.and (← not ws))
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

end parseJWTFieldWithUnquotedValue
