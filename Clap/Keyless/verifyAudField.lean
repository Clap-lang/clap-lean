import Clap.Lang.Core.FB.not
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Keyless.Input
import Clap.Lang.Poseidon.Poseidon
import Clap.Lang.Core.FB.assertBool
import Clap.Lang.Core.FB.not
import Clap.Lang.Core.F.conditionalSwap
import Clap.Keyless.Input
import Clap.Keyless.assertFieldName
import Clap.Keyless.muxFString
import Clap.Lang.Data.JWT.enforceNotNested
import Clap.Lang.Data.JWT.parseJWTFieldWithQuotedValue
import Clap.Lang.Core.FB.conditionallyAssert
import Clap.RandomOracle.HashFn

import Clap.Lang.Data.FString.isSubstring

open Clap Lang FString FArray Primes Poseidon RandomOracle

/-- Verify the audience (aud) field with override and skip support.
    CIRCOM: the `ParseJWTFieldWithQuotedValue` takes a `skip_checks` flag;
    in Lean we handle this by conditionally running the verification. -/
def verifyAudField (json : JSONStructure bn254)
  (aud : JWT.QuotedFieldInput bn254 MAX_AUD_KV_PAIR_LEN MAX_AUD_NAME_LEN MAX_AUD_VALUE_LEN)
  (audOverride : AudOverrideInput bn254) :
  ClapM bn254 Unit
:= do
  -- Validate boolean flags
  FB.assertBool audOverride.useAudOverride
  FB.assertBool audOverride.skipAudChecks
  -- Cannot skip aud checks while using override
  eq0 (← audOverride.skipAudChecks * audOverride.useAudOverride)
  let performAudChecks : FB bn254 ← not audOverride.skipAudChecks
  -- Mux the effective aud value: if useAudOverride then override else private
  let audValue ← muxFString audOverride.useAudOverride audOverride.overrideAudValue audOverride.privateAudValue
  -- Construct the effective field input with muxed value
  let audEff : JWT.QuotedFieldInput bn254 _ _ _ := { aud with value := audValue }
  -- Assert field is a substring of the decoded JWT payload (conditioned on performAudChecks)
  let field_passes ← FString.isSubstring (by decide) json.payload.data json.payloadHash audEff.field audEff.nameIndex
  FB.conditionallyAssert performAudChecks field_passes
  -- Assert fieldStringBodies matches stringBodies (conditioned on performAudChecks)
  -- CIRCOM: AssertIsSubstring(stringBodies, jwt_payload_hash, aud_field_string_bodies, aud_field_len, aud_index)
  let sb_passes ← FString.isSubstring (by decide) json.stringBodies.data json.payloadHash audEff.fieldStringBodies audEff.nameIndex
  FB.conditionallyAssert performAudChecks sb_passes
  -- Assert field is not inside nested brackets
  enforceNotNested audEff.nameIndex audEff.field.len json.bracketsDepthMap
  -- Parse the field structure, gated by skipAudChecks.
  -- CIRCOM: `succeed = checks_pass OR skip_checks; succeed === 1`
  -- We model this by passing skipChecks to the parser, which gates each constraint
  -- with `perform * constraint === 0` where `perform = NOT(skipChecks)`.
  parseJWTFieldWithQuotedValue audEff (by decide) (by decide) audOverride.skipAudChecks
  -- Verify aud name is literally "aud" (conditioned on performAudChecks)
  -- CIRCOM: aud_name[i] * performAudChecks === EXPECTED[i] * performAudChecks
  assertFieldName aud.name "aud" performAudChecks

namespace verifyAudField

end verifyAudField
