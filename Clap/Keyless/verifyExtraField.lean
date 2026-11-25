import Clap.Lang.Core.FB.not
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Keyless.Input
import Clap.Lang.Poseidon.Poseidon
import Clap.Lang.Core.FB.assertBool
import Clap.Keyless.Input
import Clap.Lang.Data.JWT.enforceNotNested
import Clap.Lang.Core.FB.conditionallyAssert
import Clap.RandomOracle.HashFn

import Clap.Lang.Data.FString.isSubstring

open Clap Lang FString FArray Primes Poseidon RandomOracle

/-- Verify the extra field (optional). -/
def verifyExtraField (json : JSONStructure bn254)
  (extra : ExtraFieldInput bn254) :
  ClapM bn254 Unit
:= do
  -- useExtraField must be boolean
  FB.assertBool extra.useExtraField
  -- Check substring
  let efPasses ←
    FString.isSubstring (by decide) json.payload.data json.payloadHash
      extra.extraField
      extra.extraFieldIndex
  -- Assert not inside nested brackets
  enforceNotNested extra.extraFieldIndex extra.extraField.len json.bracketsDepthMap
  FB.conditionallyAssert extra.useExtraField efPasses
  -- Assert extra field does not start inside a string body
  -- CIRCOM: ef_start_char === 0
  eq0 (← selectArrayValue _ json.stringBodies.data extra.extraFieldIndex)

namespace verifyExtraField

lemma convertsM
  {H : HashFn}
  (h_H : Computes H)
  {state : ClapMState bn254}
  {extra : ExtraFieldInput bn254}
  {json  : JSONStructure bn254}
  -- Ideal values
  {payload_val : String}
  {payloadHash_val : ZMod bn254}
  {stringBodies_val : Vector Bool MAX_JWT_PAYLOAD_LEN}
  {bracketsDepthMap_val : Vector (ZMod bn254) MAX_JWT_PAYLOAD_LEN}
  {useExtra_val extraFieldIndex_val : ZMod bn254}
  {extra_vals : Vector (ZMod bn254) MAX_EXTRA_FIELD_KV_PAIR_LEN}
  {extra_len : ZMod bn254}
  -- `json`
  (h_payload          : Converts FString.conversion state json.payload payload_val)
  (h_payloadHash      : Converts F.conversion state json.payloadHash payloadHash_val)
  (h_stringBodies     : Converts FArray.conversion state json.stringBodies.data stringBodies_val)
  (h_bracketsDepthMap : Converts FVec.conversion state json.bracketsDepthMap bracketsDepthMap_val)
  -- `extra`
  (h_extra_data : Converts FVec.conversion state extra.extraField.data extra_vals)
  (h_extra_len : Converts F.conversion state extra.extraField.len extra_len)
  (h_use_extra  : Converts F.conversion state extra.useExtraField useExtra_val)
  (h_extraFieldIndex : Converts F.conversion state extra.extraFieldIndex extraFieldIndex_val) :
  let payloadV := encodeV (p := bn254) MAX_JWT_PAYLOAD_LEN payload_val
  ConvertsM FUnit.conversion (verifyExtraField json extra) state
    ()
    ( -- From `FB.assertBool`
      (useExtra_val = 0 ∨ useExtra_val = 1) ∧
      -- From `isSubstring.convertsM`
      ( (∀ i : Fin MAX_EXTRA_FIELD_KV_PAIR_LEN, extra_vals[i].val < 2 ^ 8) ∧
        (extraFieldIndex_val + extra_len).val < 2 ^ minBits' MAX_JWT_PAYLOAD_LEN ∧
        extraFieldIndex_val.val < MAX_JWT_PAYLOAD_LEN ∧
        extraFieldIndex_val.val < (extraFieldIndex_val + extra_len).val
      ) ∧
      -- From `enforceNotNested.convertsM` (its three range conjuncts duplicate the block above)
      (bracketsDepthMap_val.extract extraFieldIndex_val.val
        (extraFieldIndex_val + extra_len).val
      ).sum = 0 ∧
      -- From `FB.conditionallyAssert`
      (useExtra_val = 1 →
        FString.isSubstring.accepts H payloadV payloadHash_val extra_vals extra_len
          extraFieldIndex_val
      ) ∧
      -- From `selectArrayValue`/`eq0` — CIRCOM: ef_start_char === 0
      ( extraFieldIndex_val.val < MAX_JWT_PAYLOAD_LEN ∧
        stringBodies_val.getD extraFieldIndex_val.val false = false
      )
    )
:= sorry

end verifyExtraField
