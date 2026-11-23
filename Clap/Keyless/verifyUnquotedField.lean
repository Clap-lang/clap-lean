import Clap.RandomOracle.HashFn
import Clap.Lang.Poseidon.Computes
import Clap.Lang.Data.FString.asciiDigitsToScalar
import Clap.Lang.Data.FString.isSubstring
import Clap.Lang.Data.JWT.stringBodies
import Clap.Lang.Data.JWT.enforceNotNested
import Clap.Lang.Data.JWT.parseJWTFieldWithUnquotedValue
import Clap.Lang.Core.FB.not
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Keyless.Input
import Clap.Lang.Poseidon.Poseidon

open Clap Lang FString FArray FVec Primes

/-- Verify an unquoted JWT field: substring check, not-nested check, field parsing.
    Unlike `verifyQuotedField`, this does NOT perform a full string_bodies substring
    check. Instead, CIRCOM does a point check that the field does not start inside a
    string body (`SelectArrayValue(string_bodies, index) === 0`). -/
def verifyUnquotedField {maxPairLen maxNameLen maxValueLen : ℕ}
    (h_name : maxNameLen ≤ maxPairLen)
    (h_value : maxValueLen ≤ maxPairLen)
    (h_pair : maxPairLen ≤ MAX_JWT_PAYLOAD_LEN)
    (json : JSONStructure bn254)
    (inp : JWT.UnquotedFieldInput bn254 maxPairLen maxNameLen maxValueLen) :
    ClapM bn254 Unit
:= do
  -- Assert field is a substring of the decoded JWT payload
  FString.assertIsSubstring h_pair json.payload.data json.payloadHash
    inp.field
    inp.nameIndex
  -- Assert field is not inside nested brackets
  enforceNotNested inp.nameIndex inp.field.len json.bracketsDepthMap
  -- Assert field does not start inside a string body — CIRCOM: start_char === 0
  eq0 (← selectArrayValue _ json.stringBodies.data inp.nameIndex)
  -- Parse the field structure with unquoted value
  parseJWTFieldWithUnquotedValue inp h_name h_value (← FB.ofBool false)

namespace verifyUnquotedField

open Poseidon RandomOracle Primes FiatShamir

-- Poseidon is opaque to this proof (it sits beneath `assertIsSubstring`/`hashBytesToField`),
-- as in `Data/HashToField/hashElemsToField.lean` and `Keyless/computeJSONStructure.lean`.
attribute [local irreducible] Clap.Lang.Poseidon.poseidonBN254

lemma convertsM
  {H : HashFn}
  (h_H : Computes H)
  {state : ClapMState bn254}
  -- Circuit arguments
  {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (h_name_len_lt  : maxNameLen  ≤ maxKVPairLen)
  (h_value_len_lt : maxValueLen ≤ maxKVPairLen)
  (h_pair : maxKVPairLen ≤ MAX_JWT_PAYLOAD_LEN)
  (h_len_bound    : maxKVPairLen ≤ 1953)
  {json : JSONStructure bn254}
  {unquoted : JWT.UnquotedFieldInput bn254 maxKVPairLen maxNameLen maxValueLen}
  -- Ideal values for `unquoted : JWT.UnquotedFieldInput`
  {field_vals : Vector (ZMod bn254) maxKVPairLen}
  {field_len : ZMod bn254}
  {name_vals : Vector (ZMod bn254) maxNameLen}
  {name_len : ZMod bn254}
  {value_vals : Vector (ZMod bn254) maxValueLen}
  {value_len : ZMod bn254}
  {colon_index_val value_index_val name_index_val : ZMod bn254}
  -- Ideal values for `json : JSONStructure`
  {payload_val : String}
  {payloadHash_val : ZMod bn254}
  {stringBodies_val : Vector Bool MAX_JWT_PAYLOAD_LEN}
  {bracketsDepthMap_val : Vector (ZMod bn254) MAX_JWT_PAYLOAD_LEN}
  -- Conversion hypotheses for `json : JWT.QuotedFieldInput`
  (h_field_val : Converts FVec.conversion state unquoted.field.data field_vals)
  (h_field_len : Converts F.conversion state unquoted.field.len field_len)
  (h_name_val : Converts FVec.conversion state unquoted.name.data name_vals)
  (h_name_len : Converts F.conversion state unquoted.name.len name_len)
  (h_value_val : Converts FVec.conversion state unquoted.value.data value_vals)
  (h_value_len : Converts F.conversion state unquoted.value.len value_len)
  (h_ci : Converts F.conversion state unquoted.colonIndex colon_index_val)
  (h_vi : Converts F.conversion state unquoted.valueIndex value_index_val)
  (h_ni : Converts F.conversion state unquoted.nameIndex name_index_val)
  -- Conversion hypotheses for `unquoted : JSONStructure`
  (h_payload          : Converts FString.conversion state json.payload payload_val)
  (h_payloadHash      : Converts F.conversion state json.payloadHash payloadHash_val)
  (h_stringBodies     : Converts FArray.conversion state json.stringBodies.data stringBodies_val)
  (h_bracketsDepthMap : Converts FVec.conversion state json.bracketsDepthMap bracketsDepthMap_val)
  -- Range bounds (`w := 20` is hard-coded in the body)
  (h_name_len_w : name_len.val < 2 ^ 20)
  (h_colon_index_w : colon_index_val.val < 2 ^ 20)
  (h_value_index_w : value_index_val.val < 2 ^ 20)
  (h_field_len_w : field_len.val < 2 ^ 20)
  (h_sum_len_w : (name_len + value_len).val < 2 ^ 20) :
  let payloadV := encodeV (p := bn254) MAX_JWT_PAYLOAD_LEN payload_val
  ConvertsM FUnit.conversion
    (verifyUnquotedField h_name_len_lt h_value_len_lt h_pair json unquoted)
    state
    ()
    ( ( (∀ i : Fin maxKVPairLen, field_vals[i].val < 2 ^ 8) ∧
        (name_index_val + field_len).val < 2 ^ minBits' MAX_JWT_PAYLOAD_LEN ∧
        name_index_val.val < MAX_JWT_PAYLOAD_LEN ∧
        name_index_val.val < (name_index_val + field_len).val
      ) ∧
      isSubstring.accepts H payloadV payloadHash_val field_vals field_len name_index_val = true ∧
      ( name_index_val.val < MAX_JWT_PAYLOAD_LEN ∧
        (stringBodies_val.map fun b ↦ if b then (1 : ZMod bn254) else 0).getD name_index_val.val 0 = 0
      ) ∧
      (bracketsDepthMap_val.extract name_index_val.val (name_index_val + field_len).val).sum = 0 ∧
      ( (∀ i : Fin maxNameLen, name_vals[i].val < 2^8) ∧
        (∀ i : Fin maxValueLen, value_vals[i].val < 2^8) ∧

        name_len.val + 1 < maxKVPairLen ∧
        colon_index_val.val < maxKVPairLen ∧
        (field_len - 1).val < maxKVPairLen ∧

        0 < name_len.val ∧

        (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen ∧
        value_index_val.val < maxKVPairLen ∧
        value_index_val.val < (value_index_val + value_len).val ∧
        0 < value_len.val ∧

        parseJWTFieldWithUnquotedValue.parses H field_vals field_len name_vals name_len value_vals value_len
          colon_index_val
          value_index_val
          false
      )
    )
:= by
  sorry

end verifyUnquotedField
