import Clap.RandomOracle.HashFn
import Clap.Lang.Poseidon.Computes
import Clap.Lang.Data.FString.asciiDigitsToScalar
import Clap.Lang.Data.FString.isSubstring
import Clap.Lang.Data.JWT.stringBodies
import Clap.Lang.Data.JWT.enforceNotNested
import Clap.Lang.Data.JWT.parseJWTFieldWithQuotedValue
import Clap.Lang.Core.FB.not
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Keyless.Input
import Clap.Lang.Poseidon.Poseidon

open Clap Lang FString FArray Primes

/-- Verify a quoted JWT field: substring check, not-nested check, field parsing. -/
def verifyQuotedField {maxPairLen maxNameLen maxValueLen : ℕ}
    (h_name : maxNameLen ≤ maxPairLen)
    (h_value : maxValueLen ≤ maxPairLen)
    (h_pair : maxPairLen ≤ MAX_JWT_PAYLOAD_LEN)
    (json : JSONStructure bn254)
    (inp : JWT.QuotedFieldInput bn254 maxPairLen maxNameLen maxValueLen) :
    ClapM bn254 Unit
:= do
  -- Assert field is a substring of the decoded JWT payload
  FString.assertIsSubstring h_pair json.payload.data json.payloadHash
    inp.field
    inp.nameIndex
  -- Assert fieldStringBodies is a substring of stringBodies at the same index
  -- CIRCOM: AssertIsSubstring(stringBodies, jwt_payload_hash, x_field_string_bodies, x_field_len, x_index)
  FString.assertIsSubstring h_pair json.stringBodies json.payloadHash
    inp.fieldStringBodies
    inp.nameIndex
  -- Assert field is not inside nested brackets
  enforceNotNested inp.nameIndex inp.field.len json.bracketsDepthMap
  -- Parse the field structure with quoted value
  parseJWTFieldWithQuotedValue inp h_name h_value (← FB.ofBool false)

namespace verifyQuotedField

open Poseidon RandomOracle Primes FiatShamir

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
  {quoted : JWT.QuotedFieldInput bn254 maxKVPairLen maxNameLen maxValueLen}
  -- Ideal values for `quoted : JWT.QuotedFieldInput`
  {field_vals : Vector (ZMod bn254) maxKVPairLen}
  {sb_vals : Vector Bool maxKVPairLen}
  {field_len sb_len : ZMod bn254}
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
  (h_field_val : Converts FVec.conversion state quoted.field.data field_vals)
  (h_sb_val : Converts FArray.conversion state quoted.fieldStringBodies.data sb_vals)
  (h_sb_len : Converts F.conversion state quoted.fieldStringBodies.len sb_len)
  (h_field_len : Converts F.conversion state quoted.field.len field_len)
  (h_name_val : Converts FVec.conversion state quoted.name.data name_vals)
  (h_name_len : Converts F.conversion state quoted.name.len name_len)
  (h_value_val : Converts FVec.conversion state quoted.value.data value_vals)
  (h_value_len : Converts F.conversion state quoted.value.len value_len)
  (h_ci : Converts F.conversion state quoted.colonIndex colon_index_val)
  (h_vi : Converts F.conversion state quoted.valueIndex value_index_val)
  (h_ni : Converts F.conversion state quoted.nameIndex name_index_val)
  -- Conversion hypotheses for `quoted : JSONStructure`
  (h_payload          : Converts FString.conversion state json.payload payload_val)
  (h_payloadHash      : Converts F.conversion state json.payloadHash payloadHash_val)
  (h_stringBodies     : Converts FArray.conversion state json.stringBodies stringBodies_val)
  (h_bracketsDepthMap : Converts FVec.conversion state json.bracketsDepthMap bracketsDepthMap_val)
  -- Range bounds (`w := 20` is hard-coded in the body)
  (h_name_len_w : name_len.val < 2 ^ 20)
  (h_colon_index_w : colon_index_val.val < 2 ^ 20)
  (h_value_index_w : value_index_val.val < 2 ^ 20)
  (h_field_len_w : field_len.val < 2 ^ 20)
  (h_sum_len_w : (name_len + value_len).val < 2 ^ 20) :
  let payloadV := encodeV (p := bn254) MAX_JWT_PAYLOAD_LEN payload_val
  ConvertsM FUnit.conversion
    (verifyQuotedField h_name_len_lt h_value_len_lt h_pair json quoted)
    state
    ()
    ( ( (∀ i : Fin maxKVPairLen, field_vals[i].val < 2 ^ 8) ∧
        (name_index_val + field_len).val < 2 ^ minBits' MAX_JWT_PAYLOAD_LEN ∧
        name_index_val.val < MAX_JWT_PAYLOAD_LEN ∧
        name_index_val.val < (name_index_val + field_len).val
      ) ∧
      isSubstring.accepts H payloadV payloadHash_val field_vals field_len name_index_val = true ∧
      ( -- (∀ i : Fin maxKVPairLen, (if sb_vals[i] then (1 : ZMod bn254) else 0).val < 2 ^ 8) ∧
        (name_index_val + sb_len).val < 2 ^ minBits' MAX_JWT_PAYLOAD_LEN ∧
        -- name_index_val.val < MAX_JWT_PAYLOAD_LEN ∧
        name_index_val.val < (name_index_val + sb_len).val
      ) ∧
      isSubstring.accepts H (stringBodies_val.map fun b ↦ if b then 1 else 0) payloadHash_val
        (sb_vals.map fun b ↦ if b then 1 else 0)
        sb_len name_index_val
        ∧
      -- (name_index_val + field_len).val < 2 ^ minBits' MAX_JWT_PAYLOAD_LEN ∧
      -- name_index_val.val < MAX_JWT_PAYLOAD_LEN ∧
      -- name_index_val.val < (name_index_val + field_len).val ∧
      (bracketsDepthMap_val.extract name_index_val.val (name_index_val + field_len).val).sum = 0 ∧
      ( --(∀ i : Fin maxKVPairLen, field_vals[i].val < 2^8) ∧
        (∀ i : Fin maxNameLen, name_vals[i].val < 2^8) ∧
        (∀ i : Fin maxValueLen, value_vals[i].val < 2^8) ∧

        (value_index_val - 1).val < maxKVPairLen ∧
        (value_index_val + value_len).val < maxKVPairLen ∧
        0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen ∧
        0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧ -- (value_index_val - 1).val < maxKVPairLen ∧
        0 < (value_index_val + value_len + 1).val ∧ (value_index_val + value_len + 1).val ≤ maxKVPairLen ∧ (field_len - 1).val < maxKVPairLen ∧
        1 < maxKVPairLen ∧ 1 < (name_len + 1).val ∧
        value_index_val.val < maxKVPairLen ∧ value_index_val.val < (value_index_val + value_len).val ∧

        parseJWTFieldWithQuotedValue.parses H field_vals field_len name_vals name_len value_vals value_len
          sb_vals
          colon_index_val
          value_index_val
          false
      )
    )
:= sorry

end verifyQuotedField
