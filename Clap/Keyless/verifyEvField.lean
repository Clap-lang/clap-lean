
import Clap.RandomOracle.HashFn
import Clap.Lang.Poseidon.Computes
import Clap.Lang.Data.FString.asciiDigitsToScalar
import Clap.Lang.Data.FString.isSubstring
import Clap.Lang.Data.JWT.stringBodies
import Clap.Lang.Data.JWT.enforceNotNested
import Clap.Lang.Data.JWT.emailVerifiedCheck
import Clap.Lang.Data.JWT.parseEmailVerifiedField
import Clap.Lang.Core.FB.not
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Keyless.Input
import Clap.Lang.Poseidon.Poseidon

open Clap Lang Primes

/-- Verify the email_verified field and cross-check with uid name.
    CIRCOM truth table: fail only if uidIsEmail AND NOT evInJwt. -/
def verifyEvField (json : JSONStructure bn254)
  (ev : EvFieldInput bn254 MAX_EV_KV_PAIR_LEN MAX_EV_NAME_LEN MAX_EV_VALUE_LEN)
  (uidName : FString bn254 MAX_UID_NAME_LEN) :
  ClapM bn254 Unit
:= do
  -- Cross-check: get uidIsEmail from emailVerifiedCheck
  let uidIsEmail ←
    emailVerifiedCheck
      uidName
      ev.name
      ev.value
  -- Check if ev field is in JWT (non-asserting)
  let evInJwt ←
    FString.isSubstring (by decide) json.payload.data json.payloadHash
      ev.field
      ev.nameIndex
  FB.conditionallyAssert uidIsEmail evInJwt
  -- Assert not inside nested brackets
  enforceNotNested ev.nameIndex ev.field.len json.bracketsDepthMap
  -- Parse the email_verified field (allows both quoted and unquoted true/false)
  parseEmailVerifiedField (by decide) (by decide) ev.field ev.name ev.value
    ev.colonIndex
    ev.valueIndex

namespace verifyEvField

open Poseidon RandomOracle Primes FiatShamir

-- Poseidon is opaque to this proof (it sits beneath `isSubstring`/`hashBytesToField`), as in
-- `verifyQuotedField.lean` and `Keyless/computeJSONStructure.lean`.
attribute [local irreducible] Clap.Lang.Poseidon.poseidonBN254

lemma convertsM
  {H : HashFn}
  (h_H : Computes H)
  {state : ClapMState bn254}
  {json    : JSONStructure bn254}
  {ev      : EvFieldInput bn254 MAX_EV_KV_PAIR_LEN MAX_EV_NAME_LEN MAX_EV_VALUE_LEN}
  {uidName : FString bn254 MAX_UID_NAME_LEN}
  -- Ideal values
  {field_vals : Vector (ZMod bn254) MAX_EV_KV_PAIR_LEN}
  {field_len : ZMod bn254}
  {name_index_val colon_index_val value_index_val : ZMod bn254}
  {uidName_val evName_val evValue_val : String}
  {payload_val : String}
  {payloadHash_val : ZMod bn254}
  {bracketsDepthMap_val : Vector (ZMod bn254) MAX_JWT_PAYLOAD_LEN}
  -- `ev.field`: decomposed only — nothing downstream needs it as a whole string.
  (h_field_val : Converts FVec.conversion state ev.field.data field_vals)
  (h_field_len : Converts F.conversion state ev.field.len field_len)
  (h_ni : Converts F.conversion state ev.nameIndex name_index_val)
  (h_ci : Converts F.conversion state ev.colonIndex colon_index_val)
  (h_vi : Converts F.conversion state ev.valueIndex value_index_val)
  -- `uidName` / `ev.name` / `ev.value`: whole-string facts, required by `emailVerifiedCheck`
  -- (it compares them against string literals). `parseEmailVerifiedField`'s decomposed `FVec`/`F`
  -- facts are bridged from these in the proof via `FString.converts_data` / `FString.converts_len`
  -- — the same bridge `verifyQuotedField.convertsM` uses for `json.payload`.
  (h_uidName : Converts FString.conversion state uidName uidName_val)
  (h_evName : Converts FString.conversion state ev.name evName_val)
  (h_evValue : Converts FString.conversion state ev.value evValue_val)
  -- `json`
  (h_payload          : Converts FString.conversion state json.payload payload_val)
  (h_payloadHash      : Converts F.conversion state json.payloadHash payloadHash_val)
  (h_bracketsDepthMap : Converts FVec.conversion state json.bracketsDepthMap bracketsDepthMap_val)
  -- Data-dependent side conditions `emailVerifiedCheck.convertsM` needs: facts about the free
  -- String *values*, so — unlike the constant-only side conditions it also needs (`256 < p`, the
  -- three width bounds, the three literal-length facts) — they cannot be discharged by `decide`
  -- and must be supplied here.
  (h_uidName_len : uidName_val.length < MAX_UID_NAME_LEN)
  (h_evName_len  : evName_val.length  < MAX_EV_NAME_LEN)
  (h_evValue_len : evValue_val.length < MAX_EV_VALUE_LEN)
  (h_uidName_chars : ∀ c ∈ uidName_val.toList, c.toNat < 256)
  (h_evName_chars  : ∀ c ∈ evName_val.toList,  c.toNat < 256)
  (h_evValue_chars : ∀ c ∈ evValue_val.toList, c.toNat < 256)
  -- Range bounds `parseEmailVerifiedField.convertsM` needs with no other source: `colon_index_val`
  -- / `value_index_val` / `field_len` are free top-level inputs. (The matching bounds on the
  -- name/value lengths are derived in the proof from `h_evName_len` / `h_evValue_len` instead —
  -- unlike in `verifyQuotedField`, `ev.name` / `ev.value` are tied to actual strings here.)
  (h_colon_index_w : colon_index_val.val < 2 ^ 20)
  (h_value_index_w : value_index_val.val < 2 ^ 20)
  (h_field_len_w : field_len.val < 2 ^ 20)
  :
  let payloadV := FString.encodeV (p := bn254) MAX_JWT_PAYLOAD_LEN payload_val
  let nameV := FString.encodeV (p := bn254) MAX_EV_NAME_LEN evName_val
  let nameLen : ZMod bn254 := evName_val.length
  let valueV := FString.encodeV (p := bn254) MAX_EV_VALUE_LEN evValue_val
  let valueLen : ZMod bn254 := evValue_val.length
  ConvertsM FUnit.conversion
    (verifyEvField json ev uidName)
    state
    ()
    ( -- From `emailVerifiedCheck.convertsM`.
      ( uidName_val = "email" →
        evName_val = "email_verified" ∧ (evValue_val = "true" ∨ evValue_val = "\"true\"")
      ) ∧
      -- From `isSubstring.convertsM`.
      ( (∀ i : Fin MAX_EV_KV_PAIR_LEN, field_vals[i].val < 2 ^ 8) ∧
        (name_index_val + field_len).val < 2 ^ minBits' MAX_JWT_PAYLOAD_LEN ∧
        name_index_val.val < MAX_JWT_PAYLOAD_LEN ∧
        name_index_val.val < (name_index_val + field_len).val
      ) ∧
      -- From `FB.conditionallyAssert uidIsEmail evInJwt`
      ( decide (uidName_val = "email") = true →
          FString.isSubstring.accepts H payloadV payloadHash_val field_vals field_len name_index_val
      ) ∧
      -- From `enforceNotNested.convertsM`
      ( -- redundant: (name_index_val + field_len).val < 2 ^ minBits' MAX_JWT_PAYLOAD_LEN ∧
        -- redundant: name_index_val.val < MAX_JWT_PAYLOAD_LEN ∧
        -- redundant: name_index_val.val < (name_index_val + field_len).val ∧
        (bracketsDepthMap_val.extract name_index_val.val (name_index_val + field_len).val).sum = 0
      ) ∧
      -- From `parseEmailVerifiedField.convertsM`
      ( (∀ i : Fin MAX_EV_KV_PAIR_LEN, field_vals[i].val < 2 ^ 8) ∧
        (∀ i : Fin MAX_EV_NAME_LEN, nameV[i].val < 2 ^ 8) ∧
        (∀ i : Fin MAX_EV_VALUE_LEN, valueV[i].val < 2 ^ 8) ∧

        nameLen.val + 1 < MAX_EV_KV_PAIR_LEN ∧
        colon_index_val.val < MAX_EV_KV_PAIR_LEN ∧
        (field_len - 1).val < MAX_EV_KV_PAIR_LEN ∧

        0 < nameLen.val ∧

        (value_index_val + valueLen).val < MAX_EV_KV_PAIR_LEN ∧
        value_index_val.val < (value_index_val + valueLen).val ∧
        0 < valueLen.val ∧

        parseEmailVerifiedField.parses H field_vals field_len nameV nameLen valueV valueLen
          colon_index_val
          value_index_val
      )
    )
:= by sorry

end verifyEvField
