import Clap.eDSLState.Convert.Specialised
import Clap.Lang.FString.Basic

/-!
# Keyless circuit input types

The Lean-level shape of the top-level Keyless circuit's public input, and the size constants
that fix each field's width. Allocation of these into circuit variables lives in
`Clap/Keyless/Allocate.lean`, on top of the generic allocators in
`Clap/eDSLState/PublicInput.lean`.
-/

namespace Clap

open Lang

-- JWT encoding lengths
abbrev MAX_B64U_JWT_NO_SIG_LEN := 1536
abbrev MAX_B64U_JWT_HEADER_W_DOT_LEN := 300
abbrev MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN := 1472
abbrev MAX_JWT_PAYLOAD_LEN := 3 * MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN / 4 -- 1104

-- JWT field max lengths: (kv_pair, name, value)
abbrev MAX_AUD_KV_PAIR_LEN := 140
abbrev MAX_AUD_NAME_LEN    := 40
abbrev MAX_AUD_VALUE_LEN   := 120

abbrev MAX_ISS_KV_PAIR_LEN := 140
abbrev MAX_ISS_NAME_LEN    := 40
abbrev MAX_ISS_VALUE_LEN   := 120

abbrev MAX_IAT_KV_PAIR_LEN := 50
abbrev MAX_IAT_NAME_LEN    := 10
abbrev MAX_IAT_VALUE_LEN   := 45

abbrev MAX_NONCE_KV_PAIR_LEN := 105
abbrev MAX_NONCE_NAME_LEN    := 10
abbrev MAX_NONCE_VALUE_LEN   := 100

abbrev MAX_EV_KV_PAIR_LEN := 30
abbrev MAX_EV_NAME_LEN    := 20
abbrev MAX_EV_VALUE_LEN   := 10

abbrev MAX_UID_KV_PAIR_LEN := 350
abbrev MAX_UID_NAME_LEN    := 30
abbrev MAX_UID_VALUE_LEN   := 330

abbrev MAX_EXTRA_FIELD_KV_PAIR_LEN := 350

-- RSA constants
abbrev RSA_NUM_LIMBS := 32 -- 32 × 64-bit limbs = 2048 bits
abbrev RSA_KEY_BYTES := RSA_NUM_LIMBS * 8  -- 256 bytes

-- SHA2 constants
abbrev SHA2_PADDING_LEN  := 64
abbrev SHA2_NUM_BITS_LEN := 8

-- EPK constants
abbrev EPK_NUM_FIELDS := 3

/-- Email-verified field input (special parsing: value may be quoted or unquoted). -/
structure EvFieldInput (p maxPairLen maxNameLen maxValueLen : ℕ) where
  field      : FString p maxPairLen
  name       : FString p maxNameLen
  value      : FString p maxValueLen
  nameIndex  : F p
  colonIndex : F p
  valueIndex : F p

/-- JWT raw data and SHA2 signals. -/
structure JWTRawInput (p) where
  b64u_jwt_no_sig_sha2_padded   : FString p MAX_B64U_JWT_NO_SIG_LEN
  b64u_jwt_header_w_dot         : FString p MAX_B64U_JWT_HEADER_W_DOT_LEN
  b64u_jwt_payload_sha2_padded  : FString p MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN
  b64u_jwt_payload              : FString p MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN
  sha2_num_blocks               : F p
  sha2_num_bits                 : Vector (F p) SHA2_NUM_BITS_LEN
  sha2_padding                  : Vector (F p) SHA2_PADDING_LEN

/-- RSA signature input: 32 × 64-bit limbs each. -/
structure RSAInput (p) where
  signature     : Vector (F p) RSA_NUM_LIMBS
  pubkeyModulus : Vector (F p) RSA_NUM_LIMBS

/-- Audience override signals. -/
structure AudOverrideInput (p) where
  useAudOverride   : F p
  skipAudChecks    : F p
  privateAudValue  : FString p MAX_AUD_VALUE_LEN
  overrideAudValue : FString p MAX_AUD_VALUE_LEN

/-- Extra field signals. -/
structure ExtraFieldInput (p) where
  extraField      : FString p MAX_EXTRA_FIELD_KV_PAIR_LEN
  extraFieldIndex : F p
  useExtraField   : F p

/-- Cryptographic commitment signals: EPK, expiration, pepper. -/
structure CommitmentInput (p) where
  epk        : Vector (F p) EPK_NUM_FIELDS
  epkLen     : F p
  epkBlinder : F p
  expDate    : F p
  expHorizon : F p
  pepper     : F p

/-- JWT field with an unquoted value (iat). -/
structure JWT.UnquotedFieldInput (p maxPairLen maxNameLen maxValueLen : ℕ) where
  field      : FString p maxPairLen
  name       : FString p maxNameLen
  value      : FString p maxValueLen
  nameIndex  : F p
  colonIndex : F p
  valueIndex : F p

/-- JWT field with a quoted value (aud, uid, iss, nonce). -/
structure JWT.QuotedFieldInput (p maxPairLen maxNameLen maxValueLen : ℕ) where
  field             : FString p maxPairLen
  name              : FString p maxNameLen
  value             : FString p maxValueLen
  fieldStringBodies : PaddedVector (FB p) p maxPairLen
  nameIndex         : F p
  colonIndex        : F p
  valueIndex        : F p

/-- Top-level Keyless circuit input. -/
structure FKeylessInput (p) where
  jwtRaw           : JWTRawInput p
  rsa              : RSAInput p
  aud              : JWT.QuotedFieldInput p MAX_AUD_KV_PAIR_LEN MAX_AUD_NAME_LEN MAX_AUD_VALUE_LEN
  audOverride      : AudOverrideInput p
  uid              : JWT.QuotedFieldInput p MAX_UID_KV_PAIR_LEN MAX_UID_NAME_LEN MAX_UID_VALUE_LEN
  iss              : JWT.QuotedFieldInput p MAX_ISS_KV_PAIR_LEN MAX_ISS_NAME_LEN MAX_ISS_VALUE_LEN
  iat              : JWT.UnquotedFieldInput p MAX_IAT_KV_PAIR_LEN MAX_IAT_NAME_LEN MAX_IAT_VALUE_LEN
  nonce            : JWT.QuotedFieldInput p MAX_NONCE_KV_PAIR_LEN MAX_NONCE_NAME_LEN MAX_NONCE_VALUE_LEN
  ev               : EvFieldInput p MAX_EV_KV_PAIR_LEN MAX_EV_NAME_LEN MAX_EV_VALUE_LEN
  extra            : ExtraFieldInput p
  commit           : CommitmentInput p
  publicInputsHash : F p

end Clap
