import Clap.Lang
import Clap.Wheels
import Clap.Array
import Clap.FString
import Clap.HashToField
import Clap.JWT
import Clap.Poseidon.Poseidon
import Clap.Base64Len

/-!
# Aptos Keyless Circuit

Top-level ZK circuit for Aptos Keyless accounts, translated from the CIRCOM reference at
`aptos-labs/keyless-zk-proofs/circuit/templates/{main,keyless}.circom`.

The circuit proves that a user controls a JWT from an OIDC provider (e.g., Google) without
revealing the JWT itself. It verifies JWT structure, RSA signature, field parsing, nonce
commitment, identity commitment, and produces a public inputs hash.

## References
- CIRCOM: https://github.com/aptos-labs/keyless-zk-proofs/tree/main/circuit/templates
- AIP-061: https://github.com/aptos-foundation/AIPs/blob/main/aips/aip-061-keyless-accounts.md
-/

namespace Keyless

open Clap.Lang Core Primes

-- JWT encoding lengths
abbrev MAX_B64U_JWT_NO_SIG_LEN := 1536
abbrev MAX_B64U_JWT_HEADER_W_DOT_LEN := 300
abbrev MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN := 1472
abbrev MAX_JWT_PAYLOAD_LEN := 3 * MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN / 4 -- 1104

-- JWT field max lengths: (kv_pair, name, value)
abbrev MAX_AUD_KV_PAIR_LEN := 140
abbrev MAX_AUD_NAME_LEN := 40
abbrev MAX_AUD_VALUE_LEN := 120

abbrev MAX_ISS_KV_PAIR_LEN := 140
abbrev MAX_ISS_NAME_LEN := 40
abbrev MAX_ISS_VALUE_LEN := 120

abbrev MAX_IAT_KV_PAIR_LEN := 50
abbrev MAX_IAT_NAME_LEN := 10
abbrev MAX_IAT_VALUE_LEN := 45

abbrev MAX_NONCE_KV_PAIR_LEN := 105
abbrev MAX_NONCE_NAME_LEN := 10
abbrev MAX_NONCE_VALUE_LEN := 100

abbrev MAX_EV_KV_PAIR_LEN := 30
abbrev MAX_EV_NAME_LEN := 20
abbrev MAX_EV_VALUE_LEN := 10

abbrev MAX_UID_KV_PAIR_LEN := 350
abbrev MAX_UID_NAME_LEN := 30
abbrev MAX_UID_VALUE_LEN := 330

abbrev MAX_EXTRA_FIELD_KV_PAIR_LEN := 350

-- RSA constants
abbrev RSA_NUM_LIMBS := 32 -- 32 × 64-bit limbs = 2048 bits
abbrev RSA_KEY_BYTES := RSA_NUM_LIMBS * 8  -- 256 bytes

-- SHA2 constants
abbrev SHA2_PADDING_LEN := 64
abbrev SHA2_NUM_BITS_LEN := 8

-- EPK constants
abbrev EPK_NUM_FIELDS := 3

-- Known field name lengths
abbrev AUD_NAME_LEN := 3   -- "aud"
abbrev ISS_NAME_LEN := 3   -- "iss"
abbrev IAT_NAME_LEN := 3   -- "iat"
abbrev NONCE_NAME_LEN := 5 -- "nonce"
abbrev EV_NAME_LEN := 14   -- "email_verified"

variable [Core bn254]

/-- Stub for SHA2-256 padding verification. WIP. -/
def SHA2_256_PaddingVerify
    (_data : FString bn254 MAX_B64U_JWT_NO_SIG_LEN)
    (_sha2_num_blocks : F bn254)
    (_sha2_num_bits : Vector (F bn254) SHA2_NUM_BITS_LEN)
    (_sha2_padding : Vector (F bn254) SHA2_PADDING_LEN)
    : Option Unit :=
  pure ()

/-- Stub for SHA2-256 hash of pre-padded data. WIP.
    Returns the SHA2-256 hash as 4 × 64-bit limbs. -/
def SHA2_256_Prepadded_Hash
    (_data : FString bn254 MAX_B64U_JWT_NO_SIG_LEN)
    (_sha2_num_blocks : F bn254)
    : Option (Vector (F bn254) 4) :=
  pure (Vector.replicate 4 0)

/-- Stub for RSA-2048 PKCS#1 v1.5 signature verification. WIP. -/
def RSA_2048_e_65537_PKCS1_V1_5_Verify
    (_sha2_hash : Vector (F bn254) 4)
    (_signature : Vector (F bn254) RSA_NUM_LIMBS)
    (_pubkey_modulus : Vector (F bn254) RSA_NUM_LIMBS)
    : Option Unit :=
  pure ()

/-- JWT field with a quoted value (aud, uid, iss, nonce). -/
structure QuotedFieldInput (maxPairLen maxNameLen maxValueLen : ℕ) where
  field               : FString bn254 maxPairLen
  name                : FString bn254 maxNameLen
  value               : FString bn254 maxValueLen
  field_string_bodies : Vector (FB bn254) maxPairLen
  name_index          : F bn254
  colon_index         : F bn254
  value_index         : F bn254

/-- JWT field with an unquoted value (iat). -/
structure UnquotedFieldInput (maxPairLen maxNameLen maxValueLen : ℕ) where
  field       : FString bn254 maxPairLen
  name        : FString bn254 maxNameLen
  value       : FString bn254 maxValueLen
  name_index  : F bn254
  colon_index : F bn254
  value_index : F bn254

/-- Email-verified field input (special parsing: value may be quoted or unquoted). -/
structure EvFieldInput (maxPairLen maxNameLen maxValueLen : ℕ) where
  field       : FString bn254 maxPairLen
  name        : FString bn254 maxNameLen
  value       : FString bn254 maxValueLen
  name_index  : F bn254
  colon_index : F bn254
  value_index : F bn254

/-- JWT raw data and SHA2 signals. -/
structure JWTRawInput where
  b64u_jwt_no_sig_sha2_padded   : FString bn254 MAX_B64U_JWT_NO_SIG_LEN
  b64u_jwt_header_w_dot         : FString bn254 MAX_B64U_JWT_HEADER_W_DOT_LEN
  b64u_jwt_payload_sha2_padded  : FString bn254 MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN
  b64u_jwt_payload              : FString bn254 MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN
  sha2_num_blocks               : F bn254
  sha2_num_bits                 : Vector (F bn254) SHA2_NUM_BITS_LEN
  sha2_padding                  : Vector (F bn254) SHA2_PADDING_LEN

/-- RSA signature input: 32 × 64-bit limbs each. -/
structure RSAInput where
  signature      : Vector (F bn254) RSA_NUM_LIMBS
  pubkey_modulus : Vector (F bn254) RSA_NUM_LIMBS

/-- Audience override signals. -/
structure AudOverrideInput where
  use_aud_override   : F bn254
  skip_aud_checks    : F bn254
  private_aud_value  : FString bn254 MAX_AUD_VALUE_LEN
  override_aud_value : FString bn254 MAX_AUD_VALUE_LEN

/-- Extra field signals. -/
structure ExtraFieldInput where
  extra_field : FString bn254 MAX_EXTRA_FIELD_KV_PAIR_LEN
  extra_field_index : F bn254
  use_extra_field : F bn254

/-- Cryptographic commitment signals: EPK, expiration, pepper. -/
structure CommitmentInput where
  epk         : Vector (F bn254) EPK_NUM_FIELDS
  epk_len     : F bn254
  epk_blinder : F bn254
  exp_date    : F bn254
  exp_horizon : F bn254
  pepper      : F bn254

/-- Top-level Keyless circuit input. -/
structure KeylessInput where
  jwt_raw            : JWTRawInput
  rsa                : RSAInput
  aud                : QuotedFieldInput MAX_AUD_KV_PAIR_LEN MAX_AUD_NAME_LEN MAX_AUD_VALUE_LEN
  aud_override       : AudOverrideInput
  uid                : QuotedFieldInput MAX_UID_KV_PAIR_LEN MAX_UID_NAME_LEN MAX_UID_VALUE_LEN
  iss                : QuotedFieldInput MAX_ISS_KV_PAIR_LEN MAX_ISS_NAME_LEN MAX_ISS_VALUE_LEN
  iat                : UnquotedFieldInput MAX_IAT_KV_PAIR_LEN MAX_IAT_NAME_LEN MAX_IAT_VALUE_LEN
  nonce              : QuotedFieldInput MAX_NONCE_KV_PAIR_LEN MAX_NONCE_NAME_LEN MAX_NONCE_VALUE_LEN
  ev                 : EvFieldInput MAX_EV_KV_PAIR_LEN MAX_EV_NAME_LEN MAX_EV_VALUE_LEN
  extra              : ExtraFieldInput
  commit             : CommitmentInput
  public_inputs_hash : F bn254

/-- Precomputed JSON structural data for the decoded JWT payload. -/
structure JSONStructure where
  payload            : FString bn254 MAX_JWT_PAYLOAD_LEN
  payload_hash       : F bn254
  string_bodies      : Vector (FB bn254) MAX_JWT_PAYLOAD_LEN
  brackets_depth_map : List (F bn254)

end Keyless
